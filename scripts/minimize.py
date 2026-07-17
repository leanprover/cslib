#!/usr/bin/env python3
"""
minimize.py — minimize and normalize the imports of every CSLib module.

Runs four phases, in this order:

  1. Remove transitively-redundant imports.
     If a file imports both B and C and B already (publicly) re-exports C, the import
     of C is redundant and is dropped. This is provable from the import graph, so no
     compilation is needed.

  2. Empirically minimize the remaining imports.
     Processing files in reverse-topological order (dependencies first), each unpinned
     import is removed, the module is rebuilt with `lake build <module>`, and the import
     is kept out only if the module still compiles. If a file no longer builds even before
     any removal (because an earlier file dropped an import it was inheriting), imports from
     its original transitive closure are restored until it compiles again, then reduction
     proceeds.

  3. Restore `Cslib.Init` reachability, minimally.
     `Cslib.Init` only installs linters / default tactics, so a build-based oracle happily
     drops it — but `lake exe checkInitImports` requires every module to import it
     (transitively). Phase 3 adds `public import Cslib.Init` to the smallest set of modules
     needed so that all of them reach it again.

  4. Sort the import block of every file into CSLib's canonical order:

         module[ -- annotations]

         public meta import <alphabetical>
         public import <alphabetical>

         meta import <alphabetical>
         import <alphabetical>

         <content>

Imports excluded from removal in phases 1 & 2 (never touched):
  * meta imports (their elaboration-time closure differs from the regular one);
  * imports carrying an inline `-- shake: keep` comment;
  * every import inside a file whose `module` line has `-- shake: keep-all`;
  * `shake: keep-downstream` modules other than `Cslib.Init` (currently: HasFresh).
`Cslib.Init` is deliberately *not* pinned here — phase 3 owns it.

Usage:
  scripts/minimize.py                 # run all four phases, then a final verification
  scripts/minimize.py --dry-run       # phases 1/3/4 report only; skips the phase-2 builds
  scripts/minimize.py --phases 1,3,4  # run a subset of phases
  scripts/minimize.py --resume        # continue an interrupted phase-2 pass
  scripts/minimize.py --limit N       # phase 2: only process the first N eligible files

The final `lake build` and `lake exe checkInitImports` are always run (unless --dry-run)
so the tree is left green.
"""
from __future__ import annotations
import argparse, json, os, re, subprocess, sys, time

# --------------------------------------------------------------------------- paths
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(SCRIPT_DIR)
PKGS = os.path.join(ROOT, ".lake", "packages")
STATE_FILE = os.path.join(SCRIPT_DIR, ".minimize-state.json")

# Modules exempt from the Cslib.Init requirement (see scripts/CheckInitImports.lean).
INIT_EXCEPTIONS = {"Cslib.Foundations.Lint.Basic", "Cslib.Init"}
INIT = "Cslib.Init"


def toolchain_src() -> str | None:
    try:
        tc = open(os.path.join(ROOT, "lean-toolchain")).read().strip()
    except OSError:
        return None
    name = tc.replace("/", "--").replace(":", "---")  # leanprover/lean4:v4.x -> ...---v4.x
    elan = os.environ.get("ELAN_HOME", os.path.expanduser("~/.elan"))
    path = os.path.join(elan, "toolchains", name, "src", "lean")
    return path if os.path.isdir(path) else None


# --------------------------------------------------------------------------- indexing
def index_modules() -> dict[str, str]:
    """Map every reachable module name to its .lean source file."""
    mod2file: dict[str, str] = {}

    def add_tree(base, subdirs=None):
        for dp, dn, fns in os.walk(base):
            dn[:] = [d for d in dn if d not in (".lake", ".git")]
            for fn in fns:
                if not fn.endswith(".lean"):
                    continue
                full = os.path.join(dp, fn)
                rel = os.path.relpath(full, base)
                if subdirs is not None and rel.split(os.sep)[0].removesuffix(".lean") not in subdirs:
                    continue
                mod2file.setdefault(rel.removesuffix(".lean").replace(os.sep, "."), full)

    add_tree(ROOT, ["Cslib", "CslibTests"])
    src = toolchain_src()
    if src:
        add_tree(src)
    if os.path.isdir(PKGS):
        for p in sorted(os.listdir(PKGS)):
            add_tree(os.path.join(PKGS, p))
    return mod2file


IMPORT_RE = re.compile(
    r"^(?P<mods>(?:public\s+|private\s+|meta\s+)*)import\s+(?P<all>all\s+)?"
    r"(?P<name>[A-Za-z_][\w.À-￿]*)\s*(?P<cmt>--.*)?$")
MODULE_RE = re.compile(r"^module\b(?P<rest>.*)$")
DECL_RE = re.compile(
    r"^\s*(@\[[^\]]*\]\s*)?((public|private|protected|meta|noncomputable|partial|unsafe|scoped"
    r"|local)\s+)*(theorem|lemma|def|instance|structure|inductive|abbrev|class|opaque|axiom"
    r"|example|macro|macro_rules|notation|syntax|elab|attribute|deriving|#guard|#check|#eval)\b",
    re.M)


class Import:
    __slots__ = ("name", "line", "pub", "meta", "keep", "cmt", "all")

    def __init__(self, name, line, pub, meta, keep, cmt, all=False):
        self.name, self.line, self.pub, self.meta = name, line, pub, meta
        self.keep, self.cmt, self.all = keep, cmt, all

    def rank(self):
        return 0 if self.pub and self.meta else 1 if self.pub else 2 if self.meta else 3

    def render(self):
        kw = {0: "public meta import", 1: "public import",
              2: "meta import", 3: "import"}[self.rank()]
        allkw = "all " if self.all else ""
        return f"{kw} {allkw}{self.name}{self.cmt}\n"


class Model:
    """Parsed import graph over all indexed modules, plus mutable in-repo state."""

    def __init__(self):
        self.mod2file = index_modules()
        self.parsed: dict[str, tuple[bool, list[Import]]] = {}
        self.keep_all: set[str] = set()
        self.keep_downstream: set[str] = set()
        self._pub: dict[str, set[str]] = {}  # memoized public closures
        self.targets = sorted(
            m for m in self.mod2file
            if (m == "Cslib" or m.startswith("Cslib.") or m == "CslibTests"
                or m.startswith("CslibTests."))
            and self.mod2file[m].startswith(ROOT)
            and os.sep + ".lake" + os.sep not in self.mod2file[m])
        self.target_set = set(self.targets)
        for m in self.targets:
            self.parse(m)
        # pristine snapshot for the phase-2 restore rule
        self.original_visible = {m: self.visible(m) for m in self.targets}

    # ---- parsing -----------------------------------------------------------
    def parse(self, mod):
        if mod in self.parsed:
            return self.parsed[mod]
        f = self.mod2file.get(mod)
        if f is None:
            self.parsed[mod] = (True, [])
            return self.parsed[mod]
        imports, is_module, block = [], False, 0
        with open(f, encoding="utf-8") as fh:
            for i, line in enumerate(fh, 1):
                s = line.strip()
                if block:
                    if "-/" in s:
                        block -= 1
                    continue
                if s.startswith("/-"):
                    if "-/" not in s:
                        block += 1
                    continue
                if s.startswith("--") or not s:
                    continue
                mm = MODULE_RE.match(s)
                if mm:
                    is_module = True
                    if "shake: keep-all" in mm.group("rest"):
                        self.keep_all.add(mod)
                    if "shake: keep-downstream" in mm.group("rest"):
                        self.keep_downstream.add(mod)
                    continue
                code, _, comment = s.partition("--")
                m = IMPORT_RE.match(code.strip() + (" --" + comment if comment else ""))
                if m:
                    imports.append(Import(
                        name=m.group("name"), line=i,
                        pub="public" in (m.group("mods") or ""),
                        meta="meta" in (m.group("mods") or ""),
                        keep="shake: keep" in comment,
                        cmt=(" " + m.group("cmt")) if m.group("cmt") else "",
                        all=bool(m.group("all"))))
                    continue
                if s.startswith(("prelude", "set_option", "open ")):
                    continue
                break
        self.parsed[mod] = (is_module, imports)
        return self.parsed[mod]

    def imports(self, mod):
        return self.parsed[mod][1]

    def is_module(self, mod):
        return self.parsed[mod][0]

    def has_decls(self, mod):
        return bool(DECL_RE.search(open(self.mod2file[mod], encoding="utf-8").read()))

    # ---- closures ----------------------------------------------------------
    def pub_closure(self, mod, _stack=None):
        """Modules re-exported (transitively, publicly) by importing `mod`, incl. mod."""
        cached = self._pub.get(mod)
        if cached is not None:
            return cached
        if _stack is None:
            _stack = set()
        if mod in _stack:
            return {mod}  # cycle guard: don't cache a partial result
        _stack.add(mod)
        is_mod, imps = self.parse(mod)
        acc = {mod}
        complete = True
        for im in imps:
            if im.meta:
                continue
            if im.pub or not is_mod:
                if im.name in _stack:
                    complete = False
                    acc.add(im.name)
                else:
                    acc |= self.pub_closure(im.name, _stack)
        _stack.discard(mod)
        if complete:
            self._pub[mod] = acc
        return acc

    def visible(self, mod):
        acc = set()
        for im in self.imports(mod):
            if not im.meta:
                acc |= self.pub_closure(im.name)
        return acc

    def reaches_init(self, mod):
        """True if `mod` transitively imports Cslib.Init (public or private edges)."""
        seen, stack = set(), [im.name for im in self.imports(mod)]
        while stack:
            x = stack.pop()
            if x == INIT:
                return True
            if x in seen:
                continue
            seen.add(x)
            if x in self.parsed:
                stack.extend(im.name for im in self.imports(x))
            # external modules never lead back to Cslib.Init
        return False

    def topo(self):
        """In-repo modules, dependencies before dependents."""
        order, mark = [], {}

        def visit(m):
            if mark.get(m):
                return
            mark[m] = 1
            for im in self.imports(m):
                if im.name in self.target_set:
                    visit(im.name)
            order.append(m)

        for m in self.targets:
            visit(m)
        return order

    # ---- pinning -----------------------------------------------------------
    def pinned(self, mod, im: Import):
        """True if `im` must never be removed in phases 1 & 2."""
        if im.meta or im.keep or im.all:
            return True
        if im.name in self.keep_downstream and im.name != INIT:
            return True
        return False

    # ---- file writing ------------------------------------------------------
    def write_block(self, mod, imports):
        """Overwrite `mod`'s import block with `imports` (order preserved), keeping the
        surrounding file intact. Blank lines around the block are left as-is here; phase 4
        normalizes them."""
        self._pub.clear()  # graph is changing; drop memoized closures
        path = self.mod2file[mod]
        with open(path, encoding="utf-8") as fh:
            lines = fh.readlines()
        old = self.imports(mod)
        if not old:
            # no existing block: insert after `module` (or at file head for legacy files)
            if imports:
                mi = next((i for i, l in enumerate(lines) if MODULE_RE.match(l.strip())), None)
                pos = (mi + 1) if mi is not None else 0
                ins = ["\n"] + [im.render() for im in imports] + ["\n"]
                lines = lines[:pos] + ins + lines[pos:]
                with open(path, "w", encoding="utf-8") as fh:
                    fh.writelines(lines)
            return
        first = min(im.line for im in old)
        last = max(im.line for im in old)
        # keep any non-import lines interleaved in the original block
        orig_lines = {im.line for im in old}
        interleaved = [lines[i - 1] for i in range(first, last + 1) if i not in orig_lines]
        body = [im.render() for im in imports] + interleaved
        lines = lines[:first - 1] + body + lines[last:]
        with open(path, "w", encoding="utf-8") as fh:
            fh.writelines(lines)
        # re-parse so line numbers stay consistent
        del self.parsed[mod]
        self.parse(mod)


# --------------------------------------------------------------------------- build
def build(mod):
    r = subprocess.run(["lake", "build", mod], cwd=ROOT,
                       capture_output=True, text=True, timeout=1800)
    return r.returncode == 0


def full_build():
    r = subprocess.run(["lake", "build"], cwd=ROOT)
    return r.returncode == 0


def check_init_imports():
    r = subprocess.run(["lake", "exe", "checkInitImports"], cwd=ROOT,
                       capture_output=True, text=True, timeout=1800)
    return r.returncode == 0, r.stdout + r.stderr


def log(msg):
    print(msg, flush=True)


# --------------------------------------------------------------------------- phase 1
def phase1(model: Model, dry: bool):
    log("\n=== phase 1: remove transitively-redundant imports ===")
    removed = 0
    for A in model.targets:
        if A in model.keep_all:
            continue
        is_mod = model.is_module(A)
        imps = list(model.imports(A))
        keep = []
        for C in imps:
            if C.meta or model.pinned(A, C):
                keep.append(C)
                continue
            redundant = False
            for B in imps:
                if B is C or B.meta:
                    continue
                # a public import of C needs a *public* carrier (or a legacy file)
                if C.pub and not (B.pub or not is_mod):
                    continue
                if C.name in model.pub_closure(B.name) and B.name != C.name:
                    redundant = True
                    break
            if redundant:
                removed += 1
                log(f"  - {A}: {C.name} (implied by another import)")
            else:
                keep.append(C)
        if len(keep) != len(imps) and not dry:
            model.write_block(A, keep)
    log(f"phase 1: removed {removed} redundant imports"
        + (" (dry-run, nothing written)" if dry else ""))
    return removed


# --------------------------------------------------------------------------- phase 2
def restore_until_builds(model: Model, A):
    """Add back imports from A's original closure until it compiles (the restore rule)."""
    added = []
    for _ in range(50):
        lost = model.original_visible[A] - model.visible(A)
        if not lost:
            break
        maximal = [m for m in lost
                   if not any(m in model.pub_closure(o) for o in lost if o != m)]
        maximal = maximal or sorted(lost)
        cur = list(model.imports(A))
        for m in maximal:
            cur.append(Import(m, line=-1, pub=model.is_module(A), meta=False, keep=False, cmt=""))
            added.append(m)
        model.write_block(A, cur)
        if build(A):
            break
    return added


def phase2(model: Model, dry: bool, limit, resume):
    log("\n=== phase 2: empirical per-import minimization ===")
    if dry:
        log("phase 2: skipped (--dry-run)")
        return 0
    done = set()
    if resume and os.path.exists(STATE_FILE):
        done = set(json.load(open(STATE_FILE)).get("done", []))
        log(f"  resuming: {len(done)} files already processed")

    order = [m for m in model.topo()
             if m not in model.keep_all and model.imports(m) and model.has_decls(m)]
    removed = processed = 0
    t0 = time.time()
    for m in order:
        if m in done:
            continue
        if limit and processed >= limit:
            break
        # baseline: make sure it builds before we start removing
        if not build(m):
            added = restore_until_builds(model, m)
            if added:
                log(f"  [restore] {m}: added {added}")
            if not build(m):
                log(f"  [skip] {m}: does not build even after restore")
                done.add(m)
                continue
        # Snapshot the import objects up front; the loop tracks a `keep` list by value,
        # never by identity, because write_block re-parses (new objects) after each write.
        snapshot = list(model.imports(m))
        keep = list(snapshot)
        for im in snapshot:
            if model.pinned(m, im):
                continue
            trial = [x for x in keep if x.name != im.name]
            model.write_block(m, trial)
            if build(m):
                keep = trial
                removed += 1
            # on failure, `keep` is unchanged; the next write (or the final one) restores it
        model.write_block(m, keep)  # ensure the file matches the final keep set
        processed += 1
        done.add(m)
        json.dump({"done": sorted(done)}, open(STATE_FILE, "w"))
        if processed % 10 == 0:
            log(f"  [{processed}/{len(order)}] removed {removed} so far "
                f"({time.time() - t0:.0f}s)")
    log(f"phase 2: removed {removed} imports across {processed} files")
    if os.path.exists(STATE_FILE) and not limit:
        os.remove(STATE_FILE)
    return removed


# --------------------------------------------------------------------------- phase 3
def phase3(model: Model, dry: bool):
    log("\n=== phase 3: restore Cslib.Init reachability (minimal) ===")
    order = model.topo()  # dependencies first: adding Init to a root covers its dependents
    added_to = []
    for m in order:
        if m in INIT_EXCEPTIONS or m in model.keep_all:
            continue
        if model.reaches_init(m):
            continue
        # add `public import Cslib.Init` (or plain `import` for legacy files)
        if not dry:
            cur = list(model.imports(m))
            cur.append(Import(INIT, line=-1, pub=model.is_module(m),
                              meta=False, keep=False, cmt=""))
            model.write_block(m, cur)
        added_to.append(m)
        log(f"  + {m}")
    log(f"phase 3: added Cslib.Init to {len(added_to)} modules"
        + (" (dry-run)" if dry else ""))
    return added_to


# --------------------------------------------------------------------------- phase 4
def phase4(model: Model, dry: bool):
    log("\n=== phase 4: sort import blocks into canonical order ===")
    changed = 0
    for m in model.targets:
        if m in model.keep_all:
            continue
        if sort_file(model.mod2file[m], dry):
            changed += 1
    log(f"phase 4: normalized {changed} files" + (" (dry-run)" if dry else ""))
    return changed


def sort_file(path, dry):
    with open(path, encoding="utf-8") as fh:
        lines = fh.readlines()
    idx = [i for i, l in enumerate(lines) if IMPORT_RE.match(l.strip())]
    if not idx:
        return False
    first, last = idx[0], idx[-1]
    parsed = []
    for i in idx:
        m = IMPORT_RE.match(lines[i].strip())
        parsed.append(Import(
            name=m.group("name"), line=i,
            pub="public" in (m.group("mods") or ""),
            meta="meta" in (m.group("mods") or ""),
            keep=bool(m.group("cmt") and "shake: keep" in m.group("cmt")),
            cmt=(" " + m.group("cmt")) if m.group("cmt") else "",
            all=bool(m.group("all"))))
    parsed.sort(key=lambda im: (im.rank(), im.name))

    block, prev_private = [], None
    for im in parsed:
        priv = im.rank() >= 2
        if prev_private is False and priv:
            block.append("\n")  # blank between exported and private groups
        block.append(im.render())
        prev_private = priv

    # header: everything up to the first import; ensure exactly one blank before the block
    head = lines[:first]
    while head and head[-1].strip() == "":
        head.pop()
    # tail: everything after the last import; ensure exactly one blank after the block
    tail = lines[last + 1:]
    while tail and tail[0].strip() == "":
        tail.pop(0)
    # a separating blank only makes sense when there is something to separate from
    new = (head + (["\n"] if head else [])
           + block
           + (["\n"] + tail if tail else []))
    if new != lines:
        if not dry:
            with open(path, "w", encoding="utf-8") as fh:
                fh.writelines(new)
        return True
    return False


# --------------------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser(description="Minimize and normalize CSLib imports.")
    ap.add_argument("--phases", default="1,2,3,4",
                    help="comma-separated phases to run (default: 1,2,3,4)")
    ap.add_argument("--dry-run", action="store_true",
                    help="report only; skip phase-2 builds and write nothing")
    ap.add_argument("--limit", type=int, default=0,
                    help="phase 2: process at most N files (for testing)")
    ap.add_argument("--resume", action="store_true",
                    help="phase 2: resume from the saved state file")
    ap.add_argument("--no-verify", action="store_true",
                    help="skip the final lake build + checkInitImports")
    args = ap.parse_args()
    phases = {int(p) for p in args.phases.split(",") if p.strip()}

    model = Model()
    log(f"indexed {len(model.mod2file)} modules; {len(model.targets)} CSLib targets")
    log(f"keep-all files: {sorted(model.keep_all)}")
    log(f"keep-downstream: {sorted(model.keep_downstream)}")

    if 1 in phases:
        phase1(model, args.dry_run)
    if 2 in phases:
        phase2(model, args.dry_run, args.limit, args.resume)
    if 3 in phases:
        phase3(model, args.dry_run)
    if 4 in phases:
        phase4(model, args.dry_run)

    if args.dry_run or args.no_verify:
        return
    log("\n=== verification ===")
    ok_build = full_build()
    log(f"lake build: {'ok' if ok_build else 'FAILED'}")
    ok_init, out = check_init_imports()
    log(f"checkInitImports: {'ok' if ok_init else 'FAILED'}")
    if not ok_init:
        log(out.strip()[:2000])
    sys.exit(0 if ok_build and ok_init else 1)


if __name__ == "__main__":
    main()
