#!/usr/bin/env python3
# Copyright (c) 2026 Chris Henson. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Chris Henson

"""Reproduce the certified model dispatch and five-atom classification rows.

Input JSON is exported by generate.py. All generated certificates are checked by
Lean's kernel; this renderer and its input files are not trusted proof procedures.
"""

from pathlib import Path
import argparse
import json
import math

from generate import process_sources, require

HEADER='''/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

'''
def atoms(j,k,a):
 require(a > 0, "identity is not a diversity atom")
 if a<=j:return f'.inl {a-1}'
 i,b=divmod(a-j-1,2);return f'.inr ({i}, {str(bool(b)).lower()})'
def triple(j,k,t):return '('+', '.join(atoms(j,k,a) for a in t)+')'
def nums_lines(vals,indent='  ',group=8):
 return ',\n'.join(indent+', '.join(map(str,vals[i:i+group])) for i in range(0,len(vals),group))
def numeric(n,indent='    '):
 if n.bit_length()<=240:return str(n)
 low=n%2**240;hi=n>>240
 return f'Nat.lor 0x{low:x}\n{indent}  (Nat.shiftLeft 0x{hi:x} 240)'
def chunks_array(vals,code=False):
 chunks=[]
 for off in range(0,len(vals),64):
  v=vals[off:off+64]
  if code: content=',\n'.join('    '+numeric(x) for x in v)
  else: content=nums_lines(v,'    ')
  chunks.append('  #[\n'+content+']')
 return '#[\n'+',\n'.join(chunks)+']'
def array_defs(name, vals, code=False):
 out=''
 for b,off in enumerate(range(0,len(vals),64)):
  v=vals[off:off+64]
  content=(',\n'.join('  '+numeric(x,'  ') for x in v) if code else nums_lines(v))
  out+=f'/-- Block {b} of the numeric {name} data. -/\ndef {name}{b:03d} : Array ℕ :=\n  #[\n'+content+']\n\n'
 out+=f'/-- The {name} data, stored in short blocks. -/\ndef {name}Blocks : Array (Array ℕ) :=\n  #['
 out+=',\n    '.join(f'{name}{b:03d}' for b in range(math.ceil(len(vals)/64)))+']\n'
 return out

def render_row(row, data):
 outputs = {}
 j,k=data['j'],data['k'];r=len(data['reps']);p=len(data['renames']);N=len(data['canonical_masks'])
 ns='Cslib.RelationAlgebra.Catalogue.'+row
 directory=Path('Cslib/Foundations/RelationAlgebra/Catalogue')/row
 out=HEADER+'public import Cslib.Foundations.RelationAlgebra.FastCatalogueProfiles\npublic import Mathlib.Data.Fin.VecNotation\n\n'
 out+=f'''/-!
# Cycle-profile data for the ⟨1, {j}, {k}⟩ classification

Models are ordered by increasing canonical cycle mask. These indices are generated from
Peircean orbit choices, rather than source entry numbers. Packed profiles record every atom
renaming and are linked to the actual cycle tables by the model certificate modules.
-/

@[expose] public section

namespace {ns}.Data

set_option maxRecDepth 8192

/-- The lexicographically ordered representatives of the diversity-cycle orbits. -/
def cycleReps : Fin {r} → Cycle {j} {k} :=
  !['''+',\n    '.join(triple(j,k,t) for t in data['reps'])+']\n\n'
 out+=f'''/-- The basis meets every diversity-cycle orbit. -/
theorem cycleReps_cover : ∀ c : Cycle {j} {k},
    ∃ i, (some c.1, some c.2.1, some c.2.2) ∈ cycleOrbit (cycleReps i) := by
  decide +kernel

/-- No two basis cycles lie in the same orbit. -/
theorem cycleReps_distinct : ∀ i l,
    (some (cycleReps i).1, some (cycleReps i).2.1, some (cycleReps i).2.2) ∈
      cycleOrbit (cycleReps l) ↔ i = l := by
  decide +kernel

/-- The converse-preserving permutations of the diversity atoms. -/
def renameDiversity (p : Fin {p}) : DiversityAtom {j} {k} → DiversityAtom {j} {k}
'''
 for a in range(1,5):out+=f'  | {atoms(j,k,a)} => !['+', '.join(atoms(j,k,q[a]) for q in data['renames'])+'] p\n'
 out+=f'''\n/-- Extend a diversity-atom permutation by fixing the identity atom. -/
def rename (p : Fin {p}) : Atom {j} {k} → Atom {j} {k} := Option.map (renameDiversity p)

/-- All listed atom renamings preserve identity and converse and are injective. -/
theorem rename_laws : ∀ p, Function.Injective (rename p) ∧ rename p none = none ∧
    ∀ x, rename p x.converse = (rename p x).converse := by
  decide +kernel

/-- The listed renamings include every injective identity- and converse-preserving map. -/
theorem renamings_exhaustive : ∀ f : Atom {j} {k} → Atom {j} {k},
    Function.Injective f → f none = none →
      (∀ x, f x.converse = (f x).converse) → ∃ p : Fin {p}, f = rename p := by
  unfold Function.Injective
  decide +kernel

/-- Renaming zero is the identity. -/
theorem rename_zero : ∀ x, rename 0 x = x := by decide +kernel

/-- The action of each atom renaming on the orbit basis. -/
def orbitAction : Fin {p} → Fin {r} → Fin {r} :=
  !['''+',\n    '.join('!['+', '.join(map(str,q))+']' for q in data['rename_orbits'])+']\n\n'
 out+=f'''/-- The numeric orbit action agrees with the actual atom renaming. -/
theorem orbitAction_spec : ∀ p i,
    (some (renameDiversity p (cycleReps i).1), some (renameDiversity p (cycleReps i).2.1),
      some (renameDiversity p (cycleReps i).2.2)) ∈ cycleOrbit (cycleReps (orbitAction p i)) := by
  decide +kernel

'''+array_defs('canonicalMask',data['canonical_masks'])+'\n'
 out+='''/-- The canonical profile at a model index; out-of-range indices have profile zero. -/
def canonicalMask (i : ℕ) : ℕ :=
  (canonicalMaskBlocks.getD (i / 64) #[]).getD (i % 64) 0

'''
 profile_rows=[]
 for mask in data['canonical_masks']:
  profiles=[sum(((mask>>q[c])&1)<<c for c in range(r)) for q in data['rename_orbits']]
  require(min(profiles) == mask, "profile is not canonical")
  profile_rows.append(sum(profile<<(r*q) for q,profile in enumerate(profiles)))
 out+=array_defs('profile',profile_rows,True)+'\n'
 out+=f'''/-- The profile of a model after the specified atom renaming. -/
def profiles (i q : ℕ) : ℕ :=
  Code.field ((profileBlocks.getD (i / 64) #[]).getD (i % 64) 0) (Nat.mul q {r}) {r}

'''
 slots=[];identity=int(data['identity_code']);orbits=list(map(int,data['orbit_codes']))
 for pos in range(125):
  if identity>>pos&1:slots.append(1)
  else:
   hits=[i for i,v in enumerate(orbits) if v>>pos&1];require(len(hits) <= 1, "overlapping cycle orbits")
   slots.append(hits[0]+2 if hits else 0)
 out+='''/-- Select an obligatory identity cycle, a diversity orbit, or a forbidden triple. -/
def slots (a b c : ℕ) : ℕ :=
  (#[\n'''+nums_lines(slots,'    ')+''']).getD (Code.index 5 a b c) 0

/-- The slot table represents every possible atom triple. -/
theorem slots_spec : CycleSlots cycleReps slots := by decide +kernel

'''
 out+=f'end {ns}.Data\n'
 # Keep long finite-vector expressions within style limits.
 lines=[]
 for line in out.splitlines():
  if len(line)>100 and ' => ![' in line:
   before,rest=line.split(' => ![',1);content,suffix=rest.rsplit(']',1)
   elems=content.split(', ')
   # Atom tuples include commas; break after six complete entries using parsing below.
   entries=[];depth=0;start=0
   for idx,ch in enumerate(content):
    if ch=='(':depth+=1
    elif ch==')':depth-=1
    elif ch==',' and depth==0:entries.append(content[start:idx].strip());start=idx+1
   entries.append(content[start:].strip())
   line=before+' =>\n    !['+',\n      '.join(', '.join(entries[i:i+4]) for i in range(0,len(entries),4))+']'+suffix
  lines.append(line)
 outputs[directory/'Data.lean'] = '\n'.join(lines)+'\n'
 for chunk,off in enumerate(range(0,N,64)):
  count=min(64,N-off);name=f'Models{chunk:03d}'
  s=HEADER+f'public import Cslib.Foundations.RelationAlgebra.Catalogue.{row}.Data\npublic import Mathlib.Tactic.FinCases\n'
  for i in range(off,off+count):s+=f'public import Cslib.Foundations.RelationAlgebra.Catalogue.{row}.Ra{i+1:04d}\n'
  s+=f'''\n/-!
# Certified models {off + 1}–{off + count} of the ⟨1, {j}, {k}⟩ row

Each record refers to an explicitly defined algebra and certifies its canonical cycle profile.
-/

@[expose] public section

namespace {ns}.{name}

/-- The explicit models in this block, with their certified numeric profiles. -/
def entries : Array (ProfiledCycleTable Data.cycleReps) :=
  #[\n'''
  for i in range(off,off+count):
   ra=f'Ra{i+1:04d}';code=data['table_codes'][i];mask=data['canonical_masks'][i]
   s+=f'''    ProfiledCycleTable.ofEncoded Data.cycleReps
      {{ table := {ra}.table, code := {code},
        encodes := {ra}.tableCode_eq ▸ encodesTable_tableCode {ra}.cycles }} {mask}
      (by decide +kernel)'''+(',\n' if i+1<off+count else ']\n\n')
  s+=f'''/-- The packed profiles in this block agree with the certified orbit action. -/
theorem profiles_eq : ∀ i : Fin {count}, ∀ p : Fin {p},
    Data.profiles ({off} + i.val) p.val =
      Code.permuteProfile (Data.canonicalMask ({off} + i.val)) (Data.orbitAction p) := by
  decide +kernel

/-- Every canonical profile in this block is least among its atom renamings. -/
theorem profiles_minimal : ∀ i : Fin {count}, ∀ p : Fin {p},
    Data.profiles ({off} + i.val) 0 ≤ Data.profiles ({off} + i.val) p.val := by
  decide +kernel

/-- Identity renaming reads the canonical mask in this block. -/
theorem profiles_zero : ∀ i : Fin {count},
    Data.profiles ({off} + i.val) 0 = Data.canonicalMask ({off} + i.val) := by
  decide +kernel

/-- Every mask in this block is smaller than its successor, where a successor exists. -/
theorem canonicalMask_increasing : ∀ i : Fin {min(64, N - 1 - off)},
    Data.canonicalMask ({off} + i.val) < Data.canonicalMask ({off} + i.val + 1) := by
  decide +kernel

/-- Each model record has the canonical mask stored at its global index. -/
theorem entries_profile (fallback : ProfiledCycleTable Data.cycleReps) : ∀ i : Fin {count},
    (entries.getD i.val fallback).profile =
      Data.canonicalMask ({off} + i.val) := by
  intro i
  fin_cases i <;> rfl

end {ns}.{name}
'''
  outputs[directory/(name+'.lean')] = s
 # Link the certified blocks without a large case split over all individual models.
 B=math.ceil(N/64)
 s=HEADER
 for b in range(B):s+=f'public import Cslib.Foundations.RelationAlgebra.Catalogue.{row}.Models{b:03d}\n'
 s+=f'''\n/-!
# Certified model dispatch for the ⟨1, {j}, {k}⟩ row

The two-level array selects the named entries in consecutive blocks of 64. The profile
alignment theorem checks every index, including the final partial block.
-/

@[expose] public section

namespace {ns}.Models

/-- A total lookup default; every valid index is checked to select its own entry. -/
def fallback : ProfiledCycleTable Data.cycleReps :=
  ProfiledCycleTable.ofEncoded Data.cycleReps
    {{ table := Ra0001.table, code := {data['table_codes'][0]},
      encodes := Ra0001.tableCode_eq ▸ encodesTable_tableCode Ra0001.cycles }}
    {data['canonical_masks'][0]} (by decide +kernel)

/-- Consecutive blocks containing all explicitly named models. -/
def blocks : Array (Array (ProfiledCycleTable Data.cycleReps)) :=
  #['''+',\n    '.join(f'Models{b:03d}.entries' for b in range(B))+']\n\n'
 s+=f'''/-- Select a certified model by its zero-based catalogue index. -/
def get (i : ℕ) : ProfiledCycleTable Data.cycleReps :=
  (blocks.getD (i / 64) #[]).getD (i % 64) fallback

/-- Each valid model index selects the corresponding canonical profile. -/
theorem get_profile : ∀ i : Fin {N}, (get i.val).profile = Data.canonicalMask i.val := by
  apply forall_of_blocks (n := {N})
    (property := fun i => (get i).profile = Data.canonicalMask i)
  intro b i
  have hi : i.val < 64 := lt_of_lt_of_le i.isLt (min_le_left _ _)
  have hd : (b.val * 64 + i.val) / 64 = b.val := by omega
  have hm : (b.val * 64 + i.val) % 64 = i.val := by omega
  simp only [get, hd, hm]
  fin_cases b
'''
 for b in range(B):s+=f'  · exact Models{b:03d}.entries_profile fallback i\n'
 s+=f'''\n/-- All packed profiles are the corresponding permutations of the canonical mask. -/
theorem profiles_eq : ∀ i : Fin {N}, ∀ p : Fin {p},
    Data.profiles i.val p.val =
      Code.permuteProfile (Data.canonicalMask i.val) (Data.orbitAction p) := by
  apply forall_of_blocks (n := {N})
    (property := fun i => ∀ p : Fin {p}, Data.profiles i p.val =
      Code.permuteProfile (Data.canonicalMask i) (Data.orbitAction p))
  intro b i
  fin_cases b
'''
 for b in range(B):s+=f'  · exact Models{b:03d}.profiles_eq i\n'
 s+=f'''\n/-- The canonical profile of each model is least under atom renaming. -/
theorem profiles_minimal : ∀ i : Fin {N}, ∀ p : Fin {p},
    Data.profiles i.val 0 ≤ Data.profiles i.val p.val := by
  apply forall_of_blocks (n := {N})
    (property := fun i => ∀ p : Fin {p}, Data.profiles i 0 ≤ Data.profiles i p.val)
  intro b i
  fin_cases b
'''
 for b in range(B):s+=f'  · exact Models{b:03d}.profiles_minimal i\n'
 s+=f'''\n/-- Identity renaming reads exactly the increasing canonical masks. -/
theorem profiles_zero : ∀ i : Fin {N}, Data.profiles i.val 0 = Data.canonicalMask i.val := by
  apply forall_of_blocks (n := {N})
    (property := fun i => Data.profiles i 0 = Data.canonicalMask i)
  intro b i
  fin_cases b
'''
 for b in range(B):s+=f'  · exact Models{b:03d}.profiles_zero i\n'
 s+=f'''
/-- Canonical masks increase strictly with the catalogue index. -/
theorem canonicalMask_strictMono : StrictMono (fun i : Fin {N} => Data.canonicalMask i.val) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  have h : ∀ i : Fin {N - 1}, Data.canonicalMask i.val < Data.canonicalMask (i.val + 1) := by
    apply forall_of_blocks (n := {N - 1})
      (property := fun i => Data.canonicalMask i < Data.canonicalMask (i + 1))
    intro b i
    fin_cases b
'''
 for b in range(B):s+=f'    · exact Models{b:03d}.canonicalMask_increasing i\n'
 s+=f'''  exact h

/-- Packed numeric profiles equal the profiles of the actual explicitly defined cycle tables. -/
theorem profiles_spec (i : Fin {N}) (p : Fin {p}) :
    choiceMask (fun c => decide (cycleClosure (get i.val).table.cycles
      (Data.rename p (some (Data.cycleReps c).1))
      (Data.rename p (some (Data.cycleReps c).2.1))
      (Data.rename p (some (Data.cycleReps c).2.2)))) = Data.profiles i.val p.val := by
  have hbase := (get i.val).profile_eq
  rw [get_profile i] at hbase
  exact (profileCode_eq_of_orbit_renaming Data.cycleReps (get i.val).table.cycles
    (Data.renameDiversity p) (Data.orbitAction p) (Data.orbitAction_spec p)
    (Data.canonicalMask i.val) hbase).trans (profiles_eq i p).symm

end {ns}.Models
'''
 outputs[directory/'Models.lean'] = s
 s=HEADER+f'''public import Cslib.Foundations.RelationAlgebra.Catalogue.{row}.Coverage
public import Cslib.Foundations.RelationAlgebra.Catalogue.{row}.Models

/-!
# Classification of the ⟨1, {j}, {k}⟩ catalogue row

There are exactly {N} isomorphism classes of integral relation algebras with {j} symmetric
diversity atoms and {k} converse {'pair' if k == 1 else 'pairs'}. The numbered entries are arranged by increasing canonical
cycle mask; this deterministic order is independent of numbering in any external source.
The unique-index classification proves exhaustiveness and absence of duplicates for arbitrary
relation algebras satisfying `HasSignature A 1 {j} {k}`.

The proof checks all {2**r} choices of Peircean cycle orbits in parallel using truth words,
and distinguishes models by the least cycle profile under identity- and converse-preserving
atom permutations. This module makes no assertion about representability.
-/

@[expose] public section

namespace {ns}

/-- The explicitly defined cycle tables, ordered by increasing canonical cycle mask. -/
def table (idx : Fin {N}) : IntegralCycleTable {j} {k} := (Models.get idx.val).table

/-- The {N} explicitly listed algebras, with zero-based catalogue indices. -/
abbrev Model (idx : Fin {N}) : Type := Complex (table idx)

private theorem cycles_exhaustive : ∀ bits : Fin {r} → Bool,
    AtomCompositionAssociative (selectedCycles Data.cycleReps bits) →
      ∃ i : Fin {N}, ∃ f,
        AtomRelabelling (selectedCycles Data.cycleReps bits) (table i).cycles f := by
  exact cycles_exhaustive_of_truthTable Data.cycleReps Data.cycleReps_cover
    Data.cycleReps_distinct table Data.rename Data.rename_laws Data.profiles
    Models.profiles_spec Coverage.words
    (fun _ hm => bitAt_cycleWord_of_slots Data.cycleReps Data.slots Data.slots_spec hm)
    Coverage.quads Coverage.quads_lt Coverage.check

private theorem cycles_distinct : ∀ i l : Fin {N}, ∀ f,
    AtomRelabelling (table i).cycles (table l).cycles f → i = l := by
  apply cycles_distinct_of_minimal_profiles Data.cycleReps table Data.rename 0
    Data.rename_zero Data.renamings_exhaustive (fun i p => Data.profiles i.val p.val)
    Models.profiles_spec Models.profiles_minimal
  intro i l h
  apply Models.canonicalMask_strictMono.injective
  change Data.profiles i.val 0 = Data.profiles l.val 0 at h
  simpa only [Models.profiles_zero] using h

/-- Every algebra of this signature is isomorphic to exactly one explicitly listed model. -/
theorem classification (A : Type*) [RelationAlgebra A] (h : HasSignature A 1 {j} {k}) :
    ∃! idx : Fin {N}, Nonempty (RelationAlgebraEquiv A (Model idx)) := by
  exact classification_of_cycle_basis Data.cycleReps Data.cycleReps_cover table
    cycles_exhaustive cycles_distinct A h

end {ns}
'''
 outputs[directory.parent/(row+'.lean')] = s
 return outputs


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--row", action="append", choices=["I1S2N1", "I1S4N0"])
    parser.add_argument("--data-dir", type=Path, required=True)
    parser.add_argument("--output-root", type=Path, default=Path(__file__).resolve().parents[2])
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    sources, patterns = {}, []
    for row in args.row or ["I1S2N1", "I1S4N0"]:
        with (args.data_dir / f"cslib-{row.lower()}-data.json").open(encoding="utf-8") as stream:
            data = json.load(stream)
        expected = (2, 1, 1316) if row == "I1S2N1" else (4, 0, 3013)
        require((data["j"], data["k"], len(data["canonical_masks"])) == expected,
                f"{row}: unexpected row signature or model count")
        require(data["canonical_masks"] == sorted(set(data["canonical_masks"])),
                f"{row}: canonical masks must be strictly increasing")
        sources.update(render_row(row, data))
        base = f"Cslib/Foundations/RelationAlgebra/Catalogue/{row}"
        patterns.extend([f"{base}.lean", f"{base}/Data.lean", f"{base}/Models*.lean"])
    count = process_sources(sources.items(), args.output_root, args.check, patterns)
    print(f"{'Checked' if args.check else 'Generated'} {count} classification source files")


if __name__ == "__main__":
    main()
