/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Logics.LinearLogic.CLL.Basic
public import Cslib.Foundations.Data.Multiset.Split

/-! # Cut-free proofs, cut admissibility, and cut elimination for classical linear logic

A CLL proof is *cut-free* if it never uses the cut rule (`Proof.IsCutFree`). This file defines
the cut-free fragment of CLL as an inference system `CF`, proves that the cut rule is admissible
in it (`Proof.cutAdm`), and derives cut elimination: every CLL proof can be transformed into a
cut-free proof of the same sequent (`Proof.cutElimList`, `Proof.cutElim`). All results are
definitions that compute proofs, not existence theorems, so cut elimination can be run (via
`Proof.cutElimList`; `Proof.cutElim` is noncomputable, see below).

## Main definitions

* `Proof.IsCutFree`: a proof contains no cut. `Proof.IsCutFree.rec` is induction on cut-free
  proofs, with no case for cut.
* `CF`: the cut-free fragment of CLL. `CF⇓Γ` is the subtype of cut-free proofs of `Γ`, and
  `CF.Proof.ax`, `CF.Proof.tensor`, ... are the rules of CLL other than cut, lifted to `CF`.
* `CF.Proof.weakenContext`, `CF.Proof.contractContext`: weakening and contraction of a whole
  context of `ʔ`-propositions.
* `CutAdmissibleAt a`: a cut on `a` between two cut-free proofs can be replaced by a cut-free
  proof of the same conclusion.
* `Proof.cutAdm`: cut is admissible at every proposition.
* `Proof.cutElimList`: computable cut elimination for sequents given as lists.
* `Proof.cutElim`: cut elimination for arbitrary sequents (noncomputable, see below).

## Proof strategy

We follow the standard nested induction for sequent calculi (see e.g.
[TroelstraSchwichtenberg2000]), adapted to the one-sided sequent calculus of [Girard1987].

* **Outer induction** on the size (`sizeOf`) of the cut proposition `a` (`Proof.cutAdm`). The
  induction hypothesis is `CutAdmissibleBelow`, and `Proof.cutAdmOfSmaller` performs one step
  by cases on the main connective of `a`.
* **Non-exponential cuts** (`Proof.cutAdmNonExponential`), when neither `a` nor `a⫠` is a
  `ʔ`-proposition: inner induction on the sum of the heights of the two premises.
  `Proof.principalOrCommute` looks at the last rule of one premise. If that rule does not
  introduce the cut proposition, the cut is moved above it (a *commuting* case: a recursive
  call on a shorter premise). A cut against an axiom is resolved at once. When the last rules
  of both premises introduce the cut proposition (`CF.Proof.Principal`), `Proof.cutPrincipal`
  replaces the cut by cuts on immediate subpropositions, which are smaller (the *principal*
  case).
* **Exponential cuts** (`Proof.bangCutAdm`), when `a = !b`: induction on the height of the
  premise `⊢ !b, Γ`. The cut is moved upwards in this premise until it is an axiom (and the cut
  is trivial) or a promotion of some `p : ⊢ b, Γ` (so `Γ` consists of `ʔ`-propositions). The
  other premise may use `ʔ(b⫠)` any number of times through contraction, so moving a single cut
  upwards in it does not decrease any measure. We therefore generalise to a multicut
  (`Proof.questMulticut`), in the spirit of Gentzen's mix rule: cut `!b` against `n` selected
  occurrences of `ʔ(b⫠)` at once, by structural recursion on the cut-free proof that contains
  them. Contraction increases `n`, weakening decreases it, and dereliction triggers a cut on
  the smaller proposition `b`. The case `a = ʔb` is reduced to `!(b⫠)` by swapping the premises
  (`Proof.questCutAdm`).

Cut elimination (`Proof.cutElimAux`) then works by structural recursion on a proof with cuts:
it removes the cuts in the premises first, then replaces each cut by `Proof.cutAdm`.

## Why contexts are lists

Sequents are multisets, and a multiset is a quotient of lists. A definition that returns proof
data cannot look at how a multiset is built: it cannot compute a list that enumerates a
multiset (`Multiset.toList` is noncomputable), so it cannot recurse over the elements of a
`ʔ`-context to apply weakening or contraction one proposition at a time (as
`CF.Proof.weakenContext` and `CF.Proof.contractContext` do, by recursion on a list).
So we state cut admissibility for contexts given as lists (`CutAdmissibleAt`). In each rule, we
recover list representatives of the contexts from a list that we already have, using the
functions in `Cslib.Foundations.Data.Multiset.Split`. This keeps `Proof.cutAdm` and
`Proof.cutElimList` computable. Only `Proof.cutElim`, which accepts any multiset, is
noncomputable, because it picks a list with `Multiset.toList`.

Equalities between sequents are proved by `grind only [multiset]`, the default argument of
`CF.Proof.rwConclusion`. It works from the hypotheses in the local context, so some cases bind
equations (such as `hL` in `Proof.cutElimAux`) only to make them available to it.

## References

* [J.-Y. Girard, *Linear logic*][Girard1987]
* [A. S. Troelstra and H. Schwichtenberg, *Basic Proof Theory*][TroelstraSchwichtenberg2000]
-/

@[expose] public section

namespace Cslib.Logic.CLL

open Cslib.Logic.InferenceSystem
open scoped Proposition

/-! ## Cut-free proofs

`Proof.IsCutFree` and one lemma per rule (except cut) stating that the rule preserves
cut-freeness. These lemmas are used to state the induction principle `Proof.IsCutFree.rec`. -/

/-- A proof is cut-free if it contains no application of the cut rule. -/
@[simp]
def Proof.IsCutFree {Γ : Sequent Atom} : ⇓Γ → Prop
  | ax | one | top => True
  | bot p | parr p | oplus₁ p | oplus₂ p
    | quest p | weaken p | contract p | bang _ p => p.IsCutFree
  | tensor p q | .with p q => p.IsCutFree ∧ q.IsCutFree
  | cut _ _ => False

/-- The axiom is cut-free. -/
theorem isCutFree_ax {a : Proposition Atom} :
    @Proof.IsCutFree Atom {a, a⫠} (Proof.ax (a := a)) := ⟨⟩

/-- Rule `1` is cut-free. -/
theorem isCutFree_one : @Proof.IsCutFree Atom {1} Proof.one := ⟨⟩

/-- Rule `⊤` is cut-free. -/
theorem isCutFree_top {Γ : Sequent Atom} :
    @Proof.IsCutFree Atom (⊤ ::ₘ Γ) (Proof.top (Γ := Γ)) := ⟨⟩

/-- Rule `⊥` preserves cut-freeness. -/
theorem isCutFree_bot {Γ : Sequent Atom} {p : Proof Γ} (hp : @Proof.IsCutFree Atom Γ p) :
    @Proof.IsCutFree Atom (⊥ ::ₘ Γ) (Proof.bot (Γ := Γ) p) := hp

/-- Rule `⅋` preserves cut-freeness. -/
theorem isCutFree_parr {a b : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (a ::ₘ b ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (a ::ₘ b ::ₘ Γ) p) :
    @Proof.IsCutFree Atom ((a ⅋ b) ::ₘ Γ) (Proof.parr (a := a) (b := b) (Γ := Γ) p) := hp

/-- Rule `⊗` preserves cut-freeness. -/
theorem isCutFree_tensor {a b : Proposition Atom} {Γ Δ : Sequent Atom}
    {p : Proof (a ::ₘ Γ)} {q : Proof (b ::ₘ Δ)}
    (hp : @Proof.IsCutFree Atom (a ::ₘ Γ) p)
    (hq : @Proof.IsCutFree Atom (b ::ₘ Δ) q) :
    @Proof.IsCutFree Atom ((a ⊗ b) ::ₘ (Γ + Δ))
      (Proof.tensor (a := a) (b := b) (Γ := Γ) (Δ := Δ) p q) :=
  And.intro hp hq

/-- Rule `⊕₁` preserves cut-freeness. -/
theorem isCutFree_oplus₁ {a b : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (a ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (a ::ₘ Γ) p) :
    @Proof.IsCutFree Atom ((a ⊕ b) ::ₘ Γ) (Proof.oplus₁ (a := a) (b := b) (Γ := Γ) p) := hp

/-- Rule `⊕₂` preserves cut-freeness. -/
theorem isCutFree_oplus₂ {a b : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (b ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (b ::ₘ Γ) p) :
    @Proof.IsCutFree Atom ((a ⊕ b) ::ₘ Γ) (Proof.oplus₂ (a := a) (b := b) (Γ := Γ) p) := hp

/-- Rule `&` preserves cut-freeness. -/
theorem isCutFree_with {a b : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (a ::ₘ Γ)} {q : Proof (b ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (a ::ₘ Γ) p)
    (hq : @Proof.IsCutFree Atom (b ::ₘ Γ) q) :
    @Proof.IsCutFree Atom ((a & b) ::ₘ Γ) (Proof.with (a := a) (b := b) (Γ := Γ) p q) :=
  And.intro hp hq

/-- Dereliction preserves cut-freeness. -/
theorem isCutFree_quest {a : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (a ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (a ::ₘ Γ) p) :
    @Proof.IsCutFree Atom (ʔa ::ₘ Γ) (Proof.quest (a := a) (Γ := Γ) p) := hp

/-- Weakening preserves cut-freeness. -/
theorem isCutFree_weaken {a : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof Γ} (hp : @Proof.IsCutFree Atom Γ p) :
    @Proof.IsCutFree Atom (ʔa ::ₘ Γ) (Proof.weaken (a := a) (Γ := Γ) p) := hp

/-- Contraction preserves cut-freeness. -/
theorem isCutFree_contract {a : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (ʔa ::ₘ ʔa ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (ʔa ::ₘ ʔa ::ₘ Γ) p) :
    @Proof.IsCutFree Atom (ʔa ::ₘ Γ) (Proof.contract (a := a) (Γ := Γ) p) := hp

/-- Promotion preserves cut-freeness. -/
theorem isCutFree_bang {a : Proposition Atom} {Γ : Sequent Atom}
    {hΓ : Γ.allQuest} {p : Proof (a ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (a ::ₘ Γ) p) :
    @Proof.IsCutFree Atom ((!a) ::ₘ Γ) (Proof.bang (a := a) (Γ := Γ) hΓ p) := hp

/-- Induction on cut-free proofs. This is `Proof.rec` without the `cut` case: each case
receives the premises of the last rule together with the induction hypotheses for them.
The motive may depend on the cut-freeness proof and can live in any `Sort`, so this
eliminator can define data (e.g. `Proof.questMulticut`). It is the default
`induction`/`cases` eliminator for hypotheses `h : p.IsCutFree`. -/
@[induction_eliminator, cases_eliminator, elab_as_elim]
def Proof.IsCutFree.rec
    {motive : {Γ : Sequent Atom} → {p : Proof Γ} → (h : p.IsCutFree) → Sort u}
    (ax : ∀ {a : Proposition Atom}, @motive {a, a⫠} .ax (isCutFree_ax (a := a)))
    (one : @motive {1} .one isCutFree_one)
    (top : ∀ {Γ}, @motive (⊤ ::ₘ Γ) .top (isCutFree_top (Γ := Γ)))
    (bot : ∀ {Γ} (p : Proof Γ) {hp}, @motive Γ p hp →
      @motive (⊥ ::ₘ Γ) (.bot p) (isCutFree_bot hp))
    (parr : ∀ {a b Γ} (p : Proof (a ::ₘ b ::ₘ Γ)) {hp},
      @motive (a ::ₘ b ::ₘ Γ) p hp →
      @motive ((a ⅋ b) ::ₘ Γ) (.parr p) (isCutFree_parr hp))
    (tensor : ∀ {a b Γ Δ} (p : Proof (a ::ₘ Γ)) (q : Proof (b ::ₘ Δ)) {hp hq},
      @motive (a ::ₘ Γ) p hp → @motive (b ::ₘ Δ) q hq →
      @motive ((a ⊗ b) ::ₘ (Γ + Δ)) (.tensor p q) (isCutFree_tensor hp hq))
    (oplus₁ : ∀ {a b Γ} (p : Proof (a ::ₘ Γ)) {hp},
      @motive (a ::ₘ Γ) p hp →
      @motive ((a ⊕ b) ::ₘ Γ) (.oplus₁ p) (isCutFree_oplus₁ hp))
    (oplus₂ : ∀ {a b Γ} (p : Proof (b ::ₘ Γ)) {hp},
      @motive (b ::ₘ Γ) p hp →
      @motive ((a ⊕ b) ::ₘ Γ) (.oplus₂ p) (isCutFree_oplus₂ hp))
    («with» : ∀ {a b Γ} (p : Proof (a ::ₘ Γ)) (q : Proof (b ::ₘ Γ)) {hp hq},
      @motive (a ::ₘ Γ) p hp → @motive (b ::ₘ Γ) q hq →
      @motive ((a & b) ::ₘ Γ) (.with p q) (isCutFree_with hp hq))
    (quest : ∀ {a Γ} (p : Proof (a ::ₘ Γ)) {hp},
      @motive (a ::ₘ Γ) p hp →
      @motive (ʔa ::ₘ Γ) (.quest p) (isCutFree_quest hp))
    (weaken : ∀ {a Γ} (p : Proof Γ) {hp},
      @motive Γ p hp →
      @motive (ʔa ::ₘ Γ) (.weaken p) (isCutFree_weaken hp))
    (contract : ∀ {a Γ} (p : Proof (ʔa ::ₘ ʔa ::ₘ Γ)) {hp},
      @motive (ʔa ::ₘ ʔa ::ₘ Γ) p hp →
      @motive (ʔa ::ₘ Γ) (.contract p) (isCutFree_contract hp))
    (bang : ∀ {a} {Γ : Sequent Atom} (hΓ : Γ.allQuest) (p : Proof (a ::ₘ Γ)) {hp},
      @motive (a ::ₘ Γ) p hp →
      @motive ((!a) ::ₘ Γ) (.bang hΓ p) (isCutFree_bang hp))
    {Γ} {p} (h : p.IsCutFree) : @motive Γ p h :=
  let rec @[nolint docBlame] go
      {Γ : Sequent Atom} {p : Proof Γ} (h : p.IsCutFree) : @motive Γ p h :=
    match p, h with
    | .ax, _ => ax
    | .one, _ => one
    | .top, _ => top
    | .bot p, hp => bot p (go (p := p) hp)
    | .parr p, hp => parr p (go (p := p) hp)
    | .tensor p q, hpq => tensor p q (go hpq.1) (go hpq.2)
    | .oplus₁ p, hp => oplus₁ p (go (p := p) hp)
    | .oplus₂ p, hp => oplus₂ p (go (p := p) hp)
    | .with p q, hpq => «with» p q (go hpq.1) (go hpq.2)
    | .quest p, hp => quest p (go (p := p) hp)
    | .weaken p, hp => weaken p (go (p := p) hp)
    | .contract p, hp => contract p (go (p := p) hp)
    | .bang hΓ p, hp => bang hΓ p (go (p := p) hp)
    | .cut _ _, h => nomatch h
  go h

/-- Transporting a conclusion preserves cut-freeness. -/
@[simp, scoped grind .]
theorem Proof.isCutFree_rwConclusion (h : Γ = Δ) (p : Proof Γ)
    (hp : p.IsCutFree) : (p.rwConclusion h).IsCutFree := by grind

/-! ## The cut-free inference system `CF` -/

/-- Tag for the cut-free fragment of CLL: `CF⇓Γ` is the type of cut-free proofs of `Γ`. -/
opaque CF : Type := Empty

namespace CF

open scoped CLL.Proof Sequent

/-- A cut-free proof of `Γ`: a CLL proof of `Γ` together with evidence that it contains no
cut. -/
abbrev Proof (Γ : Sequent Atom) := { p : ⇓Γ // p.IsCutFree }

instance : InferenceSystem CF (Sequent Atom) := ⟨CF.Proof⟩

instance {Γ : Sequent Atom} : Coe (CF⇓Γ) (⇓Γ) where
  coe p := p.val

/-- Rewrites the conclusion of a cut-free proof.
If `h` is omitted, tries to prove the equality using `grind only [multiset]`. -/
def Proof.rwConclusion {Γ Δ : Sequent Atom} (h : Γ = Δ := by grind only [multiset]) (p : CF⇓Γ) :
    CF⇓Δ := ⟨CLL.Proof.rwConclusion h p.val, CLL.Proof.isCutFree_rwConclusion h p.val p.property⟩

@[simp, scoped grind =]
theorem Proof.rwConclusion_val {Γ Δ : Sequent Atom} (h : Γ = Δ) (p : CF⇓Γ) :
    (p.rwConclusion h).val = CLL.Proof.rwConclusion h p.val := rfl

/-- Axiom for CF. -/
def Proof.ax {a : Proposition Atom} : CF⇓({a, a⫠} : Sequent Atom) := ⟨CLL.Proof.ax, isCutFree_ax⟩

/-- Rule `1` for CF. -/
def Proof.one : CF⇓({1} : Sequent Atom) := ⟨CLL.Proof.one, isCutFree_one⟩

/-- Rule `⊤` for CF. -/
def Proof.top {Γ : Sequent Atom} :
    CF⇓((⊤ : Proposition Atom) ::ₘ Γ) :=
  ⟨CLL.Proof.top, isCutFree_top⟩

/-- Rule `⊥` for CF. -/
def Proof.bot {Γ : Sequent Atom} (p : CF⇓Γ) : CF⇓(⊥ ::ₘ Γ) :=
  ⟨CLL.Proof.bot p.val, isCutFree_bot p.property⟩

/-- Rule `⅋` for CF. -/
def Proof.parr {a b : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓(a ::ₘ b ::ₘ Γ)) :
    CF⇓((a ⅋ b) ::ₘ Γ) := ⟨CLL.Proof.parr p.val, isCutFree_parr p.property⟩

/-- Rule `⊗` for CF. -/
def Proof.tensor {a b : Proposition Atom} {Γ Δ : Sequent Atom}
    (p : CF⇓(a ::ₘ Γ)) (q : CF⇓(b ::ₘ Δ)) : CF⇓((a ⊗ b) ::ₘ (Γ + Δ)) :=
  ⟨CLL.Proof.tensor p.val q.val, isCutFree_tensor p.property q.property⟩

/-- Rule `⊕₁` for CF. -/
def Proof.oplus₁ {a b : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓(a ::ₘ Γ)) :
    CF⇓((a ⊕ b) ::ₘ Γ) :=
  ⟨CLL.Proof.oplus₁ p.val, isCutFree_oplus₁ p.property⟩

/-- Rule `⊕₂` for CF. -/
def Proof.oplus₂ {a b : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓(b ::ₘ Γ)) :
    CF⇓((a ⊕ b) ::ₘ Γ) :=
  ⟨CLL.Proof.oplus₂ p.val, isCutFree_oplus₂ p.property⟩

/-- Rule `&` for CF. -/
def Proof.with {a b : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓(a ::ₘ Γ)) (q : CF⇓(b ::ₘ Γ)) :
    CF⇓((a & b) ::ₘ Γ) := ⟨CLL.Proof.with p.val q.val, isCutFree_with p.property q.property⟩

/-- Dereliction (`ʔ`) for CF. -/
def Proof.quest {a : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓(a ::ₘ Γ)) : CF⇓(ʔa ::ₘ Γ) :=
  ⟨CLL.Proof.quest p.val, isCutFree_quest p.property⟩

/-- Weakening of a `ʔ`-proposition for CF. -/
def Proof.weaken {a : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓Γ) : CF⇓(ʔa ::ₘ Γ) :=
  ⟨CLL.Proof.weaken p.val, isCutFree_weaken p.property⟩

/-- Contraction of a `ʔ`-proposition for CF. -/
def Proof.contract {a : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓(ʔa ::ₘ ʔa ::ₘ Γ)) :
    CF⇓(ʔa ::ₘ Γ) := ⟨CLL.Proof.contract p.val, isCutFree_contract p.property⟩

/-- Promotion (`!`) for CF: every proposition of the context must be a `ʔ`-proposition. -/
def Proof.bang {a : Proposition Atom} {Γ : Sequent Atom} (hΓ : Γ.allQuest) (p : CF⇓(a ::ₘ Γ)) :
    CF⇓((!a) ::ₘ Γ) := ⟨CLL.Proof.bang hΓ p.val, isCutFree_bang p.property⟩

/-! ## Weakening and contraction of `ʔ`-contexts

These recurse on a list, which is why `ʔ`-contexts are lists in cut admissibility. -/

/-- Weakening by a whole context: from `⊢ Δ`, derive `⊢ Γ, Δ` by one weakening for each
(`ʔ`-proposition) element of `Γ`. `Γ` is a list so that the proof can be built by recursion
on it. -/
def Proof.weakenContext {Γ : List (Proposition Atom)} {Δ : Sequent Atom} (hΓ : Γ.allQuest)
    (p : CF⇓Δ) : CF⇓(Γ + Δ) :=
  match Γ, hΓ with
  | [], _ => p.rwConclusion (Multiset.zero_add Δ).symm
  | .quest a :: Γ, hΓ =>
    (Proof.weaken (a := a) (Proof.weakenContext (Γ := Γ) hΓ p)).rwConclusion
  | .atom _ :: _, hΓ | .atomDual _ :: _, hΓ
    | .one :: _, hΓ | .zero :: _, hΓ | .top :: _, hΓ | .bot :: _, hΓ
    | .tensor _ _ :: _, hΓ | .parr _ _ :: _, hΓ
    | .oplus _ _ :: _, hΓ | .with _ _ :: _, hΓ | .bang _ :: _, hΓ =>
    nomatch hΓ

/-- Contraction of a whole context: from `⊢ Γ, Γ, Δ`, derive `⊢ Γ, Δ` by one contraction for
each (`ʔ`-proposition) element of `Γ`. `Γ` is a list so that the proof can be built by
recursion on it. -/
def Proof.contractContext {Γ : List (Proposition Atom)} {Δ : Sequent Atom} (hΓ : Γ.allQuest)
    (p : CF⇓((Γ : Sequent Atom) + Γ + Δ)) : CF⇓(Γ + Δ) :=
  match Γ, hΓ with
  | [], _ => p.rwConclusion
  | .quest a :: Γ, hΓ =>
    let p' : CF⇓(ʔa ::ₘ ʔa ::ₘ ((Γ : Sequent Atom) + Γ + Δ)) := p.rwConclusion
    let p' : CF⇓(ʔa ::ₘ ((Γ : Sequent Atom) + Γ + Δ)) := Proof.contract p'
    let p' : CF⇓((Γ : Sequent Atom) + Γ + (ʔa ::ₘ Δ)) := p'.rwConclusion
    (Proof.contractContext (Γ := Γ) (Δ := ʔa ::ₘ Δ) hΓ p').rwConclusion
  | .atom _ :: _, hΓ | .atomDual _ :: _, hΓ
    | .one :: _, hΓ | .zero :: _, hΓ | .top :: _, hΓ | .bot :: _, hΓ
    | .tensor _ _ :: _, hΓ | .parr _ _ :: _, hΓ
    | .oplus _ _ :: _, hΓ | .with _ _ :: _, hΓ | .bang _ :: _, hΓ =>
    nomatch hΓ

end CF

open scoped CF.Proof

universe u

variable {Atom : Type u}

/-! ## Statement of cut admissibility -/

/-- Cut is admissible at `a`: from cut-free proofs of `⊢ a, Γ` and `⊢ a⫠, Δ`, we can compute a
cut-free proof of `⊢ Γ, Δ`. The contexts are lists so that the proof can be computed
(see the module documentation). -/
abbrev CutAdmissibleAt (a : Proposition Atom) := ∀ {Γ Δ : List (Proposition Atom)},
  CF⇓(a ::ₘ Γ) → CF⇓(a⫠ ::ₘ Δ) → CF⇓((Γ : Sequent Atom) + Δ)

/-- Cut is admissible at every proposition of size less than `bound`. This is the induction
hypothesis of the outer induction in `Proof.cutAdm`. -/
abbrev CutAdmissibleBelow (Atom : Type u) (bound : ℕ) :=
  ∀ {a : Proposition Atom}, sizeOf a < bound → CutAdmissibleAt a

/-! ## Principal cuts

A cut whose two premises both end with a rule introducing the cut proposition is replaced by
cuts on smaller propositions. -/

/-- A cut-free proof of `⊢ a, Γ` whose last rule introduces `a` (`a` is *principal*), given by
the premises of that rule, with list contexts. There are no constructors for `0`, which has no
introduction rule; for atoms, which are introduced only by axioms (cuts against axioms are
resolved directly by `Proof.principalOrCommute`); or for `ʔ`-propositions (see
`Proof.bangCutAdm` and `Proof.questCutAdm`). -/
inductive CF.Proof.Principal (Γ : List (Proposition Atom)) : Proposition Atom → Type u where
  /-- `⊢ 1`, so the context is empty. -/
  | one (hG : (Γ : Sequent Atom) = 0) : CF.Proof.Principal Γ 1
  /-- `⊢ ⊥, Γ` from `⊢ Γ`. -/
  | bot (p : CF⇓(Γ : Sequent Atom)) : CF.Proof.Principal Γ ⊥
  /-- `⊢ ⊤, Γ`, which has no premises. -/
  | top : CF.Proof.Principal Γ ⊤
  /-- `⊢ c ⅋ d, Γ` from `⊢ c, d, Γ`. -/
  | parr {c d : Proposition Atom} (p : CF⇓(c ::ₘ d ::ₘ Γ)) : CF.Proof.Principal Γ (c ⅋ d)
  /-- `⊢ c ⊗ d, Λ, R` from `⊢ c, Λ` and `⊢ d, R`, where `Γ = Λ + R`. -/
  | tensor {c d : Proposition Atom} {Λ R : List (Proposition Atom)}
      (hG : (Γ : Sequent Atom) = (Λ : Sequent Atom) + R)
      (p : CF⇓(c ::ₘ Λ)) (q : CF⇓(d ::ₘ R)) : CF.Proof.Principal Γ (c ⊗ d)
  /-- `⊢ c ⊕ d, Γ` from `⊢ c, Γ`. -/
  | oplus₁ {c d : Proposition Atom} (p : CF⇓(c ::ₘ Γ)) : CF.Proof.Principal Γ (c ⊕ d)
  /-- `⊢ c ⊕ d, Γ` from `⊢ d, Γ`. -/
  | oplus₂ {c d : Proposition Atom} (p : CF⇓(d ::ₘ Γ)) : CF.Proof.Principal Γ (c ⊕ d)
  /-- `⊢ c & d, Γ` from `⊢ c, Γ` and `⊢ d, Γ`. -/
  | with {c d : Proposition Atom} (p : CF⇓(c ::ₘ Γ)) (q : CF⇓(d ::ₘ Γ)) :
      CF.Proof.Principal Γ (c & d)
  /-- `⊢ !c, Γ` from `⊢ c, Γ`, where `Γ` consists of `ʔ`-propositions. -/
  | bang {c : Proposition Atom} (hG : Γ.allQuest) (p : CF⇓(c ::ₘ Γ)) :
      CF.Proof.Principal Γ (!c)

/-- Principal cuts: cut two proofs whose last rules introduce `a` and `a⫠`. The cut is replaced
by at most two cuts on immediate subpropositions of `a`, which are admissible by `cutSmaller`.
The pairs `(⊤, 0)` and `(!, ʔ)` cannot occur, because `0` and `ʔ` have no `Principal`
constructor. -/
def Proof.cutPrincipal {a : Proposition Atom} (cutSmaller : CutAdmissibleBelow Atom (sizeOf a))
    {Γ Δ : List (Proposition Atom)}
    (vp : CF.Proof.Principal Γ a) (vq : CF.Proof.Principal Δ a⫠) :
    CF⇓((Γ : Sequent Atom) + Δ) :=
  match (generalizing := true) vp, vq with
  | .one hG, .bot q => q.rwConclusion (by rw [hG, Multiset.zero_add])
  | .bot p, .one hD => p.rwConclusion (by rw [hD, Multiset.add_zero])
  | .top, vq => nomatch vq
  | .bang _ _, vq => nomatch vq
  -- Cut `c` between `⊢ c, Λ` and `⊢ c⫠, d⫠, Δ`, then `d` against `⊢ d, R`.
  | .tensor (c := c) (d := d) (Λ := Λ) (R := R) hG p₁ p₂, .parr q =>
    let q' : CF⇓(d⫠ ::ₘ (Λ ++ Δ : List (Proposition Atom))) :=
      (cutSmaller (a := c) (by grind) (Δ := d⫠ :: Δ) p₁ q).rwConclusion
    (cutSmaller (a := d) (by grind) p₂ q').rwConclusion
  -- Cut `c` between `⊢ c, d, Γ` and `⊢ c⫠, Λ`, then `d` against `⊢ d⫠, R`.
  | .parr (c := c) (d := d) p, .tensor (Λ := Λ) (R := R) hD q₁ q₂ =>
    let p' : CF⇓(d ::ₘ (Γ ++ Λ : List (Proposition Atom))) :=
      (cutSmaller (a := c) (by grind) (Γ := d :: Γ) p q₁).rwConclusion
    (cutSmaller (a := d) (by grind) p' q₂).rwConclusion
  | .oplus₁ (c := c) p, .with q _ => cutSmaller (a := c) (by grind) p q
  | .oplus₂ (d := d) p, .with _ q => cutSmaller (a := d) (by grind) p q
  | .with (c := c) p _, .oplus₁ q => cutSmaller (a := c) (by grind) p q
  | .with (d := d) _ p, .oplus₂ q => cutSmaller (a := d) (by grind) p q

/-! ## Moving cuts upwards

If the cut proposition is not introduced by the last rule of a premise, the cut is moved above
that rule. -/

/-- If an axiom conclusion `{c, c⫠}` contains `x`, then the rest of it is `x⫠`. -/
theorem Sequent.eq_dual_of_pair_eq_cons {c x : Proposition Atom} {Δ : Sequent Atom}
    (h : {c, c⫠} = x ::ₘ Δ) : Δ = {x⫠} := by
  have hx : x ∈ ({c, c⫠} : Sequent Atom) := by rw [h]; exact Multiset.mem_cons_self _ _
  rcases Multiset.mem_cons.mp hx with rfl | hx
  · exact ((Multiset.cons_inj_right x).mp h).symm
  · obtain rfl : x = c⫠ := Multiset.mem_singleton.mp hx
    rw [Multiset.pair_comm, Multiset.insert_eq_cons] at h
    rw [Proposition.dual_involution]
    exact ((Multiset.cons_inj_right c⫠).mp h).symm

/-- Prepends a list of propositions to a sequent, one `::ₘ` at a time.

This exists so that a single helper can rebuild any rule after a recursive call. The premise
of a rule has the form `c ::ₘ d ::ₘ Ξ` (for `⅋`), `c ::ₘ Ξ` (for `⊕₁`, dereliction, ...), or
`Ξ` (for `⊥`, weakening), where `Ξ` is the context. Each of these is *definitionally*
`Sequent.prepend act Ξ` for the list `act` of active propositions (`[c, d]`, `[c]`, or `[]`), so
rules like `CF.Proof.parr` can be passed directly as functions on
`CF⇓(Sequent.prepend act Ξ)`, whereas `↑act + Ξ` would require a cast for every rule. See
`CutBelowHeight.rebuild` and `QuestMulticutGoal.rebuild`. -/
abbrev Sequent.prepend : List (Proposition Atom) → Sequent Atom → Sequent Atom
  | [], Ξ => Ξ
  | c :: act, Ξ => c ::ₘ Sequent.prepend act Ξ

/-- `Sequent.prepend` is addition. -/
theorem Sequent.prepend_eq_add (act : List (Proposition Atom)) (Ξ : Sequent Atom) :
    Sequent.prepend act Ξ = act + Ξ := by
  induction act with
  | nil => rw [Sequent.prepend, Multiset.coe_nil, Multiset.zero_add]
  | cons c act ih => rw [Sequent.prepend, ih]; grind only [multiset]

/-- The induction hypothesis of a commuting step: a cut on `a` against the fixed proof of
`⊢ a⫠, Δ` is admissible for every proof of `⊢ a, Γ'` of height less than `bound`. -/
abbrev CutBelowHeight (a : Proposition Atom) (Δ : List (Proposition Atom)) (bound : ℕ) :
    Type u :=
  ∀ {Γ' : List (Proposition Atom)} (p' : CF⇓(a ::ₘ Γ')), p'.val.height < bound →
    CF⇓((Γ' : Sequent Atom) + Δ)

/-- A commuting step of a cut on `a`. Let `s` be a premise of the last rule, with active
propositions `act` and context `Θ = a ::ₘ Λ` (which contains the cut proposition). Cut `s`
against the fixed proof of `⊢ a⫠, Δ` using `recur`, and apply `rule` to the result. -/
def CutBelowHeight.rebuild {a : Proposition Atom} {Δ Λ : List (Proposition Atom)}
    {Θ X : Sequent Atom} {bound : ℕ}
    (recur : CutBelowHeight a Δ bound) (act : List (Proposition Atom))
    (s : CF⇓(Sequent.prepend act Θ)) (hs : s.val.height < bound) (hΘ : Θ = a ::ₘ Λ)
    (rule : CF⇓(Sequent.prepend act ((Λ : Sequent Atom) + Δ)) → CF⇓X) : CF⇓X :=
  let s' : CF⇓(a ::ₘ ↑(act ++ Λ)) :=
    s.rwConclusion (by rw [Sequent.prepend_eq_add, hΘ]; grind only [multiset])
  rule ((recur s' (by rwa [CF.Proof.rwConclusion_val, Proof.rwConclusion_height])).rwConclusion
    (by rw [Sequent.prepend_eq_add]; grind only [multiset]))

/-- One step towards a principal cut, on one premise. Let `r` be a cut-free proof of `⊢ a, Γ`,
where `a` is not a `ʔ`-proposition, to be cut against `q : ⊢ a⫠, Δ`. Then either `a` is
principal in the last rule of `r`, and we return the premises of that rule
(`CF.Proof.Principal`), or we return a cut-free proof of `⊢ Γ, Δ` directly:
* if `r` is the axiom `⊢ a, a⫠`, the result is `q`;
* otherwise the last rule of `r` acts on `Γ`, and the cut is moved above it: `recur` (the
  induction hypothesis on proof height) cuts a premise of `r` against `q`, and the rule is
  applied again to the result.

This function is not recursive; recursion happens in its callers through `recur`. The proof
`r` is given with a separate cut-freeness proof `hr` so that it can be matched on. -/
def Proof.principalOrCommute [DecidableEq Atom]
    {a : Proposition Atom} (notQuest : ∀ b, a ≠ ʔb)
    {Θ : Sequent Atom} {Γ Δ : List (Proposition Atom)} (r : Proof Θ) (hr : r.IsCutFree) :
      Θ = a ::ₘ Γ → CF⇓(a⫠ ::ₘ Δ) → CutBelowHeight a Δ r.height →
      CF.Proof.Principal Γ a ⊕' CF⇓((Γ : Sequent Atom) + Δ) :=
  -- In the commuting cases, `hG : ↑Γ = _ ::ₘ ↑Λ` is used by the default `grind` argument of
  -- `rwConclusion`.
  match r, hr with
  | .ax, _ => fun h q _ =>
    .inr (q.rwConclusion (by rw [Sequent.eq_dual_of_pair_eq_cons h]; grind only [multiset]))
  | .one, _ => fun h _ _ =>
    match Multiset.splitCons h.symm with
    | .inl ⟨ha, hG⟩ => ha ▸ .inl (.one hG)
    | .inr ⟨_, _, hS⟩ => absurd hS Multiset.zero_ne_cons
  | .top, _ => fun h _ _ =>
    match Multiset.splitCons h.symm with
    | .inl ⟨ha, _⟩ => ha ▸ .inl .top
    | .inr ⟨Λ, hG, _⟩ =>
      .inr (CF.Proof.top (Γ := (Λ : Sequent Atom) + (Δ : Sequent Atom))).rwConclusion
  | .bot s, hs => fun h _ recur =>
    match Multiset.splitCons h.symm with
    | .inl ⟨ha, hG⟩ => ha ▸ .inl (.bot (CF.Proof.rwConclusion hG.symm ⟨s, hs⟩))
    | .inr ⟨_, hG, hS⟩ =>
      .inr (recur.rebuild [] ⟨s, hs⟩ (Nat.lt_add_one _) hS (CF.Proof.bot ·)).rwConclusion
  | .parr s, hs => fun h _ recur =>
    match Multiset.splitCons h.symm with
    | .inl ⟨ha, hG⟩ => ha ▸ .inl (.parr (CF.Proof.rwConclusion (by rw [hG]) ⟨s, hs⟩))
    | .inr ⟨_, hG, hS⟩ =>
      .inr (recur.rebuild [_, _] ⟨s, hs⟩ (Nat.lt_add_one _) hS (CF.Proof.parr ·)).rwConclusion
  | .tensor s t, hst => fun h _ recur =>
    match Multiset.splitCons h.symm with
    | .inl ⟨ha, hG⟩ =>
      -- Present the contexts of both premises as lists taken from `Γ`.
      let (⟨Λ, hL⟩, ⟨R, hR⟩) := Multiset.scanToListAdd Γ hG.symm
      ha ▸ .inl (.tensor (Λ := Λ) (R := R) (by rw [hL, hR]; exact hG)
        (CF.Proof.rwConclusion (by rw [hL]) ⟨s, hst.1⟩)
        (CF.Proof.rwConclusion (by rw [hR]) ⟨t, hst.2⟩))
    | .inr ⟨_, hG, hST⟩ =>
      -- The cut proposition is in the context of one of the two premises.
      match Multiset.splitConsAdd hST.symm with
      | .inl ⟨_, hS⟩ =>
        .inr (recur.rebuild [_] ⟨s, hst.1⟩ (by grind [Proof.height]) hS
          (CF.Proof.tensor · ⟨t, hst.2⟩)).rwConclusion
      | .inr ⟨_, hT⟩ =>
        .inr (recur.rebuild [_] ⟨t, hst.2⟩ (by grind [Proof.height]) hT
          (CF.Proof.tensor ⟨s, hst.1⟩ ·)).rwConclusion
  | .oplus₁ (b := d) s, hs => fun h _ recur =>
    match Multiset.splitCons h.symm with
    | .inl ⟨ha, hG⟩ => ha ▸ .inl (.oplus₁ (CF.Proof.rwConclusion (by rw [hG]) ⟨s, hs⟩))
    | .inr ⟨_, hG, hS⟩ =>
      .inr (recur.rebuild [_] ⟨s, hs⟩ (Nat.lt_add_one _) hS
        (CF.Proof.oplus₁ (b := d) ·)).rwConclusion
  | .oplus₂ (a := c) s, hs => fun h _ recur =>
    match Multiset.splitCons h.symm with
    | .inl ⟨ha, hG⟩ => ha ▸ .inl (.oplus₂ (CF.Proof.rwConclusion (by rw [hG]) ⟨s, hs⟩))
    | .inr ⟨_, hG, hS⟩ =>
      .inr (recur.rebuild [_] ⟨s, hs⟩ (Nat.lt_add_one _) hS
        (CF.Proof.oplus₂ (a := c) ·)).rwConclusion
  | .with s t, hst => fun h _ recur =>
    match Multiset.splitCons h.symm with
    | .inl ⟨ha, hG⟩ => ha ▸ .inl (.with (CF.Proof.rwConclusion (by rw [hG]) ⟨s, hst.1⟩)
        (CF.Proof.rwConclusion (by rw [hG]) ⟨t, hst.2⟩))
    | .inr ⟨Λ, hG, hS⟩ =>
      -- Both premises contain the cut proposition: cut both, then reapply `&`.
      let t' : CF⇓(_ ::ₘ ((Λ : Sequent Atom) + (Δ : Sequent Atom))) :=
        recur.rebuild [_] ⟨t, hst.2⟩ (by grind [Proof.height]) hS id
      .inr (recur.rebuild [_] ⟨s, hst.1⟩ (by grind [Proof.height]) hS
        (CF.Proof.with · t')).rwConclusion
  | .quest s, hs => fun h _ recur =>
    match Multiset.splitCons h.symm with
    | .inl ⟨ha, _⟩ => absurd ha (notQuest _)
    | .inr ⟨_, hG, hS⟩ =>
      .inr (recur.rebuild [_] ⟨s, hs⟩ (Nat.lt_add_one _) hS (CF.Proof.quest ·)).rwConclusion
  | .weaken (a := c) s, hs => fun h _ recur =>
    match Multiset.splitCons h.symm with
    | .inl ⟨ha, _⟩ => absurd ha (notQuest _)
    | .inr ⟨_, hG, hS⟩ =>
      .inr (recur.rebuild [] ⟨s, hs⟩ (Nat.lt_add_one _) hS
        (CF.Proof.weaken (a := c) ·)).rwConclusion
  | .contract s, hs => fun h _ recur =>
    match Multiset.splitCons h.symm with
    | .inl ⟨ha, _⟩ => absurd ha (notQuest _)
    | .inr ⟨_, hG, hS⟩ =>
      .inr (recur.rebuild [_, _] ⟨s, hs⟩ (Nat.lt_add_one _) hS
        (CF.Proof.contract ·)).rwConclusion
  | .bang hΘ s, hs => fun h _ _ =>
    match Multiset.splitCons h.symm with
    | .inl ⟨ha, hG⟩ =>
      ha ▸ .inl (.bang (by rw [← Sequent.allQuest_coe, hG]; exact hΘ)
        (CF.Proof.rwConclusion (by rw [hG]) ⟨s, hs⟩))
    -- The context of a promotion consists of `ʔ`-propositions, so it cannot contain `a`.
    | .inr ⟨_, _, hS⟩ =>
      absurd (Sequent.exists_quest_of_mem_allQuest hΘ (hS ▸ Multiset.mem_cons_self _ _))
        (not_exists.mpr notQuest)
  | .cut _ _, h => nomatch h

/-! ## Non-exponential cuts -/

/-- Cut admissibility at a proposition `a` such that neither `a` nor `a⫠` is a
`ʔ`-proposition, assuming it holds for smaller propositions. By induction on the sum of the
heights of the premises: move the cut upwards in the left premise until `a` is principal
there, then do the same in the right premise (`Proof.principalOrCommute`), and finally reduce
the principal cut (`Proof.cutPrincipal`). -/
def Proof.cutAdmNonExponential [DecidableEq Atom] {a : Proposition Atom}
    (cutSmaller : CutAdmissibleBelow Atom (sizeOf a))
    (notQuest : ∀ b, a ≠ ʔb) (dualNotQuest : ∀ b, a⫠ ≠ ʔb) {Γ Δ : List (Proposition Atom)}
    (p : CF⇓(a ::ₘ Γ)) (q : CF⇓(a⫠ ::ₘ Δ)) : CF⇓((Γ : Sequent Atom) + Δ) :=
  match Proof.principalOrCommute notQuest p.val p.property rfl q
      (fun p' _ => Proof.cutAdmNonExponential cutSmaller notQuest dualNotQuest p' q) with
  | .inr r => r
  | .inl vp =>
    match Proof.principalOrCommute (Γ := Δ) (Δ := Γ) dualNotQuest q.val q.property rfl
        (p.rwConclusion (by rw [Proposition.dual_involution]))
        (fun q' _ =>
          (Proof.cutAdmNonExponential cutSmaller notQuest dualNotQuest p q').rwConclusion) with
    | .inr r => r.rwConclusion
    | .inl vq => Proof.cutPrincipal cutSmaller vp vq
termination_by p.val.height + q.val.height
decreasing_by all_goals lia

/-! ## Exponential cuts

Cutting `!a` against `ʔ(a⫠)` requires a multicut, because `ʔ(a⫠)` may be contracted. -/

/-- An axiom conclusion `{c, c⫠}` contains at most one copy of `x`, since `x ≠ x⫠`. -/
theorem Sequent.eq_dual_of_pair_eq_replicate_succ {c x : Proposition Atom} {m : ℕ}
    {Δ : Sequent Atom} (h : {c, c⫠} = Multiset.replicate (m + 1) x + Δ) : Δ = {x⫠} := by
  rw [Multiset.replicate_succ, Multiset.cons_add] at h
  have h := Sequent.eq_dual_of_pair_eq_cons h
  cases m with
  | zero => rwa [Multiset.replicate_zero, Multiset.zero_add] at h
  | succ m =>
    have hx : x ∈ ({x⫠} : Sequent Atom) := by
      rw [← h, Multiset.replicate_succ, Multiset.cons_add]
      exact Multiset.mem_cons_self _ _
    exact absurd (Multiset.mem_singleton.mp hx) (Proposition.dual_neq x)

/-- What `Proof.questMulticut` computes from a cut-free proof of `Θ`, where `p : ⊢ a, Γ` is
fixed: for every presentation of `Θ` as `n` selected occurrences of `ʔ(a⫠)` plus a residual
context `Δ`, a cut-free proof of `⊢ Γ, Δ` (the selected occurrences have been cut against the
promotion `⊢ !a, Γ` of `p`). The residual context is a list because the cut on `a`
(dereliction case) takes list contexts, and because
`Multiset.splitReplicateCons`/`Multiset.splitReplicateAdd` compute the residual contexts of
premises from it. -/
abbrev QuestMulticutGoal (a : Proposition Atom) (Γ : List (Proposition Atom))
    (Θ : Sequent Atom) : Type u :=
  ∀ {n : ℕ} {Δ : List (Proposition Atom)},
    Θ = Multiset.replicate n (ʔ(a⫠)) + Δ → CF⇓((Γ : Sequent Atom) + Δ)

/-- If the principal proposition `b` of a rule is not `ʔ(a⫠)`, then it is not selected: it
belongs to the residual context `Δ = b ::ₘ Δ'`. -/
def residualHead [DecidableEq Atom] {a b : Proposition Atom} {Θ : Sequent Atom} {n : ℕ}
    {Δ : List (Proposition Atom)} (h : b ::ₘ Θ = Multiset.replicate n (ʔ(a⫠)) + Δ)
    (hb : b ≠ ʔ(a⫠) := by nofun) :
    {Δ' : List (Proposition Atom) //
      (Δ : Sequent Atom) = b ::ₘ Δ' ∧ Θ = Multiset.replicate n (ʔ(a⫠)) + Δ'} :=
  match Multiset.splitReplicateCons h with
  | .replicate _ _ hb' _ => absurd hb' hb
  | .list Δ' hΔ hΘ => ⟨Δ', hΔ, hΘ⟩

/-- Commutes the multicut past a rule with one premise whose principal proposition `b` is
residual: cut the premise (whose active propositions are `act`) using the induction
hypothesis `ih`, then apply the rule again. -/
def QuestMulticutGoal.rebuild {a b : Proposition Atom} {Γ : List (Proposition Atom)}
    {Θ : Sequent Atom} (act : List (Proposition Atom))
    (ih : QuestMulticutGoal a Γ (Sequent.prepend act Θ))
    {n : ℕ} {Δ Δ' : List (Proposition Atom)}
    (hΔ : (Δ : Sequent Atom) = b ::ₘ Δ') (hΘ : Θ = Multiset.replicate n (ʔ(a⫠)) + Δ')
    (rule : CF⇓(Sequent.prepend act ((Γ : Sequent Atom) + Δ')) →
      CF⇓(b ::ₘ ((Γ : Sequent Atom) + Δ'))) :
    CF⇓((Γ : Sequent Atom) + Δ) :=
  have hih : Sequent.prepend act Θ = Multiset.replicate n (ʔ(a⫠)) + ↑(act ++ Δ') := by
    rw [Sequent.prepend_eq_add, hΘ]; grind only [multiset]
  (rule ((ih hih).rwConclusion (by rw [Sequent.prepend_eq_add]; grind only [multiset])))
    |>.rwConclusion

/-- `QuestMulticutGoal.rebuild` for a rule whose principal proposition `b` cannot be
selected, because it is not `ʔ(a⫠)`. -/
def QuestMulticutGoal.commute [DecidableEq Atom] {a b : Proposition Atom}
    {Γ : List (Proposition Atom)} {Θ : Sequent Atom} (act : List (Proposition Atom))
    (ih : QuestMulticutGoal a Γ (Sequent.prepend act Θ))
    (rule : ∀ {Ξ : Sequent Atom}, CF⇓(Sequent.prepend act Ξ) → CF⇓(b ::ₘ Ξ))
    (hb : b ≠ ʔ(a⫠) := by nofun) :
    QuestMulticutGoal a Γ (b ::ₘ Θ) := fun h =>
  let ⟨_, hΔ, hΘ⟩ := residualHead h hb
  ih.rebuild act hΔ hΘ rule

/-- Axiom case of `Proof.questMulticut`. The axiom `⊢ c, c⫠` contains at most one selected
occurrence of `ʔ(a⫠)`, since `c ≠ c⫠`. If it contains none (`n = 0`), the result is the axiom
weakened by `Γ`. Otherwise, the other side of the axiom is `(ʔ(a⫠))⫠ = !a`, and the result is
the promotion of `p`. -/
def Proof.questMulticutAx {a : Proposition Atom} {Γ : List (Proposition Atom)}
    (hΓ : Γ.allQuest) (p : CF⇓(a ::ₘ Γ)) {c : Proposition Atom} :
    QuestMulticutGoal a Γ {c, c⫠} := fun {n} {Δ} h =>
  match n with
  | 0 =>
    (CF.Proof.weakenContext hΓ (CF.Proof.ax (a := c))).rwConclusion
      (by rw [h, Multiset.replicate_zero, Multiset.zero_add])
  | _ + 1 =>
    have hΔ : (Δ : Sequent Atom) = {!a} := by
      rw [Sequent.eq_dual_of_pair_eq_replicate_succ h, Proposition.dual,
        Proposition.dual_involution]
    (CF.Proof.bang (Sequent.allQuest_coe Γ ▸ hΓ) p).rwConclusion (by grind only [multiset])

/-- Multicut for the exponential case. Let `p : ⊢ a, Γ` be the premise of a promotion (so `Γ`
consists of `ʔ`-propositions), and let `q : ⊢ ʔ(a⫠)ⁿ, Δ` be a cut-free proof in which `n`
occurrences of `ʔ(a⫠)` are selected. The result cuts `!a` (the promotion of `p`) against all
`n` selected occurrences at once, giving `⊢ Γ, Δ`. The conclusion contains `Γ` exactly once,
whatever `n` is: the copies of `Γ` produced by several cuts are merged by contraction
(`CF.Proof.contractContext`), and when there are no cuts `Γ` is added by weakening
(`CF.Proof.weakenContext`).

The definition is by structural recursion on `q` (`Proof.IsCutFree.rec`), with motive
`QuestMulticutGoal`. A selected occurrence is dropped when weakening introduced it, becomes
two selected occurrences when contraction introduced it, and is cut against `p` (at the
smaller proposition `a`, via `cutSmaller`) when dereliction introduced it. Every other rule is
commuted with the multicut. -/
def Proof.questMulticut [DecidableEq Atom] {a : Proposition Atom}
    (cutSmaller : CutAdmissibleBelow Atom (sizeOf (!a)))
    {Γ Δ : List (Proposition Atom)} (hΓ : Γ.allQuest) (p : CF⇓(a ::ₘ Γ)) {n : ℕ}
    (q : CF⇓(Multiset.replicate n (ʔ(a⫠)) + Δ)) : CF⇓((Γ : Sequent Atom) + Δ) :=
  have hΓm : Sequent.allQuest (Γ : Sequent Atom) := Sequent.allQuest_coe Γ ▸ hΓ
  -- Each case binds, in order: the implicit arguments of the rule, its premises, their
  -- (implicit) cut-freeness proofs, the induction hypotheses, and then the arguments
  -- `{n Δ} h` of `QuestMulticutGoal`.
  Proof.IsCutFree.rec (motive := fun {Θ} {_} _ => QuestMulticutGoal a Γ Θ)
    (ax := Proof.questMulticutAx hΓ p)
    (one := fun h =>
      let ⟨_, hΔ, h0⟩ := residualHead h
      (CF.Proof.weakenContext hΓ CF.Proof.one).rwConclusion
        (by rw [hΔ, Multiset.eq_zero_of_zero_eq_add h0]; rfl))
    (top := fun {Θ} {n Δ} h =>
      let ⟨Δ', hΔ, _⟩ := residualHead h
      (CF.Proof.top (Γ := (Γ : Sequent Atom) + (Δ' : Sequent Atom))).rwConclusion)
    (bot := fun {Θ} _ {_} ih => ih.commute [] CF.Proof.bot)
    (parr := fun {c d Θ} _ {_} ih => ih.commute [c, d] CF.Proof.parr)
    (tensor := fun {c d Θ₁ Θ₂} _ _ {_ _} ihp ihq {n Δ} h =>
      let ⟨Δ', hΔ, hΘ⟩ := residualHead h
      -- Distribute the selected occurrences and the residual context over the two premises,
      -- cut both, and contract the two copies of `Γ`.
      let ⟨k₁, k₂, Δ₁, Δ₂, _, h₁, h₂, hres⟩ := Multiset.splitReplicateAdd hΘ
      let p' : CF⇓(c ::ₘ ((Γ : Sequent Atom) + Δ₁)) :=
        (ihp (n := k₁) (Δ := c :: Δ₁) (by grind only [multiset])).rwConclusion
      let q' : CF⇓(d ::ₘ ((Γ : Sequent Atom) + Δ₂)) :=
        (ihq (n := k₂) (Δ := d :: Δ₂) (by grind only [multiset])).rwConclusion
      let t : CF⇓((Γ : Sequent Atom) + Γ + ((c ⊗ d) ::ₘ ((Δ₁ : Sequent Atom) + Δ₂))) :=
        (CF.Proof.tensor p' q').rwConclusion
      (CF.Proof.contractContext hΓ t).rwConclusion)
    (oplus₁ := fun {c d Θ} _ {_} ih => ih.commute [c] CF.Proof.oplus₁)
    (oplus₂ := fun {c d Θ} _ {_} ih => ih.commute [d] CF.Proof.oplus₂)
    («with» := fun {c d Θ} _ _ {_ _} ihp ihq {n Δ} h =>
      let ⟨Δ', hΔ, hΘ⟩ := residualHead h
      let p' : CF⇓(c ::ₘ ((Γ : Sequent Atom) + Δ')) :=
        (ihp (n := n) (Δ := c :: Δ') (by grind only [multiset])).rwConclusion
      let q' : CF⇓(d ::ₘ ((Γ : Sequent Atom) + Δ')) :=
        (ihq (n := n) (Δ := d :: Δ') (by grind only [multiset])).rwConclusion
      (CF.Proof.with p' q').rwConclusion)
    (quest := fun {c Θ} _ {_} ih {n Δ} h =>
      match Multiset.splitReplicateCons h with
      -- A selected occurrence introduced by dereliction: after eliminating the other
      -- selected occurrences, cut the exposed `a⫠` against `p` and contract `Γ`.
      | .replicate m hn hc hΘ =>
        have hc : c = a⫠ := by injection hc
        let r : CF⇓(a⫠ ::ₘ ((Γ ++ Δ : List (Proposition Atom)) : Sequent Atom)) :=
          (ih (n := m) (Δ := c :: Δ) (by grind only [multiset])).rwConclusion
        CF.Proof.contractContext hΓ (cutSmaller (by simp) p r).rwConclusion
      | .list _ hΔ hΘ => ih.rebuild [c] hΔ hΘ (CF.Proof.quest ·))
    (weaken := fun {c Θ} _ {_} ih {n Δ} h =>
      match Multiset.splitReplicateCons h with
      -- A selected occurrence introduced by weakening is dropped.
      | .replicate _ _ _ hΘ => ih hΘ
      | .list _ hΔ hΘ => ih.rebuild [] hΔ hΘ CF.Proof.weaken)
    (contract := fun {c Θ} _ {_} ih {n Δ} h =>
      match Multiset.splitReplicateCons h with
      -- A selected occurrence introduced by contraction becomes two selected occurrences.
      | .replicate m hn hc hΘ => ih (n := n + 1) (by grind only [multiset])
      | .list _ hΔ hΘ => ih.rebuild [ʔc, ʔc] hΔ hΘ (CF.Proof.contract ·))
    (bang := fun {c Θ} hΘq _ {_} ih {n Δ} h =>
      let ⟨Δ', hΔ, hΘ⟩ := residualHead h
      -- The new context `Γ + Δ'` of the promotion still consists of `ʔ`-propositions.
      have hside : Sequent.allQuest ((Γ : Sequent Atom) + (Δ' : Sequent Atom)) := by
        rw [hΘ, Sequent.allQuest_add] at hΘq
        exact Sequent.allQuest_add.mpr ⟨hΓm, hΘq.2⟩
      ih.rebuild [c] hΔ hΘ (CF.Proof.bang hside))
    q.property rfl

/-- Cut admissibility at `!a`, assuming it holds for propositions smaller than `!a`. By
induction on the height of the proof `p` of `⊢ !a, Γ`: move the cut upwards in `p`
(`Proof.principalOrCommute`) until `!a` is introduced by a promotion with premise `⊢ a, Γ`.
Then cut this promotion against the single selected occurrence of `ʔ(a⫠)` in `q`, using
`Proof.questMulticut` with `n = 1`. -/
def Proof.bangCutAdm [DecidableEq Atom] {a : Proposition Atom}
    (cutSmaller : CutAdmissibleBelow Atom (sizeOf (!a)))
    {Γ Δ : List (Proposition Atom)}
    (p : CF⇓((!a) ::ₘ Γ)) (q : CF⇓(ʔ(a⫠) ::ₘ Δ)) :
    CF⇓((Γ : Sequent Atom) + Δ) :=
  match Proof.principalOrCommute (a := !a) (fun _ => nofun) p.val p.property rfl q
      (fun p' _ => Proof.bangCutAdm cutSmaller p' q) with
  | .inr r => r
  | .inl (.bang hG p₀) => Proof.questMulticut (n := 1) cutSmaller hG p₀ q
termination_by p.val.height
decreasing_by assumption

/-- Cut admissibility at `ʔa`. Since `(ʔa)⫠ = !(a⫠)` has the same size, swap the premises and
use `Proof.bangCutAdm` at `!(a⫠)`. -/
def Proof.questCutAdm [DecidableEq Atom] {a : Proposition Atom}
    (cutSmaller : CutAdmissibleBelow Atom (sizeOf (ʔa)))
    {Γ Δ : List (Proposition Atom)}
    (p : CF⇓(ʔa ::ₘ Γ)) (q : CF⇓((!(a⫠)) ::ₘ Δ)) :
    CF⇓((Γ : Sequent Atom) + Δ) :=
  let cutSmaller' : CutAdmissibleBelow Atom (sizeOf (!(a⫠))) := fun hb =>
    cutSmaller (by rwa [Proposition.bang.sizeOf_spec, Proposition.dual_sizeOf] at hb)
  (Proof.bangCutAdm (Δ := Γ) cutSmaller' q (p.rwConclusion (by rw [Proposition.dual_involution])))
    |>.rwConclusion

/-! ## Cut admissibility -/

/-- The step of the outer induction: cut admissibility at `a`, assuming it at all smaller
propositions, by cases on the main connective of `a`: `Proof.bangCutAdm` for `!`,
`Proof.questCutAdm` for `ʔ`, and `Proof.cutAdmNonExponential` otherwise. -/
def Proof.cutAdmOfSmaller [DecidableEq Atom] {a : Proposition Atom}
    (cutSmaller : CutAdmissibleBelow Atom (sizeOf a)) : CutAdmissibleAt a :=
  match a with
  | .bang _ => Proof.bangCutAdm cutSmaller
  | .quest _ => Proof.questCutAdm cutSmaller
  | .atom _ | .atomDual _ | .one | .zero | .top | .bot | .tensor _ _ | .parr _ _
  | .oplus _ _ | .with _ _ =>
    Proof.cutAdmNonExponential cutSmaller (fun _ => nofun) (fun _ => nofun)

/-- **Cut admissibility** for CF: from cut-free proofs of `⊢ a, Γ` and `⊢ a⫠, Δ`, compute a
cut-free proof of `⊢ Γ, Δ`, by well-founded recursion on the size of `a`. -/
def Proof.cutAdm [DecidableEq Atom] {a : Proposition Atom} {Γ Δ : List (Proposition Atom)}
    (p : CF⇓(a ::ₘ Γ)) (q : CF⇓(a⫠ ::ₘ Δ)) : CF⇓((Γ : Sequent Atom) + Δ) :=
  Proof.cutAdmOfSmaller (fun {c} _hc {_ _} p' q' => Proof.cutAdm (a := c) p' q') p q
termination_by sizeOf a
decreasing_by exact _hc

/-! ## Cut elimination -/

/-- Cut elimination for a proof `r` of `Θ`, given a list `Γ` that represents `Θ`. By structural
recursion on `r`: each rule other than cut is rebuilt from the cut-free proofs of its premises,
whose contexts are given as lists taken from `Γ` (`List.erase`, or
`Multiset.scanToListAdd` for the two premises of `⊗` and cut), and each cut is replaced by
`Proof.cutAdm`. -/
def Proof.cutElimAux [DecidableEq Atom] {Θ : Sequent Atom} (r : Proof Θ)
    (Γ : List (Proposition Atom)) (h : Θ = (Γ : Sequent Atom)) : CF⇓(Γ : Sequent Atom) :=
  -- In each case, `hL : Θ' = ↑(Γ.erase _)` presents the premise context as a list; it is used
  -- by the default `grind` argument of `rwConclusion`.
  match r with
  | .ax (a := c) => (CF.Proof.ax (a := c)).rwConclusion h
  | .one => (CF.Proof.one (Atom := Atom)).rwConclusion h
  | .top (Γ := Ξ) => (CF.Proof.top (Γ := Ξ)).rwConclusion h
  | .bot s =>
    have hL := Multiset.eq_coe_erase_of_cons_eq h
    (CF.Proof.bot (cutElimAux s _ hL)).rwConclusion
  | .parr (a := c) (b := d) s =>
    have hL := Multiset.eq_coe_erase_of_cons_eq h
    let s' := cutElimAux s (c :: d :: Γ.erase (c ⅋ d)) (by grind only [multiset])
    (CF.Proof.parr (a := c) (b := d) (Γ := Γ.erase (c ⅋ d)) s').rwConclusion
  | .tensor (a := c) (b := d) s t =>
    have hK := Multiset.eq_coe_erase_of_cons_eq h
    let (⟨Λ, hL⟩, ⟨R, hR⟩) := Multiset.scanToListAdd _ hK
    let s' := cutElimAux s (c :: Λ) (by grind only [multiset])
    let t' := cutElimAux t (d :: R) (by grind only [multiset])
    (CF.Proof.tensor (a := c) (b := d) (Γ := Λ) (Δ := R) s' t').rwConclusion
  | .oplus₁ (a := c) (b := d) s =>
    have hL := Multiset.eq_coe_erase_of_cons_eq h
    let s' := cutElimAux s (c :: Γ.erase (c ⊕ d)) (by grind only [multiset])
    (CF.Proof.oplus₁ (a := c) (b := d) (Γ := Γ.erase (c ⊕ d)) s').rwConclusion
  | .oplus₂ (a := c) (b := d) s =>
    have hL := Multiset.eq_coe_erase_of_cons_eq h
    let s' := cutElimAux s (d :: Γ.erase (c ⊕ d)) (by grind only [multiset])
    (CF.Proof.oplus₂ (a := c) (b := d) (Γ := Γ.erase (c ⊕ d)) s').rwConclusion
  | .with (a := c) (b := d) s t =>
    have hL := Multiset.eq_coe_erase_of_cons_eq h
    let s' := cutElimAux s (c :: Γ.erase (c & d)) (by grind only [multiset])
    let t' := cutElimAux t (d :: Γ.erase (c & d)) (by grind only [multiset])
    (CF.Proof.with (a := c) (b := d) (Γ := Γ.erase (c & d)) s' t').rwConclusion
  | .quest (a := c) s =>
    have hL := Multiset.eq_coe_erase_of_cons_eq h
    let s' := cutElimAux s (c :: Γ.erase (ʔc)) (by grind only [multiset])
    (CF.Proof.quest (a := c) (Γ := Γ.erase (ʔc)) s').rwConclusion
  | .weaken (a := c) s =>
    have hL := Multiset.eq_coe_erase_of_cons_eq h
    (CF.Proof.weaken (a := c) (cutElimAux s _ hL)).rwConclusion
  | .contract (a := c) s =>
    have hL := Multiset.eq_coe_erase_of_cons_eq h
    let s' := cutElimAux s (ʔc :: ʔc :: Γ.erase (ʔc)) (by grind only [multiset])
    (CF.Proof.contract (a := c) (Γ := Γ.erase (ʔc)) s').rwConclusion
  | .bang (a := c) hS s =>
    have hL := Multiset.eq_coe_erase_of_cons_eq h
    let s' := cutElimAux s (c :: Γ.erase (!c)) (by grind only [multiset])
    (CF.Proof.bang (a := c) (Γ := Γ.erase (!c)) (hL ▸ hS) s').rwConclusion
  | .cut (a := c) s t =>
    let (⟨Λ, hL⟩, ⟨R, hR⟩) := Multiset.scanToListAdd Γ h
    let s' := cutElimAux s (c :: Λ) (by grind only [multiset])
    let t' := cutElimAux t (c⫠ :: R) (by grind only [multiset])
    (Proof.cutAdm s' t').rwConclusion

/-- **Cut elimination** for sequents given as lists: every proof of `Γ` can be transformed into
a cut-free proof of `Γ`. Computable. -/
def Proof.cutElimList [DecidableEq Atom] {Γ : List (Proposition Atom)}
    (p : ⇓(Γ : Sequent Atom)) : CF⇓(Γ : Sequent Atom) := cutElimAux p Γ rfl

/-- **Cut elimination**: every proof of `Γ` can be transformed into a cut-free proof of `Γ`.
Noncomputable only because it picks a list representative of `Γ` (`Multiset.toList`); use
`Proof.cutElimList` to compute. -/
noncomputable def Proof.cutElim [DecidableEq Atom] {Γ : Sequent Atom} (p : ⇓Γ) : CF⇓Γ :=
  (cutElimAux p Γ.toList (Multiset.coe_toList Γ).symm).rwConclusion (Multiset.coe_toList Γ)

end Cslib.Logic.CLL
