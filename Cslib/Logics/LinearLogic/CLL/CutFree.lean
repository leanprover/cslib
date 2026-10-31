/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Logics.LinearLogic.CLL.Basic
public import Cslib.Foundations.Data.Multiset.Basic
public import Cslib.Foundations.Data.Multiset.Grind

/-! # Cut-free proofs, cut admissibility, and cut elimination for classical linear logic -/

@[expose] public section

namespace Cslib.Logic.CLL

open Cslib.Logic.InferenceSystem

/-- A proof is cut-free if it does not contain any applications of rule cut. -/
@[simp]
def Proof.IsCutFree {Γ : Sequent Atom} : ⇓Γ → Prop
  | ax | one | top => True
  | bot p | parr p | oplus₁ p | oplus₂ p
    | quest p | weaken p | contract p | bang _ p => p.IsCutFree
  | tensor p q | .with p q => p.IsCutFree ∧ q.IsCutFree
  | cut _ _ => False

theorem isCutFree_ax {a : Proposition Atom} :
    @Proof.IsCutFree Atom {a, a⫠} (Proof.ax (a := a)) := ⟨⟩

theorem isCutFree_one : @Proof.IsCutFree Atom {1} Proof.one := ⟨⟩

theorem isCutFree_top {Γ : Sequent Atom} :
    @Proof.IsCutFree Atom (⊤ ::ₘ Γ) (Proof.top (Γ := Γ)) := ⟨⟩

theorem isCutFree_bot {Γ : Sequent Atom} {p : Proof Γ} (hp : @Proof.IsCutFree Atom Γ p) :
    @Proof.IsCutFree Atom (⊥ ::ₘ Γ) (Proof.bot (Γ := Γ) p) := hp

theorem isCutFree_parr {a b : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (a ::ₘ b ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (a ::ₘ b ::ₘ Γ) p) :
    @Proof.IsCutFree Atom ((a ⅋ b) ::ₘ Γ) (Proof.parr (a := a) (b := b) (Γ := Γ) p) := hp

theorem isCutFree_tensor {a b : Proposition Atom} {Γ Δ : Sequent Atom}
    {p : Proof (a ::ₘ Γ)} {q : Proof (b ::ₘ Δ)}
    (hp : @Proof.IsCutFree Atom (a ::ₘ Γ) p)
    (hq : @Proof.IsCutFree Atom (b ::ₘ Δ) q) :
    @Proof.IsCutFree Atom ((a ⊗ b) ::ₘ (Γ + Δ))
      (Proof.tensor (a := a) (b := b) (Γ := Γ) (Δ := Δ) p q) :=
  And.intro hp hq

theorem isCutFree_oplus₁ {a b : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (a ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (a ::ₘ Γ) p) :
    @Proof.IsCutFree Atom ((a ⊕ b) ::ₘ Γ) (Proof.oplus₁ (a := a) (b := b) (Γ := Γ) p) := hp

theorem isCutFree_oplus₂ {a b : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (b ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (b ::ₘ Γ) p) :
    @Proof.IsCutFree Atom ((a ⊕ b) ::ₘ Γ) (Proof.oplus₂ (a := a) (b := b) (Γ := Γ) p) := hp

theorem isCutFree_with {a b : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (a ::ₘ Γ)} {q : Proof (b ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (a ::ₘ Γ) p)
    (hq : @Proof.IsCutFree Atom (b ::ₘ Γ) q) :
    @Proof.IsCutFree Atom ((a & b) ::ₘ Γ) (Proof.with (a := a) (b := b) (Γ := Γ) p q) :=
  And.intro hp hq

theorem isCutFree_quest {a : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (a ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (a ::ₘ Γ) p) :
    @Proof.IsCutFree Atom (ʔa ::ₘ Γ) (Proof.quest (a := a) (Γ := Γ) p) := hp

theorem isCutFree_weaken {a : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof Γ} (hp : @Proof.IsCutFree Atom Γ p) :
    @Proof.IsCutFree Atom (ʔa ::ₘ Γ) (Proof.weaken (a := a) (Γ := Γ) p) := hp

theorem isCutFree_contract {a : Proposition Atom} {Γ : Sequent Atom}
    {p : Proof (ʔa ::ₘ ʔa ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (ʔa ::ₘ ʔa ::ₘ Γ) p) :
    @Proof.IsCutFree Atom (ʔa ::ₘ Γ) (Proof.contract (a := a) (Γ := Γ) p) := hp

theorem isCutFree_bang {a : Proposition Atom} {Γ : Sequent Atom}
    {hΓ : Γ.allQuest} {p : Proof (a ::ₘ Γ)} (hp : @Proof.IsCutFree Atom (a ::ₘ Γ) p) :
    @Proof.IsCutFree Atom ((!a) ::ₘ Γ) (Proof.bang (a := a) (Γ := Γ) hΓ p) := hp

/-- Recursor for cut-free proofs: never sees the `cut` case. -/
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
  match p, h with
  | .ax, _ => ax
  | .one, _ => one
  | .top, _ => top
  | .bot p, hp =>
    bot p (IsCutFree.rec ax one top bot parr tensor oplus₁ oplus₂ «with» quest weaken contract bang
      (p := p) hp)
  | .parr p, hp =>
    parr p (IsCutFree.rec ax one top bot parr tensor oplus₁ oplus₂ «with» quest weaken contract bang
      (p := p) hp)
  | .tensor p q, hpq =>
    tensor p q
      (IsCutFree.rec ax one top bot parr tensor oplus₁ oplus₂ «with» quest weaken contract bang
        hpq.1)
      (IsCutFree.rec ax one top bot parr tensor oplus₁ oplus₂ «with» quest weaken contract bang
        hpq.2)
  | .oplus₁ p, hp =>
    oplus₁ p (IsCutFree.rec ax one top bot parr tensor oplus₁ oplus₂ «with» quest weaken contract
      bang (p := p) hp)
  | .oplus₂ p, hp =>
    oplus₂ p (IsCutFree.rec ax one top bot parr tensor oplus₁ oplus₂ «with» quest weaken contract
      bang (p := p) hp)
  | .with p q, hpq =>
    «with» p q
      (IsCutFree.rec ax one top bot parr tensor oplus₁ oplus₂ «with» quest weaken contract bang
        hpq.1)
      (IsCutFree.rec ax one top bot parr tensor oplus₁ oplus₂ «with» quest weaken contract bang
        hpq.2)
  | .quest p, hp =>
    quest p (IsCutFree.rec ax one top bot parr tensor oplus₁ oplus₂ «with» quest weaken contract
      bang (p := p) hp)
  | .weaken p, hp =>
    weaken p (IsCutFree.rec ax one top bot parr tensor oplus₁ oplus₂ «with» quest weaken contract
      bang (p := p) hp)
  | .contract p, hp =>
    contract p (IsCutFree.rec ax one top bot parr tensor oplus₁ oplus₂ «with» quest weaken contract
      bang (p := p) hp)
  | .bang hΓ p, hp =>
    bang hΓ p (IsCutFree.rec ax one top bot parr tensor oplus₁ oplus₂ «with» quest weaken contract
      bang (p := p) hp)
  | .cut _ _, h => nomatch h

/-- Transporting a conclusion preserves cut-freeness. -/
@[simp, scoped grind .]
theorem Proof.isCutFree_rwConclusion (h : Γ = Δ) (p : Proof Γ) (hp : p.IsCutFree) :
    (p.rwConclusion h).IsCutFree := by grind

/-- Tag for the cut-free fragment of CLL. -/
opaque CF : Type := Empty

namespace CF

open scoped CLL.Proof Sequent

/-- Proofs in the CF inference system. -/
abbrev Proof (Γ : Sequent Atom) := { p : ⇓Γ // p.IsCutFree }

instance : InferenceSystem CF (Sequent Atom) := ⟨CF.Proof⟩

instance {Γ : Sequent Atom} : Coe (CF⇓Γ) (⇓Γ) where
  coe p := p.val

/-- Rewrites the conclusion of a cut-free proof. -/
def Proof.rwConclusion {Γ Δ : Sequent Atom} (h : Γ = Δ) (p : CF⇓Γ) : CF⇓Δ :=
  ⟨CLL.Proof.rwConclusion h p.val, CLL.Proof.isCutFree_rwConclusion h p.val p.property⟩

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

/-- Rule `?` (dereliction) for CF. -/
def Proof.quest {a : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓(a ::ₘ Γ)) : CF⇓(ʔa ::ₘ Γ) :=
  ⟨CLL.Proof.quest p.val, isCutFree_quest p.property⟩

/-- Rule `?` (weaken) for CF. -/
def Proof.weaken {a : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓Γ) : CF⇓(ʔa ::ₘ Γ) :=
  ⟨CLL.Proof.weaken p.val, isCutFree_weaken p.property⟩

/-- Rule `?` (contract) for CF. -/
def Proof.contract {a : Proposition Atom} {Γ : Sequent Atom} (p : CF⇓(ʔa ::ₘ ʔa ::ₘ Γ)) :
    CF⇓(ʔa ::ₘ Γ) := ⟨CLL.Proof.contract p.val, isCutFree_contract p.property⟩

/-- Rule `!` (bang/promotion) for CF. -/
def Proof.bang {a : Proposition Atom} {Γ : Sequent Atom} (hΓ : Γ.allQuest) (p : CF⇓(a ::ₘ Γ)) :
    CF⇓((!a) ::ₘ Γ) := ⟨CLL.Proof.bang hΓ p.val, isCutFree_bang p.property⟩

/-- Given a list of `ʔ`-propositions `Γ`, transforms a cut-free proof of `Δ` into a proof of `Γ + Δ`
via weakening. -/
def Proof.weakenContext {Γ : List (Proposition Atom)} {Δ : Sequent Atom} (hΓ : Γ.allQuest)
    (p : CF⇓Δ) : CF⇓(Γ + Δ) :=
  match Γ, hΓ with
  | [], _ => p.rwConclusion (Multiset.zero_add Δ).symm
  | .quest a :: Γ, hΓ =>
    (Proof.weaken (a := a) (Proof.weakenContext (Γ := Γ) hΓ p)).rwConclusion
      (Multiset.cons_add (ʔa) Γ Δ).symm
  | .atom _ :: _, hΓ | .atomDual _ :: _, hΓ
    | .one :: _, hΓ | .zero :: _, hΓ | .top :: _, hΓ | .bot :: _, hΓ
    | .tensor _ _ :: _, hΓ | .parr _ _ :: _, hΓ
    | .oplus _ _ :: _, hΓ | .with _ _ :: _, hΓ | .bang _ :: _, hΓ =>
    nomatch hΓ

/-- Given a list of `ʔ`-propositions `Γ`, transforms a proof of `Γ + Γ + Δ` into a proof of `Γ + Δ`
via contraction. -/
def Proof.contractContext {Γ : List (Proposition Atom)} {Δ : Sequent Atom} (hΓ : Γ.allQuest)
    (p : CF⇓((Γ : Sequent Atom) + Γ + Δ)) : CF⇓(Γ + Δ) :=
  match Γ, hΓ with
  | [], _ => p.rwConclusion (by simp)
  | .quest a :: Γ, hΓ =>
    let p' : CF⇓(ʔa ::ₘ ʔa ::ₘ ((Γ : Sequent Atom) + Γ + Δ)) := p.rwConclusion
      (by grind only [multiset])
    let p' : CF⇓(ʔa ::ₘ ((Γ : Sequent Atom) + Γ + Δ)) := Proof.contract p'
    let p' : CF⇓((Γ : Sequent Atom) + Γ + (ʔa ::ₘ Δ)) := p'.rwConclusion (by grind only [multiset])
    (Proof.contractContext (Γ := Γ) (Δ := ʔa ::ₘ Δ) hΓ p').rwConclusion (by grind only [multiset])
  | .atom _ :: _, hΓ | .atomDual _ :: _, hΓ
    | .one :: _, hΓ | .zero :: _, hΓ | .top :: _, hΓ | .bot :: _, hΓ
    | .tensor _ _ :: _, hΓ | .parr _ _ :: _, hΓ
    | .oplus _ _ :: _, hΓ | .with _ _ :: _, hΓ | .bang _ :: _, hΓ =>
    nomatch hΓ

end CF

open scoped CF.Proof

universe u

variable {Atom : Type u} {a b : Proposition Atom} {Γ Δ Θ : Sequent Atom}

namespace Sequent

/-- An empty sum has an empty right residual context. -/
theorem eq_zero_of_zero_eq_add (h : (0 : Sequent Atom) = Γ + Δ) : Δ = 0 := by
  apply Multiset.le_zero.mp
  rw [h]
  exact Multiset.le_add_left _ _

/-- Distinguish a principal selected occurrence using decidable equality.
Given `a ::ₘ Γ = b ::ₘ Δ`, either `a = b` and `Γ = Δ`, or `a ≠ b` and the propositions are swapped:
`Γ = b ::ₘ Λ` and `Δ = a ::ₘ Λ` for some `Λ`. -/
def splitCons [DecidableEq Atom] {Γ Δ : List (Proposition Atom)} (h : a ::ₘ Γ = b ::ₘ Δ) :
    (a = b ∧ (Γ : Sequent Atom) = Δ) ⊕'
      {Θ : List (Proposition Atom) //
        a ≠ b ∧ (Γ : Sequent Atom) = b ::ₘ Θ ∧ (Δ : Sequent Atom) = a ::ₘ Θ} := by
  by_cases hab : a = b
  · subst b
    exact .inl ⟨rfl, (Multiset.cons_inj_right a).mp h⟩
  · have hba : b ≠ a := Ne.symm hab
    have hbΓ : b ∈ (Γ : Sequent Atom) := by
      have hb : b ∈ a ::ₘ (Γ : Sequent Atom) := by
        rw [h]
        simp
      simpa [hba] using hb
    have hΓ : (Γ : Sequent Atom) = b ::ₘ (Γ.erase b : Sequent Atom) := by
      exact Multiset.coe_eq_coe.mpr (List.perm_cons_erase hbΓ)
    have hΔ : (Δ : Sequent Atom) = a ::ₘ (Γ.erase b : Sequent Atom) := by
      grind only [multiset]
    exact .inr ⟨Γ.erase b, hab, hΓ, hΔ⟩

/-- Given `a ::ₘ Γ = (Δ : Sequent) + Θ`, locate `a` in either `Δ` or `Θ` and
erase it from that summand, returning the residual list. -/
def splitConsAdd [DecidableEq Atom] {Γ Δ Θ : List (Proposition Atom)}
    (h : a ::ₘ Γ = (Δ : Sequent Atom) + Θ) :
    {Δ' : List (Proposition Atom) //
      (Δ : Sequent Atom) = a ::ₘ Δ' ∧ (Γ : Sequent Atom) = (Δ' : Sequent Atom) + Θ} ⊕'
    {Θ' : List (Proposition Atom) //
      (Θ : Sequent Atom) = a ::ₘ Θ' ∧ (Γ : Sequent Atom) = (Δ : Sequent Atom) + Θ'} := by
  by_cases haΔ : a ∈ (Δ : Sequent Atom)
  · have hΔ : (Δ : Sequent Atom) = a ::ₘ (Δ.erase a : Sequent Atom) := by
      exact Multiset.coe_eq_coe.mpr (List.perm_cons_erase haΔ)
    have hΓ : (Γ : Sequent Atom) = (Δ.erase a : Sequent Atom) + Θ := by grind only [multiset]
    exact .inl ⟨Δ.erase a, hΔ, hΓ⟩
  · have haΘ : a ∈ (Θ : Sequent Atom) := by
      have ha : a ∈ (Δ : Sequent Atom) + Θ := by grind only [multiset]
      grind only [multiset]
    have hΘ : (Θ : Sequent Atom) = a ::ₘ (Θ.erase a : Sequent Atom) := by
      exact Multiset.coe_eq_coe.mpr (List.perm_cons_erase haΘ)
    have hΓ : (Γ : Sequent Atom) = (Δ : Sequent Atom) + (Θ.erase a : Sequent Atom) := by
      grind only [multiset]
    exact .inr ⟨Θ.erase a, hΘ, hΓ⟩

/-- Given `Multiset.replicate n a + Γ = b ::ₘ Δ`, either the head `b` is one of the
`n` copies of `a` (so `b = a` and the tail is `replicate (n-1) a + Γ`), or `b` belongs to
`Γ` (so `Δ = a ::ₘ Γ'` where `Γ = b ::ₘ Γ'`). -/
def splitReplicateCons [DecidableEq Atom] {Γ Δ : List (Proposition Atom)} {n : ℕ}
    (h : Multiset.replicate n a + Γ = b ::ₘ Δ) :
    {m : ℕ // n = m + 1 ∧ b = a ∧ (Δ : Sequent Atom) = Multiset.replicate m a + Γ} ⊕'
      {Γ' : List (Proposition Atom) // (Γ : Sequent Atom) = b ::ₘ Γ' ∧
        (Δ : Sequent Atom) = Multiset.replicate n a + Γ'} := by
  cases n with
  | zero => exact .inr ⟨Δ, by simpa using h, by simp⟩
  | succ n =>
      by_cases hba : b = a
      · subst b
        have ht : Multiset.replicate n a + (Γ : Sequent Atom) = (Δ : Sequent Atom) := by
          grind only [multiset]
        exact .inl ⟨n, by lia, rfl, ht.symm⟩
      · have hbΓ : b ∈ (Γ : Sequent Atom) := by
          have hb : b ∈ Multiset.replicate (Nat.succ n) a + (Γ : Sequent Atom) := by
            rw [h]
            simp
          rcases Multiset.mem_add.mp hb with hb | hb
          · exact (hba (Multiset.eq_of_mem_replicate hb)).elim
          · exact hb
        have hΓ : (Γ : Sequent Atom) = b ::ₘ (Γ.erase b : Sequent Atom) := by
          exact Multiset.coe_eq_coe.mpr (List.perm_cons_erase hbΓ)
        have ht : Multiset.replicate (Nat.succ n) a + (Γ.erase b : Sequent Atom) =
            (Δ : Sequent Atom) := by
          grind only [multiset]
        exact .inr ⟨Γ.erase b, hΓ, ht.symm⟩

/-- Given `Multiset.replicate n a + Γ = (Δ : Sequent) + Θ`, split the `n` copies of `a`
between `Δ` and `Θ`, returning counts `k` and `l` and residual lists. -/
def splitReplicateAdd [DecidableEq Atom] {Γ Δ Θ : List (Proposition Atom)} {n : ℕ}
    (h : Multiset.replicate n a + Γ = (Δ : Sequent Atom) + Θ) :
    Σ (k l : ℕ) (Δ' : List (Proposition Atom)),
      {Θ' : List (Proposition Atom) // n = k + l ∧
        (Δ : Sequent Atom) = Multiset.replicate k a + Δ' ∧
        (Θ : Sequent Atom) = Multiset.replicate l a + Θ' ∧
        (Γ : Sequent Atom) = (Δ' : Sequent Atom) + Θ'} := by
  induction n generalizing Δ Θ with
  | zero =>
      refine ⟨0, 0, Δ, ⟨Θ, ?_⟩⟩
      simpa using h
  | succ n ih =>
      have hR : ((List.replicate n a ++ Γ : List (Proposition Atom)) : Sequent Atom) =
          Multiset.replicate n a + (Γ : Sequent Atom) := by
        grind only [multiset]
      have hHead : a ::ₘ ((List.replicate n a ++ Γ : List (Proposition Atom)) : Sequent Atom) =
          (Δ : Sequent Atom) + Θ := by
        rw [hR]
        simpa [Nat.succ_eq_add_one, Multiset.replicate_succ] using h
      cases splitConsAdd (a := a) (Γ := List.replicate n a ++ Γ) (Δ := Δ) (Θ := Θ) hHead with
      | inl r =>
          rcases r with ⟨Δ₁, hΔ, hrest⟩
          rw [hR] at hrest
          rcases ih (Δ := Δ₁) (Θ := Θ) hrest with ⟨k, l, Δ', Θ', hn, hΔ₁, hΘ, hΓ⟩
          refine ⟨Nat.succ k, l, Δ', ⟨Θ', ?_, ?_, hΘ, hΓ⟩⟩ <;> grind only [multiset]
      | inr r =>
          rcases r with ⟨Θ₁, hΘ, hrest⟩
          rw [hR] at hrest
          rcases ih (Δ := Δ) (Θ := Θ₁) hrest with ⟨k, l, Δ', Θ', hn, hΔ, hΘ₁, hΓ⟩
          refine ⟨k, Nat.succ l, Δ', ⟨Θ', ?_, hΔ, ?_, hΓ⟩⟩ <;> grind only [multiset]

end Sequent

/-- Cut admissibility at a fixed proposition `a`: for any list sequents `Γ`, `Δ`, given
cut-free proofs of `a ::ₘ Γ` and `a⫠ ::ₘ Δ`, produce a cut-free proof of
`(Γ : Sequent Atom) + Δ`. -/
abbrev CutAdmissibleAt (a : Proposition Atom) := ∀ {Γ Δ : List (Proposition Atom)},
  CF⇓(a ::ₘ Γ) → CF⇓(a⫠ ::ₘ Δ) → CF⇓((Γ : Sequent Atom) + Δ)

/-- The outer induction hypothesis for cut admissibility: for all propositions `a` with
`sizeOf a < rank`, cut is admissible at `a`. -/
abbrev CutAdmissibleBelow (Atom : Type u) (rank : ℕ) :=
  ∀ {a : Proposition Atom}, a.rank < rank → CutAdmissibleAt a

/-- Generalized version of `splitReplicateCons`: the tail is an arbitrary
multiset, so first compute a list presentation of it.
Extracted from `Proof.questMulticut`. -/
def splitHead [DecidableEq Atom] {a b : Proposition Atom} {Θ : Sequent Atom} {n : ℕ}
    {Δ : List (Proposition Atom)}
    (h : b ::ₘ Θ = Multiset.replicate n (ʔ(a⫠)) + Δ) :
    {m : ℕ //
      n = m + 1 ∧
      b = ʔ(a⫠) ∧
      Θ = Multiset.replicate m (ʔ(a⫠)) + Δ} ⊕'
    {Δ' : List (Proposition Atom) //
      (Δ : Sequent Atom) = b ::ₘ Δ' ∧
      Θ = Multiset.replicate n (ʔ(a⫠)) + Δ'} := by
  let Λ := List.replicate n (ʔ(a⫠)) ++ Δ
  have hL : (Λ : Sequent Atom) = Multiset.replicate n (ʔ(a⫠)) + Δ := by
    grind only [multiset]
  have hΘle : Θ ≤ (Λ : Sequent Atom) := by
    rw [hL, ← h]
    exact Multiset.le_cons_self _ _
  let sΘ := Multiset.scanToList Λ Θ hΘle
  have hsΘ : (sΘ.1 : Sequent Atom) = Θ := sΘ.2
  have hs : Multiset.replicate n (ʔ(a⫠)) + Δ = b ::ₘ sΘ.1 := by
    rw [hsΘ]; exact h.symm
  rcases Sequent.splitReplicateCons (a := ʔ(a⫠)) hs with hs | hs
  · exact .inl ⟨hs.1, hs.2.1, hs.2.2.1, hsΘ.symm.trans hs.2.2.2⟩
  · exact .inr ⟨hs.1, hs.2.1, hsΘ.symm.trans hs.2.2⟩

/-- Likewise for a sum whose two summands are arbitrary multisets.
Extracted from `Proof.questMulticut`. -/
def splitAdd [DecidableEq Atom] {a : Proposition Atom} {Θ₁ Θ₂ : Sequent Atom} {n : ℕ}
    {Δ : List (Proposition Atom)}
    (h : Θ₁ + Θ₂ = Multiset.replicate n (ʔ(a⫠)) + Δ) :
    Σ k : ℕ, Σ l : ℕ, Σ Δ₁ : List (Proposition Atom),
      {Δ₂ : List (Proposition Atom) //
        n = k + l ∧
        Θ₁ = Multiset.replicate k (ʔ(a⫠)) + Δ₁ ∧
        Θ₂ = Multiset.replicate l (ʔ(a⫠)) + Δ₂ ∧
        (Δ : Sequent Atom) =
          (Δ₁ : Sequent Atom) + Δ₂} := by
  let Λ := List.replicate n (ʔ(a⫠)) ++ Δ
  have hL : (Λ : Sequent Atom) = Multiset.replicate n (ʔ(a⫠)) + Δ := by
    grind only [multiset]
  have h₁le : Θ₁ ≤ (Λ : Sequent Atom) := by
    rw [hL, ← h]
    exact Multiset.le_add_right _ _
  have h₂le : Θ₂ ≤ (Λ : Sequent Atom) := by
    rw [hL, ← h]
    exact Multiset.le_add_left _ _
  let s₁ := Multiset.scanToList Λ Θ₁ h₁le
  let s₂ := Multiset.scanToList Λ Θ₂ h₂le
  have hs₁ : (s₁.1 : Sequent Atom) = Θ₁ := s₁.2
  have hs₂ : (s₂.1 : Sequent Atom) = Θ₂ := s₂.2
  have hs : Multiset.replicate n (ʔ(a⫠)) + Δ = (s₁.1 : Sequent Atom) + s₂.1 := by
    rw [hs₁, hs₂]; exact h.symm
  rcases Sequent.splitReplicateAdd (a := ʔ(a⫠)) hs with ⟨k, l, Δ₁, Δ₂, hn, h₁, h₂, hΔ⟩
  exact ⟨k, l, Δ₁, ⟨Δ₂, hn, hs₁.symm.trans h₁, hs₂.symm.trans h₂, hΔ⟩⟩

/-- Ax case for `questMulticut`: the selected dual question mark is one of the copies of `a⫠`.
This isolates the recursive branch from the plain-term outer proof. -/
def Proof.questMulticutAx [DecidableEq Atom] {a : Proposition Atom}
    {Γ : List (Proposition Atom)} (hΓ : Γ.allQuest) (p : CF⇓(a ::ₘ Γ))
    {c : Proposition Atom} {n : ℕ} {Δ : List (Proposition Atom)}
    (h : c ::ₘ ([c⫠] : List (Proposition Atom)) = Multiset.replicate n (ʔ(a⫠)) + Δ) :
    CF⇓((Γ : Sequent Atom) + Δ) := by
  have hs : Multiset.replicate n (ʔ(a⫠)) + Δ = c ::ₘ ([c⫠] : List (Proposition Atom)) := by
    simpa using h.symm
  rcases Sequent.splitReplicateCons (a := ʔ(a⫠)) hs with hs | hs
  · rcases hs with ⟨m, hn, hc, htail⟩
    have hs₂ : Multiset.replicate m (ʔ(a⫠)) + Δ = c⫠ ::ₘ ([] : List (Proposition Atom)) := by
      simpa using htail.symm
    rcases Sequent.splitReplicateCons (a := ʔ(a⫠)) hs₂ with hs₂ | hs₂
    · rcases hs₂ with ⟨_, _, hcdual, _⟩
      have : c = c⫠ := hc.trans hcdual.symm
      exact (Proposition.dual_neq c this).elim
    · rcases hs₂ with ⟨Δ', hΔ, hzero⟩
      have hΔ'zero : (Δ' : Sequent Atom) = 0 := Sequent.eq_zero_of_zero_eq_add hzero
      have hcdual : c⫠ = !a := by
        rw [hc]
        simp [Proposition.dual]
      have hΔbang : (Δ : Sequent Atom) = ({!a} : Sequent Atom) := by
        rw [hΔ, hΔ'zero, hcdual]; rfl
      let r : CF⇓((!a) ::ₘ (Γ : Sequent Atom)) := CF.Proof.bang (by simpa using hΓ) p
      exact r.rwConclusion (by
        rw [hΔbang, Multiset.add_comm]
        exact (Multiset.singleton_add _ _).symm)
  · rcases hs with ⟨Δ₁, hΔ, htail⟩
    have hs₂ : Multiset.replicate n (ʔ(a⫠)) + Δ₁ = c⫠ ::ₘ ([] : List (Proposition Atom)) := by
      simpa using htail.symm
    rcases Sequent.splitReplicateCons (a := ʔ(a⫠)) hs₂ with hs₂ | hs₂
    · rcases hs₂ with ⟨m, hn, hcdual, hzero⟩
      have hΔ₁zero : (Δ₁ : Sequent Atom) = 0 := Sequent.eq_zero_of_zero_eq_add hzero
      have hc : c = !a := by
        have := congrArg Proposition.dual hcdual
        simpa [Proposition.dual] using this
      have hΔbang : (Δ : Sequent Atom) = ({!a} : Sequent Atom) := by
        rw [hΔ, hΔ₁zero, hc]; rfl
      let r : CF⇓((!a) ::ₘ (Γ : Sequent Atom)) := CF.Proof.bang (by simpa using hΓ) p
      exact r.rwConclusion (by
        rw [hΔbang, Multiset.add_comm]
        exact (Multiset.singleton_add _ _).symm)
    · rcases hs₂ with ⟨Δ₂, hΔ₁, hzero⟩
      have hΔ₂zero : (Δ₂ : Sequent Atom) = 0 := Sequent.eq_zero_of_zero_eq_add hzero
      have hΔpair : (Δ : Sequent Atom) = ({c, c⫠} : Sequent Atom) := by
        rw [hΔ, hΔ₁, hΔ₂zero]; rfl
      let r : CF⇓((Γ : Sequent Atom) + ({c, c⫠} : Sequent Atom)) :=
        CF.Proof.weakenContext (by simpa using hΓ) (CF.Proof.ax (a := c))
      exact r.rwConclusion (by rw [hΔpair])

/-- Exponential/multicut helper: given `p : CF⇓(a ::ₘ Γ)` (the "substitutend") and
`q : CF⇓(Multiset.replicate n (ʔ(a⫠)) + Δ)` (the "supply" with `n` selected dual question marks),
produce `CF⇓((Γ : Sequent) + Δ)`. -/
def Proof.questMulticut [DecidableEq Atom] (cutSmaller : CutAdmissibleBelow Atom (!a).rank)
    {Γ Δ : List (Proposition Atom)} (hΓ : Γ.allQuest) (p : CF⇓(a ::ₘ Γ)) {n : ℕ}
    (q : CF⇓(Multiset.replicate n (ʔ(a⫠)) + Δ)) : CF⇓((Γ : Sequent Atom) + Δ) :=
  let hΓm : Sequent.allQuest (Γ : Sequent Atom) := by simpa using hΓ
  let haSmall : a.rank < (!a).rank := by simp
  /-
  Generalized version of `splitReplicateCons`: the tail is an arbitrary
  multiset, so first compute a list presentation of it.
  -/
  let motive : {Θ : Sequent Atom} → {r : Proof Θ} → (hr : r.IsCutFree) → Type u :=
    fun {Θ} {_} _ =>
      ∀ {n : ℕ} {Δ : List (Proposition Atom)},
        Θ = Multiset.replicate n (ʔ(a⫠)) + Δ →
        CF⇓((Γ : Sequent Atom) + Δ)
  let ax : ∀ {c : Proposition Atom} {n : ℕ} {Δ : List (Proposition Atom)},
      c ::ₘ ([c⫠] : List (Proposition Atom)) = Multiset.replicate n (ʔ(a⫠)) + Δ →
      CF⇓((Γ : Sequent Atom) + Δ) :=
    fun {c} {n} {Δ} h =>
      Proof.questMulticutAx (a := a) (Γ := Γ) hΓ p h
  (Proof.IsCutFree.rec
      (motive := motive)
      /- ax -/
      (ax := ax)
      /- one -/
      (one := by
        intro n Δ h
        have hs :
            Multiset.replicate n (ʔ(a⫠)) + Δ =
              (1 : Proposition Atom) ::ₘ ([] : List (Proposition Atom)) := h.symm
        rcases Sequent.splitReplicateCons (a := ʔ(a⫠)) hs with hs | hs
        · rcases hs with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hs with ⟨Δ', hΔ, hzero⟩
          have hΔ'zero : (Δ' : Sequent Atom) = 0 := Sequent.eq_zero_of_zero_eq_add hzero
          have hΔone : (Δ : Sequent Atom) = ({1} : Sequent Atom) := by
            rw [hΔ, hΔ'zero]; rfl
          let r : CF⇓((Γ : Sequent Atom) + ({1} : Sequent Atom)) :=
            CF.Proof.weakenContext hΓ
              (CF.Proof.one (Atom := Atom))
          exact r.rwConclusion (by rw [hΔone]))
      /- top -/
      (top := by
        intro Θ n Δ h
        rcases splitHead h with hs | hs
        · rcases hs with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r : CF⇓((⊤ : Proposition Atom) ::ₘ ((Γ : Sequent Atom) + Δ')) :=
            CF.Proof.top
          exact r.rwConclusion (by grind only [multiset]))
      /- bot -/
      (bot := by
        intro Θ r hr ih n Δ h
        rcases splitHead h with hs | hs
        · rcases hs with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := Δ') htail
          exact (CF.Proof.bot r').rwConclusion (by grind only [multiset]))
      /- parr -/
      (parr := by
        intro c d Θ r hr ih n Δ h
        rcases splitHead h with hs | hs
        · rcases hs with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := c :: d :: Δ') (by grind only [multiset])
          let r'' : CF⇓(c ::ₘ d ::ₘ ((Γ : Sequent Atom) + Δ')) :=
            r'.rwConclusion (by grind only [multiset])
          exact (CF.Proof.parr r'').rwConclusion (by grind only [multiset]))
      /- tensor -/
      (tensor := by
        intro c d Θ₁ Θ₂ r s hr hs ihr ihs n Δ h
        rcases splitHead h with hp | hp
        · rcases hp with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hp with ⟨Δ', hΔ, htail⟩
          rcases splitAdd htail with
            ⟨k, l, Δ₁, Δ₂, hn, h₁, h₂, hres⟩
          let r' := ihr (n := k) (Δ := c :: Δ₁) (by grind only [multiset])
          let s' := ihs (n := l) (Δ := d :: Δ₂) (by grind only [multiset])
          let r'' : CF⇓(c ::ₘ ((Γ : Sequent Atom) + Δ₁)) :=
            r'.rwConclusion (Multiset.add_cons _ _ _)
          let s'' : CF⇓(d ::ₘ ((Γ : Sequent Atom) + Δ₂)) :=
            s'.rwConclusion (Multiset.add_cons _ _ _)
          let t := CF.Proof.tensor r'' s''
          let t' : CF⇓((Γ : Sequent Atom) + Γ + ((c ⊗ d) ::ₘ ((Δ₁ : Sequent Atom) + Δ₂))) :=
            t.rwConclusion (by grind only [multiset])
          let t'' := CF.Proof.contractContext (Γ := Γ) hΓ t'
          exact t''.rwConclusion (by rw [← hres, ← hΔ]))
      /- oplus₁ -/
      (oplus₁ := by
        intro c d Θ r hr ih n Δ h
        rcases splitHead h with hs | hs
        · rcases hs with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := c :: Δ') (by grind only [multiset])
          let r'' : CF⇓(c ::ₘ ((Γ : Sequent Atom) + Δ')) :=
            r'.rwConclusion (Multiset.add_cons _ _ _)
          exact (CF.Proof.oplus₁ (b := d) r'').rwConclusion (by grind only [multiset]))
      /- oplus₂ -/
      (oplus₂ := by
        intro c d Θ r hr ih n Δ h
        rcases splitHead h with hs | hs
        · rcases hs with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := d :: Δ') (by grind only [multiset])
          let r'' : CF⇓(d ::ₘ ((Γ : Sequent Atom) + Δ')) :=
            r'.rwConclusion (Multiset.add_cons _ _ _)
          exact (CF.Proof.oplus₂ (a := c) r'').rwConclusion (by grind only [multiset]))
      /- with -/
      («with» := by
        intro c d Θ r s hr hs ihr ihs n Δ h
        rcases splitHead h with hp | hp
        · rcases hp with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hp with ⟨Δ', hΔ, htail⟩
          let r' := ihr (n := n) (Δ := c :: Δ') (by grind only [multiset])
          let s' := ihs (n := n) (Δ := d :: Δ') (by grind only [multiset])
          let r'' : CF⇓(c ::ₘ ((Γ : Sequent Atom) + Δ')) :=
            r'.rwConclusion (Multiset.add_cons _ _ _)
          let s'' : CF⇓(d ::ₘ ((Γ : Sequent Atom) + Δ')) :=
            s'.rwConclusion (Multiset.add_cons _ _ _)
          exact (CF.Proof.with r'' s'').rwConclusion (by grind only [multiset]))
      /- quest -/
      (quest := by
        intro c Θ r hr ih n Δ h
        rcases splitHead h with hs | hs
        /- The displayed `?` is one of the selected copies. -/
        · rcases hs with ⟨m, hn, hcq, htail⟩
          have hc : c = a⫠ := by
            injection hcq
          /-
          First eliminate all the remaining selected copies, keeping the
          exposed `a⫠` as part of the residual sequent.
          -/
          let r' := ih (n := m) (Δ := c :: Δ) (by grind only [multiset])
          let r'' : CF⇓(a⫠ ::ₘ (((Γ ++ Δ : List (Proposition Atom))) : Sequent Atom)) :=
            r'.rwConclusion (by
              rw [hc]
              exact Multiset.add_cons _ (Γ : Sequent Atom) (Δ : Sequent Atom))
          /-
          Now cut the exposed `a⫠` against `p`.  This duplicates Γ.
          -/
          let t := cutSmaller haSmall p r''
          let t' : CF⇓((Γ : Sequent Atom) + Γ + Δ) :=
            t.rwConclusion (Multiset.add_assoc (Γ : Sequent Atom) Γ Δ).symm
          exact CF.Proof.contractContext (Γ := Γ) hΓ t'
        /- The displayed `?` belongs to the residual sequent. -/
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := c :: Δ') (by grind only [multiset])
          let r'' : CF⇓(c ::ₘ ((Γ : Sequent Atom) + Δ')) :=
            r'.rwConclusion (Multiset.add_cons _ _ _)
          exact (CF.Proof.quest r'').rwConclusion (by grind only [multiset]))
      /- weaken -/
      (weaken := by
        intro c Θ r hr ih n Δ h
        rcases splitHead h with hs | hs
        /- This weakening introduced a selected occurrence. -/
        · rcases hs with ⟨m, hn, hc, htail⟩
          exact ih (n := m) (Δ := Δ) htail
        /- It introduced an unselected occurrence. -/
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := Δ') htail
          exact (CF.Proof.weaken (a := c) r').rwConclusion (by grind only [multiset]))
      /- contract -/
      (contract := by
        intro c Θ r hr ih n Δ h
        rcases splitHead h with hs | hs
        /-
        A selected contracted occurrence corresponds to two selected
        occurrences in the premise.
        -/
        · rcases hs with ⟨m, hn, hc, htail⟩
          exact ih (n := n + 1) (Δ := Δ) (by grind only [multiset])
        /-
        Otherwise both copies in the premise are residual and contraction
        is rebuilt after the recursive call.
        -/
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := ʔc :: ʔc :: Δ') (by grind only [multiset])
          let r'' : CF⇓(ʔc ::ₘ ʔc ::ₘ ((Γ : Sequent Atom) + Δ')) :=
            r'.rwConclusion (by grind only [multiset])
          exact (CF.Proof.contract r'').rwConclusion (by grind only [multiset]))
      /- bang -/
      (bang := by
        intro c Θ hΘ r hr ih n Δ h
        rcases splitHead h with hs | hs
        · rcases hs with ⟨_, _, hbad, _⟩
          cases hbad
        · rcases hs with ⟨Δ', hΔ, htail⟩
          let r' := ih (n := n) (Δ := c :: Δ') (by grind only [multiset])
          have hΔ' : Sequent.allQuest (Δ' : Sequent Atom) := by
            have hq :
                Sequent.allQuest (Multiset.replicate n (ʔ(a⫠)) +
                  (Δ' : Sequent Atom)) := by
              rw [← htail]
              exact hΘ
            exact (Sequent.allQuest_add.mp hq).2
          have hside :
              Sequent.allQuest ((Γ : Sequent Atom) +
                (Δ' : Sequent Atom)) :=
            Sequent.allQuest_add.mpr ⟨hΓm, hΔ'⟩
          let r'' : CF⇓(c ::ₘ ((Γ : Sequent Atom) + Δ')) :=
            r'.rwConclusion (Multiset.add_cons _ _ _)
          exact (CF.Proof.bang hside r'').rwConclusion (by grind only [multiset]))
      q.property)
      rfl

/-- Present both summands using only the supplied list. -/
def Sequent.presentSumForCut [DecidableEq Atom]
    (Γ : List (Proposition Atom)) {Θ T : Sequent Atom}
    (h : (Γ : Sequent Atom) = Θ + T) :
    Σ Λ : List (Proposition Atom),
      {R : List (Proposition Atom) //
        (Λ : Sequent Atom) = Θ ∧ (R : Sequent Atom) = T} :=
  let l := Multiset.scanToList Γ Θ (by
    rw [h]
    exact Multiset.le_add_right Θ T)
  let r := Multiset.scanToList Γ T (by
    rw [h]
    exact Multiset.le_add_left T Θ)
  ⟨l.val, r.val, l.property, r.property⟩

/-- Present a tail without choosing a multiset representative. -/
def Sequent.presentTailForCut [DecidableEq Atom]
    (Γ : List (Proposition Atom)) {b : Proposition Atom} {Θ : Sequent Atom}
    (h : b ::ₘ Θ = (Γ : Sequent Atom)) :
    {Λ : List (Proposition Atom) // (Λ : Sequent Atom) = Θ} :=
  Multiset.scanToList Γ Θ (by
    rw [← h]
    exact Multiset.le_cons_self Θ b)

/-- Split a selected occurrence against a rule head; the rule tail can be a multiset. -/
def Sequent.splitCutHead [DecidableEq Atom]
    {a b : Proposition Atom} {Γ : List (Proposition Atom)} {Θ : Sequent Atom}
    (h : a ::ₘ Γ = b ::ₘ Θ) :
    (a = b ∧ (Γ : Sequent Atom) = Θ) ⊕'
      {Λ : List (Proposition Atom) //
        (Γ : Sequent Atom) = b ::ₘ Λ ∧ Θ = a ::ₘ Λ} := by
  let s := Sequent.presentTailForCut (a :: Γ) h.symm
  have hs : a ::ₘ Γ = b ::ₘ s.val := by grind
  rcases Sequent.splitCons hs with hp | hn
  · exact .inl ⟨hp.1, hp.2.trans s.property⟩
  · exact .inr ⟨hn.val, hn.property.2.1,
      s.property.symm.trans hn.property.2.2⟩

/-- The shape of a cut-free proof when the cut proposition is in principal position.
Each constructor corresponds to a rule whose conclusion matches the cut proposition.
Axioms are handled separately in `cutStep`. Tensor carries explicit presentations
of both premises' residual contexts. -/
inductive Proof.CutPrincipal (Γ : List (Proposition Atom)) :
    Proposition Atom → Type u where
  | one (hG : (Γ : Sequent Atom) = 0) : Proof.CutPrincipal Γ 1
  | bot (p : CF⇓(Γ : Sequent Atom)) : Proof.CutPrincipal Γ ⊥
  | top : Proof.CutPrincipal Γ ⊤
  | parr {c d : Proposition Atom} (p : CF⇓(c ::ₘ d ::ₘ Γ)) :
      Proof.CutPrincipal Γ (c ⅋ d)
  | tensor {c d : Proposition Atom} {Λ R : List (Proposition Atom)}
      (hG : (Γ : Sequent Atom) = (Λ : Sequent Atom) + R)
      (p : CF⇓(c ::ₘ Λ)) (q : CF⇓(d ::ₘ R)) :
      Proof.CutPrincipal Γ (c ⊗ d)
  | oplus1 {c d : Proposition Atom} (p : CF⇓(c ::ₘ Γ)) :
      Proof.CutPrincipal Γ (c ⊕ d)
  | oplus2 {c d : Proposition Atom} (p : CF⇓(d ::ₘ Γ)) :
      Proof.CutPrincipal Γ (c ⊕ d)
  | with {c d : Proposition Atom}
      (p : CF⇓(c ::ₘ Γ)) (q : CF⇓(d ::ₘ Γ)) :
      Proof.CutPrincipal Γ (c & d)
  | bang {c : Proposition Atom} (hG : Γ.allQuest) (p : CF⇓(c ::ₘ Γ)) :
      Proof.CutPrincipal Γ (!c)

/-- Decompose a cut against a cut-free proof: either expose a principal rule matching
the cut proposition, or commute the cut through one inference (non-principal case).
Every recursive call is on a strictly shorter supplying derivation. -/
def Proof.cutStep [DecidableEq Atom]
    {a : Proposition Atom} (notQuest : ∀ b, a ≠ ʔb)
    {Θ : Sequent Atom} {Γ Δ : List (Proposition Atom)} (r : Proof Θ) (hr : r.IsCutFree) :
      Θ = a ::ₘ Γ →
      (q : CF⇓(a⫠ ::ₘ Δ)) →
      (∀ {Γ' : List (Proposition Atom)} (p' : CF⇓(a ::ₘ Γ')),
        p'.val.height < r.height → CF⇓((Γ' : Sequent Atom) + Δ)) →
      Proof.CutPrincipal Γ a ⊕' CF⇓((Γ : Sequent Atom) + Δ) :=
  match r, hr with
  | .ax (a := c), _ => by
      intro h q recur
      have ha : a = c ∨ a = c⫠ := by
        have ha : a ∈ ({c, c⫠} : Sequent Atom) := by
          rw [h]
          simp
        simpa using ha
      have hG : (Γ : Sequent Atom) = {a⫠} := by
        rcases ha with ha | ha
        · subst a
          apply (Multiset.cons_inj_right c).mp
          simpa using h.symm
        · subst a
          apply (Multiset.cons_inj_right c⫠).mp
          simpa only [Proposition.dual_involution, Multiset.insert_eq_cons] using
            h.symm.trans (Multiset.pair_comm c c⫠)
      exact .inr (q.rwConclusion (by
        rw [hG]
        exact (Multiset.singleton_add _ _).symm))
  | .one, _ => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        exact .inl (.one hG)
      · rcases hn with ⟨Λ, hG, hS⟩
        exact (Multiset.zero_ne_cons hS).elim
  | .top (Γ := Θ), _ => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        exact .inl .top
      · rcases hn with ⟨Λ, hG, hS⟩
        let t : CF⇓((⊤ : Proposition Atom) ::ₘ ((Λ : Sequent Atom) + Δ)) := CF.Proof.top
        exact .inr (t.rwConclusion (by grind only [multiset]))
  | .bot (Γ := Θ) s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        let s' : CF⇓(Γ : Sequent Atom) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓Θ)) hG.symm
        exact .inl (.bot s')
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ Λ) := CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓Θ)) hS
        have hlt : s'.val.height < (Proof.bot s).height := by grind [Proof.height]
        exact .inr ((CF.Proof.bot (recur s' hlt)).rwConclusion
          (by grind only [multiset]))
  | .parr (a := c) (b := d) (Γ := Θ) s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        let s' : CF⇓(c ::ₘ d ::ₘ Γ) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(c ::ₘ d ::ₘ Θ))) (by rw [← hG])
        exact .inl (.parr s')
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ (c :: d :: Λ : List (Proposition Atom))) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(c ::ₘ d ::ₘ Θ)))
            (by grind only [multiset])
        have hlt : s'.val.height < (Proof.parr s).height := by grind [Proof.height]
        let t : CF⇓(c ::ₘ d ::ₘ ((Λ : Sequent Atom) + Δ)) :=
          (recur s' hlt).rwConclusion (by grind only [multiset])
        exact .inr ((CF.Proof.parr t).rwConclusion (by grind only [multiset]))
  | .tensor (a := c) (b := d) (Γ := Θ) (Δ := T) s t, hst => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        rcases Sequent.presentSumForCut Γ hG with ⟨Λ, R, hL, hR⟩
        let s' : CF⇓(c ::ₘ Λ) :=
          CF.Proof.rwConclusion (p := (⟨s, hst.1⟩ : CF⇓(c ::ₘ Θ))) (by rw [← hL])
        let t' : CF⇓(d ::ₘ R) :=
          CF.Proof.rwConclusion (p := (⟨t, hst.2⟩ : CF⇓(d ::ₘ T))) (by rw [← hR])
        exact .inl (.tensor (by rw [hL, hR]; exact hG) s' t')
      · rcases hn with ⟨Κ, hG, hST⟩
        rcases Sequent.presentSumForCut (a :: Κ) hST.symm with ⟨Λ, R, hL, hR⟩
        have hsplit : a ::ₘ Κ = (Λ : Sequent Atom) + R := by
          rw [hL, hR]; exact hST.symm
        rcases Sequent.splitConsAdd hsplit with hl | hr
        · rcases hl with ⟨Λ', hLL, hK⟩
          let s' : CF⇓(a ::ₘ (c :: Λ' : List (Proposition Atom))) :=
            CF.Proof.rwConclusion (p := (⟨s, hst.1⟩ : CF⇓(c ::ₘ Θ)))
              (by grind only [multiset])
          have hlt : s'.val.height < (Proof.tensor s t).height := by grind [Proof.height]
          let s'' : CF⇓(c ::ₘ ((Λ' : Sequent Atom) + Δ)) :=
            (recur s' hlt).rwConclusion (Multiset.cons_add _ _ _)
          exact .inr
            ((CF.Proof.tensor s'' (⟨t, hst.2⟩ : CF⇓(d ::ₘ T))).rwConclusion
              (by grind only [multiset]))
        · rcases hr with ⟨R', hRR, hK⟩
          let t' : CF⇓(a ::ₘ (d :: R' : List (Proposition Atom))) :=
            CF.Proof.rwConclusion (p := (⟨t, hst.2⟩ : CF⇓(d ::ₘ T)))
              (by grind only [multiset])
          have hlt : t'.val.height < (Proof.tensor s t).height := by grind [Proof.height]
          let t'' : CF⇓(d ::ₘ ((R' : Sequent Atom) + Δ)) :=
            (recur t' hlt).rwConclusion (Multiset.cons_add _ _ _)
          exact .inr
            ((CF.Proof.tensor (⟨s, hst.1⟩ : CF⇓(c ::ₘ Θ)) t'').rwConclusion
              (by grind only [multiset]))
  | .oplus₁ (a := c) (b := d) (Γ := Θ) s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        let s' : CF⇓(c ::ₘ Γ) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(c ::ₘ Θ))) (by rw [← hG])
        exact .inl (.oplus1 s')
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ (c :: Λ : List (Proposition Atom))) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(c ::ₘ Θ))) (by grind only [multiset])
        have hlt : s'.val.height < (Proof.oplus₁ (b := d) s).height := by grind [Proof.height]
        let t : CF⇓(c ::ₘ ((Λ : Sequent Atom) + Δ)) :=
          (recur s' hlt).rwConclusion (Multiset.cons_add _ _ _)
        exact .inr ((CF.Proof.oplus₁ (b := d) t).rwConclusion
          (by grind only [multiset]))
  | .oplus₂ (a := c) (b := d) (Γ := Θ) s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        let s' : CF⇓(d ::ₘ Γ) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(d ::ₘ Θ))) (by rw [← hG])
        exact .inl (.oplus2 s')
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ (d :: Λ : List (Proposition Atom))) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(d ::ₘ Θ))) (by grind only [multiset])
        have hlt : s'.val.height < (Proof.oplus₂ (a := c) s).height := by grind [Proof.height]
        let t : CF⇓(d ::ₘ ((Λ : Sequent Atom) + Δ)) :=
          (recur s' hlt).rwConclusion (Multiset.cons_add _ _ _)
        exact .inr ((CF.Proof.oplus₂ (a := c) t).rwConclusion
          (by grind only [multiset]))
  | .with (a := c) (b := d) (Γ := Θ) s t, hst => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        let s' : CF⇓(c ::ₘ Γ) :=
          CF.Proof.rwConclusion (p := (⟨s, hst.1⟩ : CF⇓(c ::ₘ Θ))) (by rw [← hG])
        let t' : CF⇓(d ::ₘ Γ) :=
          CF.Proof.rwConclusion (p := (⟨t, hst.2⟩ : CF⇓(d ::ₘ Θ))) (by rw [← hG])
        exact .inl (.with s' t')
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ (c :: Λ : List (Proposition Atom))) :=
          CF.Proof.rwConclusion (p := (⟨s, hst.1⟩ : CF⇓(c ::ₘ Θ)))
            (by grind only [multiset])
        let t' : CF⇓(a ::ₘ (d :: Λ : List (Proposition Atom))) :=
          CF.Proof.rwConclusion (p := (⟨t, hst.2⟩ : CF⇓(d ::ₘ Θ)))
            (by grind only [multiset])
        have hslt : s'.val.height < (Proof.with s t).height := by grind [Proof.height]
        have htlt : t'.val.height < (Proof.with s t).height := by grind [Proof.height]
        let s'' : CF⇓(c ::ₘ ((Λ : Sequent Atom) + Δ)) :=
          (recur s' hslt).rwConclusion (Multiset.cons_add _ _ _)
        let t'' : CF⇓(d ::ₘ ((Λ : Sequent Atom) + Δ)) :=
          (recur t' htlt).rwConclusion (Multiset.cons_add _ _ _)
        exact .inr ((CF.Proof.with s'' t'').rwConclusion (by grind only [multiset]))
  | .quest (a := c) (Γ := Θ) s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · exact (notQuest c hp.1).elim
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ (c :: Λ : List (Proposition Atom))) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(c ::ₘ Θ))) (by grind only [multiset])
        have hlt : s'.val.height < (Proof.quest s).height := by grind [Proof.height]
        let t : CF⇓(c ::ₘ ((Λ : Sequent Atom) + Δ)) :=
          (recur s' hlt).rwConclusion (Multiset.cons_add _ _ _)
        exact .inr ((CF.Proof.quest t).rwConclusion (by grind only [multiset]))
  | .weaken (a := c) (Γ := Θ) s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · exact (notQuest c hp.1).elim
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ Λ) := CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓Θ)) hS
        have hlt : s'.val.height < (Proof.weaken (a := c) s).height := by grind [Proof.height]
        exact .inr
          ((CF.Proof.weaken (a := c) (recur s' hlt)).rwConclusion
            (by grind only [multiset]))
  | .contract (a := c) (Γ := Θ) s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · exact (notQuest c hp.1).elim
      · rcases hn with ⟨Λ, hG, hS⟩
        let s' : CF⇓(a ::ₘ (ʔc :: ʔc :: Λ : List (Proposition Atom))) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(ʔc ::ₘ ʔc ::ₘ Θ)))
            (by grind only [multiset])
        have hlt : s'.val.height < (Proof.contract s).height := by grind [Proof.height]
        let t : CF⇓(ʔc ::ₘ ʔc ::ₘ ((Λ : Sequent Atom) + Δ)) :=
          (recur s' hlt).rwConclusion (by grind only [multiset])
        exact .inr ((CF.Proof.contract t).rwConclusion (by grind only [multiset]))
  | .bang (a := c) (Γ := Θ) hS s, hs => by
      intro h q recur
      rcases Sequent.splitCutHead h.symm with hp | hn
      · rcases hp with ⟨ha, hG⟩
        subst a
        have hGm : Sequent.allQuest (Γ : Sequent Atom) := by
          rw [hG]
          exact hS
        have hGl : Γ.allQuest := by
          simpa only [Sequent.allQuest_coe] using hGm
        let s' : CF⇓(c ::ₘ Γ) :=
          CF.Proof.rwConclusion (p := (⟨s, hs⟩ : CF⇓(c ::ₘ Θ))) (by rw [← hG])
        exact .inl (.bang hGl s')
      · rcases hn with ⟨Λ, hG, htail⟩
        have hf : False := by
          have ha : a ∈ Θ := by rw [htail]; simp
          obtain ⟨b, hb⟩ := Sequent.exists_quest_of_mem_allQuest hS ha
          exact notQuest b hb
        exact hf.elim
  | .cut _ _, h => nomatch h


/-- Cut a bang proposition by commuting through its supplying proof to an axiom or promotion.
At promotion, delegates to `questMulticut` with one selected occurrence. -/
def Proof.bangCutAdm [DecidableEq Atom]
    (cutSmaller : CutAdmissibleBelow Atom (!a).rank)
    {Γ Δ : List (Proposition Atom)}
    (p : CF⇓((!a) ::ₘ Γ)) (q : CF⇓(ʔ(a⫠) ::ₘ Δ)) :
    CF⇓((Γ : Sequent Atom) + Δ) := by
  have go : ∀ k : ℕ, ∀ {Γ Δ : List (Proposition Atom)}
      (p : CF⇓((!a) ::ₘ Γ)) (q : CF⇓(ʔ(a⫠) ::ₘ Δ)),
      p.val.height = k → CF⇓((Γ : Sequent Atom) + Δ) := by
    intro k
    induction k using Nat.strongRec with | ind k ih => ?_
    intro Γ Δ p q hk
    let recur {Γ' : List (Proposition Atom)}
        (p' : CF⇓((!a) ::ₘ Γ')) (hlt : p'.val.height < p.val.height) :
        CF⇓((Γ' : Sequent Atom) + Δ) :=
      ih p'.val.height (by lia) p' q rfl
    rcases Proof.cutStep (a := !a) (by intro b hb; cases hb)
        p.val p.property rfl q recur with v | r
    · match v with
      | .bang hG p0 =>
          exact Proof.questMulticut (a := a) (n := 1) cutSmaller hG p0
            (q.rwConclusion rfl)
    · exact r
  exact go p.val.height p q rfl

/-- Reverse the exponential cut orientation using `bangCutAdm`, duality, and exchange.
This is a wrapper, not a recursive call that swaps premises at the same measure. -/
def Proof.questCutAdm [DecidableEq Atom]
    (cutSmaller : CutAdmissibleBelow Atom (ʔa).rank)
    {Γ Δ : List (Proposition Atom)}
    (p : CF⇓(ʔa ::ₘ Γ)) (q : CF⇓((!(a⫠)) ::ₘ Δ)) :
    CF⇓((Γ : Sequent Atom) + Δ) := by
  have hsize : (!(a⫠)).rank = (ʔa).rank := by
    simp
  let cutSmaller' : CutAdmissibleBelow Atom (!(a⫠)).rank :=
    fun {b} hb => cutSmaller (a := b) (by simpa only [hsize] using hb)
  let p' : CF⇓(ʔ((a⫠)⫠) ::ₘ Γ) := p.rwConclusion (by simp [Proposition.dual_involution a])
  exact (Proof.bangCutAdm (a := a⫠) cutSmaller' q p').rwConclusion
    (Multiset.add_comm _ _)

open scoped Proposition

/-- Reduce a pair of principal rules whose conclusions match the cut proposition.
Every recursive call is on a proper subproposition of the original cut proposition,
so termination is guaranteed by proposition size. -/
def Proof.cutPrincipal {a : Proposition Atom} (cutSmaller : CutAdmissibleBelow Atom a.rank)
    {Γ Δ : List (Proposition Atom)}
  (vp : Proof.CutPrincipal Γ a) (vq : Proof.CutPrincipal Δ a⫠) :
    CF⇓((Γ : Sequent Atom) + Δ) :=
  match (generalizing := true) vp, vq with
  | .one hG, .bot q0 => q0.rwConclusion (by simp [hG])
  | .bot p0, .one hD => p0.rwConclusion (by simp [hD])
  | .top, vq => nomatch vq
  | .bang _ _, vq => nomatch vq
  | .tensor (c := c) (d := d) (Λ := Λ) (R := R) hG p1 p2, .parr q0 => by
      have hc : c.rank < (c ⊗ d).rank := by grind
      have hd : d.rank < (c ⊗ d).rank := by grind
      let t := cutSmaller (a := c) hc (Γ := Λ) (Δ := d⫠ :: Δ) p1 q0
      let t' : CF⇓(d⫠ ::ₘ (Λ ++ Δ : List (Proposition Atom))) :=
        t.rwConclusion (by grind only [multiset])
      let u := cutSmaller (a := d) hd (Γ := R) (Δ := Λ ++ Δ) p2 t'
      exact u.rwConclusion (by grind only [multiset])
  | .parr (c := c) (d := d) p0,
      .tensor (Λ := Λ) (R := R) hD q1 q2 => by
      have hc : c.rank < (c ⅋ d).rank := by grind
      have hd : d.rank < (c ⅋ d).rank := by grind
      let t := cutSmaller (a := c) hc (Γ := d :: Γ) (Δ := Λ) p0 q1
      let t' : CF⇓(d ::ₘ (Γ ++ Λ : List (Proposition Atom))) :=
        t.rwConclusion (by grind only [multiset])
      let u := cutSmaller (a := d) hd (Γ := Γ ++ Λ) (Δ := R) t' q2
      exact u.rwConclusion (by grind only [multiset])
  | .oplus1 (c := c) (d := d) p0, .with q1 _ =>
      cutSmaller (a := c) (by grind) p0 q1
  | .oplus2 (c := c) (d := d) p0, .with _ q2 =>
      cutSmaller (a := d) (by grind) p0 q2
  | .with (c := c) (d := d) p1 _, .oplus1 q0 =>
      cutSmaller (a := c) (by grind) p1 q0
  | .with (c := c) (d := d) _ p2, .oplus2 q0 =>
      cutSmaller (a := d) (by grind) p2 q0

/-- Cut admissibility for non-exponential propositions: uses height induction on the
sum of premise heights, with commuting cases for non-principal rules.
Only callable when neither `a` nor `a⫠` is a question mark. -/
def Proof.cutAdmNonExponential [DecidableEq Atom]
    (cutSmaller : CutAdmissibleBelow Atom a.rank)
    (notQuest : ∀ b, a ≠ ʔb)
    (dualNotQuest : ∀ b, a⫠ ≠ ʔb) : CutAdmissibleAt a := by
  have go : ∀ k : ℕ, ∀ {Γ Δ : List (Proposition Atom)}
      (p : CF⇓(a ::ₘ Γ)) (q : CF⇓(a⫠ ::ₘ Δ)),
      p.val.height + q.val.height = k → CF⇓((Γ : Sequent Atom) + Δ) := by
    intro k
    induction k using Nat.strongRec with | ind k ih => ?_
    intro Γ Δ p q hk
    let recurLeft {Γ' : List (Proposition Atom)}
        (p' : CF⇓(a ::ₘ Γ')) (hlt : p'.val.height < p.val.height) :
        CF⇓((Γ' : Sequent Atom) + Δ) :=
      ih (p'.val.height + q.val.height) (by lia) p' q rfl
    rcases Proof.cutStep notQuest p.val p.property rfl q recurLeft with vp | r
    · let p' : CF⇓((a⫠)⫠ ::ₘ Γ) :=
        p.rwConclusion (by simp [Proposition.dual_involution a])
      let recurRight {Δ' : List (Proposition Atom)}
        (q' : CF⇓(a⫠ ::ₘ Δ')) (hlt : q'.val.height < q.val.height) :
          CF⇓((Δ' : Sequent Atom) + Γ) :=
        (ih (p.val.height + q'.val.height) (by lia) p q' rfl).rwConclusion
          (Multiset.add_comm _ _)
      rcases Proof.cutStep dualNotQuest q.val q.property rfl p' recurRight with vq | r
      · exact Proof.cutPrincipal cutSmaller vp vq
      · exact r.rwConclusion (Multiset.add_comm _ _)
    · exact r
  intro Γ Δ p q
  exact go (p.val.height + q.val.height) p q rfl

/-- The proposition-size induction step for cut admissibility.
Dispatches to `bangCutAdm`, `questCutAdm`, or `cutAdmNonExponential` depending on
the top-level connective. -/
def Proof.cutAdmOfSmaller [DecidableEq Atom]
    (cutSmaller : CutAdmissibleBelow Atom a.rank) : CutAdmissibleAt a := by
  cases a <;> first
    | exact Proof.bangCutAdm cutSmaller
    | exact Proof.questCutAdm cutSmaller
    | exact Proof.cutAdmNonExponential cutSmaller
        (by intro b hb; cases hb)
        (by intro b hb; cases hb)

/-- The core cut admissibility implementation: given decidable atom equality and explicit
list sequents, combine cut-free proofs of dual distinguished propositions into a cut-free
proof of the sum of their residual sequents. Uses rank-based strong induction. -/
def Proof.cutAdmImpl [DecidableEq Atom]
    {Γ Δ : List (Proposition Atom)}
  (p : CF⇓(a ::ₘ Γ)) (q : CF⇓(a⫠ ::ₘ Δ)) :
    CF⇓((Γ : Sequent Atom) + Δ) := by
  suffices CutAdmissibleAt a from this p q
  clear p q Γ Δ
  induction hn : a.rank using Nat.strongRec generalizing a with | ind n ih =>
  refine Proof.cutAdmOfSmaller ?_
  intro c hc
  have hcrank : c.rank < n := by grind only [Proposition.rank_eq_sizeOf]
  exact @ih c.rank hcrank c rfl

/-- Public entry point for cut admissibility: given cut-free proofs of `a ::ₘ Γ` and
`a⫠ ::ₘ Δ`, produce a cut-free proof of `(Γ : Sequent) + Δ`. -/
def Proof.cutAdm [DecidableEq Atom] {Γ Δ : List (Proposition Atom)}
    (p : CF⇓(a ::ₘ Γ)) (q : CF⇓(a⫠ ::ₘ Δ)) : CF⇓((Γ : Sequent Atom) + Δ) := cutAdmImpl p q

/-- Compute cut-free proofs by structural recursion on the original (possibly
non-cut-free) proof. Each case recursively normalises the premises, then uses
`cutAdm` at each cut. The list `Γ` is the explicit sequent for the current subgoal. -/
def Proof.cutElimAux [DecidableEq Atom] {Θ : Sequent Atom} (r : Proof Θ) :
    ∀ (Γ : List (Proposition Atom)), Θ = (Γ : Sequent Atom) → CF⇓(Γ : Sequent Atom) :=
  match r with
  | .ax (a := c) => fun Γ h =>
      (CF.Proof.ax (a := c)).rwConclusion h
  | .one => fun Γ h =>
      (CF.Proof.one (Atom := Atom)).rwConclusion h
  | .top (Γ := Θ) => fun Γ h =>
      (CF.Proof.top (Γ := Θ)).rwConclusion h
  | .bot (Γ := Θ) s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s Λ hL.symm
      exact (CF.Proof.bot s').rwConclusion (by rw [hL, h])
  | .parr (a := c) (b := d) (Γ := Θ) s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s (c :: d :: Λ) (by grind only [multiset])
      exact (CF.Proof.parr (a := c) (b := d) (Γ := Λ) s').rwConclusion (by grind only [multiset])
  | .tensor (a := c) (b := d) (Γ := Θ) (Δ := T) s t => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Κ, hK⟩
      rcases Sequent.presentSumForCut Κ hK with ⟨Λ, R, hL, hR⟩
      let s' := Proof.cutElimAux s (c :: Λ) (by grind only [multiset])
      let t' := Proof.cutElimAux t (d :: R) (by grind only [multiset])
      exact (CF.Proof.tensor (a := c) (b := d) (Γ := Λ) (Δ := R) s' t').rwConclusion
        (by grind only [multiset])
  | .oplus₁ (a := c) (b := d) (Γ := Θ) s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s (c :: Λ) (by grind only [multiset])
      exact (CF.Proof.oplus₁ (a := c) (b := d) (Γ := Λ) s').rwConclusion (by grind only [multiset])
  | .oplus₂ (a := c) (b := d) (Γ := Θ) s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s (d :: Λ) (by grind only [multiset])
      exact (CF.Proof.oplus₂ (a := c) (b := d) (Γ := Λ) s').rwConclusion (by grind only [multiset])
  | .with (a := c) (b := d) (Γ := Θ) s t => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s (c :: Λ) (by grind only [multiset])
      let t' := Proof.cutElimAux t (d :: Λ) (by grind only [multiset])
      exact (CF.Proof.with (a := c) (b := d) (Γ := Λ) s' t').rwConclusion (by grind only [multiset])
  | .quest (a := c) (Γ := Θ) s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s (c :: Λ) (by grind only [multiset])
      exact (CF.Proof.quest (a := c) (Γ := Λ) s').rwConclusion (by grind only [multiset])
  | .weaken (a := c) (Γ := Θ) s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s Λ hL.symm
      exact (CF.Proof.weaken (a := c) s').rwConclusion (by grind only [multiset])
  | .contract (a := c) (Γ := Θ) s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s (ʔc :: ʔc :: Λ) (by grind only [multiset])
      exact (CF.Proof.contract (a := c) (Γ := Λ) s').rwConclusion (by grind only [multiset])
  | .bang (a := c) (Γ := Θ) hS s => by
      intro Γ h
      rcases Sequent.presentTailForCut Γ h with ⟨Λ, hL⟩
      let s' := Proof.cutElimAux s (c :: Λ) (by grind only [multiset])
      have hLq : Sequent.allQuest (Λ : Sequent Atom) := by
        rw [hL]
        exact hS
      exact (CF.Proof.bang (a := c) (Γ := Λ) hLq s').rwConclusion (by grind only [multiset])
  | .cut (a := c) (Γ := Θ) (Δ := T) s t => by
      intro Γ h
      rcases Sequent.presentSumForCut Γ h.symm with ⟨Λ, R, hL, hR⟩
      let s' := Proof.cutElimAux s (c :: Λ) (by grind only [multiset])
      let t' := Proof.cutElimAux t (c⫠ :: R) (by grind only [multiset])
      exact (Proof.cutAdm (a := c) (Γ := Λ) (Δ := R) s' t').rwConclusion
        (by grind only [multiset])

/-- List-based cut elimination with the concrete list presentation explicit. -/
def Proof.cutElimList [DecidableEq Atom] {Γ : List (Proposition Atom)}
    (p : ⇓(Γ : Sequent Atom)) : CF⇓(Γ : Sequent Atom) := cutElimAux p Γ rfl

/-- Cut elimination, using a noncomputable list presentation. -/
noncomputable def Proof.cutElim [DecidableEq Atom] {Γ : Sequent Atom} (p : ⇓Γ) : CF⇓Γ :=
  (cutElimAux p Γ.toList (Multiset.coe_toList Γ).symm).rwConclusion (Multiset.coe_toList Γ)

end Cslib.Logic.CLL
