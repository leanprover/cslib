/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Marianna Girlando
-/

module

public import Cslib.Logics.Modal.Basic
public import Cslib.Foundations.Semantics.Frame.Basic

/-! # Semantics of Modal Logic -/

@[expose] public section

namespace Cslib.Logic.Modal

/-- A model is a frame equipped with a valuation of atoms at worlds. -/
structure Model World (τ : PFunctor) Atom extends Frame World τ where
  /-- Valuation of atoms at a world. -/
  v : World → Atom → Prop

/-- Satisfaction relation. `Satisfies m w φ` means that, in the model `m`, the world `w` satisfies
the proposition `φ`. -/
def Satisfies (m : Model World τ Atom) (w : World) : Proposition τ Atom → Prop
  | .atom p => m.v w p
  | .false => False
  | .not φ => ¬Satisfies m w φ
  | .or φ₁ φ₂ => Satisfies m w φ₁ ∨ Satisfies m w φ₂
  | .triangle op φs => ∃ ws : τ.B op → World, m.r op w ws ∧ ∀ i, Satisfies m (ws i) (φs i)

/-- Judgement, representing the conclusions one reaches in modal logic. -/
structure Judgement World τ Atom where
  /-- Constructs a judgement. -/
  mk ::
  /-- Model. -/
  m : Model World τ Atom
  /-- The world satisfying the proposition `φ`. -/
  w : World
  /-- The proposition satisfied by the world `w`. -/
  φ : Proposition τ Atom

@[inherit_doc] scoped notation "Modal[" m "," w " ⊨ " φ "]" => Judgement.mk m w φ

/-- Satisfaction for judgements. This just refers to the unbundled `Satisfies`. -/
def Satisfies.Bundled (j : Judgement World τ Atom) : Prop := Satisfies j.m j.w j.φ

instance {World : Type*} {τ : PFunctor} {Atom : Type*} :
    HasInferenceSystem (Judgement World τ Atom) := ⟨Satisfies.Bundled⟩

open scoped InferenceSystem Proposition PropositionMap Frame PFunctor

@[scoped grind =]
theorem derivation_def {m : Model World τ Atom} {w : World} {φ : Proposition τ Atom} :
  Satisfies m w φ = ⇓Modal[m,w ⊨ φ] := rfl

@[simp, scoped grind =, modal =]
theorem Satisfies.atom_iff {a : Atom} : ⇓Modal[m,w ⊨ a] ↔ m.v w a := by rfl

@[simp, scoped grind =, modal =]
theorem Satisfies.false : ⇓Modal[m,w ⊨ ⊥] ↔ False := by rfl

/-- A world satisfies a proposition iff it does not satisfy the negation of the proposition. -/
@[scoped grind =, modal =]
theorem Satisfies.not_iff_not : ⇓Modal[m,w ⊨ ¬φ] ↔ ¬⇓Modal[m,w ⊨ φ] := by rfl

@[simp, scoped grind ., modal .]
theorem Satisfies.true : ⇓Modal[m,w ⊨ ⊤] := by
  grind [=_ Proposition.true_def, Proposition.true]

@[scoped grind =, modal =]
theorem Satisfies.or_iff_or {m : Model World τ Atom} :
    ⇓Modal[m,w ⊨ φ₁ ∨ φ₂] ↔ ⇓Modal[m,w ⊨ φ₁] ∨ ⇓Modal[m,w ⊨ φ₂] := by rfl

@[scoped grind =]
theorem Satisfies.triangle_iff_exists {m : Model World τ Atom} :
    ⇓Modal[m,w ⊨ Δ[op]φs] ↔ ∃ ws, m.r op w ws ∧ ∀ i, ⇓Modal[m,(ws i) ⊨ (φs i)] := by rfl

@[scoped grind =]
theorem Satisfies.triangle_not_iff_exists_not {φs : τ.B op → Proposition τ Atom}
    {m : Model World τ Atom} : ⇓Modal[m,w ⊨ Δ[op]¬φs] ↔
      ∃ ws, m.r op w ws ∧ ∀ i, ¬⇓Modal[m,(ws i) ⊨ (φs i)] := by
  have : (¬φs) = (fun i => ¬(φs i)) := rfl
  grind

/-- Characterisation of the `∧` connective.

Conjunction is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct. -/
@[scoped grind =, modal =]
theorem Satisfies.and_iff_and {m : Model World τ Atom} :
    ⇓Modal[m,w ⊨ φ₁ ∧ φ₂] ↔ ⇓Modal[m,w ⊨ φ₁] ∧ ⇓Modal[m,w ⊨ φ₂] := by
  grind [=_ Proposition.and_def, Proposition.and]

/-- Characterisation of the `→` connective.

Implication is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct.
-/
@[scoped grind =, modal =]
theorem Satisfies.imp_iff_imp {m : Model World τ Atom} :
    ⇓Modal[m,w ⊨ φ₁ → φ₂] ↔ (⇓Modal[m,w ⊨ φ₁] → ⇓Modal[m,w ⊨ φ₂]) := by
  grind [=_ Proposition.imp_def, Proposition.imp]

/-- Characterisation of the `↔` connective.

Bi-implication is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct. -/
@[scoped grind =, modal =]
theorem Satisfies.iff_iff_iff {m : Model World τ Atom} :
    ⇓Modal[m,w ⊨ φ₁ ↔ φ₂] ↔ (⇓Modal[m,w ⊨ φ₁] ↔ ⇓Modal[m,w ⊨ φ₂]) := by
  simp only [HasIff.iff, Proposition.iff]
  grind

/-- Characterisation of `∇`.

Necessity is defined in terms of the more primitive connectives given in `Proposition`.
This result proves that the definition is correct. -/
@[scoped grind =]
theorem Satisfies.nabla_iff_forall {m : Model World τ Atom} :
    ⇓Modal[m,w ⊨ ∇[op]φs] ↔ ∀ ws, m.r op w ws → ∃ i, ⇓Modal[m,(ws i) ⊨ (φs i)] := by
  grind [=_ Proposition.nabla_def, Proposition.nabla]

/-- The theory of a world in a model is the set of all propositions that it satisfies. -/
abbrev theory {World : Type*} {τ : PFunctor} {Atom : Type*} (m : Model World τ Atom)
    (w : World) : Set (Proposition τ Atom) := {φ | ⇓Modal[m,w ⊨ φ]}

/-- Two worlds are theory-equivalent under a model if they have the same theory. -/
abbrev TheoryEq (m : Model World τ Atom) (w₁ w₂ : World) :=
  theory m w₁ = theory m w₂

theorem TheoryEq.ext_iff : TheoryEq m w₁ w₂ ↔ (∀ φ, φ ∈ theory m w₁ ↔ φ ∈ theory m w₂) := by
  grind

/-- Any proposition satisfied by a world is in the theory of that world. -/
@[scoped grind →]
theorem satisfies_theory (h : ⇓Modal[m,w ⊨ φ]) : φ ∈ theory m w := by grind

/-- If two worlds are not theory equivalent, there exists a distinguishing proposition. -/
lemma not_theoryEq_satisfies (h : ¬TheoryEq m w₁ w₂) :
    ∃ φ, (⇓Modal[m,w₁ ⊨ φ] ∧ ¬⇓Modal[m,w₂ ⊨ φ]) := by grind [=_ Satisfies.not_iff_not]

/-- If two worlds are theory equivalent and the former satisfies a proposition, the latter does as
well. -/
theorem theoryEq_satisfies {m : Model World τ Atom} (h : TheoryEq m w₁ w₂)
    (hs : Satisfies m w₁ φ) : ⇓Modal[m,w₂ ⊨ φ] := by
  apply TheoryEq.ext_iff.1 at h
  exact (h φ).mp hs

/-- Every frame induces an inference system tag for proving valid axioms under the frame. -/
inductive Axiom (f : Frame World τ)

/-- A proposition `φ` is an axiom under a frame `f` if it holds for all valuations and worlds. -/
instance {World : Type*} {τ : PFunctor} {Atom : Type*} (f : Frame World τ) :
    InferenceSystem (Axiom f) (Proposition τ Atom) where
  derivation φ := ∀ v w, ⇓Modal[⟨f,v⟩,w ⊨ φ]

@[scoped grind ⇒]
theorem Satisfies.axiom_def (f : Frame World τ) :
    (∀ v w, ⇓Modal[⟨f,v⟩,w ⊨ φ]) ↔ Axiom f⇓φ := by rfl

@[modal .]
theorem Satisfies.der_of_axiom (h : Axiom m.toFrame⇓φ) : ⇓Modal[m,w ⊨ φ] := h m.v w

/-- If a proposition is an axiom under the frame of a model, it is satisfied by every world. -/
@[scoped grind ., modal .]
theorem Satisfies.of_axiom (m : Model World τ Atom) (φ : Proposition τ Atom) (h : Axiom m.toFrame⇓φ)
    (w : World) : ⇓Modal[m,w ⊨ φ] := h m.v w

@[scoped grind =]
theorem Satisfies.subst_apply_iff [DecidableEq (τ.B op)] {φs : PropositionMap τ op Atom}
    {i j : τ.B op} {φ : Proposition τ Atom} : ⇓Modal[m,w ⊨ φs[i := φ] j] ↔
      (j = i ∧ ⇓Modal[m,w ⊨ φ]) ∨ (j ≠ i ∧ ⇓Modal[m,w ⊨ φs j]) :=
  Function.pred_update (P := fun _ φ' => Satisfies m w φ') φs i φ j

/-- Axiom K, valid for all frames. -/
@[scoped grind ., modal .]
theorem Satisfies.k (f : Frame World τ) {φs : PropositionMap τ op Atom} [DecidableEq (τ.B op)]
    {i : τ.B op} {φ₁ φ₂ : Proposition τ Atom} (hi : φs i = (φ₁ → φ₂)) :
    Axiom f⇓(∇[op]φs → (∇[op]φs[i := φ₁] → ∇[op]φs[i := φ₂])) := by grind

/-- The dual axiom, valid for all frames. -/
theorem Satisfies.dual (f : Frame World τ) {φs : PropositionMap τ op Atom} :
    Axiom f⇓(Δ[op]φs ↔ ¬∇[op]¬φs) := by grind

/-- Possibility preserves conjunction. -/
@[scoped grind ., modal .]
theorem Satisfies.triangle_and (f : Frame World τ) (φs₁ φs₂ : PropositionMap τ op Atom) :
    Axiom f⇓(Δ[op](φs₁ ∧ φs₂) → (Δ[op]φs₁ ∧ Δ[op]φs₂)) := by grind

/-- Possibility can be combined with necessity. -/
@[modal .]
theorem Satisfies.triangle_and_nabla {m : Model World τ Atom} [DecidableEq (τ.B op)]
    (h : ⇓Modal[m,w ⊨ Δ[op]φs₁ ∧ ∇[op]φs₂]) : ∃ i, ⇓Modal[m,w ⊨ Δ[op]φs₁[i := φs₁ i ∧ φs₂ i]] := by
  grind

/-- If `φ₁` is necessary and some successor exists, then some successor satisfies `φ₁`. -/
@[scoped grind ., modal .]
theorem Satisfies.triangle_of_nabla {φs₁ φs₂ : PropositionMap τ op Atom}
    [DecidableEq (τ.B op)] (h : ⇓Modal[m,w ⊨ ∇[op]φs₁ ∧ Δ[op]φs₂]) :
    ∃ i, ⇓Modal[m,w ⊨ Δ[op]φs₂[i := φs₁ i]] := by grind

@[scoped grind .]
theorem Satisfies.triangle_of_diagonal {m : Model World τ Atom} {op : τ.A} {w : World}
    {φ : Proposition τ Atom} [instRefl : Std.Refl (m.toFrame.diagonal op)]
    (h : ⇓Modal[m,w ⊨ φ]) : ⇓Modal[m,w ⊨ Δ[op](PropositionMap.const op φ)] :=
  ⟨fun _ => w, instRefl.refl w, by grind⟩

/-- Axiom T. -/
theorem Satisfies.t (f : Frame World τ) [instRefl : Std.Refl (f.diagonal op)]
    (φ : Proposition τ Atom) : Axiom f⇓(φ → Δ[op](PropositionMap.const op φ)) := by grind

/-- Any frame admitting T for `op` has a reflexive diagonal relation. -/
theorem Satisfies.t_refl (f : Frame World τ) {op : τ.A} [Nonempty Atom]
    (h : ∀ φ : Proposition τ Atom, Axiom f⇓(φ → Δ[op](PropositionMap.const op φ))) :
    Std.Refl (f.diagonal op) where
  refl w := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (_ : Atom) => w' = w
    have h' := h (v := v) (w := w) (φ := a)
    rw [Satisfies.imp_iff_imp] at h'
    specialize h' rfl
    obtain ⟨ws, hr, _⟩ := h'
    have hws : ws = fun _ => w := by grind
    grind [Frame.diagonal]

/-- In any model whose diagonal relation for `op` is reflexive, `∇[op]φ → φ` is equivalent to
`φ → Δ[op]φ`. -/
theorem Satisfies.t_nabla_triangle (f : Frame World τ) [Std.Refl (f.diagonal op)] :
    Axiom f⇓((∇[op](PropositionMap.const op φ) → φ) ↔ (φ → Δ[op](PropositionMap.const op φ))) := by
  intro _ w
  have hr : f.r op w (fun _ => w) := by
    simpa [Frame.diagonal] using (Std.Refl.refl (r := f.diagonal op) w)
  grind

/-- Axiom B, valid for diagonally symmetric frames. -/
theorem Satisfies.b (f : Frame World τ) [f.DiagonalSymm op] (φ : Proposition τ Atom) :
    Axiom f⇓(φ → ∇[op](PropositionMap.const op (Δ[op](PropositionMap.const op φ)))) := by
  intro _ w
  have := Frame.DiagonalSymm.symm (f := f) (op := op)
  grind

/-- Any frame that admits B at `op` is diagonally symmetric at `op`. -/
theorem Satisfies.b_symm (f : Frame World τ) [Nonempty Atom]
    (h : ∀ φ : Proposition τ Atom,
      Axiom f⇓(φ → ∇[op](PropositionMap.const op (Δ[op](PropositionMap.const op φ))))) :
    f.DiagonalSymm op where
  symm w ws hwws := by
    have a := Classical.arbitrary Atom
    let v := fun (w' : World) (_ : Atom) => w' = w
    let h' := h (v := v) (w := w) (φ := a)
    rw [Satisfies.imp_iff_imp] at h'
    specialize h' (by grind)
    rw [Satisfies.nabla_iff_forall] at h'
    obtain ⟨i, ws', _⟩ := h' ws hwws
    have : ws' = fun _ => w := by grind
    grind

/-- The 4 axiom, valid for transitive frames. -/
theorem Satisfies.four (f : Frame World τ) [f.Trans op]
    (φs ψs : PropositionMap τ op Atom) (i : τ.B op)
    (hi : φs i = (Δ[op]ψs)) :
    Axiom f⇓(Δ[op]φs → Δ[op]ψs) := by
  have ht := Frame.Trans.trans (f := f) (op := op) (i := i)
  grind only [modal, =_ axiom_def, = triangle_iff_exists]

/-- Any frame that admits 4 at `op` is transitive at `op`. -/
theorem Satisfies.four_trans (f : Frame World τ) [Nonempty Atom]
    (e : τ.B op ↪ Atom) (h : ∀ (φs ψs : PropositionMap τ op Atom) (i : τ.B op),
      φs i = (Δ[op]ψs) → Axiom f⇓(Δ[op]φs → Δ[op]ψs)) : f.Trans op where
  trans w ws i ws' h₁ h₂ := by
    classical
    let a := Classical.arbitrary Atom
    -- Each coordinate gets its own atom.
    let ψs : PropositionMap τ op Atom := fun j => e j
    -- A tautology for the irrelevant coordinates of the outer triangle.
    let top : Proposition τ Atom := a → a
    let φs : PropositionMap τ op Atom :=
      fun j => if j = i then Δ[op]ψs else top
    -- Atom `e j` holds exactly at `ws' j`.
    let v : World → Atom → Prop :=
      fun x p => ∃ j, p = e j ∧ x = ws' j
    have hi : φs i = (Δ[op]ψs) := by grind only
    have h' := h φs ψs i hi (v := v) (w := w)
    have hφs : ⇓Modal[⟨f, v⟩,w ⊨ Δ[op]φs] := by
      rw [Satisfies.triangle_iff_exists]
      refine ⟨ws, h₁, ?_⟩
      grind only [modal, of_axiom, axiom_def, = triangle_iff_exists]
    rw [Satisfies.imp_iff_imp] at h'
    specialize h' hφs
    rw [Satisfies.triangle_iff_exists] at h'
    obtain ⟨xs, hr, hs⟩ := h'
    have hxs : xs = ws' := by grind
    grind only

/-- Axiom 5, valid for right-Euclidean frames. -/
theorem Satisfies.five (f : Frame World τ) [f.RightEuclidean op]
    (φs : PropositionMap τ op Atom) :
    Axiom f⇓(Δ[op]φs → ∇[op](PropositionMap.const op (Δ[op]φs))) := by
  have he := Frame.RightEuclidean.rightEuclidean (f := f) (op := op)
  grind

/-- Any frame that admits 5 at `op` is right-Euclidean at `op`. -/
theorem Satisfies.five_rightEuclidean (f : Frame World τ) (e : τ.B op ↪ Atom)
    (h : ∀ φs : PropositionMap τ op Atom,
      Axiom f⇓(Δ[op]φs → ∇[op](PropositionMap.const op (Δ[op]φs)))) : f.RightEuclidean op where
  rightEuclidean {w ws₁ ws₂} h₁ h₂ := by
    let φs : PropositionMap τ op Atom := fun i => e i
    let v : World → Atom → Prop :=
      fun w' a => ∃ i, a = e i ∧ w' = ws₁ i
    have h' := h φs (v := v) (w := w)
    have hφs : ⇓Modal[⟨f,v⟩,w ⊨ Δ[op]φs] := by grind
    rw [Satisfies.imp_iff_imp] at h'
    specialize h' hφs
    rw [Satisfies.nabla_iff_forall] at h'
    obtain ⟨i, hi⟩ := h' ws₂ h₂
    obtain ⟨ws', hr, hs⟩ := hi
    have hws : ws' = ws₁ := by
      funext j
      have hj := hs j
      simp only [φs] at hj
      rcases hj with ⟨k, hk, hw⟩
      have hjk : j = k := e.injective hk
      simpa [hjk] using hw
    grind only

/-- A proposition is valid in a class of models `S` (modelled as a set) if it is satisfied under
all models in `S` for all worlds. -/
@[simp, scoped grind =]
def Proposition.valid {World : Type*} {τ : PFunctor} {Atom : Type*} (S : Set (Model World τ Atom))
    (φ : Proposition τ Atom) : Prop := ∀ m ∈ S, ∀ (w : World), ⇓Modal[m,w ⊨ φ]

/-- The modal logic of a class of models `S` is the set of all propositions valid in `S`. -/
@[simp, scoped grind =]
def logic {World : Type*} {τ : PFunctor} {Atom : Type*} (S : Set (Model World τ Atom)) :
    Set (Proposition τ Atom) := {φ | φ.valid S}

/-- Modal logic is antitone (wrt the class of models). -/
theorem logic_antitone {World : Type*} {τ : PFunctor} {Atom : Type*} :
    Antitone (logic (World := World) (τ := τ) (Atom := Atom)) :=
  fun _ _ hS₁S₂ _ hφ m hm w => hφ m (hS₁S₂ hm) w

/-- The class of all models generated by a frame (relation). -/
abbrev modelsOfFrame {World : Type*} {τ : PFunctor} {Atom : Type*} (f : Frame World τ) :
    Set (Model World τ Atom) := {m | m.toFrame = f}

/-- A proposition is an axiom of a frame exactly when it belongs to the logic of all models over
that frame. -/
theorem axiom_iff_mem_logic_modelsOfFrame (f : Frame World τ) (φ : Proposition τ Atom) :
    Axiom f⇓φ ↔ φ ∈ logic (modelsOfFrame f) := by
  constructor
  case mp =>
    rintro h m rfl w
    exact h m.v w
  case mpr => grind [Satisfies.axiom_def]

end Cslib.Logic.Modal
