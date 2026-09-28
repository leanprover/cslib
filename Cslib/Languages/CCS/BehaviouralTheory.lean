/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Syntax.Congruence
public import Cslib.Languages.CCS.Semantics

/-! # Behavioural theory of CCS

## Main results

- `CCS.bisimilarityCongruence`: bisimilarity is a congruence in CCS.

Additionally, some standard laws of bisimilarity for CCS, including:
- `CCS.bisimilarity_par_nil`: P | 𝟎 ~ P.
- `CCS.bisimilarity_par_comm`: P | Q ~ Q | P
- `CCS.bisimilarity_choice_comm`: P + Q ~ Q + P
-/

@[expose] public section

namespace Cslib

section CCS.BehaviouralTheory

open LTS

variable {Name : Type u} {Constant : Type v} {defs : Constant → Option (CCS.Process Name Constant)}

namespace CCS

open Process Act Act.Co Context

attribute [local grind] Tr

@[local grind]
private inductive ParNil : Process Name Constant → Process Name Constant → Prop where
| parNil : ParNil (par p nil) p

/-- P | 𝟎 ~ P -/
@[simp, scoped grind .]
theorem bisimilarity_par_nil : (par p nil) ~[lts (defs := defs)] p := by
  unfold lts at *
  exists ParNil, .parNil
  intro _ _ _ _
  constructor
  case left => grind
  case right =>
    intro s2' htr
    exists par s2' nil
    grind

@[local grind]
private inductive ParComm : Process Name Constant → Process Name Constant → Prop where
| parComm : ParComm (par p q) (par q p)

/-- P | Q ~ Q | P -/
@[scoped grind .]
theorem bisimilarity_par_comm : (par p q) ~[lts (defs := defs)] (par q p) := by
  let defParComm : Process Name Constant → Process Name Constant
    | par p q => par q p
    | _ => nil
  use ParComm, ParComm.parComm
  intro _ _ _ _
  unfold lts at *
  split_ands <;> intro p _ <;> exists defParComm p <;> grind

/-- 𝟎 | P ~ P -/
@[simp, scoped grind .]
theorem bisimilarity_nil_par : (par nil p) ~[lts (defs := defs)] p :=
  calc
    (par nil p) ~[lts (defs := defs)] (par p nil) := by grind
    _ ~[lts (defs := defs)] p := by simp

@[local grind]
private inductive ParAssoc : Process Name Constant → Process Name Constant → Prop where
  | assoc : ParAssoc (par p (par q r)) (par (par p q) r)
  | id : ParAssoc p p

/-- P | (Q | R) ~ (P | Q) | R -/
theorem bisimilarity_par_assoc :
    (par p (par q r)) ~[lts (defs := defs)] (par (par p q) r) := by
  use ParAssoc, ParAssoc.assoc
  intro s1 s2 hr μ
  apply And.intro <;> cases hr
  case right.assoc =>
    intro s2' htr
    unfold lts at *
    cases htr
    case parL p q r p' htr =>
      cases htr
      case parL p q r p' _ =>
        exists p'.par (q.par r)
        grind
      case parR p q r q' _ =>
        exists p.par (q'.par r)
        grind
      case com μ p' μ' q' _ htrp htrq =>
        exists p'.par (q'.par r)
        grind
    case parR p q r r' htr =>
      exists p.par (q.par r')
      grind
    case com p q r μ p' μ' r' _ htr htr' =>
      cases htr
      case parL p' _ =>
        use p'.par (q.par r')
        grind
      case parR q' _ =>
        use p.par (q'.par r')
        grind
      case com => grind
  case left.assoc =>
    intro s2' htr
    unfold lts at *
    cases htr
    case parR htr =>
      cases htr
      case parL p q r q' _ =>
        exists (p.par q').par r
        grind
      case parR p q r r' _ =>
        exists (p.par q).par r'
        grind
      case com p q r μ q' μ' r' _ htrp htrq =>
        use (p.par q').par r'
        grind
    case parL p q r p' htr =>
      exists (p'.par q).par r
      grind
    case com p q r μ p' μ' q' _ htr htr' =>
      cases htr'
      case parL q' _ =>
        use (p'.par q').par r
        grind
      case parR r' _ =>
        use (p'.par q).par r'
        grind
      case com => grind
  all_goals grind

private inductive ChoiceNil : Process Name Constant → Process Name Constant → Prop where
  | nil : ChoiceNil (choice p nil) p
  | id : ChoiceNil p p

/-- P + 𝟎 ~ P -/
theorem bisimilarity_choice_nil : (choice p nil) ~[lts (defs := defs)] p := by
  use ChoiceNil, ChoiceNil.nil
  intro s1 s2 hr μ
  apply And.intro <;> cases hr
  case left.nil =>
    unfold lts
    grind [ChoiceNil]
  case right.nil =>
    intro s2' htr
    exists s2'
    constructor
    · apply Tr.choiceL
      assumption
    · exact ChoiceNil.id
  all_goals grind [ChoiceNil]

@[local grind]
private inductive ChoiceIdem : Process Name Constant → Process Name Constant → Prop where
  | idem : ChoiceIdem (choice p p) p
  | id : ChoiceIdem p p

/-- P + P ~ P -/
theorem bisimilarity_choice_idem :
    (choice p p) ~[lts (defs := defs)] p := by
  exists ChoiceIdem
  apply And.intro
  case left => grind
  case right =>
    intro s1 s2 hr μ
    apply And.intro <;> cases hr <;> unfold lts
    case right.idem =>
      intro s1' htr
      exists s1'
      grind
    all_goals grind

private inductive ChoiceComm : Process Name Constant → Process Name Constant → Prop where
  | choiceComm : ChoiceComm (choice p q) (choice q p)
  | bisim : (p ~[lts (defs := defs)] q) → ChoiceComm p q

open Bisimilarity in
/-- P + Q ~ Q + P -/
theorem bisimilarity_choice_comm : (choice p q) ~[lts (defs := defs)] (choice q p) := by
  exists @ChoiceComm Name Constant defs
  constructor
  · exact ChoiceComm.choiceComm
  intro s1 s2 hr μ
  cases hr
  case choiceComm p q =>
    constructor
    case left =>
      intro s1' htr
      exists s1'
      constructor
      · unfold lts
        cases htr with grind
      · grind [HomBisimilarity.refl, ChoiceComm]
    case right =>
      intro s1' htr
      exists s1'
      constructor
      · unfold lts
        cases htr with grind
      · grind [HomBisimilarity.refl, ChoiceComm]
  case bisim h =>
    grind [IsBisimulation, ChoiceComm]

private inductive ChoiceAssoc : Process Name Constant → Process Name Constant → Prop where
  | assoc : ChoiceAssoc (choice p (choice q r)) (choice (choice p q) r)
  | id : ChoiceAssoc p p

/-- P + (Q + R) ~ (P + Q) + R -/
theorem bisimilarity_choice_assoc :
    (choice p (choice q r)) ~[lts (defs := defs)] (choice (choice p q) r) := by
  use ChoiceAssoc, ChoiceAssoc.assoc
  intro s1 s2 hr μ
  apply And.intro <;> cases hr
  case left.assoc p q r =>
    intro s htr
    refine ⟨s, ?_, ChoiceAssoc.id⟩
    cases htr
    case choiceL htr => apply Tr.choiceL; apply Tr.choiceL; assumption
    case choiceR htr =>
      cases htr
      case choiceL htr => apply Tr.choiceL; apply Tr.choiceR; assumption
      case choiceR htr => apply Tr.choiceR; assumption
  case right.assoc p q r =>
    intro s htr
    refine ⟨s, ?_, ChoiceAssoc.id⟩
    cases htr
    case choiceL htr =>
      cases htr
      case choiceL htr => apply Tr.choiceL; assumption
      case choiceR htr => apply Tr.choiceR; apply Tr.choiceL; assumption
    case choiceR htr => apply Tr.choiceR; apply Tr.choiceR; assumption
  all_goals grind [ChoiceAssoc.id]

@[local grind]
private inductive PreBisim : Process Name Constant → Process Name Constant → Prop where
| pre : (p ~[lts (defs := defs)] q) → PreBisim (pre μ p) (pre μ q)
| bisim : (p ~[lts (defs := defs)] q) → PreBisim p q

/-- P ~ Q → μ.P ~ μ.Q -/
theorem bisimilarity_congr_pre :
    (p ~[lts (defs := defs)] q) → (pre μ p) ~[lts (defs := defs)] (pre μ q) := by
  intro hpq
  exists @PreBisim _ _ defs
  constructor
  · grind
  intro s1 s2 hr μ'
  cases hr
  case pre p' q' μ hbis =>
    unfold lts
    constructor <;> intro _ _ <;> [exists q'; exists p'] <;> grind
  case bisim => grind [IsBisimulation, IsBisimulation.le_bisimilarity]

@[local grind]
private inductive ResBisim : Process Name Constant → Process Name Constant → Prop where
| res : (p ~[lts (defs := defs)] q) → ResBisim (res a p) (res a q)
-- | bisim : (p ~[lts (defs := defs)] q) → ResBisim p q

/-- P ~ Q → (ν a) P ~ (ν a) Q -/
theorem bisimilarity_congr_res :
    (p ~[lts (defs := defs)] q) → (res a p) ~[lts (defs := defs)] (res a q) := by
  intro hpq
  refine ⟨@ResBisim Name Constant defs, .res hpq, ?_⟩
  intro s1 s2 hr μ
  cases hr with
  | res h =>
    constructor
    · intro _ htr
      cases htr with
      | res hn hn' htr =>
        obtain ⟨q', htr', h'⟩ := h.follow_fst htr
        exact ⟨_, .res hn hn' htr', .res h'⟩
    · intro _ htr
      cases htr with
      | res hn hn' htr =>
        obtain ⟨p', htr', h'⟩ := h.follow_snd htr
        exact ⟨_, .res hn hn' htr', .res h'⟩

private inductive ChoiceBisim : Process Name Constant → Process Name Constant → Prop where
| choice : (p ~[lts (defs := defs)] q) → ChoiceBisim (choice p r) (choice q r)
| bisim : (p ~[lts (defs := defs)] q) → ChoiceBisim p q

/-- P ~ Q → P + R ~ Q + R -/
theorem bisimilarity_congr_choice :
    (p ~[lts (defs := defs)] q) → (choice p r) ~[lts (defs := defs)] (choice q r) := by
  intro hpq
  refine ⟨@ChoiceBisim Name Constant defs, .choice hpq, ?_⟩
  intro s1 s2 hr μ
  cases hr with
  | choice h =>
    constructor
    · intro s htr
      cases htr with
      | choiceL htr =>
        obtain ⟨s', htr', h'⟩ := h.follow_fst htr
        exact ⟨s', .choiceL htr', .bisim h'⟩
      | choiceR htr => exact ⟨s, .choiceR htr, .bisim (.refl s)⟩
    · intro s htr
      cases htr with
      | choiceL htr =>
        obtain ⟨s', htr', h'⟩ := h.follow_snd htr
        exact ⟨s', .choiceL htr', .bisim h'⟩
      | choiceR htr => exact ⟨s, .choiceR htr, .bisim (.refl s)⟩
  | bisim h =>
    constructor
    · intro _ htr
      obtain ⟨s', htr', h'⟩ := h.follow_fst htr
      exact ⟨s', htr', .bisim h'⟩
    · intro _ htr
      obtain ⟨s', htr', h'⟩ := h.follow_snd htr
      exact ⟨s', htr', .bisim h'⟩

@[local grind]
private inductive ParBisim : Process Name Constant → Process Name Constant → Prop where
| par : (p ~[lts (defs := defs)] q) → ParBisim (par p r) (par q r)

/-- P ~ Q → P | R ~ Q | R -/
theorem bisimilarity_congr_par :
    (p ~[lts (defs := defs)] q) → (par p r) ~[lts (defs := defs)] (par q r) := by
  intro hpq
  refine ⟨@ParBisim Name Constant defs, .par hpq, ?_⟩
  intro s1 s2 hr μ
  cases hr with
  | par h =>
    constructor
    · intro _ htr
      cases htr with
      | parL htr =>
        obtain ⟨q', htr', h'⟩ := h.follow_fst htr
        exact ⟨_, .parL htr', .par h'⟩
      | parR htr => exact ⟨_, .parR htr, .par h⟩
      | com hco htrp htrr =>
        obtain ⟨q', htr', h'⟩ := h.follow_fst htrp
        exact ⟨_, .com hco htr' htrr, .par h'⟩
    · intro _ htr
      cases htr with
      | parL htr =>
        obtain ⟨p', htr', h'⟩ := h.follow_snd htr
        exact ⟨_, .parL htr', .par h'⟩
      | parR htr => exact ⟨_, .parR htr, .par h⟩
      | com hco htrq htrr =>
        obtain ⟨p', htr', h'⟩ := h.follow_snd htrq
        exact ⟨_, .com hco htr' htrr, .par h'⟩

/-- Bisimilarity is a congruence in CCS. -/
theorem bisimilarity_is_congruence
    (p q : Process Name Constant) (c : Context Name Constant) (h : p ~[lts (defs := defs)] q) :
    (c.fill p) ~[lts (defs := defs)] (c.fill q) := by
  induction c with
  | parR r c _ =>
    calc
      _ ~[lts (defs := defs)] (c.fill p |>.par r)  := by grind
      _ ~[lts (defs := defs)] (c.fill q |>.par r)  := by grind [bisimilarity_congr_par]
      _ ~[lts (defs := defs)] (c.parR r |>.fill q) := by grind
  | choiceR r c _ =>
    calc
      _ ~[lts (defs := defs)] (c.fill p |>.choice r)  := by grind [bisimilarity_choice_comm]
      _ ~[lts (defs := defs)] (c.fill q |>.choice r)  := by grind [bisimilarity_congr_choice]
      _ ~[lts (defs := defs)] (c.choiceR r |>.fill q) := by grind [bisimilarity_choice_comm]
  | _ => grind [bisimilarity_congr_pre, bisimilarity_congr_par,
                bisimilarity_congr_choice, bisimilarity_congr_res]

instance : Congruence (HomBisimilarity (lts (defs := defs))) := ⟨⟩

/-- Bisimilarity is a congruence in CCS. -/
instance bisimilarityCongruence : LawfulCongruence (HomBisimilarity (lts (defs := defs))) where
  elim := by grind [Covariant, bisimilarity_is_congruence]

end CCS

end CCS.BehaviouralTheory

end Cslib
