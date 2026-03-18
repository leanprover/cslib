/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Cslib.Foundations.Semantics.LTS.Bisimulation
public import Cslib.Foundations.Syntax.Congruence
public import Cslib.Languages.CCS.Semantics

@[expose] public section

/-! # Behavioural theory of CCS

## Main results

- `CCS.bisimilarityCongruence`: bisimilarity is a congruence in CCS.

Additionally, some standard laws of bisimilarity for CCS, including:
- `CCS.bisimilarity_par_nil`: P | 𝟎 ~ P.
- `CCS.bisimilarity_par_comm`: P | Q ~ Q | P
- `CCS.bisimilarity_choice_comm`: P + Q ~ Q + P
-/

namespace Cslib

section CCS.BehaviouralTheory

variable {Name : Type u} {Constant : Type v} {defs : Constant → CCS.Process Name Constant → Prop}

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

open Bisimilarity LTS in
/-- P + Q ~ Q + P -/
theorem bisimilarity_choice_comm : (choice p q) ~[lts (defs := defs)] (choice q p) := by
  exists @ChoiceComm Name Constant defs
  repeat constructor
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
      · grind [ChoiceComm]
    case right =>
      intro s1' htr
      exists s1'
      constructor
      · unfold lts
        cases htr with grind
      · grind [ChoiceComm]
  case bisim h =>
    grind [ChoiceComm]

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

open scoped LTS in
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
  case bisim => grind [Bisimilarity.largest_bisimulation]

@[local grind]
private inductive ResBisim : Process Name Constant → Process Name Constant → Prop where
| res : (p ~[lts (defs := defs)] q) → ResBisim (res a p) (res a q)
-- | bisim : (p ~[lts (defs := defs)] q) → ResBisim p q

/-- P ~ Q → (ν a) P ~ (ν a) Q -/
theorem bisimilarity_congr_res :
    (p ~[lts (defs := defs)] q) → (res a p) ~[lts (defs := defs)] (res a q) := by
  intro hpq
  exists @ResBisim _ _ defs
  constructor
  · grind
  intro s1 s2 hr μ'
  cases hr
  rename_i p q a h
  constructor
  case left =>
    intro s1' htr
    cases htr with | res _ _ htr =>
    obtain ⟨q', _⟩ := Bisimilarity.is_bisimulation.follow_fst h htr
    exists res a q'
    unfold lts at *
    grind
  case right =>
    intro s2' htr
    cases htr with | res _ _ htr =>
    obtain ⟨p', _⟩ := Bisimilarity.is_bisimulation.follow_snd h htr
    exists res a p'
    unfold lts at *
    grind

private inductive ChoiceBisim : Process Name Constant → Process Name Constant → Prop where
| choice : (p ~[lts (defs := defs)] q) → ChoiceBisim (choice p r) (choice q r)
| bisim : (p ~[lts (defs := defs)] q) → ChoiceBisim p q

/-- P ~ Q → P + R ~ Q + R -/
theorem bisimilarity_congr_choice :
    (p ~[lts (defs := defs)] q) → (choice p r) ~[lts (defs := defs)] (choice q r) := by
  intro h
  exists @ChoiceBisim _ _ defs
  constructor
  · constructor; assumption
  intro s1 s2 r μ
  constructor
  case left =>
    intro s1' htr
    cases r
    case choice p q r hbisim =>
      obtain ⟨rel, hr, hb⟩ := hbisim
      cases htr
      case choiceL a b c htr =>
        obtain ⟨s2', htr2, hr2⟩ := hb.follow_fst hr htr
        exists s2'
        constructor
        · apply Tr.choiceL htr2
        · constructor
          apply Bisimilarity.largest_bisimulation hb hr2
      case choiceR a b c htr =>
        exists s1'
        constructor
        · apply Tr.choiceR htr
        · constructor
          apply Bisimilarity.refl
    case bisim hbisim =>
      obtain ⟨rel, hr, hb⟩ := hbisim
      obtain ⟨s2', htr2, hr2⟩ := hb.follow_fst hr htr
      exists s2'
      constructor
      · assumption
      constructor
      apply Bisimilarity.largest_bisimulation hb hr2
  case right =>
    intro s2' htr
    cases r
    case choice p q r hbisim =>
      obtain ⟨rel, hr, hb⟩ := hbisim
      cases htr
      case choiceL a b c htr =>
        obtain ⟨s1', htr1, hr1⟩ := hb.follow_snd hr htr
        exists s1'
        constructor
        · apply Tr.choiceL htr1
        · constructor
          apply Bisimilarity.largest_bisimulation hb hr1
      case choiceR a b c htr =>
        exists s2'
        constructor
        · apply Tr.choiceR htr
        · constructor
          apply Bisimilarity.refl
    case bisim hbisim =>
      obtain ⟨rel, hr, hb⟩ := hbisim
      obtain ⟨s1', htr1, hr1⟩ := hb.follow_snd hr htr
      exists s1'
      constructor
      · assumption
      · constructor
        apply Bisimilarity.largest_bisimulation hb hr1

@[local grind]
private inductive ParBisim : Process Name Constant → Process Name Constant → Prop where
| par : (p ~[lts (defs := defs)] q) → ParBisim (par p r) (par q r)

/-- P ~ Q → P | R ~ Q | R -/
theorem bisimilarity_congr_par :
    (p ~[lts (defs := defs)] q) → (par p r) ~[lts (defs := defs)] (par q r) := by
  intro h
  exists @ParBisim _ _ defs
  constructor
  · grind
  intro s1 s2 r μ
  constructor
  case left =>
    intro s1' htr
    cases r
    unfold lts at *
    have : {Tr :=  Tr (defs := defs)} = lts (defs := defs) := by rfl
    case par p q r hbisim =>
      obtain ⟨rel, hr, hb⟩ := hbisim
      cases htr
      case parL p' htr =>
        obtain ⟨q', _⟩ := hb.follow_fst hr htr
        exists par q' r
        grind
      case parR r' htr =>
        exists par q r'
        grind
      case com r' _ htrp _ =>
        obtain ⟨q', _⟩ := hb.follow_fst hr htrp
        exists par q' r'
        grind
  case right =>
    intro s2' htr
    cases r
    unfold lts at *
    have : {Tr :=  Tr (defs := defs)} = lts (defs := defs) := by rfl
    case par p _ r hbisim =>
      obtain ⟨_, hr, hb⟩ := hbisim
      cases htr
      case parL htr =>
        obtain ⟨p', _⟩ := hb.follow_snd hr htr
        exists par p' r
        grind
      case parR _ _ r' htr =>
        exists par p r'
        grind
      case com r' hco htrq htrr =>
        obtain ⟨q', _⟩ := hb.follow_snd hr htrq
        exists par q' r'
        grind

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

/-- Bisimilarity is a congruence in CCS. -/
instance bisimilarityCongruence :
    Congruence (Process Name Constant) (Bisimilarity (lts (defs := defs))) where
  covariant := ⟨by grind [Covariant, bisimilarity_is_congruence]⟩

end CCS

end CCS.BehaviouralTheory

end Cslib
