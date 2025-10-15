/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.LTS.Basic
import Cslib.Foundations.Semantics.LTS.Bisimulation
import Cslib.Languages.CCS.Basic
import Cslib.Languages.CCS.Semantics

/-! # Behavioural theory of CCS

## Main results

- `CCS.bisimilarity_congr`: bisimilarity is a congruence in CCS

Additionally, some standard laws of bisimilarity for CCS, including:
- `CCS.bisimilarity_par_nil`: P | 𝟎 ~ P.
- `CCS.bisimilarity_par_comm`: P | Q ~ Q | P
- `CCS.bisimilarity_choice_comm`: P + Q ~ Q + P
-/

namespace Cslib

section CCS.BehaviouralTheory

variable {Name : Type u} {Constant : Type v} {defs : Constant → (CCS.Process Name Constant) → Prop}

open CCS CCS.Process CCS.Act

namespace CCS

@[grind cases]
private inductive ParNil : (Process Name Constant) → (Process Name Constant) → Prop where
| parNil : ParNil (par p nil) p

attribute [grind] ParNil.parNil

/-- P | 𝟎 ~ P -/
@[simp, scoped grind]
theorem bisimilarity_par_nil : (par p nil) ~[lts (defs := defs)] p := by
  unfold lts at *
  exists ParNil
  constructor; constructor
  intro s1 s2 hr μ
  constructor
  case left =>
    grind [cases Tr]
  case right =>
    intro s2' htr
    exists (par s2' nil)
    grind [Tr.parL]

private inductive ParComm : (Process Name Constant) → (Process Name Constant) → Prop where
| parComm : ParComm (par p q) (par q p)

/-- P | Q ~ Q | P -/
@[scoped grind]
theorem bisimilarity_par_comm : (par p q) ~[lts (defs := defs)] (par q p) := by
  exists ParComm
  constructor
  case left =>
    constructor
  case right =>
    simp only [LTS.IsBisimulation]
    intro s1 s2 hr μ
    cases hr
    case parComm p q =>
      constructor
      case left =>
        intro t htr
        cases htr
        case parL p' htr' =>
          exists (par q p')
          constructor
          · apply Tr.parR htr'
          · constructor
        case parR q' htr' =>
          exists (par q' p)
          constructor
          · apply Tr.parL htr'
          · constructor
        case com μ p' μ' q' hco htrp htrq =>
          exists (par q' p')
          constructor
          · apply Tr.com hco.symm htrq htrp
          · constructor
      case right =>
        intro t htr
        cases htr
        case parL q' htr' =>
          exists (par p q')
          constructor
          · apply Tr.parR htr'
          · constructor
        case parR p' htr' =>
          exists (par p' q)
          constructor
          · apply Tr.parL htr'
          · constructor
        case com μ p' μ' q' hco htrp htrq =>
          exists (par q' p')
          constructor
          · apply Tr.com hco.symm htrq htrp
          · constructor

/-- 𝟎 | P ~ P -/
@[simp, scoped grind]
theorem bisimilarity_nil_par : (par nil p) ~[lts (defs := defs)] p :=
  calc
    (par nil p) ~[lts (defs := defs)] (par p nil) := by grind
    _ ~[lts (defs := defs)] p := by simp


private inductive ParAssoc : (Process Name Constant) → (Process Name Constant) → Prop where
  | assoc : ParAssoc (par p (par q r)) (par (par p q) r)
  | id : ParAssoc p p

/-- P | (Q | R) ~ (P | Q) | R -/
theorem bisimilarity_par_assoc :
  (par p (par q r)) ~[lts (defs := defs)] (par (par p q) r) := by
  refine ⟨ParAssoc, ParAssoc.assoc, ?_⟩
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
        grind [Tr.parL, ParAssoc]
      case parR p q r q' _ =>
        exists p.par (q'.par r)
        grind [Tr.parL, Tr.parR, ParAssoc]
      case com μ p' μ' q' _ htrp htrq =>
        exists p'.par (q'.par r)
        have htrq' : Tr (defs := defs) (q.par r) μ' (q'.par r) := by apply Tr.parL; assumption
        grind [Tr.com, Tr.parL, ParAssoc]
    case parR p q r r' htr =>
      exists p.par (q.par r')
      grind [Tr.parR, ParAssoc]
    case com p q r μ p' μ' r' _ htr htr' =>
      cases htr
      case parL p' _ =>
        refine ⟨ p'.par (q.par r'), ?_, ParAssoc.assoc⟩
        apply Tr.com (μ := μ) (μ' := μ') <;> grind [Tr.parR]
      case parR q' _ =>
        use p.par (q'.par r')
        grind [Tr.parR, Tr.com, ParAssoc.assoc]
      case com μ p' q' _ _ =>
        unfold Act.Co at *
        grind
  case left.assoc =>
    intro s2' htr
    unfold lts at *
    cases htr
    case parR htr =>
      cases htr
      case parL p q r q' _ =>
        exists (p.par q').par r
        grind [Tr.parL, Tr.parR, ParAssoc]
      case parR p q r r' _ =>
        exists (p.par q).par r'
        grind [Tr.parL, Tr.parR, ParAssoc]
      case com p q r μ q' μ' r' _ htrp htrq =>
        refine ⟨(p.par q').par r', ?_, ParAssoc.assoc⟩
        apply Tr.com (μ := μ) (μ' := μ') <;> grind [Tr.parR]
    case parL p q r p' htr =>
      exists (p'.par q).par r
      grind [Tr.parL, ParAssoc]
    case com p q r μ p' μ' q' _ htr htr' =>
      cases htr'
      case parL q' _ =>
        use (p'.par q').par r
        grind [Tr.parL, Tr.com, ParAssoc.assoc]
      case parR r' _ =>
        refine ⟨ (p'.par q).par r', ?_, ParAssoc.assoc⟩
        apply Tr.com (μ := μ) (μ' := μ') <;> grind [Tr.parL]
      case com =>
        unfold Act.Co at *
        grind
  all_goals grind [ParAssoc]

private inductive ChoiceNil : (Process Name Constant) → (Process Name Constant) → Prop where
  | nil : ChoiceNil (choice p nil) p
  | id : ChoiceNil p p

/-- P + 𝟎 ~ P -/
theorem bisimilarity_choice_nil : (choice p nil) ~[lts (defs := defs)] p := by
  refine ⟨ChoiceNil, ChoiceNil.nil, ?_⟩
  intro s1 s2 hr μ
  apply And.intro <;> cases hr
  case left.nil =>
    unfold lts
    grind [cases Tr, ChoiceNil]
  case right.nil =>
    intro s2' htr
    exists s2'
    constructor
    · apply Tr.choiceL
      assumption
    · exact ChoiceNil.id
  all_goals grind [ChoiceNil]

private inductive ChoiceIdem : (Process Name Constant) → (Process Name Constant) → Prop where
  | idem : ChoiceIdem (choice p p) p
  | id : ChoiceIdem p p

/-- P + P ~ P -/
theorem bisimilarity_choice_idem :
  (choice p p) ~[lts (defs := defs)] p := by
  exists ChoiceIdem
  apply And.intro
  case left => grind [ChoiceIdem]
  case right =>
    intro s1 s2 hr μ
    apply And.intro <;> cases hr
    case left.idem =>
      unfold lts
      grind [cases Tr, ChoiceIdem]
    case left.id =>
      grind [ChoiceIdem]
    case right.idem =>
      intro s1' htr
      exists s1'
      unfold lts at *
      grind [Tr, ChoiceIdem]
    case right.id =>
      grind [ChoiceIdem]

private inductive ChoiceComm : (Process Name Constant) → (Process Name Constant) → Prop where
  | choiceComm : ChoiceComm (choice p q) (choice q p)
  | bisim : (p ~[lts (defs := defs)] q) → ChoiceComm p q

/-- P + Q ~ Q + P -/
theorem bisimilarity_choice_comm : (choice p q) ~[lts (defs := defs)] (choice q p) := by
  exists @ChoiceComm Name Constant defs
  repeat constructor
  simp only [LTS.IsBisimulation]
  intro s1 s2 hr μ
  cases hr
  case choiceComm =>
    rename_i p q
    constructor
    case left =>
      intro s1' htr
      exists s1'
      constructor
      · unfold lts
        cases htr with grind [Tr.choiceR, Tr.choiceL]
      · constructor
        grind
    case right =>
      intro s1' htr
      exists s1'
      constructor
      · unfold lts
        cases htr with grind [Tr.choiceR, Tr.choiceL]
      · grind [ChoiceComm]
  case bisim h =>
    grind [ChoiceComm]

private inductive ChoiceAssoc : (Process Name Constant) → (Process Name Constant) → Prop where
  | assoc : ChoiceAssoc (choice p (choice q r)) (choice (choice p q) r)
  | id : ChoiceAssoc p p

/-- P + (Q + R) ~ (P + Q) + R -/
theorem bisimilarity_choice_assoc :
    (choice p (choice q r)) ~[lts (defs := defs)] (choice (choice p q) r) := by
  refine ⟨ChoiceAssoc, ChoiceAssoc.assoc, ?_⟩
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

private inductive PreBisim : (Process Name Constant) → (Process Name Constant) → Prop where
| pre : (p ~[lts (defs := defs)] q) → PreBisim (pre μ p) (pre μ q)
| bisim : (p ~[lts (defs := defs)] q) → PreBisim p q

/-- P ~ Q → μ.P ~ μ.Q -/
theorem bisimilarity_congr_pre :
  (p ~[lts (defs := defs)] q) → (pre μ p) ~[lts (defs := defs)] (pre μ q) := by
  intro hpq
  exists @PreBisim _ _ defs
  constructor
  · constructor; assumption
  simp only [LTS.IsBisimulation]
  intro s1 s2 hr μ'
  cases hr
  case pre =>
    rename_i p' q' μ hbis
    constructor
    case left =>
      intro s1' htr
      cases htr
      exists q'
      constructor; constructor
      apply PreBisim.bisim hbis
    case right =>
      intro s2' htr
      cases htr
      exists p'
      constructor; constructor
      apply PreBisim.bisim hbis
  case bisim hbis =>
    constructor
    case left =>
      intro s1' htr
      obtain ⟨r, hr, hb⟩ := hbis
      let hbisim := hb
      obtain ⟨s2', htr2, hr2⟩ := hb.follow_fst hr htr
      exists s2'
      apply And.intro htr2
      constructor
      apply Bisimilarity.largest_bisimulation hbisim hr2
    case right =>
      intro s2' htr
      obtain ⟨r, hr, hb⟩ := hbis
      let hbisim := hb
      specialize hb hr μ'
      obtain ⟨hb1, hb2⟩ := hb
      specialize hb2 _ htr
      obtain ⟨s1', htr1, hr1⟩ := hb2
      exists s1'
      apply And.intro htr1
      constructor
      apply Bisimilarity.largest_bisimulation hbisim hr1

private inductive ResBisim : (Process Name Constant) → (Process Name Constant) → Prop where
| res : (p ~[lts (defs := defs)] q) → ResBisim (res a p) (res a q)
-- | bisim : (p ~[lts (defs := defs)] q) → ResBisim p q

/-- P ~ Q → (ν a) P ~ (ν a) Q -/
theorem bisimilarity_congr_res :
  (p ~[lts (defs := defs)] q) → (res a p) ~[lts (defs := defs)] (res a q) := by
  intro hpq
  exists @ResBisim _ _ defs
  constructor
  · constructor; assumption
  simp only [LTS.IsBisimulation]
  intro s1 s2 hr μ'
  cases hr
  rename_i p q a h
  constructor
  case left =>
    intro s1' htr
    cases htr
    rename_i p' h1 h2 htr
    have h := Bisimilarity.is_bisimulation.follow_fst h htr
    obtain ⟨q', htrq, h⟩ := h
    exists (res a q')
    constructor; constructor; repeat assumption
    constructor; assumption
  case right =>
    intro s2' htr
    cases htr
    rename_i q' h1 h2 htr
    have h := Bisimilarity.is_bisimulation.follow_snd h htr
    obtain ⟨p', htrq, h⟩ := h
    exists (res a p')
    constructor; constructor; repeat assumption
    constructor; assumption

private inductive ChoiceBisim : (Process Name Constant) → (Process Name Constant) → Prop where
| choice : (p ~[lts (defs := defs)] q) → ChoiceBisim (choice p r) (choice q r)
| bisim : (p ~[lts (defs := defs)] q) → ChoiceBisim p q

/-- P ~ Q → P + R ~ Q + R -/
theorem bisimilarity_congr_choice :
  (p ~[lts (defs := defs)] q) → (choice p r) ~[lts (defs := defs)] (choice q r) := by
  intro h
  exists @ChoiceBisim _ _ defs
  constructor
  · constructor; assumption
  simp only [LTS.IsBisimulation]
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

private inductive ParBisim : (Process Name Constant) → (Process Name Constant) → Prop where
| par : (p ~[lts (defs := defs)] q) → ParBisim (par p r) (par q r)

/-- P ~ Q → P | R ~ Q | R -/
theorem bisimilarity_congr_par :
  (p ~[lts (defs := defs)] q) → (par p r) ~[lts (defs := defs)] (par q r) := by
  intro h
  exists @ParBisim _ _ defs
  constructor
  · constructor; assumption
  simp only [LTS.IsBisimulation]
  intro s1 s2 r μ
  constructor
  case left =>
    intro s1' htr
    cases r
    case par p q r hbisim =>
      obtain ⟨rel, hr, hb⟩ := hbisim
      cases htr
      case parL _ _ p' htr =>
        obtain ⟨q', htr2, hr2⟩ := hb.follow_fst hr htr
        exists (par q' r)
        constructor
        · apply Tr.parL htr2
        · constructor
          apply Bisimilarity.largest_bisimulation hb hr2
      case parR _ _ r' htr =>
        exists (par q r')
        constructor
        · apply Tr.parR htr
        · constructor
          apply Bisimilarity.largest_bisimulation hb hr
      case com _ p' _ r' hco htrp htrr =>
        obtain ⟨q', htr2, hr2⟩ := hb.follow_fst hr htrp
        exists (par q' r')
        constructor
        · apply Tr.com hco htr2 htrr
        · constructor
          apply Bisimilarity.largest_bisimulation hb hr2
  case right =>
    intro s2' htr
    cases r
    case par p q r hbisim =>
      obtain ⟨rel, hr, hb⟩ := hbisim
      cases htr
      case parL _ _ p' htr =>
        obtain ⟨p', htr2, hr2⟩ := hb.follow_snd hr htr
        exists (par p' r)
        constructor
        · apply Tr.parL htr2
        · constructor
          apply Bisimilarity.largest_bisimulation hb hr2
      case parR _ _ r' htr =>
        exists (par p r')
        constructor
        · apply Tr.parR htr
        · constructor
          apply Bisimilarity.largest_bisimulation hb hr
      case com _ p' _ r' hco htrq htrr =>
        obtain ⟨q', htr2, hr2⟩ := hb.follow_snd hr htrq
        exists (par q' r')
        constructor
        · apply Tr.com hco htr2 htrr
        · constructor
          apply Bisimilarity.largest_bisimulation hb hr2

/-- Bisimilarity is a congruence in CCS. -/
theorem bisimilarity_congr
  (c : Context Name Constant) (p q : Process Name Constant) (h : p ~[lts (defs := defs)] q) :
  (c.fill p) ~[lts (defs := defs)] (c.fill q) := by
  induction c
  case hole => exact h
  case pre _ _  ih => exact bisimilarity_congr_pre ih
  case parL _ _ ih => exact bisimilarity_congr_par ih
  case parR r c ih =>
    apply Bisimilarity.trans
    · apply bisimilarity_par_comm
    · apply Bisimilarity.trans
      · apply bisimilarity_congr_par
        exact ih
      · apply bisimilarity_par_comm
  case choiceL _ _ ih => exact bisimilarity_congr_choice ih
  case choiceR r c ih =>
    apply Bisimilarity.trans
    · apply bisimilarity_choice_comm
    · apply Bisimilarity.trans
      · exact bisimilarity_congr_choice ih
      · exact bisimilarity_choice_comm
  case res =>
    apply bisimilarity_congr_res
    assumption

end CCS

end CCS.BehaviouralTheory

end Cslib
