/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Foundations.Semantics.Lts.Basic
import Cslib.Foundations.Semantics.Lts.Bisimulation
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
    simp only [Lts.IsBisimulation]
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
        case com p q p' q' μ htrp htrq =>
          exists (par q' p')
          constructor
          · rw [← Act.co.involution Name μ] at htrp
            apply Tr.com htrq htrp
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
        case com p q p' q' μ htrp htrq =>
          exists (par q' p')
          constructor
          · rw [← Act.co.involution Name μ] at htrp
            apply Tr.com htrq htrp
          · constructor

/-- 𝟎 | P ~ P -/
@[simp, scoped grind]
theorem bisimilarity_nil_par : (par nil p) ~[lts (defs := defs)] p :=
  calc
    (par nil p) ~[lts (defs := defs)] (par p nil) := by grind
    _ ~[lts (defs := defs)] p := by simp

/-- P | (Q | R) ~ (P | Q) | R -/
proof_wanted bisimilarity_par_assoc :
  (par p (par q r)) ~[lts (defs := defs)] (par (par p q) r)

/-- P + 𝟎 ~ P -/
proof_wanted bisimilarity_choice_nil :
  (choice p nil) ~[lts (defs := defs)] p

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
  simp only [Lts.IsBisimulation]
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

/-- P + (Q + R) ~ (P + Q) + R -/
proof_wanted bisimilarity_choice_assoc :
  (choice p (choice q r)) ~[lts (defs := defs)] (choice (choice p q) r)

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
  simp only [Lts.IsBisimulation]
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
  simp only [Lts.IsBisimulation]
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
  simp only [Lts.IsBisimulation]
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
  simp only [Lts.IsBisimulation]
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
      case com _ _ p' r' μ' htrp htrr =>
        obtain ⟨q', htr2, hr2⟩ := hb.follow_fst hr htrp
        exists (par q' r')
        constructor
        · apply Tr.com htr2 htrr
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
      case com _ _ p' r' μ' htrq htrr =>
        obtain ⟨q', htr2, hr2⟩ := hb.follow_snd hr htrq
        exists (par q' r')
        constructor
        · apply Tr.com htr2 htrr
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
