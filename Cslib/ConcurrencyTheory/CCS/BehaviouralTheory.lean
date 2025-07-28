/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

import Cslib.Semantics.Lts.Basic
import Cslib.Semantics.Lts.Bisimulation
import Cslib.ConcurrencyTheory.CCS.Basic
import Cslib.ConcurrencyTheory.CCS.Semantics

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

private inductive ParNil : (Process Name Constant) → (Process Name Constant) → Prop where
| parNil : ParNil (par p nil) p

/-- P | 𝟎 ~ P -/
theorem bisimilarity_par_nil : (par p nil) ~[@lts Name Constant defs] p := by
  exists ParNil
  constructor; constructor
  simp only [Bisimulation]
  intro s1 s2 hr μ
  constructor
  case left =>
    intro s1' htr
    cases hr
    cases htr
    case parL p' htr =>
      exists p'
      apply And.intro htr ParNil.parNil
    case parR q' htr =>
      cases htr
    case com μ p' q' htrp htrq =>
      cases htrq
  case right =>
    intro s2' htr
    cases hr
    exists (par s2' nil)
    constructor
    case left =>
      apply Tr.parL htr
    case right =>
      constructor

private inductive ParComm : (Process Name Constant) → (Process Name Constant) → Prop where
| parComm : ParComm (par p q) (par q p)

/-- P | Q ~ Q | P -/
theorem bisimilarity_par_comm : (par p q) ~[@lts Name Constant defs] (par q p) := by
  exists ParComm
  constructor
  case left =>
    constructor
  case right =>
    simp only [Bisimulation]
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
        case com μ p' q' htrp htrq =>
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
        case com μ p' q' htrp htrq =>
          exists (par q' p')
          constructor
          · rw [← Act.co.involution Name μ] at htrp
            apply Tr.com htrq htrp
          · constructor

private inductive ParAssoc : (Process Name Constant) → (Process Name Constant) → Prop where
| parAssoc : ParAssoc (par p (par q r)) (par (par p q) r)

attribute [local grind] CCS.Tr
attribute [local grind cases] ParAssoc
attribute [local grind] ParAssoc
attribute [local grind <=] CCS.Tr.parL CCS.Tr.parR CCS.Tr.com

/-- P | (Q | R) ~ (P | Q) | R -/
theorem bisimilarity_par_assoc :
  (par p (par q r)) ~[@lts Name Constant defs] (par (par p q) r) := by
  exists ParAssoc
  constructor
  case left =>
    constructor
  case right =>
    intro s1 s2 hr μ
    cases hr
    case parAssoc p q r =>
      constructor
      case left =>
        intro s1' htr
        cases htr
        case parL p q p' htr' =>
          exists (par (par p' q) r)
          -- grind
          -- aesop
          --   (add safe constructors Tr) (add safe apply Tr.parL) (add safe constructors ParAssoc)
          constructor
          case left =>
            aesop (add unsafe constructors Tr)

            -- repeat apply Tr.parL
            -- assumption
          -- case right =>
          --   constructor
        case parR p q qr' htr' =>
          cases htr'





private inductive ChoiceComm : (Process Name Constant) → (Process Name Constant) → Prop where
| choiceComm : ChoiceComm (choice p q) (choice q p)
| bisim : (p ~[@lts Name Constant defs] q) → ChoiceComm p q

/-- P + Q ~ Q + P -/
theorem bisimilarity_choice_comm : (choice p q) ~[@lts Name Constant defs] (choice q p) := by
  exists @ChoiceComm Name Constant defs
  repeat constructor
  simp only [Bisimulation]
  intro s1 s2 hr μ
  cases hr
  rename_i p q
  constructor
  case left =>
    intro s1' htr
    exists s1'
    constructor
    · cases htr
      · apply Tr.choiceR
        assumption
      · apply Tr.choiceL
        assumption
    · constructor
      apply Bisimilarity.refl (@lts _ _ defs) s1'
  case right =>
    intro s1' htr
    exists s1'
    constructor
    · cases htr
      · apply Tr.choiceR
        assumption
      · apply Tr.choiceL
        assumption
    · constructor
      apply Bisimilarity.refl (@lts _ _ defs) s1'
  case bisim h =>
    constructor
    case left =>
      intro s1' htr
      have hb := Bisimulation.follow_fst (Bisimilarity.is_bisimulation lts) h htr
      obtain ⟨s2', htr2, hr2⟩ := hb
      exists s2'
      apply And.intro htr2
      constructor; assumption
    case right =>
      intro s2' htr
      have hb := Bisimulation.follow_snd (Bisimilarity.is_bisimulation lts) h htr
      obtain ⟨s1', htr1, hr1⟩ := hb
      exists s1'
      apply And.intro htr1
      constructor; assumption

private inductive PreBisim : (Process Name Constant) → (Process Name Constant) → Prop where
| pre : (p ~[@lts Name Constant defs] q) → PreBisim (pre μ p) (pre μ q)
| bisim : (p ~[@lts Name Constant defs] q) → PreBisim p q

/-- P ~ Q → μ.P ~ μ.Q -/
theorem bisimilarity_congr_pre :
  (p ~[@lts Name Constant defs] q) → (pre μ p) ~[@lts Name Constant defs] (pre μ q) := by
  intro hpq
  exists @PreBisim _ _ defs
  constructor; constructor; assumption
  simp only [Bisimulation]
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
      apply Bisimilarity.largest_bisimulation _ hbisim hr2
    case right =>
      intro s2' htr
      obtain ⟨r, hr, hb⟩ := hbis
      let hbisim := hb
      specialize hb _ _ hr μ'
      obtain ⟨hb1, hb2⟩ := hb
      specialize hb2 _ htr
      obtain ⟨s1', htr1, hr1⟩ := hb2
      exists s1'
      apply And.intro htr1
      constructor
      apply Bisimilarity.largest_bisimulation _ hbisim hr1

private inductive ResBisim : (Process Name Constant) → (Process Name Constant) → Prop where
| res : (p ~[@lts Name Constant defs] q) → ResBisim (res a p) (res a q)
-- | bisim : (p ~[@lts Name Constant defs] q) → ResBisim p q

/-- P ~ Q → (ν a) P ~ (ν a) Q -/
theorem bisimilarity_congr_res :
  (p ~[@lts Name Constant defs] q) → (res a p) ~[@lts Name Constant defs] (res a q) := by
  intro hpq
  exists @ResBisim _ _ defs
  constructor; constructor; assumption
  simp only [Bisimulation]
  intro s1 s2 hr μ'
  cases hr
  rename_i p q a h
  constructor
  case left =>
    intro s1' htr
    cases htr
    rename_i p' h1 h2 htr
    have h := Bisimulation.follow_fst (Bisimilarity.is_bisimulation lts) h htr
    obtain ⟨q', htrq, h⟩ := h
    exists (res a q')
    constructor; constructor; repeat assumption
    constructor; assumption
  case right =>
    intro s2' htr
    cases htr
    rename_i q' h1 h2 htr
    have h := Bisimulation.follow_snd (Bisimilarity.is_bisimulation lts) h htr
    obtain ⟨p', htrq, h⟩ := h
    exists (res a p')
    constructor; constructor; repeat assumption
    constructor; assumption

private inductive ChoiceBisim : (Process Name Constant) → (Process Name Constant) → Prop where
| choice : (p ~[@lts Name Constant defs] q) → ChoiceBisim (choice p r) (choice q r)
| bisim : (p ~[@lts Name Constant defs] q) → ChoiceBisim p q

/-- P ~ Q → P + R ~ Q + R -/
theorem bisimilarity_congr_choice :
  (p ~[@lts Name Constant defs] q) → (choice p r) ~[@lts Name Constant defs] (choice q r) := by
  intro h
  exists @ChoiceBisim _ _ defs
  constructor; constructor; assumption
  simp only [Bisimulation]
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
          apply Bisimilarity.largest_bisimulation _ hb hr2
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
      constructor; assumption
      constructor
      apply Bisimilarity.largest_bisimulation _ hb hr2
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
          apply Bisimilarity.largest_bisimulation _ hb hr1
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
        apply Bisimilarity.largest_bisimulation _ hb hr1

private inductive ParBisim : (Process Name Constant) → (Process Name Constant) → Prop where
| par : (p ~[@lts Name Constant defs] q) → ParBisim (par p r) (par q r)

/-- P ~ Q → P | R ~ Q | R -/
theorem bisimilarity_congr_par :
  (p ~[@lts Name Constant defs] q) → (par p r) ~[@lts Name Constant defs] (par q r) := by
  intro h
  exists @ParBisim _ _ defs
  constructor; constructor; assumption
  simp only [Bisimulation]
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
          apply Bisimilarity.largest_bisimulation _ hb hr2
      case parR _ _ r' htr =>
        exists (par q r')
        constructor
        · apply Tr.parR htr
        · constructor
          apply Bisimilarity.largest_bisimulation _ hb hr
      case com μ' p' r' htrp htrr =>
        obtain ⟨q', htr2, hr2⟩ := hb.follow_fst hr htrp
        exists (par q' r')
        constructor
        · apply Tr.com htr2 htrr
        · constructor
          apply Bisimilarity.largest_bisimulation _ hb hr2
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
          apply Bisimilarity.largest_bisimulation _ hb hr2
      case parR _ _ r' htr =>
        exists (par p r')
        constructor
        · apply Tr.parR htr
        · constructor
          apply Bisimilarity.largest_bisimulation _ hb hr
      case com μ' p' r' htrq htrr =>
        obtain ⟨q', htr2, hr2⟩ := hb.follow_snd hr htrq
        exists (par q' r')
        constructor
        · apply Tr.com htr2 htrr
        · constructor
          apply Bisimilarity.largest_bisimulation _ hb hr2

/-- Bisimilarity is a congruence in CCS. -/
theorem bisimilarity_congr
  (c : Context Name Constant) (p q : Process Name Constant) (h : p ~[@lts Name Constant defs] q) :
  (c.fill p) ~[@lts Name Constant defs] (c.fill q) := by
  induction c
  case hole =>
    simp only [Context.fill]
    exact h
  case pre μ c ih =>
    simp [Context.fill]
    apply bisimilarity_congr_pre ih
  case parL c r ih =>
    simp [Context.fill]
    apply bisimilarity_congr_par ih
  case parR r c ih =>
    apply Bisimilarity.trans
    · apply bisimilarity_par_comm
    · apply Bisimilarity.trans
      · apply bisimilarity_congr_par
        exact ih
      · apply bisimilarity_par_comm
  case choiceL c r ih =>
    simp [Context.fill]
    apply bisimilarity_congr_choice
    exact ih
  case choiceR r c ih =>
    simp [Context.fill]
    apply Bisimilarity.trans
    · apply bisimilarity_choice_comm
    · apply Bisimilarity.trans
      · apply bisimilarity_congr_choice
        exact ih
      · apply bisimilarity_choice_comm
  case res =>
    simp [Context.fill]
    apply bisimilarity_congr_res
    assumption

end CCS

end CCS.BehaviouralTheory
