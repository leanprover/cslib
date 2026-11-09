/-
Copyright (c) 2026 Thomas Waring. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Waring
-/

module

public import Cslib.Foundations.Logic.InferenceSystem
public import Cslib.Foundations.Logic.Operators

/-! # Combinators on derivations -/

@[expose] public section

namespace Cslib.Logic.InferenceSystem

variable (S α : Type*) [InferenceSystem S α]

/-! ### Operator elimination rules -/

class HasMP [HasImp α] where
  protected mp {a b : α} : S⇓(a → b) → S⇓a → S⇓b

scoped infixl:100 " ⬝ " => HasMP.mp

class HasImpRefl [HasImp α] where
  impSelf (a : α) : S⇓(a → a)

class HasWeak [HasImp α] where
  weak (a b : α) : S⇓(a → b → a)

class HasImpTrans [HasImp α] where
  comp (a b c : α) : S⇓((b → c) → (a → b) → a → c)

class HasImpFlip [HasImp α] where
  flip (a b c : α) : S⇓((a → b → c) → b → a → c)

class HasSComb [HasImp α] where
  combS (a b c : α) : S⇓((a → b → c) → (a → b) → a → c)

class HasAndIntro [HasImp α] [HasAnd α] where
  andI (a b c : α) : S⇓((a → b) → (a → c) → a → b ∧ c)

class HasAndElim [HasImp α] [HasAnd α] where
  andE₁ (a b : α) : S⇓(a ∧ b → a)
  andE₂ (a b : α) : S⇓(a ∧ b → b)

class HasOrIntro [HasImp α] [HasOr α] where
  orI₁ (a b : α) : S⇓(a → a ∨ b)
  orI₂ (a b : α) : S⇓(b → a ∨ b)

class HasOrElim [HasImp α] [HasOr α] where
  orE (a b c : α) : S⇓((a → c) → (b → c) → a ∨ b → c)

class HasIffIntro [HasImp α] [HasIff α] where
  iffI (a b c : α) : S⇓((a → b → c) → (a → c → b) → (a → (b ↔ c)))

class HasIffElim [HasImp α] [HasIff α] where
  iffMP (a b : α) : S⇓((a ↔ b) → a → b)
  iffMPR (a b : α) : S⇓((a ↔ b) → b → a)

class HasNotIntro [HasImp α] [HasNot α] [Bot α] where
  notI (a : α) : S⇓((a → ⊥) → ¬a)

class HasNotElim [HasImp α] [HasNot α] [Bot α] where
  notE (a : α) : S⇓(¬a → a → ⊥)

variable {S α} {a b c d : α}

open HasSComb HasImpTrans

lemma DerivableIn.mp [HasImp α] [HasMP S α] (hab : DerivableIn S (a → b)) (ha : DerivableIn S a) :
    DerivableIn S b := ⟨hab.some ⬝ ha.some⟩

lemma derivableIn_id [HasImp α] [HasImpRefl S α] (a : α) : DerivableIn S (a → a) :=
  ⟨HasImpRefl.impSelf a⟩

lemma DerivableIn.weak [HasImp α] [HasMP S α] [HasWeak S α] (h : DerivableIn S a) :
    DerivableIn S (b → a) := .mp ⟨HasWeak.weak a b⟩ h

lemma DerivableIn.dep_mp [HasImp α] [HasMP S α] [HasSComb S α] (h : DerivableIn S (a → b → c))
    (h' : DerivableIn S (a → b)) : DerivableIn S (a → c) :=
  ⟨combS a b c ⬝ h.some ⬝ h'.some⟩

abbrev hasImpReflOfSK [HasImp α] [HasMP S α] [HasWeak S α] [HasSComb S α] : HasImpRefl S α where
  impSelf a :=
    combS a (a → a) a ⬝ HasWeak.weak a (a → a) ⬝ HasWeak.weak a a

variable (S α) in
abbrev hasImpTransOfSK [HasImp α] [HasMP S α] [HasWeak S α] [HasSComb S α] : HasImpTrans S α where
  comp a b c := by
    refine combS (b → c) _ _ ⬝ ?_ ⬝ HasWeak.weak (b → c) a
    exact HasWeak.weak _ _ ⬝ combS a b c

lemma DerivableIn.trans [HasImp α] [HasMP S α] [HasImpTrans S α] (hab : DerivableIn S (a → b))
    (hbc : DerivableIn S (b → c)) : DerivableIn S (a → c) :=
  ⟨comp a b c ⬝ hbc.some ⬝ hab.some⟩

variable (S α) in
abbrev hasImpFlipOfSK [HasImp α] [HasMP S α] [HasWeak S α] [HasSComb S α] : HasImpFlip S α where
  flip a b c := by
    refine combS (a → b → c) (b → a → b) (b → a → c) ⬝ ?_ ⬝ ?_
    · refine combS _ (b → (a → b) → a → c) _ ⬝ ?_ ⬝ ?_
      · exact HasWeak.weak _ (a → b → c) ⬝ combS b (a → b) (a → c)
      · refine combS _ ((a → b) → a → c) _ ⬝ ?_ ⬝ combS ..
        refine HasWeak.weak .. ⬝ HasWeak.weak ..
    · exact (HasWeak.weak (b → a → b) (a → b → c) ⬝ HasWeak.weak b a)

lemma DerivableIn.flip [HasImp α] [HasMP S α] [HasImpFlip S α] (h : DerivableIn S (a → b → c)) :
    DerivableIn S (b → a → c) := ⟨HasImpFlip.flip a b c ⬝ h.some⟩

def HasImpTrans.flipComp [HasImp α] [HasMP S α] [HasImpFlip S α] [HasImpTrans S α] (a b c : α) :
    S⇓((a → b) → (b → c) → a → c) := HasImpFlip.flip (b → c) (a → b) (a → c) ⬝ comp a b c

lemma DerivableIn.andI [HasImp α] [HasAnd α] [HasMP S α] [HasAndIntro S α]
    (hab : DerivableIn S (a → b)) (hac : DerivableIn S (a → c)) : DerivableIn S (a → b ∧ c) :=
  ⟨HasAndIntro.andI a b c ⬝ hab.some ⬝ hac.some⟩

lemma DerivableIn.andE₁ [HasImp α] [HasAnd α] [HasMP S α] [HasImpTrans S α] [HasAndElim S α]
    (h : DerivableIn S (a → b ∧ c)) : DerivableIn S (a → b) :=
  h.trans ⟨HasAndElim.andE₁ b c⟩

lemma DerivableIn.andE₂ [HasImp α] [HasAnd α] [HasMP S α] [HasImpTrans S α] [HasAndElim S α]
    (h : DerivableIn S (a → b ∧ c)) : DerivableIn S (a → c) :=
  h.trans ⟨HasAndElim.andE₂ b c⟩

lemma DerivableIn.orI₁ [HasImp α] [HasOr α] [HasMP S α] [HasOrIntro S α] [HasImpTrans S α]
    (h : DerivableIn S (a → b)) : DerivableIn S (a → b ∨ c) :=
  h.trans ⟨HasOrIntro.orI₁ b c⟩

lemma DerivableIn.orI₂ [HasImp α] [HasOr α] [HasMP S α] [HasOrIntro S α] [HasImpTrans S α]
    (h : DerivableIn S (a → c)) : DerivableIn S (a → b ∨ c) :=
  h.trans ⟨HasOrIntro.orI₂ b c⟩

lemma DerivableIn.orE [HasImp α] [HasOr α] [HasMP S α] [HasOrElim S α] [HasSComb S α]
    [HasImpTrans S α] (h : DerivableIn S (a → b ∨ c)) (hb : DerivableIn S (a → b → d))
    (hc : DerivableIn S (a → c → d)) : DerivableIn S (a → d) := by
  refine .dep_mp (.dep_mp ?_ hc) h
  exact hb.trans ⟨HasOrElim.orE b c d⟩

lemma DerivableIn.iffI [HasImp α] [HasIff α] [HasMP S α] [HasIffIntro S α]
    (hmp : DerivableIn S (a → b → c)) (hmpr : DerivableIn S (a → c → b)) :
    DerivableIn S (a → (b ↔ c)) :=
  ⟨HasIffIntro.iffI a b c ⬝ hmp.some ⬝ hmpr.some⟩

lemma DerivableIn.iff_mp [HasImp α] [HasIff α] [HasMP S α] [HasIffElim S α]
    (hab : DerivableIn S (a ↔ b)) (ha : DerivableIn S a) : DerivableIn S b :=
  ⟨HasIffElim.iffMP a b ⬝ hab.some ⬝ ha.some⟩

lemma DerivableIn.iff_mpr [HasImp α] [HasIff α] [HasMP S α] [HasIffElim S α]
    (hab : DerivableIn S (a ↔ b)) (hb : DerivableIn S b) : DerivableIn S a :=
  ⟨HasIffElim.iffMPR a b ⬝ hab.some ⬝ hb.some⟩

lemma DerivableIn.rw_iff_consequent [HasImp α] [HasIff α] [HasMP S α] [HasIffElim S α]
    [HasImpTrans S α] (hab : DerivableIn S (a → b)) (hbc : DerivableIn S (b ↔ c)) :
    DerivableIn S (a → c) :=
  hab.trans (.mp ⟨HasIffElim.iffMP b c⟩ hbc)

lemma DerivableIn.rw_iff_antecedent [HasImp α] [HasIff α] [HasMP S α] [HasIffElim S α]
    [HasImpTrans S α] (hac : DerivableIn S (a → c)) (hab : DerivableIn S (a ↔ b)) :
    DerivableIn S (b → c) :=
  (DerivableIn.mp ⟨HasIffElim.iffMPR a b⟩ hab).trans hac

lemma DerivableIn.iff_symm [HasImp α] [HasIff α] [HasMP S α] [HasIffIntro S α] [HasIffElim S α]
    [HasImpFlip S α] (h : DerivableIn S (a ↔ b)) : DerivableIn S (b ↔ a) := by
  refine .mp (.iffI ⟨HasIffElim.iffMPR a b⟩ ⟨HasIffElim.iffMP a b⟩) h

/-! ### Axioms -/

variable (S α) in
class HasEFQ [HasImp α] [Bot α] where
  botImp (a : α) : S⇓(⊥ → a)

lemma HasEFQ.derivableIn_bot_imp [HasImp α] [Bot α] [HasEFQ S α] (a : α) :
  DerivableIn S (⊥ → a) := ⟨botImp a⟩

def HasEFQ.notImpSelfImp [HasImp α] [Bot α] [HasNot α] [HasMP S α] [HasSComb S α]
    [HasEFQ S α] [HasNotElim S α] [HasImpTrans S α] [HasWeak S α] (a b : α) : S⇓(¬a → a → b) := by
  refine comp (¬a) (a → ⊥) (a → b) ⬝ ?_ ⬝ HasNotElim.notE a
  exact combS a ⊥ b ⬝ (HasWeak.weak (⊥ → b) a ⬝ HasEFQ.botImp b)

variable (S α) in
class HasDNE [HasImp α] [HasNot α] where
  dne (a : α) : S⇓(¬¬a → a)

lemma HasDNE.derivableIn_dne [HasImp α] [HasNot α] [HasDNE S α] (a : α) :
  DerivableIn S (¬¬a → a) := ⟨dne a⟩

protected def HasDNE.botImp [HasImp α] [HasNot α] [Bot α] [HasMP S α] [HasDNE S α]
    [HasImpTrans S α] [HasWeak S α] [HasNotIntro S α] (a : α) : S⇓(⊥ → a) :=
  comp ⊥ (¬¬a) a ⬝ HasDNE.dne a ⬝
    (comp ⊥ (¬a → ⊥) (¬¬a) ⬝ HasNotIntro.notI (¬a) ⬝ HasWeak.weak ⊥ (¬a))

abbrev HasDNE.hasEFQ [HasImp α] [HasNot α] [Bot α] [HasMP S α] [HasDNE S α]
    [HasImpTrans S α] [HasWeak S α] [HasNotIntro S α] : HasEFQ S α where
  botImp := HasDNE.botImp

def HasDNE.ofNotImpSelf [HasImp α] [HasNot α] [Bot α] [HasMP S α] [HasSComb S α]
    [HasImpTrans S α] [HasNotIntro S α] [HasNotElim S α] [HasDNE S α] (a : α) :
    S⇓((¬a → a) → a) :=
  comp _ _ _ ⬝ HasDNE.dne _ ⬝
    (comp _ _ _ ⬝ HasNotIntro.notI _ ⬝
      (combS .. ⬝ HasNotElim.notE a))

def HasDNE.pierce [HasImp α] [HasNot α] [Bot α] [HasMP S α] [HasSComb S α] [HasNotIntro S α]
    [HasNotElim S α] [HasDNE S α] [HasEFQ S α] [HasImpTrans S α] [HasImpFlip S α] [HasWeak S α]
    (a b : α) :
    S⇓(((a → b) → a) → a) :=
  comp _ _ _ ⬝ ofNotImpSelf a ⬝ (flipComp _ _ _ ⬝ HasEFQ.notImpSelfImp ..)

def HasDNE.lem [HasImp α] [HasNot α] [HasOr α] [Bot α] [HasDNE S α] [HasMP S α] [HasNotIntro S α]
    [HasNotElim S α] [HasSComb S α] [HasOrIntro S α] [HasImpTrans S α] [HasImpFlip S α] (a : α) :
    S⇓(a ∨ ¬ a) := by
  refine HasDNE.ofNotImpSelf (a ∨ ¬a) ⬝ ?_
  refine comp .. ⬝ HasOrIntro.orI₂ a (¬ a) ⬝ ?_
  refine comp .. ⬝ HasNotIntro.notI a ⬝ ?_
  refine comp .. ⬝ ?_ ⬝ HasNotElim.notE (a ∨ ¬a)
  exact flipComp a (a ∨ ¬a) ⊥ ⬝ HasOrIntro.orI₁ a ¬a

variable (S α) in
class HasLEM [HasOr α] [HasNot α] where
  lem (a : α) : S⇓(a ∨ ¬ a)

lemma HasLEM.derivableIn_lem [HasOr α] [HasNot α] [HasLEM S α] (a : α) :
  DerivableIn S (a ∨ ¬ a) := ⟨lem a⟩

abbrev HasDNE.hasLEM [HasImp α] [HasNot α] [HasOr α] [Bot α] [HasDNE S α] [HasMP S α]
    [HasNotIntro S α] [HasNotElim S α] [HasSComb S α] [HasOrIntro S α]
    [HasImpTrans S α] [HasImpFlip S α] : HasLEM S α where
  lem := HasDNE.lem

variable (S α) in
class HasPierce [HasImp α] where
  pierce (a b : α) : S⇓(((a → b) → a) → a)

lemma HasPierce.derivableIn_pierce [HasImp α] [HasPierce S α] (a b : α) :
  DerivableIn S (((a → b) → a) → a) := ⟨pierce a b⟩

abbrev HasDNE.hasPierce [HasImp α] [HasNot α] [Bot α] [HasMP S α] [HasSComb S α] [HasNotIntro S α]
    [HasNotElim S α] [HasDNE S α] [HasEFQ S α] [HasImpTrans S α] [HasImpFlip S α] [HasWeak S α] :
    HasPierce S α where
  pierce := HasDNE.pierce

end Cslib.Logic.InferenceSystem
