/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import Cslib.Computability.Machines.MultiTapeTuring.TapeView
public import Cslib.Computability.Machines.MultiTapeTuring.StructuralMachines

namespace Turing
namespace Routines

/-- Turing machine `tm` computes a function on data from tape `i` and updates tape `j`. -/
-- TODO move this somewhere else
@[expose]
public def computes_function_update {k : ℕ}
  {α : Type} [StrEnc α]
  (tm : MultiTapeTM k Char) (f : α → α)
  (j : Fin k) :=
  ∀ (x : α) (views : Fin k → TapeView),
    (views j = TapeView.ofEnc x) →
    tm.eval_struct views = .some (Function.update views j (TapeView.ofEnc (f x)))

/-- TODO document -/
@[expose]
public def computes_function_read_update {k : ℕ}
  {α : Type} [StrEnc α]
  (tm : MultiTapeTM k Char) (f : α → TapeView → TapeView)
  (i j : Fin k) :=
  ∀ (x : α) (views : Fin k → TapeView),
    ((views i).current = StrEnc.toData x) →
    tm.eval_struct views = .some (Function.update views j (f x (views j)))

/-- TODO document -/
@[expose]
public def computes_function_read_update' {k : ℕ}
  {α β : Type} [StrEnc α] [StrEnc β]
  (tm : MultiTapeTM k Char) (f : α → β → β)
  (i j : Fin k) :=
  ∀ (x : α) (y : β) (views : Fin k → TapeView),
    ((views i).current = StrEnc.toData x) →
    views j = TapeView.ofEnc y →
    tm.eval_struct views = .some (Function.update views j (TapeView.ofEnc (f x y)))

/-- TODO document -/
@[expose]
public def computes_function_read_read_update {k : ℕ}
  {α β : Type} [StrEnc α] [StrEnc β]
  (tm : MultiTapeTM k Char) (f : α → β → TapeView → TapeView)
  (i j r : Fin k) :=
  ∀ (x : α) (y : β) (views : Fin k → TapeView),
    ((views i).current = StrEnc.toData x) →
    ((views j).current = StrEnc.toData y) →
    tm.eval_struct views = .some (Function.update views r (f x y (views r)))

/-- TODO document -/
@[expose]
public def computes_function_read_read_update' {k : ℕ}
  {α β γ : Type} [StrEnc α] [StrEnc β] [StrEnc γ]
  (tm : MultiTapeTM k Char) (f : α → β → γ → γ)
  (i j r : Fin k) :=
  ∀ (x : α) (y : β) (z : γ) (views : Fin k → TapeView),
    ((views i).current = StrEnc.toData x) →
    ((views j).current = StrEnc.toData y) →
    views r = TapeView.ofEnc z →
    tm.eval_struct views = .some (Function.update views r (TapeView.ofEnc (f x y z)))


/-- TODO document -/
@[expose]
public def computes_function_read_replace {k : ℕ}
  {α β : Type} [StrEnc α] [StrEnc β]
  (tm : MultiTapeTM k Char)
  (f : α → β)
  (i j : Fin k) :=
  computes_function_read_update' tm (fun d _ => f d) i j

-- /-- Turing machine `tm` computes a function on data from tape `i` and pushes data to the
-- list on tape `j`. -/
-- @[expose]
-- public def computes_function_read_push {k : ℕ}
--   {α β : Type} [StrEnc α] [StrEnc β]
--   (tm : MultiTapeTM k Char)
--   (f : α → β)
--   (i j : Fin k) :=
--   computes_function_read_update tm (fun d tv => tv.pushList (StrEnc.toData (f d))) i j

/-- TODO document -/
@[expose]
public def computes_function_read_push {k : ℕ}
  {α β : Type} [StrEnc α] [StrEnc β]
  (tm : MultiTapeTM k Char)
  (f : α → β)
  (i j : Fin k) :=
  computes_function_read_update tm (fun d tv => tv.pushList (StrEnc.toData (f d))) i j

-- If the list is heterogeneous, use β = Data
/-- TODO document -/
@[expose]
public def computes_function_read_push' {k : ℕ}
  {α β : Type} [StrEnc α] [StrEnc β]
  (tm : MultiTapeTM k Char)
  (f : α → β)
  (i j : Fin k) :=
  computes_function_read_update' tm (fun d ls => (f d) :: ls) i j

/-- TODO document -/
@[expose]
public def computes_function_read_read_push {k : ℕ}
  {α β γ : Type} [StrEnc α] [StrEnc β] [StrEnc γ]
  (tm : MultiTapeTM k Char)
  (f : α → β → γ)
  (i j s : Fin k) :=
  computes_function_read_read_update tm
    (fun x y tv => tv.pushList (StrEnc.toData (f x y))) i j s

/-- TODO document -/
@[expose]
public def computes_function_read_read_push' {k : ℕ}
  {α β γ : Type} [StrEnc α] [StrEnc β] [StrEnc γ]
  (tm : MultiTapeTM k Char)
  (f : α → β → γ)
  (i j s : Fin k) :=
  computes_function_read_read_update' tm
    (fun x y (ls : List Data) => StrEnc.toData (f x y) :: ls) i j s


/-- Turing machine `tm` updates the head of tape `i`. -/
public def computes_function_head_update {k : ℕ}
  {α β : Type} [StrEnc α] [StrEnc β]
  (tm : MultiTapeTM k Char) (f : α → β)
  (i : Fin k) :=
  ∀ views, tm.eval_struct views =
    .some (Function.update views i ((views i).updateListHeadTyped f))

@[simp, grind =>]
public theorem computes_function_seq₁ {k : ℕ}
  {α β γ : Type} [StrEnc α] [StrEnc β] [StrEnc γ]
  {tm₁ tm₂ : MultiTapeTM k Char} {f₁ : α → β} {f₂ : β → γ}
  {i j : Fin k}
  (h_comp₁ : computes_function_read_push tm₁ f₁ i j)
  (h_comp₂ : computes_function_head_update tm₂ f₂ j) :
  computes_function_read_push (tm₁;ₜ tm₂) (fun x => f₂ (f₁ x)) i j := by sorry

@[simp, grind =>]
public theorem computes_function_seq₂ {k : ℕ}
  {α β γ δ : Type} [StrEnc α] [StrEnc β] [StrEnc γ] [StrEnc δ]
  {tm₁ tm₂ : MultiTapeTM k Char} {f₁ : α → β → γ} {f₂ : γ → δ}
  {i j r : Fin k}
  (h_comp₁ : computes_function_read_read_push tm₁ f₁ i j r)
  (h_comp₂ : computes_function_head_update tm₂ f₂ r) :
  computes_function_read_read_push (tm₁;ₜ tm₂) (fun x y => f₂ (f₁ x y)) i j r := by sorry


@[grind =>]
public theorem computes_function_read_read_push_swap {k : ℕ}
  {α β γ : Type} [StrEnc α] [StrEnc β] [StrEnc γ]
  {tm : MultiTapeTM k Char} {f : α → β → γ}
  {i j r : Fin k}
  (h : computes_function_read_read_push tm f i j r) :
  computes_function_read_read_push tm (fun x y => f y x) j i r := by sorry


end Routines
end Turing
