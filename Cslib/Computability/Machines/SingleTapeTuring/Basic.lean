/-
Copyright (c) 2025 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module

public import Cslib.Computability.Automata.Acceptors.Acceptor
public import Cslib.Computability.Automata.Acceptors.OmegaAcceptor
public import Cslib.Foundations.Data.OmegaSequence.InfOcc
public import Cslib.Foundations.Semantics.ReductionSystem.Basic
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Computability.PostTuringMachine
public import Mathlib.Computability.TuringMachine


namespace Turing

/--
List of option values that don't end with none
-/
structure OList (α : Type) where
  (asList : List (Option α))
  -- The list can be empty (i.e. none), but if it is not empty, the last element is not (some) none
  (h : asList.getLast? ≠ some none)

def OList.empty {α} : OList α := { asList := [], h := by simp }

def OList.map_some {α} (l : List α) : OList α := { asList := l.map some, h := by simp }

instance {α : Type} : Inhabited (OList α) where
  default := OList.empty


def OList.length {α} (l : OList α) : ℕ := l.asList.length

def OList.cons {α} : Option α -> OList α -> OList α
| none, l => { asList := [], h := by simp }
| some a, l => {
    asList := some a :: l.asList,
    h := by
      cases hl : l.asList with
      | nil => simp
      | cons hd tl =>
        simp only [List.getLast?_cons_cons]
        rw [← hl]
        exact l.h
       }

def OList.tail {α} (l : OList α) : OList α :=
  match hl : l.asList with
  | [] => OList.empty
  | hd :: t => { asList := t, h := by
                  match t with
                  | [] => simp
                  | hd' :: t' =>
                    have lh := l.h
                    rw [hl] at lh
                    simp only [List.getLast?_cons_cons] at lh
                    have := l.h
                    rw [hl, List.getLast?_cons_cons] at this
                    exact this
  }

def OList.head {α} (l : OList α) : Option α :=
  match l.asList with
  | [] => none
  | h :: _ => h

lemma OList.length_tail_le {α} (l : OList α) : l.tail.length ≤ l.length := by
  unfold tail length
  split
  · simp [empty]
  · next heq => simp [heq]

lemma OList.length_cons_none {α} (l : OList α) : (OList.cons none l).length = 0 := by
  simp [cons, length, empty]

lemma OList.length_cons_some {α} (a : α) (l : OList α) :
    (OList.cons (some a) l).length = l.length + 1 := by
  simp [cons, length]

lemma OList.length_cons_le {α} (o : Option α) (l : OList α) :
    (OList.cons o l).length ≤ l.length + 1 := by
  cases o with
  | none => simp [length_cons_none]
  | some a => simp [length_cons_some]

lemma OList.length_map_some {α} (l : List α) : (OList.map_some l).length = l.length := by
  simp [map_some, length]

lemma OList.length_empty {α} : (OList.empty : OList α).length = 0 := by
  simp [empty, length]

/--
I find this more convenient than mathlib's Tape type,
because that requires the type tobe inhabited,
and it is easy to confuse a list representing one thing with a list representing another,
if the representations are the same except for a sequence of default values at the end.

The head of the machine is the current symbol under the tape head.
We do not assume here, but could add, that the ends of the tape are never none.
The move function should guarantee this, so that two tapes are equal
even if one has written none to the side
-/
structure OTape (α : Type) where
  (head : Option α)
  (left : OList α)
  (right : OList α)
deriving Inhabited

def OTape.mk₁ (l : List Bool) : OTape Bool :=
  match l with
  | [] => { head := none, left := OList.empty, right := OList.empty }
  | h :: t => { head := some h, left := OList.empty, right := OList.map_some t }

-- TODO incorrect, we must delete blanks from the ends, refactor out OList
def OTape.move {α} : Turing.OTape α → Dir → Turing.OTape α
  | t, .left =>
    match t.left, t.head, t.right with
    | l, h, r => { head := l.head, left := l.tail, right := OList.cons h r }
  | t, .right =>
    match t.left, t.head, t.right with
    | l, h, r => { head := r.head, left := OList.cons h l, right := r.tail }


def OTape.move? {α} : Turing.OTape α → Option Dir → Turing.OTape α
  | t, none => t
  | t, some d => t.move d

def OTape.write {α} : Turing.OTape α → Option α → Turing.OTape α
  | t, a => { t with head := a }

open Classical in
noncomputable def ListBlank.space_used {α} [Inhabited α] (l : ListBlank α) : ℕ :=
  Nat.find (p := fun n => ∀ i > n, l.nth i = default)
    (l.inductionOn (fun xs => ⟨xs.length, fun i hi => by
      change (ListBlank.mk xs).nth i = default
      rw [ListBlank.nth_mk]
      exact List.getI_eq_default xs (Nat.le_of_lt hi)⟩))

/--
The space used by a OTape is the number of symbols
between and including the head, and leftmost and rightmost non-blank symbols on the OTape
-/
noncomputable def OTape.space_used {α} [Inhabited α] (t : Turing.OTape α) : ℕ :=
  1 + t.left.length + t.right.length

lemma OTape.space_used_write {α} [Inhabited α] (t : Turing.OTape α) (a : Option α) :
    (t.write a).space_used = t.space_used := by
  rfl

lemma OTape.space_used_mk₁ (l : List Bool) :
    (OTape.mk₁ l).space_used = max 1 l.length := by
  cases l with
  | nil =>
    simp [mk₁, space_used, OList.length_empty]
  | cons h t =>
    simp [mk₁, space_used, OList.length_empty, OList.length_map_some]
    omega

open Classical in
lemma ListBlank.nth_ge_space_used {α} [Inhabited α] (l : ListBlank α) (i : ℕ)
    (hi : i > l.space_used) : l.nth i = default := by
  unfold space_used at hi
  have H : ∃ n, ∀ i > n, l.nth i = default := l.inductionOn (fun xs => ⟨xs.length, fun i hi =>
    (ListBlank.nth_mk xs i).symm ▸ List.getI_eq_default xs (Nat.le_of_lt hi)⟩)
  have h := Nat.find_spec H
  exact h i hi

open Classical in
lemma ListBlank.space_used_cons_le {α} [Inhabited α] (a : α) (l : ListBlank α) :
    (l.cons a).space_used ≤ l.space_used + 1 := by
  unfold space_used
  apply Nat.find_le
  intro i hi
  cases i with
  | zero => omega
  | succ i =>
    rw [ListBlank.nth_succ, ListBlank.tail_cons]
    exact ListBlank.nth_ge_space_used l i (by unfold space_used; omega)

open Classical in
lemma ListBlank.space_used_tail_le {α} [Inhabited α] (l : ListBlank α) :
    l.tail.space_used ≤ l.space_used := by
  unfold space_used
  apply Nat.find_le
  intro i hi
  rw [← ListBlank.nth_succ]
  exact ListBlank.nth_ge_space_used l (i + 1) (by unfold space_used; omega)

lemma OTape.space_used_move {α} [Inhabited α] (t : Turing.OTape α) (d : Dir) :
    (t.move d).space_used ≤ t.space_used + 1 := by
  cases d with
  | left =>
    simp only [move, space_used]
    have h1 := OList.length_tail_le t.left
    have h2 := OList.length_cons_le t.head t.right
    omega
  | right =>
    simp only [move, space_used]
    have h1 := OList.length_cons_le t.head t.left
    have h2 := OList.length_tail_le t.right
    omega

namespace BinTM0

/-- A Turing machine "statement" is just a command to move
  left or right, and write a symbol on the OTape. -/
def Stmt := (Option Bool) × Option (Dir)
deriving Inhabited

end BinTM0

/-- A TM0 over the alphabet of Option Bool (none is blank OTape symbol). -/
structure BinTM0 where
  /-- type of state labels -/
  (Λ : Type)
  /-- finiteness of the state type -/
  [FintypeΛ : Fintype Λ]
  /-- Initial state -/
  (q₀ : Λ)
  /-- Transition function, mapping a state and a head symbol
  to a Stmt to invoke, and optionally a new state (none for halt) -/
  (M : Λ → (Option Bool) → (Turing.BinTM0.Stmt × Option Λ))


namespace BinTM0

section

variable (tm : BinTM0)

instance : Inhabited tm.Λ :=
  ⟨tm.q₀⟩

instance : Fintype tm.Λ :=
  tm.FintypeΛ

instance inhabitedStmt : Inhabited (Stmt) := inferInstance

/-- The type of configurations (functions) corresponding to this TM. -/
structure Cfg : Type where
  /-- the state of the TM (or none for the halting state) -/
  state : Option tm.Λ
  /-- the OTape contents, which -/
  OTape : OTape (Bool)
deriving Inhabited

/-- The step function corresponding to this TM. -/
@[simp]
def step : tm.Cfg → Option tm.Cfg :=
  fun ⟨q, t⟩ =>
    match q with
    -- If in the halting state, there is no next configuration
    | none => none
    -- If in state q'
    | some q' =>
      -- Look up the transition function
      match tm.M q' t.head with
      | ⟨(wr, dir), q''⟩ =>
          -- enter a new configuration
          some ⟨
            -- With state q'' (or none for halting)
            q'',
            -- And OTape updated according to the Stmt
            (t.write wr).move? dir⟩
end

/-- The initial configuration corresponding to a list in the input alphabet. -/
def initCfg (tm : BinTM0) (s : List Bool) : tm.Cfg := ⟨some tm.q₀, OTape.mk₁ s⟩

/-- The final configuration corresponding to a list in the output alphabet.
(We demand that the head halts at the leftmost position of the output.)
-/
def haltCfg (tm : BinTM0) (s : List (Bool)) : tm.Cfg := ⟨none, OTape.mk₁ s⟩

/--
The `ReductionSystem` corresponding to a `BinTM0` is defined by the `step` function,
which maps a configuration to its next configuration if it exists.
-/
def ReductionSystem (tm : BinTM0) : Cslib.ReductionSystem (tm.Cfg) :=
  { Red := fun cfg cfg' => tm.step cfg = some cfg' }
-- TODO use this, rather than the current setup


noncomputable def Cfg.space_used (tm : BinTM0) (cfg : tm.Cfg) : ℕ :=
  cfg.OTape.space_used

open Classical in
lemma ListBlank.space_used_mk_nil {α} [Inhabited α] :
    (ListBlank.mk ([] : List α)).space_used = 0 := by
  unfold ListBlank.space_used
  rw [Nat.find_eq_zero]
  intro i hi
  rw [ListBlank.nth_mk]
  exact List.getI_nil i

-- Helper lemma for space_used of a ListBlank created from a list
open Classical in
lemma ListBlank.space_used_mk {α} [Inhabited α] (l : List α) :
    (ListBlank.mk l).space_used ≤ l.length := by
  unfold ListBlank.space_used
  apply Nat.find_le
  intro i hi
  rw [ListBlank.nth_mk]
  exact List.getI_eq_default l (Nat.le_of_lt hi)

-- /-- The space_used of a OTape created from a list
-- equals the maximum of 1 and the list length -/
-- lemma OTape.space_used_mk₁ {α} [Inhabited α] (l : List α) :
--     (OTape.mk₁ l).space_used = max 1 l.length := by
--   unfold OTape.mk₁ OTape.mk₂ OTape.mk' OTape.space_used
--   simp only [ListBlank.space_used_mk_nil, add_zero, ListBlank.tail_mk]
--   cases l with
--   | nil =>
--     simp [ListBlank.space_used_mk_nil]
--   | cons h t =>
--     simp only [List.tail_cons, List.length_cons, le_add_iff_nonneg_left, zero_le, sup_of_le_right]
--     rw [add_comm]
--     simp only [Nat.add_right_cancel_iff]
--     sorry

lemma Cfg.space_used_initCfg (tm : BinTM0) (s : List Bool) :
    (tm.initCfg s).space_used = max 1 s.length := by
  simp [initCfg, Cfg.space_used, OTape.space_used_mk₁]

lemma Cfg.space_used_haltCfg (tm : BinTM0) (s : List Bool) :
    (tm.haltCfg s).space_used = max 1 s.length := by
  simp [haltCfg, Cfg.space_used, OTape.space_used_mk₁]

lemma Cfg.space_used_step {tm : BinTM0} (cfg cfg' : tm.Cfg)
    (hstep : tm.step cfg = some cfg') :
    cfg'.space_used ≤ cfg.space_used + 1 := by
  unfold Cfg.space_used
  cases cfg with | mk state tape =>
  cases state with
  | none => simp [step] at hstep
  | some q =>
    simp only [step] at hstep
    generalize hM : tm.M q tape.head = result at hstep
    obtain ⟨⟨wr, dir⟩, q''⟩ := result
    simp only at hstep
    cases hstep
    cases dir with
    | none =>
      simp only [OTape.move?]
      rw [OTape.space_used_write]
      omega
    | some d =>
      simp only [OTape.move?]
      have h1 := OTape.space_used_move (tape.write wr) d
      rw [OTape.space_used_write] at h1
      exact h1

/-- `f` eventually reaches `b` when repeatedly evaluated on `a`, in exactly `steps` steps. -/
def EvalsToInTime {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ) (steps : ℕ) : Prop :=
  (· >>= f)^[steps] a = b

/-- Reflexivity of `EvalsTo` in 0 steps. -/
lemma EvalsToInTime.refl {σ : Type*} (f : σ → Option σ) (a : σ) : EvalsToInTime f a (some a) 0 :=
  rfl

/-- Transitivity of `EvalsTo` in the sum of the numbers of steps. -/
@[trans]
lemma EvalsToInTime.trans {σ : Type*} (f : σ → Option σ) (a : σ) (b : σ) (c : Option σ)
    (steps₁ steps₂ : ℕ)
    (h₁ : EvalsToInTime f a b steps₁)
    (h₂ : EvalsToInTime f b c steps₂) :
    EvalsToInTime f a c (steps₂ + steps₁) := by
  simp_all only [EvalsToInTime, Option.bind_eq_bind]
  rw [Function.iterate_add_apply, h₁, h₂]

/-- If we evaluate to some state in n+1 steps, there is an intermediate state
    that we reach in n steps, and then one more step reaches the final state. -/
lemma EvalsToInTime.succ_decompose {σ : Type*} (f : σ → Option σ) (a : σ) (b : σ)
    (n : ℕ) (h : EvalsToInTime f a (some b) (n + 1)) :
    ∃ c : σ, EvalsToInTime f a (some c) n ∧ f c = some b := by
  set c' := (· >>= f)^[n] (some a) with hc'
  simp only [EvalsToInTime, Option.bind_eq_bind] at h hc' ⊢
  rw [Function.iterate_succ_apply'] at h
  -- h : (· >>= f) ((· >>= f)^[n] (some a)) = some b
  -- This means (· >>= f)^[n] (some a) >>= f = some b
  -- So (· >>= f)^[n] (some a) = some c for some c with f c = some b
  rw [<-hc'] at h
  revert h hc'
  cases c' with
  | none =>
    grind
  | some c =>
    intros h hc'
    use c
    grind

lemma EvalsToInTime.succ_iff {σ : Type*} (f : σ → Option σ) (a : σ) (b : σ)
    (n : ℕ) :
    EvalsToInTime f a (some b) (n + 1) ↔
      ∃ c : σ, EvalsToInTime f a (some c) n ∧ f c = some b := by
  constructor
  · exact EvalsToInTime.succ_decompose f a b n
  · intro ⟨c, hc_eval, hc_step⟩
    simp only [EvalsToInTime, Option.bind_eq_bind, Function.iterate_succ_apply'] at hc_eval ⊢
    simp only [hc_eval, Option.bind_some, hc_step]

theorem Turing.BinTM0.EvalsToInTime.congr.extracted_1_2.{u_2, u_1}
    {σ : Type u_1} {σ' : Type u_2} (f : σ → Option σ)
    (f' : σ' → Option σ') (g : σ → σ')
    (hg : ∀ (x : σ), Option.map g (f x) = f' (g x)) (n : ℕ) (a : σ) :
    (Option.map g ((flip Option.bind f)^[n] (some a))).bind f' =
      ((flip Option.bind f)^[n] (some a)).bind fun a ↦ f' (g a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Function.iterate_succ_apply, flip, Option.bind_some, <- hg] at ih ⊢
    grind





/--
If `f` is homomorphic to `f'` via `g`, then if `f` evals to `b` from `a` in `steps` steps,
then `f'` evals to `g b` from `g a` in `steps` steps.
-/
lemma EvalsToInTime.map {σ σ' : Type*} (f : σ → Option σ) (f' : σ' → Option σ')
    (g : σ → σ') (hg : ∀ x, Option.map g (f x) = f' (g x))
    (a : σ) (b : Option σ)
    (steps : ℕ)
    (h : EvalsToInTime f a b steps) : EvalsToInTime f' (g a) (Option.map g b) steps := by
  induction steps generalizing a b with
  | zero =>
    simp only [EvalsToInTime, Option.bind_eq_bind, Function.iterate_zero, id_eq] at h ⊢
    subst h
    rfl
  | succ n ih =>
    simp only [EvalsToInTime, Option.bind_eq_bind, Function.iterate_succ_apply',
      forall_eq'] at h ih ⊢
    subst h
    rw [ih]
    clear ih
    simp only [Option.map_bind, Function.comp_apply, hg]
    exact Turing.BinTM0.EvalsToInTime.congr.extracted_1_2 f f' g hg n a

/--
If `h : σ → ℕ` increases by at most 1 on each step of `f`,
then the value of `h` at the output after `steps` steps is at most `h` at the input plus `steps`.
-/
lemma EvalsToInTime.small_change {σ : Type*} (f : σ → Option σ) (h : σ → ℕ)
    (h_step : ∀ a b, f a = some b → h b ≤ h a + 1)
    (a : σ) (b : σ)
    (steps : ℕ)
    (hevals : EvalsToInTime f a b steps) :
    h b ≤ h a + steps := by
  induction steps generalizing a b with
  | zero =>
    simp only [EvalsToInTime, Option.bind_eq_bind, Function.iterate_zero, id_eq, Option.some.injEq,
      add_zero] at hevals ⊢
    subst hevals
    exact Nat.le_refl (h a)
  | succ n ih =>
    rw [EvalsToInTime.succ_iff] at hevals
    obtain ⟨c, hevals_n, h_step_eq⟩ := hevals
    specialize ih a c hevals_n
    specialize h_step c b h_step_eq
    omega


-- m -> step_bound
/-- `f` eventually reaches `b` in at most `m` steps when repeatedly
evaluated on `a`. -/
def EvalsToWithinTime {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ) (m : ℕ) : Prop :=
  ∃ steps ≤ m, EvalsToInTime f a b steps

/-- Reflexivity of `EvalsToWithinTime` in 0 steps. -/
def EvalsToWithinTime.refl {σ : Type*} (f : σ → Option σ) (a : σ) :
    EvalsToWithinTime f a (some a) 0 := by
  use 0
  exact if_false_right.mp rfl

/-- Transitivity of `EvalsToWithinTime` in the sum of the numbers of steps. -/
@[trans]
def EvalsToWithinTime.trans {σ : Type*} (f : σ → Option σ) (m₁ : ℕ) (m₂ : ℕ) (a : σ) (b : σ)
    (c : Option σ) (h₁ : EvalsToWithinTime f a b m₁) (h₂ : EvalsToWithinTime f b c m₂) :
    EvalsToWithinTime f a c (m₂ + m₁) := by
  obtain ⟨steps₁, hsteps₁, hevals₁⟩ := h₁
  obtain ⟨steps₂, hsteps₂, hevals₂⟩ := h₂
  use steps₂ + steps₁
  constructor
  · omega
  · exact EvalsToInTime.trans f a b c steps₁ steps₂ hevals₁ hevals₂

def EvalsToWithinTime.map {σ σ' : Type*} (f : σ → Option σ) (f' : σ' → Option σ')
    (g : σ → σ') (hg : ∀ x, Option.map g (f x) = f' (g x))
    (a : σ) (b : Option σ)
    (m : ℕ)
    (h : EvalsToWithinTime f a b m) : EvalsToWithinTime f' (g a) (Option.map g b) m := by
  obtain ⟨steps, hsteps, hevals⟩ := h
  use steps
  constructor
  · exact hsteps
  · exact EvalsToInTime.map f f' g hg a b steps hevals

/--
Monotonicity of `EvalsToWithinTime` in the time bound.
-/
def EvalsToWithinTime.mono_time {σ : Type*} (f : σ → Option σ) (a : σ) (b : Option σ)
    {m₁ m₂ : ℕ} (h : EvalsToWithinTime f a b m₁) (hm : m₁ ≤ m₂) : EvalsToWithinTime f a b m₂ := by
  obtain ⟨steps, hsteps, hevals⟩ := h
  use steps
  simp_all only
  simp
  omega

lemma EvalsToWithinTime.small_change {σ : Type*} (f : σ → Option σ) (h : σ → ℕ)
    (h_step : ∀ a b, f a = some b → h b ≤ h a + 1)
    (a : σ) (b : σ)
    (m : ℕ)
    (hevals : EvalsToWithinTime f a (some b) m) :
    h b ≤ h a + m := by
  obtain ⟨steps, hsteps, hevals_steps⟩ := hevals
  have := EvalsToInTime.small_change f h h_step a b steps hevals_steps
  omega

/-- A proof of tm outputting l' when given l. -/
def OutputsInTime (tm : BinTM0) (l : List (Bool)) (l' : Option (List (Bool))) :=
  EvalsToInTime tm.step (initCfg tm l) ((Option.map (haltCfg tm)) l')

/-- A proof of tm outputting l' when given l in at most m steps. -/
def OutputsWithinTime (tm : BinTM0) (l : List (Bool)) (l' : Option (List (Bool)))
    (m : ℕ) :=
  EvalsToWithinTime tm.step (initCfg tm l) ((Option.map (haltCfg tm)) l') m

-- /-- A (bundled TM0) Turing machine
-- with input alphabet equivalent to `Γ₀` and output alphabet equivalent to `Γ₁`.
-- TODO this is something of a holdover, might get rid
-- -/
-- structure ComputableAux (Γ₀ Γ₁ : Type) where
--   /-- the underlying bundled TM0 -/
--   tm : BinTM0
--   /-- the input alphabet is equivalent to `Γ₀` -/
--   inputAlphabet : Bool ≃ Γ₀
--   /-- the output alphabet is equivalent to `Γ₁` -/
--   outputAlphabet : Bool ≃ Γ₁

/-- A Turing machine + a proof it outputsInTime `f`. -/
structure Computable (f : List Bool → List Bool) where
  /-- the underlying bundled TM0 -/
  tm : BinTM0
  steps : ℕ
  /-- a proof this machine outputsInTime `f` -/
  outputsFun :
    ∀ a,
      OutputsInTime tm ((a))
        (Option.some (((f a))))
        steps

/-- A Turing machine + a time function +
a proof it outputsInTime `f` in at most `time(input.length)` steps. -/
structure ComputableInTime (f : List Bool → List Bool) where
  /-- the underlying bundled TM0 -/
  tm : BinTM0
  /-- a time function -/
  time : ℕ → ℕ
  /-- proof this machine outputsInTime `f` in at most `time(input.length)` steps -/
  outputsFun :
    ∀ a,
      tm.OutputsWithinTime
        ((a))
        (Option.some (((f a))))
        (time ( a).length)

/-- A Turing machine + a polynomial time function +
a proof it outputsInTime `f` in at most `time(input.length)` steps. -/
structure ComputableInPolyTime (f : List Bool → List Bool) where
  /-- the underlying bundled TM0 -/
  tm : BinTM0
  /-- a polynomial time function -/
  time : Polynomial ℕ
  /-- proof that this machine outputsInTime `f` in at most `time(input.length)` steps -/
  outputsFun :
    ∀ a,
      OutputsWithinTime tm (( a))
        (Option.some (((f a))))
        (time.eval ( a).length)

-- /-- A forgetful map, forgetting the time bound on the number of steps. -/
-- def ComputableInTime.toComputable {α β : Type} {ea : BinEncoding α} {eb : BinEncoding β}
--     {f : α → β} (h : ComputableInTime ea eb f) : Computable ea eb f :=
--   ⟨h.tm, fun a => OutputsWithinTime.toOutputsInTime (h.outputsFun a)⟩

/-- A forgetful map, forgetting that the time function is polynomial. -/
def ComputableInPolyTime.toComputableInTime {f : List Bool → List Bool}  (h : ComputableInPolyTime f) :
    ComputableInTime f :=
  ⟨h.tm, fun n => h.time.eval n, h.outputsFun⟩

open Turing.TM0.Stmt

/-- A Turing machine computing the identity. -/
def idComputer : BinTM0 where
  Λ := PUnit
  q₀ := PUnit.unit
  M := fun _ b => ⟨(b, none), none⟩

noncomputable section

/-- A proof that the identity map on α is computable in polytime. -/
def ComputableInPolyTime.id :
    @ComputableInPolyTime id where
  tm := idComputer
  time := 1
  outputsFun x := by
    use 1
    simp only [Polynomial.eval_one, le_refl, id_eq, Option.map_some, true_and]
    simp only [EvalsToInTime, initCfg, haltCfg, idComputer,
      Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
    congr 1


    -- { steps := 1
    --   evals_in_steps := rfl
    --   steps_le_m := by simp only [Polynomial.eval_one, le_refl] }

-- instance inhabitedComputableInPolyTime :
--     Inhabited (ComputableInPolyTime (default : BinEncoding Bool) default id) :=
--   ⟨idComputableInPolyTime Computability.inhabitedBinEncoding.default⟩

-- instance inhabitedOutputsWithinTime :
--     Inhabited
--       (OutputsWithinTime (idComputer finEncodingBoolBool)
--         (List.map (Equiv.cast rfl).invFun [false])
--         (some (List.map (Equiv.cast rfl).invFun [false])) (Polynomial.eval 1 1)) :=
--   ⟨(idComputableInPolyTime finEncodingBoolBool).outputsFun false⟩

-- instance inhabitedOutputsInTime :
--     Inhabited
--       (OutputsInTime (idComputer finEncodingBoolBool) (List.map (Equiv.cast rfl).invFun [false])
--         (some (List.map (Equiv.cast rfl).invFun [false]))) :=
--   ⟨OutputsWithinTime.toOutputsInTime Turing.inhabitedOutputsWithinTime.default⟩

-- instance inhabitedEvalsToWithinTime :
--     Inhabited (EvalsToWithinTime (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩) 0) :=
--   ⟨EvalsToWithinTime.refl _ _⟩

-- instance inhabitedTM0EvalsToInTime :
--     Inhabited (EvalsToInTime (fun _ : Unit => some ⟨⟩) ⟨⟩ (some ⟨⟩)) :=
--   ⟨EvalsTo.refl _ _⟩

/-- A proof that the identity map on α is computable in time. -/
def ComputableInTime.id  :
    @ComputableInTime id :=
  ComputableInPolyTime.toComputableInTime <| ComputableInPolyTime.id

-- instance inhabitedComputableInTime :
--     Inhabited (ComputableInTime finEncodingBoolBool finEncodingBoolBool id) :=
--   ⟨idComputableInTime Computability.inhabitedBinEncoding.default⟩

-- /-- A proof that the identity map on α is computable. -/
-- def idComputable {α : Type} (ea : BinEncoding α) : @Computable α α ea ea id :=
--   ComputableInTime.toComputable <| ComputableInTime.id ea

-- instance inhabitedComputable :
--     Inhabited (Computable finEncodingBoolBool finEncodingBoolBool id) :=
--   ⟨idComputable Computability.inhabitedBinEncoding.default⟩

-- instance inhabitedComputableAux : Inhabited (ComputableAux Bool Bool) :=
--   ⟨(default : Computable finEncodingBoolBool finEncodingBoolBool id).toComputableAux⟩

def compComputer {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : ComputableInTime f)
    (hg : ComputableInTime g) :
    BinTM0 :=
  {
    Λ := hf.tm.Λ ⊕ hg.tm.Λ
    q₀ := Sum.inl hf.tm.q₀
    M := fun q h =>
      match q with
      -- If we are in the first machine's states, run that machine
      | Sum.inl ql => match hf.tm.M ql (h) with
        -- The action should be the same, and the state should either be the corresponding state
        -- in the first machine, or transition to the start state of the second machine if halting
        | (ql', stmt) => (ql',
            match stmt with
            -- If it halts, transition to the start state of the second machine
            | none => some (Sum.inr hg.tm.q₀)
            -- Otherwise continue as normal
            | _ => Option.map Sum.inl stmt)
      -- If we are in the second machine's states, run that machine
      | Sum.inr qr =>
        match hg.tm.M qr (h) with
        -- The action should be the same, and the state should be the corresponding state
        -- in the second machine, or halting if the second machine halts
        | (qr', stmt) => (qr',
            match stmt with
            -- If it halts, transition to the halting state
            | none => none
            -- Otherwise continue as normal
            | _ => Option.map Sum.inr stmt)
  }

lemma compComputer_q₀_eq (f : List Bool → List Bool) (g : List Bool → List Bool)
  (hf : ComputableInTime f)
  (hg : ComputableInTime g) :
    (compComputer hf hg).q₀ = Sum.inl hf.tm.q₀ :=
  rfl

/-- Lift a config over a tm to a config over the comp -/
def liftCompCfg_left {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : ComputableInTime  f)
    (hg : ComputableInTime g)
    (cfg : hf.tm.Cfg) :
    (compComputer hf hg).Cfg :=
  {
    state := Option.map Sum.inl cfg.state
    OTape := cfg.OTape
  }

def liftCompCfg_right{f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : ComputableInTime  f)
    (hg : ComputableInTime  g)
    (cfg : hg.tm.Cfg) :
    (compComputer hf hg).Cfg :=
  {
    state := Option.map Sum.inr cfg.state
    OTape := cfg.OTape
  }

theorem map_liftCompCfg_left_step
    {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : ComputableInTime f) (hg : ComputableInTime g)
    (x : hf.tm.Cfg)
    (hx : ∀ cfg, hf.tm.step x = some cfg → cfg.state.isSome) :
    Option.map (liftCompCfg_left hf hg) (hf.tm.step x) =
      (compComputer hf hg).step (liftCompCfg_left hf hg x) := by
  cases x with
  | mk state OTape =>
    cases state with
    | none =>
      -- x is already in halting state, step returns none on both sides
      simp only [step, liftCompCfg_left, Option.map_none, compComputer]
    | some q =>
      simp only [step, liftCompCfg_left, compComputer, Option.map_some]
      -- Get the transition result
      generalize hM : hf.tm.M q OTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      simp only
      -- Case on whether the next state is none (halting) or some
      cases nextState with
      | none =>
        -- The first machine halts, but hx says the result has state.isSome
        simp only [step, hM] at hx
        have := hx ⟨none, (OTape.write wr).move? dir⟩ rfl
        simp at this
      | some q' =>
        -- Normal step case - both sides produce the lifted config
        simp only [hM, Option.map_some, liftCompCfg_left]

/-- Helper lemma: liftCompCfg_right commutes with step for the second machine -/
theorem map_liftCompCfg_right_step
    {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : ComputableInTime f) (hg : ComputableInTime g)
    (x : hg.tm.Cfg) :
    Option.map (liftCompCfg_right hf hg) (hg.tm.step x) =
      (compComputer hf hg).step (liftCompCfg_right hf hg x) := by
  cases x with
  | mk state OTape =>
    cases state with
    | none =>
      simp only [step, liftCompCfg_right, Option.map_none, compComputer]
    | some q =>
      simp only [step, liftCompCfg_right, compComputer, Option.map_some]
      generalize hM : hg.tm.M q OTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      cases nextState with
      | none => simp only [hM, Option.map_some, liftCompCfg_right, Option.map_none]
      | some q' => simp only [hM, Option.map_some, liftCompCfg_right]

/-- When the first machine would halt, the composed machine transitions to the second machine -/
theorem comp_transition_to_right {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : ComputableInTime f) (hg : ComputableInTime g)
    (tp : OTape (Bool))
    (q : hf.tm.Λ)
    (hM : (hf.tm.M q tp.head).2 = none) :
    (compComputer hf hg).step { state := some (Sum.inl q), OTape := tp } =
      some { state := some (Sum.inr hg.tm.q₀),
             OTape := (tp.write (hf.tm.M q tp.head).1.1).move? (hf.tm.M q tp.head).1.2 } := by
  simp only [step, compComputer, hM]
  generalize hfM_eq : hf.tm.M q tp.head = result
  obtain ⟨⟨wr, dir⟩, nextState⟩ := result
  simp only [hfM_eq]

/-- Helper: lifting to Sum.inl and transitioning to Sum.inr on halt -/
def liftCompCfg_left_or_right {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : ComputableInTime f)
    (hg : ComputableInTime g)
    (cfg : hf.tm.Cfg) :
    (compComputer hf hg).Cfg :=
  match cfg.state with
  | some q => { state := some (Sum.inl q), OTape := cfg.OTape }
  | none => { state := some (Sum.inr hg.tm.q₀), OTape := cfg.OTape }

/-- The lifting function commutes with step, converting halt to transition -/
theorem map_liftCompCfg_left_or_right_step
    {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : ComputableInTime  f) (hg : ComputableInTime  g)
    (x : hf.tm.Cfg)
    (hx : x.state.isSome) :
    Option.map (liftCompCfg_left_or_right hf hg) (hf.tm.step x) =
      (compComputer hf hg).step (liftCompCfg_left_or_right hf hg x) := by
  cases x with
  | mk state OTape =>
    cases state with
    | none => simp at hx
    | some q =>
      simp only [step, liftCompCfg_left_or_right, compComputer]
      generalize hM : hf.tm.M q OTape.head = result
      obtain ⟨⟨wr, dir⟩, nextState⟩ := result
      cases nextState with
      | none => simp only [hM, Option.map_some, liftCompCfg_left_or_right]
      | some q' => simp only [hM, Option.map_some, liftCompCfg_left_or_right]

/-- General simulation: if the first machine goes from cfg to halt, the composed machine
    goes from lifted cfg to Sum.inr hg.tm.q₀ -/
theorem comp_left_simulation_general {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : ComputableInTime f) (hg : ComputableInTime  g)
    (cfg : hf.tm.Cfg)
    (hcfg : cfg.state.isSome)
    (haltCfg : hf.tm.Cfg)
    -- (haltCfg_state : haltCfg.state = none)
    (steps : ℕ)
    (h : EvalsToInTime hf.tm.step cfg (some haltCfg) steps) :
    EvalsToInTime (compComputer hf hg).step
      (liftCompCfg_left_or_right hf hg cfg)
      (some (liftCompCfg_left_or_right hf hg haltCfg))
      steps := by
  -- Proof by induction on steps.
  -- Key insight: liftCompCfg_left_or_right maps:
  --   { state := some q, OTape } -> { state := some (Sum.inl q), OTape }
  --   { state := none, OTape }   -> { state := some (Sum.inr hg.tm.q₀), OTape }
  -- For non-halting configs, the composed machine simulates exactly.
  -- When the first machine halts, the composed machine transitions to Sum.inr hg.tm.q₀.
  induction steps generalizing cfg haltCfg with
  | zero =>
    simp only [EvalsToInTime, Option.bind_eq_bind, step, Function.iterate_zero, id_eq,
      Option.some.injEq] at h ⊢
    rw [h]
  | succ n ih =>
    -- Use the decomposition lemma: cfg evals to some intermediate c in n steps,
    -- and then c steps to haltCfg
    -- obtain ⟨c, hc_n, hc_step⟩ := EvalsToInTime.succ_decompose hf.tm.step cfg haltCfg n h
    rw [EvalsToInTime.succ_iff] at h ⊢
    obtain ⟨c, hc_n, hc_step⟩ := h
    use liftCompCfg_left_or_right hf hg c
    constructor
    · apply ih
      · exact hcfg
      · exact hc_n
    · cases c with
      | mk state OTape =>
        cases state with
        | none =>
          simp_all
        | some q =>
          rw [← map_liftCompCfg_left_or_right_step hf hg ⟨some q, OTape⟩ (by simp)]
          simp only [hc_step, Option.map_some]


/--
Simulation for the first phase of the composed computer.
When the first machine runs from start to halt, the composed machine
runs from start (with Sum.inl state) to Sum.inr hg.tm.q₀ (the start of the second phase).
This takes the same number of steps because the halt transition becomes a transition to the
second machine.
-/
theorem comp_left_simulation {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : ComputableInTime  f) (hg : ComputableInTime  g)
    (a : List Bool)
    (hf_outputsFun :
      EvalsToWithinTime hf.tm.step
        { state := some hf.tm.q₀, OTape := OTape.mk₁ ( a) }
        (some { state := none, OTape := OTape.mk₁ ( (f a)) })
        (hf.time ( a).length)) :
    EvalsToWithinTime (compComputer hf hg).step
      { state := some (Sum.inl hf.tm.q₀), OTape := OTape.mk₁ ( a) }
      (some { state := some (Sum.inr hg.tm.q₀), OTape := OTape.mk₁ ( (f a)) })
      (hf.time ( a).length) := by
  obtain ⟨steps, hsteps_le, hsteps_eval⟩ := hf_outputsFun
  use steps
  constructor
  · exact hsteps_le
  · have := comp_left_simulation_general hf hg
      { state := some hf.tm.q₀, OTape := OTape.mk₁ ( a) }
      (by simp)
      { state := none, OTape := OTape.mk₁ ( (f a)) }
      steps
      hsteps_eval
    simp only [liftCompCfg_left_or_right] at this
    exact this

/-- Simulation lemma for the second machine in the composed computer -/
theorem comp_right_simulation
    {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : ComputableInTime  f) (hg : ComputableInTime g)
    (x : hg.tm.Cfg) (y : Option hg.tm.Cfg) (m : ℕ)
    (h : EvalsToWithinTime hg.tm.step x y m) :
    EvalsToWithinTime (compComputer hf hg).step
      (liftCompCfg_right hf hg x)
      (Option.map (liftCompCfg_right hf hg) y)
      m := by
  exact EvalsToWithinTime.map hg.tm.step (compComputer hf hg).step
    (liftCompCfg_right hf hg) (map_liftCompCfg_right_step hf hg) x y m h




lemma output_length_le_input_length_add_time (tm : BinTM0) (l l' : List Bool) (t : ℕ)
    (h : tm.OutputsWithinTime l (some l') t) :
    l'.length ≤ max 1 l.length + t := by
  unfold OutputsWithinTime at h
  obtain ⟨steps, hsteps_le, hevals⟩ := h
  replace hevals := hevals.small_change
  specialize hevals (Cfg.space_used tm)
  simp only [Cfg.space_used_initCfg, Cfg.space_used_haltCfg] at hevals
  suffices l'.length ≤ max 1 l.length + steps
    by omega
  specialize hevals fun a b hstep ↦ Cfg.space_used_step a b (Option.mem_def.mp hstep)
  omega

/--
A composition for ComputableInTime.

If f and g are computed by turing machines M₁ and M₂
then we can construct a turing machine M which computes g ∘ f by first running M₁
and then, when M₁ halts, transitioning to the start state of M₂ and running M₂.

This results in time bounded by the amount of time taken by M₁ plus the maximum time taken by M₂ on
inputs of length of the maximum output length of M₁ for that input size (which is itself bounded by
the time taken by M₁).

Note that we require the time function of the second machine to be monotone;
this is to ensure that if the first machine returns an output
which is shorter than the maximum possible length of output for that input size,
then the time bound for the second machine still holds for that shorter input to the second machine.

TODO refactor out the definition of the composed TM.
Prove separately that it
evals to the intermediate state from the start state and
then from the intermediate state to the final state.
-/
def ComputableInTime.comp
    {f : List Bool → List Bool} {g : List Bool → List Bool}
    (hf : ComputableInTime  f)
    (hg : ComputableInTime g)
    (h_mono : Monotone hg.time) :
    (ComputableInTime (g ∘ f)) where
  tm := compComputer hf hg
  time l := (hf.time l) + hg.time (max 1 l + hf.time l)
  outputsFun a := by
    have hf_outputsFun := hf.outputsFun a
    have hg_outputsFun := hg.outputsFun (f a)
    simp only [OutputsWithinTime, initCfg, compComputer_q₀_eq, Function.comp_apply,
      Option.map_some, haltCfg] at hg_outputsFun hf_outputsFun ⊢
    -- The computer evals a to f a in time hf.time ( a)
    have h_a_evalsTo_f_a :
        EvalsToWithinTime (compComputer hf hg).step
          { state := some (Sum.inl hf.tm.q₀), OTape := OTape.mk₁ ( a) }
          (some { state := some (Sum.inr hg.tm.q₀), OTape := OTape.mk₁ ( ((f a))) })
          (hf.time ( a).length) :=
      comp_left_simulation hf hg a hf_outputsFun
    have h_f_a_evalsTo_g_f_a :
        EvalsToWithinTime (compComputer hf hg).step
          { state := some (Sum.inr hg.tm.q₀), OTape := OTape.mk₁ ( ((f a))) }
          (some { state := none, OTape := OTape.mk₁ ( ((g (f a)))) })
          (hg.time ( ((f a))).length) := by
      -- Use the simulation lemma for the second machine
      have := comp_right_simulation hf hg
        { state := some hg.tm.q₀, OTape := OTape.mk₁ ( (f a)) }
        (some { state := none, OTape := OTape.mk₁ ( (g (f a))) })
        (hg.time ( (f a)).length)
        hg_outputsFun
      simp only [liftCompCfg_right, Option.map_some] at this
      exact this
    have h_a_evalsTo_g_f_a :=
      EvalsToWithinTime.trans
        (compComputer hf hg).step _ _ _ _ _ h_a_evalsTo_f_a h_f_a_evalsTo_g_f_a
    apply EvalsToWithinTime.mono_time _ _ _ h_a_evalsTo_g_f_a
    nth_rw 1 [← add_comm]
    apply add_le_add
    · omega
    · apply h_mono
      -- Use the lemma about output length being bounded by input length + time
      exact output_length_le_input_length_add_time hf.tm _ _ _ (hf.outputsFun a)

end

end BinTM0

end Turing
