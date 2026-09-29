import Mathlib.Computability.StateTransition
import Cslib.Foundations.Relation.Confluence

/-! # Non-deterministic state transisions

- Can we generalise `f : σ → Option σ` and `f : σ → List σ` to any monadic codomain?
- Is a general "find" function for `f : σ →. σ` and `p : σ → Bool` useful?
-/

universe u

variable {α β γ σ : Type*}

open Part PFun Sum

lemma PFun.exists_inl_mem_of_mem_fix {f : α →. β ⊕ α} {a : α} {b : β} (hb : b ∈ f.fix a) :
    ∃ a', inl b ∈ f a' :=
  PFun.fixInduction' hb (fun a' ha' _ ↦ ⟨a', ha'⟩) (fun _ _ hb₁ _ ih _ ↦ ih hb₁) hb

def iterFind (f : σ → σ) (p : σ → Bool) : σ →. σ :=
  PFun.fix <| PFun.lift fun (x : σ) ↦ (p x).rec (inr <| f x) (inl x)

variable {f : σ → σ} {p : σ → Bool}

lemma iterFind_stop {x : σ} (h : p x = true) : x ∈ iterFind f p x :=
  fix_stop <| by simp [h]

lemma mem_iterFind_iff_of_true {x y : σ} (h : p x = true) : y ∈ iterFind f p x ↔ y = x := by
  grind [Part.mem_eq, iterFind_stop]

grind_pattern mem_iterFind_iff_of_true => y ∈ iterFind f p x where
  guard p x = true

alias ⟨eq_of_mem_iterFind_of_true, _⟩ := mem_iterFind_iff_of_true

lemma iterFind_fwd_eq {x : σ} (hx : p x = false) : iterFind f p x = iterFind f p (f x) :=
  fix_fwd_eq <| by simp [hx]

lemma iterFind_fwd {x y : σ} (h : y ∈ iterFind f p x) (hx : p x = false) :
    y ∈ iterFind f p (f x) := iterFind_fwd_eq hx ▸ h

grind_pattern iterFind_fwd => y ∈ iterFind f p x where
  guard p x = false

@[elab_as_elim]
def iterFindRec {y : σ} {C : σ → Sort u} {x : σ} (h : y ∈ iterFind f p x)
    (stop : (x : σ) → p x = true → y ∈ iterFind f p x → C x)
    (fwd : (x : σ) → p x = false → y ∈ iterFind f p x → ((x' : σ) → f x = x' → C x') → C x) : C x :=
  PFun.fixInduction h <| fun x' hmem ih ↦
    match hx' : p x' with
    | true => stop x' hx' hmem
    | false => fwd x' hx' hmem fun x'' heq ↦ ih x'' <| by simp [hx', heq]

lemma iterFindRec_true {y : σ} {C : σ → Sort u} {x : σ} (h : y ∈ iterFind f p x)
    (stop : (x : σ) → p x = true → y ∈ iterFind f p x → C x)
    (fwd : (x : σ) → p x = false → y ∈ iterFind f p x → ((x' : σ) → f x = x' → C x') → C x)
    (hx : p x = true) : iterFindRec h stop fwd = stop x hx h := by
  grind [iterFind, iterFindRec, fixInduction_spec]

lemma iterFindRec_false {y : σ} {C : σ → Sort u} {x : σ} (h : y ∈ iterFind f p x)
    (stop : (x : σ) → p x = true → y ∈ iterFind f p x → C x)
    (fwd : (x : σ) → p x = false → y ∈ iterFind f p x → ((x' : σ) → f x = x' → C x') → C x)
    (hx : p x = false) : iterFindRec h stop fwd =
      fwd x hx h (fun x' heq ↦ iterFindRec (x := x') (by grind) stop fwd) := by
  grind [iterFind, iterFindRec, fixInduction_spec]

lemma iterFind_spec {x y : σ} (h : y ∈ iterFind f p x) : p y :=
  iterFindRec h (by grind) (fun x _ _ ih ↦ ih (f x) rfl)

lemma eq_iterate_of_mem_iterFind {x y : σ} (h : y ∈ iterFind f p x) : ∃ n, f^[n] x = y := by
  refine iterFindRec h ?_ ?_
  · intro x hx hmem
    exact ⟨0, (eq_of_mem_iterFind_of_true hx hmem).symm⟩
  · intro x hx hmem ih
    obtain ⟨n, hn⟩ := ih (f x) rfl
    exact ⟨n + 1, hn⟩

lemma exists_le_iterate_mem {x : σ} {n : ℕ} (h : p (f^[n] x) = true) :
    ∃ m ≤ n, f^[m] x ∈ iterFind f p x := by
  induction n generalizing x with
  | zero => exact ⟨0, le_rfl, iterFind_stop h⟩
  | succ n ih =>
    rcases hx : p x
    · obtain ⟨m, hle, hm⟩ := ih h
      refine ⟨m + 1, Nat.add_le_add_right hle 1, ?_⟩
      rwa [iterFind_fwd_eq hx]
    · exact ⟨0, Nat.zero_le _, iterFind_stop hx⟩

lemma dom_iterFind_apply_iff (x : σ) : (iterFind f p x).Dom ↔ ∃ n, p (f^[n] x) = true := by
  rw [Part.dom_iff_mem]
  constructor
  · intro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := eq_iterate_of_mem_iterFind hy
    use n, iterFind_spec hy
  · intro ⟨n, hn⟩
    obtain ⟨m, -, hm⟩ := exists_le_iterate_mem hn
    exact ⟨f^[m] x, hm⟩

-- section Prime

-- /-- Iterate `f` (possibly infinitely) until a value satisfying `p` is found. -/
-- def evalFind' (f : List σ → List σ) (p : σ → Bool) : List σ →. σ :=
--   PFun.fix <| PFun.lift fun (l : List σ) ↦ (f l).find? p |>.elim (Sum.inr (f l)) Sum.inl

-- lemma evalFind'_spec {x : σ} {l : List σ} (h : x ∈ evalFind' f p l) : p x := by
--   obtain ⟨l', _, h'⟩ := exists_inl_mem_of_mem_fix h
--   rcases heq : (f l').find? p
--   all_goals grind [PFun.coe_val, Part.get_some]

-- attribute [local implicit_reducible] PFun

-- lemma mem_evalFind'_iff {x : σ} {l : List σ} :
--     x ∈ evalFind' f p l ↔
--       x ∈ (f l).find? p ∨ (∀ y ∈ f l, p y = false) ∧ x ∈ evalFind' f p (f l) := by
--   rcases hl : (f l).find? p with (_ | x')
--   · rw [evalFind', mem_fix_iff]
--     simp [hl]
--     grind [List.find?_eq_none.mp hl]
--   · rw [evalFind', mem_fix_iff]
--     simp [hl]
--     grind [List.find?_isSome]

-- end Prime

-- def evalFind (f : σ → List σ) (p : σ → Bool) : σ →. σ :=
--   fun x ↦ if p x then Part.some x else evalFind' (List.flatMap f) p [x]

-- variable {f : σ → List σ} {p : σ → Bool} {x y : σ}

-- lemma evalFind_true (h : p x = true) : evalFind f p x = Part.some x := by
--   simp_all [evalFind]

-- lemma evalFind_false (h : p x = false) :
--     evalFind f p x = evalFind' (List.flatMap f) p [x] := by
--   simp_all [evalFind]

-- lemma evalFind_spec (h : y ∈ evalFind f p x) : p y := by
--   cases hx : p x
--   · rw [evalFind_false hx] at h
--     exact evalFind'_spec h
--   · suffices y = x from this ▸ hx
--     exact Part.mem_unique h <| Part.eq_some_iff.mp (evalFind_true hx)

-- lemma mem_evalFind_self_iff : x ∈ evalFind f p x ↔ p x := by
--   cases hx : p x
--   · grind [evalFind_spec]
--   · simp [← Part.eq_some_iff, evalFind_true hx]

-- lemma mem_evalFind_iff :
--     y ∈ evalFind f p x ↔ (x = y ∧ p x) ∨ (¬ p x ∧ ∃ z ∈ f x)

-- -- abbrev Function.RelEval (f : α → List β) (a : α) (b : β) : Prop := b ∈ f a

-- -- namespace Relation

-- -- def Catalogues (f : α → List β) (r : α → β → Prop) := ∀ a b, b ∈ f a ↔ r a b

-- -- lemma Catalogues.comp {f : α → List β} {g : β → List γ} {r : α → β → Prop} {s : β → γ → Prop}
-- --     (h : Catalogues f r) (h' : Catalogues g s) :
-- --     Catalogues (f · |>.flatMap g) (Comp r s) := by
-- --   intro a c
-- --   simp [List.mem_flatMap, h a, (h' · c), Comp]

-- -- end Relation
