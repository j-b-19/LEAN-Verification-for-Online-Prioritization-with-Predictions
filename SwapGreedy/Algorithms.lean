import SwapGreedy.Defs

/-! The algorithm `δ`-SwapGreedy (human-checked). -/

namespace SwapGreedy

variable {n : ℕ}

/-- Step `t` turns schedule `x` into `y`: `x s` is the available item of maximal value at step `t` with the smallest index, swapped into position `t` if it beats the occupant by more than `δ` or the occupant is not item `t`. -/
def Step (δ : ℝ) (S : Instance n) (t : Fin n) (x y : Fin n → Fin n) : Prop :=
  ∃ s : Fin n, t ≤ s ∧
    (∀ s' : Fin n, t ≤ s' → S (x s') t ≤ S (x s) t) ∧
    (∀ s' : Fin n, t ≤ s' → S (x s') t = S (x s) t → x s ≤ x s') ∧
    y = if δ * S (x t) t < S (x s) t ∨ x t ≠ t then x ∘ Equiv.swap t s else x

/-- `π` is the result of running the steps `0, …, n-1` from the identity. -/
def IsSGResult (δ : ℝ) (S : Instance n) (π : Fin n → Fin n) : Prop :=
  ∃ πₜ : ℕ → Fin n → Fin n,
    πₜ 0 = id ∧
    (∀ t : Fin n, Step δ S t (πₜ t) (πₜ ((t : ℕ) + 1))) ∧
    πₜ n = π

open Classical in
/-- `δ`-SwapGreedy as an algorithm (the fallback `else` branch is never taken). -/
noncomputable def swapGreedy (δ : ℝ) : Algorithm := fun ⦃n⦄ S =>
  if h : ∃ π : Fin n ↪ Fin n, IsSGResult δ S π then h.choose else Function.Embedding.refl _

end SwapGreedy
