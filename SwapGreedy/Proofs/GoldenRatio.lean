import SwapGreedy.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The golden ratio

`φ² = φ + 1` and the bounds on `φ` used in the proofs.
-/

namespace SwapGreedy

theorem one_le_φ : 1 ≤ φ := by
  unfold φ
  nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

theorem φ_sq : φ ^ 2 = φ + 1 := by
  unfold φ
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

theorem φ_pos : 0 < φ := zero_lt_one.trans_le one_le_φ

theorem φ_le_two : φ ≤ 2 := by nlinarith [φ_sq, one_le_φ]

/-- `1/φ² + 1/φ = 1`. -/
theorem inv_φ_sq_add_inv_φ : 1 / φ ^ 2 + 1 / φ = 1 := by
  have := φ_pos
  field_simp
  nlinarith [φ_sq]

end SwapGreedy
