import SwapGreedy.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The prediction error is attained

`PredictionError S` is defined as an infimum. On an instance on which the identity is
`η`-optimal for some `η`, that infimum is a minimum: the identity is
`PredictionError S`-optimal (`etaOptimal_predictionError`), and the error is `≥ 1`
(`one_le_predictionError`). These are the two facts needed to instantiate the theorems
about a `η`-optimal prediction at `η = PredictionError S`.
-/

namespace SwapGreedy

variable {n : ℕ} {S : Instance n}

/-- Local optimality gets weaker as the factor grows (for a non-negative instance). -/
theorem EtaOptimal.mono {η η' : ℝ} (h : EtaOptimal S η)
    (hle : η ≤ η') : EtaOptimal S η' := fun I J hJI μ =>
  (h I J hJI μ).trans (mul_le_mul_of_nonneg_right hle (Finset.sum_nonneg fun _ _ => S.nonneg _ _))

/-- The set of local optimality factors `≥ 1`, over which `PredictionError` takes the
infimum. -/
private def factors (S : Instance n) : Set ℝ := {η : ℝ | 1 ≤ η ∧ EtaOptimal S η}

private theorem factors_nonempty (h : ∃ η : ℝ, EtaOptimal S η) :
    (factors S).Nonempty := by
  obtain ⟨η, hη⟩ := h
  exact ⟨max η 1, le_max_right _ _, hη.mono (le_max_left _ _)⟩

/-- The prediction error is at least `1`. -/
theorem one_le_predictionError (h : ∃ η : ℝ, EtaOptimal S η) :
    1 ≤ PredictionError S :=
  le_csInf (factors_nonempty h) fun _ hη => hη.1

/-- The infimum defining the prediction error is attained: the identity is
`PredictionError S`-optimal. -/
theorem etaOptimal_predictionError
    (h : ∃ η : ℝ, EtaOptimal S η) : EtaOptimal S (PredictionError S) := by
  intro I J hJI μ
  have hb : 0 ≤ ∑ t ∈ I, S t t := Finset.sum_nonneg fun _ _ => S.nonneg _ _
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨η, hη, hlt⟩ := exists_lt_of_csInf_lt (factors_nonempty h)
    (show PredictionError S < PredictionError S + ε / (∑ t ∈ I, S t t + 1) by
      have : (0:ℝ) < ε / (∑ t ∈ I, S t t + 1) := by positivity
      linarith)
  have key := (hη.2 I J hJI μ).trans (mul_le_mul_of_nonneg_right hlt.le hb)
  have hbound : ε / (∑ t ∈ I, S t t + 1) * (∑ t ∈ I, S t t) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  nlinarith [key, hbound]

end SwapGreedy
