import SwapGreedy.Proofs.SmallComponents
import SwapGreedy.Proofs.Robustness
import SwapGreedy.Proofs.SGRun
import SwapGreedy.Proofs.Existence
import SwapGreedy.Proofs.PredictionError
import SwapGreedy.Proofs.ConsistencyRobustness

/-!
# Conclusion: the main theorems for `δ`-SwapGreedy

`Run.toGreedy` shows that `δ`-SwapGreedy satisfies the algorithmic inequalities, and
`Greedy.prefix_le` (`SmallComponents.lean`) gives the competitive ratio `η · λ̂` of
`thmUpper` for every prefix.
-/

namespace SwapGreedy

variable {n : ℕ} {S : Instance n}

/-- `δ`-SwapGreedy from a `c`-optimal identity is `c · λ̂`-competitive. -/
theorem Run.competitive {δ : ℝ} (R : Run δ S) (hδ : 1 ≤ δ) {c : ℝ} (hc : 1 ≤ c)
    (hloc : EtaOptimal S c) : CompetitiveSchedule S (c * lamHat δ) R.result :=
  competitive_of_forall_prefix fun _ σ => (R.toGreedy hδ).prefix_le hδ hc hloc σ

/-! ## The algorithm of `Algorithms.lean` -/

/-- `swapGreedy δ` is `η ↦ η · λ̂`-competitive. -/
theorem swapGreedy_competitive_aux (δ : ℝ) (hδ : 1 ≤ δ) :
    Algorithm.Competitive (fun η => η * lamHat δ) (swapGreedy δ) := by
  intro n S hfin
  obtain ⟨R, hR⟩ := Run.isSGResult_iff.mp (isSGResult_swapGreedy δ S)
  exact hR ▸ R.competitive hδ (one_le_predictionError hfin) (etaOptimal_predictionError hfin)

/-- `prop:robustness` for `swapGreedy δ`: for `δ ≥ 1` its output on every instance is
`(1 + δ)`-competitive. -/
theorem swapGreedy_competitiveSchedule_one_add (δ : ℝ) (hδ : 1 ≤ δ) (S : Instance n) :
    CompetitiveSchedule S (1 + δ) (swapGreedy δ S) := by
  obtain ⟨R, hR⟩ := Run.isSGResult_iff.mp (isSGResult_swapGreedy δ S)
  exact hR ▸ R.robust hδ

/-- The main theorem `swapGreedy_robust`: `swapGreedy δ` is `(1 + δ)`-robust. -/
theorem swapGreedy_robust_aux (δ : ℝ) (hδ : 1 ≤ δ) :
    Algorithm.Robust (1 + δ) (swapGreedy δ) :=
  fun _ S _ => swapGreedy_competitiveSchedule_one_add δ hδ S

/-- The main theorem `swapGreedy_competitive` (`thm:main`): `swapGreedy δ` is
`η ↦ min(η · max(δ, 1 + 1/δ), 1 + δ)`-competitive. -/
theorem swapGreedy_competitive_min_aux (δ : ℝ) (hδ : 1 ≤ δ) :
    Algorithm.Competitive (fun η => min (η * max δ (1 + 1 / δ)) (1 + δ))
      (swapGreedy δ) :=
  fun _ S hfin => (swapGreedy_competitive_aux δ hδ S hfin).min
    (swapGreedy_competitiveSchedule_one_add δ hδ S)

/-- `swapGreedy δ` is `λ̂`-consistent. -/
theorem swapGreedy_consistent_aux (δ : ℝ) (hδ : 1 ≤ δ) :
    Algorithm.Consistent (lamHat δ) (swapGreedy δ) := by
  simpa using (swapGreedy_competitive_aux δ hδ).consistent

end SwapGreedy
