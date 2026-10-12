import SwapGreedy.Algorithms
import SwapGreedy.Proofs.Conclusion
import SwapGreedy.Proofs.LowerBound
import SwapGreedy.Proofs.Online

/-! The main results (human-checked). -/

namespace SwapGreedy

/-! ## The lower bound (on instances of two steps) -/

/-- No online algorithm is better than `φ`-consistent. -/
theorem φ_le_consistency {A : Algorithm} {c : ℝ} (hon : A.Online) (hc : A.Consistent c) :
    φ ≤ c :=
  φ_le_of_consistent hon hc

/-- No online algorithm is better than `2`-robust. -/
theorem two_le_robustness {A : Algorithm} {r : ℝ} (hon : A.Online) (hr : A.Robust r) :
    2 ≤ r :=
  two_le_of_robust hon hr

/-- A `c`-consistent online algorithm is at best `c/(c-1)`-robust. -/
theorem consistency_robustness_tradeoff {A : Algorithm} {c r : ℝ}
    (hon : A.Online) (hc : A.Consistent c) (hr : A.Robust r) :
      c / (c - 1) ≤ r :=
  div_le_of_consistent_of_robust hon hc hr

/-! ## `δ`-SwapGreedy -/

/-- `δ`-SwapGreedy is online. -/
theorem swapGreedy_online {δ : ℝ} : (swapGreedy δ).Online :=
  swapGreedy_online_aux δ

/-- `δ`-SwapGreedy is `min(η · max(δ, 1 + 1/δ), 1 + δ)`-competitive for prediction error `η`. -/
theorem swapGreedy_competitive {δ : ℝ} (hδ : 1 ≤ δ) :
    (swapGreedy δ).Competitive (fun η => min (η * max δ (1 + 1 / δ)) (1 + δ))
       :=
  swapGreedy_competitive_min_aux δ hδ

/-- `δ`-SwapGreedy is `max(δ, 1 + 1/δ)`-consistent. -/
theorem swapGreedy_consistent {δ : ℝ} (hδ : 1 ≤ δ) :
    (swapGreedy δ).Consistent (max δ (1 + 1 / δ)) :=
  swapGreedy_consistent_aux δ hδ

/-- `δ`-SwapGreedy is `(1 + δ)`-robust. -/
theorem swapGreedy_robust {δ : ℝ} (hδ : 1 ≤ δ) :
    (swapGreedy δ).Robust (1 + δ) :=
  swapGreedy_robust_aux δ hδ

end SwapGreedy
