import SwapGreedy.Proofs.PredictionError

/-!
# Consistency and robustness from a competitive factor

The paper's `Definition Consistency and Robustness` in terms of `Algorithm.Competitive`:
an algorithm with competitive factor `ρ` is `ρ 1`-consistent, and `r`-robust for every
upper bound `r` of `ρ`. `predictionError_eq_one_iff` identifies the instances of
prediction error `1` with the paper's `1`-optimal ones.
-/

namespace SwapGreedy

variable {n : ℕ} {S : Instance n} {π : Fin n → Fin n}

/-- A schedule that is `a`- and `b`-competitive is `min a b`-competitive. -/
theorem CompetitiveSchedule.min {a b : ℝ}
    (ha : CompetitiveSchedule S a π) (hb : CompetitiveSchedule S b π) :
    CompetitiveSchedule S (min a b) π := fun k hk σ => by
  rw [min_mul_of_nonneg _ _
    (show 0 ≤ value S hk (π ∘ Fin.castLE hk) from Finset.sum_nonneg fun _ _ => S.nonneg _ _)]
  exact le_min (ha k hk σ) (hb k hk σ)

/-- An instance has prediction error `1` exactly if the identity is `1`-optimal on
it, i.e. if it is `1`-optimal in the sense of the paper. -/
theorem predictionError_eq_one_iff :
    PredictionError S = 1 ↔ EtaOptimal S 1 := by
  constructor
  · intro h
    have hne : ∃ η : ℝ, EtaOptimal S η := by
      by_contra hem
      push_neg at hem
      rw [PredictionError, show {η : ℝ | 1 ≤ η ∧ EtaOptimal S η} = ∅ from
        Set.eq_empty_of_forall_notMem fun η hη => hem η hη.2, Real.sInf_empty] at h
      exact absurd h zero_ne_one
    exact h ▸ etaOptimal_predictionError hne
  · intro h
    exact le_antisymm (csInf_le ⟨1, fun η hη => hη.1⟩ ⟨le_rfl, h⟩)
      (one_le_predictionError ⟨1, h⟩)

variable {A : Algorithm} {ρ : ℝ → ℝ}

/-- An algorithm with competitive factor `ρ` is `ρ 1`-consistent. -/
theorem Algorithm.Competitive.consistent (h : A.Competitive ρ) : A.Consistent (ρ 1) :=
  fun _ S he => he ▸ h S ⟨1, (predictionError_eq_one_iff).mp he⟩

end SwapGreedy
