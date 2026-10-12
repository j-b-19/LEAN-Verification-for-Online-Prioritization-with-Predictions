import SwapGreedy.Proofs.SGRun

/-!
# Robustness

`prop:robustness` of `latex/swap_greedy.tex`: for `δ ≥ 1`, every run of `δ`-SwapGreedy on a
instance is `(1 + δ)`-competitive, whatever the prediction quality.

The proof follows the paper. For a stopping step `k` and a comparison schedule `σ`, the item
`σ(t)` collected at step `t < k` is

* either collected by `δ`-SwapGreedy at an earlier step `p < t`, so `σ(t)(t) ≤ σ(t)(p) = v_p`
  by (D); this is charged to `a_{σ(t)} = v_p`,
* or available at step `t`, so `σ(t)(t) ≤ δ · v_t` by (A) (`Run.le_mul_of_available`); this
  is charged to `b_t = δ · v_t`.

Summing, `f_k(σ) ≤ ∑_i a_i + ∑_t b_t = (1 + δ) · f_k(π)`.
-/

namespace SwapGreedy

open Finset

variable {n : ℕ} {δ : ℝ} {S : Instance n}

namespace Run

variable (R : Run δ S)

/-- `prop:robustness`: for `δ ≥ 1`, a run of `δ`-SwapGreedy is `(1 + δ)`-competitive on
every instance. -/
theorem robust (hδ : 1 ≤ δ) : CompetitiveSchedule S (1 + δ) R.result := by
  classical
  intro k hk σ
  -- `v p` is the value collected at step `p < k`, `a i` the value collected with item `i`
  let v : Fin k → ℝ := fun p => S (R.result (Fin.castLE hk p)) (Fin.castLE hk p)
  let a : Fin n → ℝ := fun i => ∑ p : Fin k, if R.result (Fin.castLE hk p) = i then v p else 0
  have hv_nonneg : ∀ p, 0 ≤ v p := fun p => S.nonneg _ _
  have ha_nonneg : ∀ i, 0 ≤ a i := fun i =>
    sum_nonneg fun p _ => by split_ifs; exacts [hv_nonneg p, le_rfl]
  have hsum_a : ∑ i, a i = ∑ p, v p := by
    simp only [a]
    rw [sum_comm]
    simp
  have hbound : ∀ t : Fin k, S (σ t) (Fin.castLE hk t) ≤ a (σ t) + δ * v t := by
    intro t
    by_cases hA : ∃ p : Fin k, p < t ∧ R.result (Fin.castLE hk p) = σ t
    · -- `σ(t)` was collected at an earlier step `p`
      obtain ⟨p, hpt, hp⟩ := hA
      have h1 : S (σ t) (Fin.castLE hk t) ≤ v p := by
        simp only [v]
        rw [hp]
        exact S.antitone _ (show Fin.castLE hk p ≤ Fin.castLE hk t from hpt.le)
      have h2 : v p ≤ a (σ t) := by
        have := single_le_sum
          (f := fun p' => if R.result (Fin.castLE hk p') = σ t then v p' else 0)
          (fun p' _ => by dsimp only; split_ifs; exacts [hv_nonneg p', le_rfl]) (mem_univ p)
        simpa [hp] using this
      nlinarith [hv_nonneg t]
    · -- `σ(t)` is available at step `t`
      push_neg at hA
      have hav : ∀ p : Fin n, p < Fin.castLE hk t → R.result p ≠ σ t := by
        intro p hp
        have hpk : (p : ℕ) < k := by
          have := t.isLt
          simp only [Fin.lt_def, Fin.val_castLE] at hp
          omega
        have := hA ⟨p, hpk⟩ (by simpa [Fin.lt_def] using hp)
        simpa using this
      have := R.le_mul_of_available hδ hav
      linarith [ha_nonneg (σ t)]
  calc value S hk σ = ∑ t, S (σ t) (Fin.castLE hk t) := rfl
    _ ≤ ∑ t, (a (σ t) + δ * v t) := sum_le_sum fun t _ => hbound t
    _ = ∑ t, a (σ t) + δ * ∑ t, v t := by rw [sum_add_distrib, mul_sum]
    _ ≤ ∑ i, a i + δ * ∑ t, v t := by
        gcongr ?_ + _
        rw [← sum_map univ σ a]
        exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => ha_nonneg i
    _ = (1 + δ) * value S hk (R.result ∘ Fin.castLE hk) := by
        rw [hsum_a]
        simp only [value, v, Function.comp_apply]
        ring

end Run

end SwapGreedy
