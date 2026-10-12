import SwapGreedy.Proofs.Existence

/-!
# `δ`-SwapGreedy is online

The remark after `alg:swapgreedy` in `latex/swap_greedy.tex`: the item `π_SG(t)` only
depends on the first `t` columns of the instance.

A loop iteration at step `t` only reads column `t` of the instance (`Step.congr`), and with
the paper's tie-breaking it is deterministic on injective schedules (`Step.unique`). So two
runs on instances that agree up to column `t` pass through the same schedules up to step
`t + 1` (`Run.state_eq_of_agree`), and the item collected at step `t` is final from then on.
-/

namespace SwapGreedy

variable {n : ℕ} {δ : ℝ} {S S' : Instance n}

/-- A loop iteration at step `t` only reads column `t` of the instance. -/
theorem Step.congr {t : Fin n} {x y : Fin n → Fin n} (hcol : ∀ i, S i t = S' i t)
    (h : Step δ S t x y) : Step δ S' t x y := by
  obtain ⟨s, hts, hmax, htie, hy⟩ := h
  exact ⟨s, hts, by simpa [hcol] using hmax, by simpa [hcol] using htie,
    by simpa [hcol] using hy⟩

/-- With the paper's tie-breaking, a loop iteration is deterministic on an injective
schedule: the maximizer with the smallest item index sits at a single position. -/
theorem Step.unique {t : Fin n} {x y y' : Fin n → Fin n} (hx : Function.Injective x)
    (h : Step δ S t x y) (h' : Step δ S t x y') : y = y' := by
  obtain ⟨s, hts, hmax, htie, rfl⟩ := h
  obtain ⟨s', hts', hmax', htie', rfl⟩ := h'
  have hv : S (x s') t = S (x s) t := le_antisymm (hmax s' hts') (hmax' s hts)
  obtain rfl : s = s' := hx (le_antisymm (htie s' hts' hv) (htie' s hts hv.symm))
  rfl

/-- Runs on two instances that agree up to column `t` pass through the same schedules up
to the end of step `t`. -/
theorem Run.state_eq_of_agree (R : Run δ S) (R' : Run δ S') {t : Fin n}
    (hS : ∀ i s : Fin n, s ≤ t → S i s = S' i s) :
    ∀ j ≤ (t : ℕ) + 1, R.state j = R'.state j := by
  intro j
  induction j with
  | zero => intro _; rw [R.init, R'.init]
  | succ j ih =>
    intro hj
    have hjn : j < n := by omega
    have h1 : Step δ S ⟨j, hjn⟩ (R.state j) (R.state (j + 1)) := R.step ⟨j, hjn⟩
    have h2 : Step δ S' ⟨j, hjn⟩ (R'.state j) (R'.state (j + 1)) := R'.step ⟨j, hjn⟩
    rw [ih (by omega)] at h1
    exact Step.unique (R'.inv_state j hjn.le).2
      (h1.congr fun i => hS i _ (by rw [Fin.le_def]; simp; omega)) h2

/-- `swapGreedy δ` is online: on two instances that agree up to column `t` it collects the
same item at step `t`. -/
theorem swapGreedy_online_aux (δ : ℝ) : Algorithm.Online (swapGreedy δ) := by
  intro n S S' t hS
  obtain ⟨R, hR⟩ := Run.isSGResult_iff.mp (isSGResult_swapGreedy δ S)
  obtain ⟨R', hR'⟩ := Run.isSGResult_iff.mp (isSGResult_swapGreedy δ S')
  calc swapGreedy δ S t = R.result t := (congrFun hR t).symm
    _ = R.state ((t : ℕ) + 1) t := R.result_eq_succ t
    _ = R'.state ((t : ℕ) + 1) t := congrFun (R.state_eq_of_agree R' hS _ le_rfl) t
    _ = R'.result t := (R'.result_eq_succ t).symm
    _ = swapGreedy δ S' t := congrFun hR' t

end SwapGreedy
