import SwapGreedy.Proofs.SGRun
import Mathlib.Data.Fintype.Card

/-!
# Existence of results

Every loop iteration has a successor state, so `δ`-SwapGreedy has a result
on every instance; as every result is a schedule (`Run.result_injective`), the `Algorithm`
`swapGreedy δ` really returns one.
-/

namespace SwapGreedy

variable {n : ℕ}

/-! ## `δ`-SwapGreedy (`alg:swapgreedy`) -/

/-- Every schedule has a successor under the loop iteration of `δ`-SwapGreedy: take a
maximizer of `S(·, t)` among the positions `≥ t`, and among all of them the one holding the
smallest item. -/
theorem Step.exists_next (δ : ℝ) (S : Instance n) (t : Fin n) (x : Fin n → Fin n) :
    ∃ y, Step δ S t x y := by
  classical
  obtain ⟨s₀, hs₀, hmax₀⟩ := Finset.exists_max_image {s | t ≤ s}
    (fun s => S (x s) t) ⟨t, by simp⟩
  obtain ⟨s, hs, hmin⟩ := Finset.exists_min_image
    ({s | t ≤ s ∧ S (x s) t = S (x s₀) t} : Finset (Fin n)) (fun s => x s)
    ⟨s₀, by simpa using hs₀⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs hmin
  refine ⟨_, s, hs.1, fun s' h => ?_, fun s' h heq => hmin s' ⟨h, heq.trans hs.2⟩, rfl⟩
  rw [hs.2]
  exact hmax₀ s' (by simpa using h)

/-- The sequence of schedules of `δ`-SwapGreedy. -/
noncomputable def sgRun (δ : ℝ) (S : Instance n) : ℕ → Fin n → Fin n
  | 0 => id
  | t + 1 => if h : t < n then (Step.exists_next δ S ⟨t, h⟩ (sgRun δ S t)).choose
      else sgRun δ S t

theorem exists_isSGResult (δ : ℝ) (S : Instance n) :
    ∃ π, IsSGResult δ S π := by
  refine ⟨sgRun δ S n, sgRun δ S, rfl, fun t => ?_, rfl⟩
  simp only [sgRun, dif_pos t.isLt]
  exact (Step.exists_next δ S t _).choose_spec

/-- The `Algorithm` `swapGreedy δ` returns a result of `δ`-SwapGreedy. -/
theorem isSGResult_swapGreedy (δ : ℝ) (S : Instance n) :
    IsSGResult δ S (swapGreedy δ S) := by
  unfold swapGreedy
  split
  · next h => exact h.choose_spec
  · next h =>
    obtain ⟨π, hπ⟩ := exists_isSGResult δ S
    obtain ⟨R, rfl⟩ := Run.isSGResult_iff.mp hπ
    exact absurd ⟨⟨R.result, R.result_injective⟩, Run.isSGResult_iff.mpr ⟨R, rfl⟩⟩ h

end SwapGreedy
