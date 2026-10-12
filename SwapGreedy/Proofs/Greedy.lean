import SwapGreedy.Algorithms
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Algorithmic inequalities

Section *Algorithmic Inequalities* of `latex/swap_greedy.tex`: the analysis only uses the
inequalities of `lem:PMA`, not the algorithm itself. `Greedy δ S` packages a schedule with
these inequalities (with `δ` for the paper's `λ`); `δ`-SwapGreedy produces such a schedule
(`Run.toGreedy`).

"Item `c` is available at step `t`", i.e. `c ∉ SG[t-1]`, is `∀ p < t, result p ≠ c`, and
`t ∉ SG[t]` is `∀ p ≤ t, result p ≠ t`.
-/

namespace SwapGreedy

variable {n : ℕ}

/-- A schedule `result` satisfying the inequalities (A), (M), (P) of `lem:PMA`. -/
structure Greedy (δ : ℝ) (S : Instance n) where
  result : Fin n → Fin n
  result_injective : Function.Injective result
  /-- (A): `c(s) ≤ δ · v_t` for every item `c` available at step `t` and every `s ≥ t`. -/
  ineq_A : ∀ {t c s : Fin n}, (∀ p : Fin n, p < t → result p ≠ c) → t ≤ s →
    S c s ≤ δ * S (result t) t
  /-- (M): if `SG(t) ≠ t`, then `c(s) ≤ v_t` for every item `c` available at step `t` and
  every `s ≥ t`. -/
  ineq_M : ∀ {t c s : Fin n}, result t ≠ t → (∀ p : Fin n, p < t → result p ≠ c) → t ≤ s →
    S c s ≤ S (result t) t
  /-- (P): if `t ∉ SG[t]`, then `δ · t(t) ≤ v_t`. -/
  ineq_P : ∀ {t : Fin n}, (∀ p : Fin n, p ≤ t → result p ≠ t) → δ * S t t ≤ S (result t) t

namespace Greedy

variable {δ : ℝ} {S : Instance n} (G : Greedy δ S)

theorem result_bijective : Function.Bijective G.result :=
  Finite.injective_iff_bijective.mp G.result_injective

/-- The collection time `t_c = SG⁻¹(c)` of item `c`. -/
noncomputable def collTime : Fin n → Fin n :=
  (Equiv.ofBijective G.result G.result_bijective).symm

theorem result_collTime (c : Fin n) : G.result (G.collTime c) = c :=
  Equiv.ofBijective_apply_symm_apply _ _ _

theorem collTime_result (t : Fin n) : G.collTime (G.result t) = t :=
  Equiv.ofBijective_symm_apply_apply _ _ _

theorem collTime_eq_iff {c t : Fin n} : G.collTime c = t ↔ G.result t = c :=
  ⟨fun h => h ▸ G.result_collTime c, fun h => h ▸ G.collTime_result t⟩

/-- Item `c` is available at step `t` iff it is collected at a step `≥ t`. -/
theorem available_iff {c t : Fin n} : (∀ p : Fin n, p < t → G.result p ≠ c) ↔ t ≤ G.collTime c := by
  constructor
  · intro h
    by_contra hlt
    exact h _ (not_le.mp hlt) (G.result_collTime c)
  · intro h p hp hpc
    rw [← G.collTime_eq_iff] at hpc
    exact absurd (hpc ▸ h) (not_le.mpr hp)

/-- `t ∉ SG[t]` iff item `t` is collected after step `t`. -/
theorem not_mem_iff {t : Fin n} : (∀ p : Fin n, p ≤ t → G.result p ≠ t) ↔ t < G.collTime t := by
  constructor
  · intro h
    by_contra hle
    exact h _ (not_lt.mp hle) (G.result_collTime t)
  · intro h p hp hpt
    rw [← G.collTime_eq_iff] at hpt
    exact absurd (hpt ▸ h) (not_lt.mpr hp)

end Greedy

end SwapGreedy
