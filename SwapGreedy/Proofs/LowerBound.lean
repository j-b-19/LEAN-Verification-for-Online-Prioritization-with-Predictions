import SwapGreedy.Proofs.ConsistencyRobustness
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.BigOperators.Fin
import SwapGreedy.Proofs.Splitting
import SwapGreedy.Proofs.GoldenRatio

/-!
# The consistency-robustness trade-off

The lower bound of `latex/swap_greedy.tex`, for online algorithms on instances of size
two. For a parameter `x > 0` the two instances

`S  = ![![1, 0], ![x, x]]`  and  `S' = ![![1, 1], ![x, 0]]`

have the same first column, so an online algorithm collects the same item at step `0` on
both. On `S` the prediction `id` is perfect; on `S'` it is not. Collecting item `0` first
costs a factor `x` of consistency on `S` and a factor `1 + x` of robustness on `S'`,
collecting item `1` first costs a factor `1 + 1/x` of consistency on `S` (`lb_dichotomy`).

Taking `x = φ` gives `φ ≤ c`, `x = 1` gives `2 ≤ r`, and letting `x` tend to `1/(c-1)`
gives `1 ≤ (c - 1) * (r - 1)`, i.e. the trade-off `c/(c-1) ≤ r`.
-/

namespace SwapGreedy

open Finset

variable {x : ℝ}

/-- The instance on which the prediction `id` is perfect. -/
def lbMatrix (x : ℝ) : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![x, x]]

/-- The instance with the same first column on which `id` is a bad prediction. -/
def lbMatrix' (x : ℝ) : Fin 2 → Fin 2 → ℝ := ![![1, 1], ![x, 0]]

theorem lbMatrix_00 : lbMatrix x 0 0 = 1 := rfl
theorem lbMatrix_01 : lbMatrix x 0 1 = 0 := rfl
theorem lbMatrix_10 : lbMatrix x 1 0 = x := rfl
theorem lbMatrix_11 : lbMatrix x 1 1 = x := rfl
theorem lbMatrix'_00 : lbMatrix' x 0 0 = 1 := rfl
theorem lbMatrix'_01 : lbMatrix' x 0 1 = 1 := rfl
theorem lbMatrix'_10 : lbMatrix' x 1 0 = x := rfl
theorem lbMatrix'_11 : lbMatrix' x 1 1 = 0 := rfl

/-! ## The two instances -/

/-- The first matrix as an instance. -/
def lbInstance (hx : 0 ≤ x) : Instance 2 where
  S := lbMatrix x
  nonneg i t := by fin_cases i <;> fin_cases t <;> simp [lbMatrix, hx]
  antitone i := by
    intro a b hab
    fin_cases i <;> fin_cases a <;> fin_cases b <;> simp_all [lbMatrix, Fin.le_def]

/-- The second matrix as an instance. -/
def lbInstance' (hx : 0 ≤ x) : Instance 2 where
  S := lbMatrix' x
  nonneg i t := by fin_cases i <;> fin_cases t <;> simp [lbMatrix', hx]
  antitone i := by
    intro a b hab
    fin_cases i <;> fin_cases a <;> fin_cases b <;> simp_all [lbMatrix', Fin.le_def]

@[simp] theorem lbInstance_S (hx : 0 ≤ x) : (lbInstance hx).S = lbMatrix x := rfl
@[simp] theorem lbInstance'_S (hx : 0 ≤ x) : (lbInstance' hx).S = lbMatrix' x := rfl

/-- An injective map of `Fin 2` is the identity or the transposition. -/
theorem fin_two_cases {π : Fin 2 → Fin 2} (h : Function.Injective π) :
    (π 0 = 0 ∧ π 1 = 1) ∨ (π 0 = 1 ∧ π 1 = 0) := by
  have h01 : π 0 ≠ π 1 := fun he => by simpa using h he
  revert h01
  generalize π 0 = a
  generalize π 1 = b
  revert a b
  decide

/-- On `Fin 2` there are only the identity and the transposition. -/
theorem perm_two (τ : Equiv.Perm (Fin 2)) : τ = 1 ∨ τ = Equiv.swap 0 1 := by
  rcases fin_two_cases τ.injective with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl (Equiv.ext fun t => by fin_cases t <;> simpa using ‹_›)
  · refine Or.inr (Equiv.ext fun t => ?_)
    fin_cases t
    · simpa [Equiv.swap_apply_left] using h0
    · simpa [Equiv.swap_apply_right] using h1

/-- A sum over the support of the transposition of `Fin 2`. -/
theorem sum_support_swap (f : Fin 2 → ℝ) :
    ∑ t ∈ (Equiv.swap (0 : Fin 2) 1).support, f t = f 0 + f 1 := by
  rw [Equiv.Perm.support_swap (by decide)]
  rw [Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)]

/-- On the first instance the prediction is perfect. -/
theorem lbInstance_etaOptimal (hx : 0 ≤ x) : EtaOptimal (lbInstance hx) 1 := by
  refine etaOptimal_of_perm le_rfl fun τ => ?_
  rcases perm_two τ with rfl | rfl
  · simp
  · rw [sum_support_swap, sum_support_swap]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, lbInstance_S, lbMatrix_00,
      lbMatrix_01, lbMatrix_10, lbMatrix_11, one_mul]
    linarith

theorem lbInstance_predictionError (hx : 0 ≤ x) : PredictionError (lbInstance hx) = 1 :=
  predictionError_eq_one_iff.mpr (lbInstance_etaOptimal hx)

/-- On the second instance the identity is `(1 + x)`-optimal, so the prediction
error is finite. -/
theorem lbInstance'_error_finite (hx : 0 ≤ x) : ∃ η : ℝ, EtaOptimal (lbInstance' hx) η := by
  refine ⟨1 + x, etaOptimal_of_perm (by linarith) fun τ => ?_⟩
  rcases perm_two τ with rfl | rfl
  · simp
  · rw [sum_support_swap, sum_support_swap]
    simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, lbInstance'_S, lbMatrix'_00,
      lbMatrix'_01, lbMatrix'_10, lbMatrix'_11]
    nlinarith

/-! ## Values on the two instances -/

theorem value_two (S : Instance 2) (σ : Fin 2 → Fin 2) :
    value S (le_refl 2) σ = S (σ 0) 0 + S (σ 1) 1 := by
  simp [value, Fin.sum_univ_two]

theorem value_one (S : Instance 2) (σ : Fin 1 → Fin 2) :
    value S (by norm_num : 1 ≤ 2) σ = S (σ 0) 0 := by
  simp [value]

/-! ## The trade-off -/

variable {A : Algorithm}

/-- The case analysis of the lower bound. An online algorithm collects the same item at
step `0` on the two instances, and either choice is expensive: item `0` costs a factor `x`
of consistency on `S` and a factor `1 + x` of robustness on `S'`, item `1` costs a factor
`1 + 1/x` of consistency on `S`. -/
theorem lb_dichotomy (hon : A.Online) (hx : 0 < x) :
    ((∀ c : ℝ, A.Consistent c → x ≤ c) ∧ ∀ r : ℝ, A.Robust r → 1 + x ≤ r) ∨
      ∀ c : ℝ, A.Consistent c → 1 + 1 / x ≤ c := by
  have hx0 : (0:ℝ) ≤ x := hx.le
  have hinj : Function.Injective (A (lbInstance hx0)) :=
    (A (lbInstance hx0)).injective
  have hinj' : Function.Injective (A (lbInstance' hx0)) :=
    (A (lbInstance' hx0)).injective
  -- the two instances agree in their first column
  have hsame : A (lbInstance hx0) 0 = A (lbInstance' hx0) 0 := by
    refine hon _ _ 0 fun i s hs => ?_
    have : s = 0 := le_antisymm hs (Fin.zero_le _)
    subst this
    fin_cases i <;> rfl
  rcases fin_two_cases hinj with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · -- the algorithm collects item `0` at step `0`
    obtain ⟨h0', h1'⟩ : A (lbInstance' hx0) 0 = 0 ∧ A (lbInstance' hx0) 1 = 1 := by
      rcases fin_two_cases hinj' with h | h
      · exact h
      · exact absurd (hsame ▸ h0) (by rw [h.1]; decide)
    refine Or.inl ⟨fun c hc => ?_, fun r hr => ?_⟩
    · -- consistency on `S` at the stopping step `1`, against item `1`
      have h := hc (lbInstance hx0) (lbInstance_predictionError hx0) 1
        (by norm_num) ⟨![1], fun a b _ => Subsingleton.elim a b⟩
      rw [value_one, value_one] at h
      simpa [h0, lbInstance_S, lbMatrix_00, lbMatrix_10] using h
    · -- robustness on `S'` at the stopping step `2`, against the swapped schedule
      have h := hr (lbInstance' hx0)
        (lbInstance'_error_finite hx0) 2 le_rfl (Equiv.swap (0 : Fin 2) 1).toEmbedding
      rw [value_two, value_two] at h
      simp only [Equiv.coe_toEmbedding, Equiv.swap_apply_left, Equiv.swap_apply_right,
        Function.comp_apply, Fin.castLE_rfl, id_eq, h0', h1', lbInstance'_S, lbMatrix'_00,
        lbMatrix'_01, lbMatrix'_10, lbMatrix'_11, add_zero, mul_one] at h
      linarith
  · -- the algorithm collects item `1` at step `0` and item `0` at step `1`
    refine Or.inr fun c hc => ?_
    have h := hc (lbInstance hx0) (lbInstance_predictionError hx0) 2
      le_rfl (Function.Embedding.refl _)
    rw [value_two, value_two] at h
    simp only [Function.Embedding.coe_refl, id_eq, Function.comp_apply, Fin.castLE_rfl, h0, h1,
      lbInstance_S, lbMatrix_00, lbMatrix_01, lbMatrix_10, lbMatrix_11, add_zero] at h
    rw [← sub_nonneg, show c - (1 + 1 / x) = (c * x - (1 + x)) / x by field_simp; ring]
    exact div_nonneg (by linarith) hx.le

/-- **No online algorithm is better than `φ`-consistent.** -/
theorem φ_le_of_consistent (hon : A.Online) {c : ℝ} (hc : A.Consistent c) :
    φ ≤ c := by
  have hφ : (0:ℝ) < φ := zero_lt_one.trans_le one_le_φ
  have hone : 1 + 1 / φ = φ := by
    field_simp
    nlinarith [φ_sq]
  rcases lb_dichotomy hon hφ with ⟨h, -⟩ | h
  · exact h c hc
  · exact hone ▸ h c hc

/-- **No online algorithm is better than `2`-robust.** -/
theorem two_le_of_robust (hon : A.Online) {r : ℝ} (hr : A.Robust r) :
    2 ≤ r := by
  rcases lb_dichotomy hon one_pos with ⟨-, h⟩ | h
  · linarith [h r hr]
  · linarith [h r (Algorithm.Competitive.consistent hr)]

/-- `(c - 1) · (r - 1) ≥ 1` for every online algorithm that is `c`-consistent and
`r`-robust. -/
theorem one_le_tradeoff (hon : A.Online) {c r : ℝ} (hc : A.Consistent c)
    (hr : A.Robust r) : 1 ≤ (c - 1) * (r - 1) := by
  have hφ : (1:ℝ) < φ := by nlinarith [φ_sq, one_le_φ]
  have hc1 : 1 < c := hφ.trans_le (φ_le_of_consistent hon hc)
  have hc1' : (0:ℝ) < c - 1 := by linarith
  by_contra hcon
  push_neg at hcon
  have hrx : r - 1 < 1 / (c - 1) := by
    rw [lt_div_iff₀ hc1']
    nlinarith
  have hinv : (0:ℝ) < 1 / (c - 1) := by positivity
  set x := (max (r - 1) 0 + 1 / (c - 1)) / 2 with hxdef
  have hmax : max (r - 1) 0 < 1 / (c - 1) := max_lt hrx hinv
  have hmax0 : (0:ℝ) ≤ max (r - 1) 0 := le_max_right _ _
  have hx0 : 0 < x := by rw [hxdef]; linarith
  have hxlt : x < 1 / (c - 1) := by rw [hxdef]; linarith
  have hxgt : r - 1 < x := by
    have : r - 1 ≤ max (r - 1) 0 := le_max_left _ _
    rw [hxdef]; linarith
  rcases lb_dichotomy hon hx0 with ⟨-, h⟩ | h
  · linarith [h r hr]
  · have hxc : x * (c - 1) < 1 := by
      rw [← lt_div_iff₀ hc1']
      exact hxlt
    have : c - 1 < 1 / x := by rw [lt_div_iff₀ hx0]; linarith
    linarith [h c hc]

/-- A `c`-consistent online algorithm is at best `c/(c-1)`-robust. -/
theorem div_le_of_consistent_of_robust (hon : A.Online) {c r : ℝ}
    (hc : A.Consistent c) (hr : A.Robust r) : c / (c - 1) ≤ r := by
  have hφ : (1:ℝ) < φ := by nlinarith [φ_sq, one_le_φ]
  have hc1 : 1 < c := hφ.trans_le (φ_le_of_consistent hon hc)
  have h := one_le_tradeoff hon hc hr
  rw [div_le_iff₀ (by linarith : (0:ℝ) < c - 1)]; nlinarith

end SwapGreedy
