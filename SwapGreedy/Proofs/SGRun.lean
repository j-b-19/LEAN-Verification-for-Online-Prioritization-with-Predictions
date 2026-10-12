import SwapGreedy.Proofs.Greedy
import Mathlib.Logic.Equiv.Basic

/-!
# Runs of `δ`-SwapGreedy and their algorithmic inequalities

`δ`-SwapGreedy (`Step δ S` in `Algorithms.lean`) always replaces an occupant `π(t) ≠ t`
(a delayed item) by the maximizer among the available items. The comparator factor `δ` is
arbitrary except where stated (`1 ≤ δ` for (A)). The tie-breaking is not used.

Facts about single steps and runs that do not use the comparator:
* positions before `t` are untouched and the schedule stays injective;
* the invariant `Inv j x`: at the start of step `j`, every position `s ≥ j` holds either
  its home item `s` or an item delayed before step `j`;
* for a run from the identity: the result is injective, an item not collected before `t`
  sits at a position `≥ t`, and if its index is `≥ t` it sits at its home position.

The inequalities: at every step `t`,
* (A) if `π(t) = t`, then `c(t) ≤ δ · t(t)` for every item `c` not collected before `t`
  (this needs `1 ≤ δ`);
* (M') if `π(t) ≠ t`, then `c(t) ≤ π(t)(t)` for every item `c` not collected before `t`
  (the collected item is a maximizer among all available items, delayed or not);
* (P) if `π(t) ≠ t` and item `t` is available at `t`, then `δ · t(t) ≤ π(t)(t)`.

Thus every run yields a `Greedy δ S l` for every `l`, without any further assumption:
steps collecting a delayed item satisfy (M') just like the "remaining" preemption steps.
-/

namespace SwapGreedy

variable {n : ℕ} {δ : ℝ} {S : Instance n}

/-! ## Single steps -/

/-- A step at `t` exchanges position `t` with a position `s ≥ t` or does nothing. -/
theorem Step.eq_swap_or_eq {t : Fin n} {x y : Fin n → Fin n} (h : Step δ S t x y) :
    ∃ s : Fin n, t ≤ s ∧ (y = x ∘ Equiv.swap t s ∨ y = x) := by
  obtain ⟨s, hts, -, -, rfl⟩ := h
  exact ⟨s, hts, by split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl⟩

/-- A step at `t` does not change positions before `t`. -/
theorem Step.apply_of_lt {t : Fin n} {x y : Fin n → Fin n} (h : Step δ S t x y)
    {p : Fin n} (hp : p < t) : y p = x p := by
  obtain ⟨s, hts, rfl | rfl⟩ := h.eq_swap_or_eq
  · simp [Equiv.swap_apply_of_ne_of_ne hp.ne (hp.trans_le hts).ne]
  · rfl

theorem Step.injective {t : Fin n} {x y : Fin n → Fin n} (h : Step δ S t x y)
    (hx : Function.Injective x) : Function.Injective y := by
  obtain ⟨s, -, rfl | rfl⟩ := h.eq_swap_or_eq
  · exact hx.comp (Equiv.injective _)
  · exact hx

/-- The invariant at the start of step `j`: every position `s ≥ j` holds its home item `s`
or an item delayed before step `j`. -/
def Inv (j : ℕ) (x : Fin n → Fin n) : Prop :=
  ∀ s : Fin n, j ≤ s → x s = s ∨ (x s : ℕ) < j

theorem Step.inv {t : Fin n} {x y : Fin n → Fin n} (h : Step δ S t x y) (hx : Inv t x) :
    Inv ((t : ℕ) + 1) y := by
  obtain ⟨s', hts', rfl | rfl⟩ := h.eq_swap_or_eq
  · intro s hs
    -- the occupant of position `t` is item `t` or a delayed item
    have hocc : (x t : ℕ) ≤ t := by
      rcases hx t le_rfl with h1 | h1
      · rw [h1]
      · exact h1.le
    simp only [Function.comp_apply]
    by_cases hss : s = s'
    · subst hss
      rw [Equiv.swap_apply_right]
      exact Or.inr (by omega)
    · have hst : s ≠ t := fun h => by rw [h] at hs; omega
      rw [Equiv.swap_apply_of_ne_of_ne hst hss]
      rcases hx s (by omega) with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (by omega)
  · intro s hs
    rcases hx s (by omega) with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (by omega)

/-! ## Runs -/

/-- A run of `δ`-SwapGreedy on the instance `S`. -/
structure Run (δ : ℝ) (S : Instance n) where
  state : ℕ → Fin n → Fin n
  init : state 0 = id
  step : ∀ t : Fin n, Step δ S t (state t) (state ((t : ℕ) + 1))

namespace Run

variable (R : Run δ S)

/-- The schedule returned by the run. -/
def result : Fin n → Fin n := R.state n

theorem isSGResult_iff {π : Fin n → Fin n} :
    IsSGResult δ S π ↔ ∃ R : Run δ S, R.result = π :=
  ⟨fun ⟨x, h0, hs, hπ⟩ => ⟨⟨x, h0, hs⟩, hπ⟩, fun ⟨R, hR⟩ => ⟨R.state, R.init, R.step, hR⟩⟩

theorem inv_state : ∀ j ≤ n, Inv j (R.state j) ∧ Function.Injective (R.state j) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [R.init]
    exact ⟨fun s _ => Or.inl rfl, Function.injective_id⟩
  | succ j ih =>
    intro hj
    obtain ⟨hinv, hinj⟩ := ih (by omega)
    have hstep := R.step ⟨j, by omega⟩
    exact ⟨hstep.inv hinv, hstep.injective hinj⟩

/-- Positions before `j` are final from step `j` on. -/
theorem state_stable {j j' : ℕ} (hjj' : j ≤ j') (hj' : j' ≤ n) {p : Fin n} (hp : (p : ℕ) < j) :
    R.state j' p = R.state j p := by
  induction j', hjj' using Nat.le_induction with
  | base => rfl
  | succ j' hjj' ih =>
    rw [(R.step ⟨j', by omega⟩).apply_of_lt (show p < ⟨j', by omega⟩ from by
      rw [Fin.lt_def]; simp; omega)]
    exact ih (by omega)

theorem result_eq {j : ℕ} (hj : j ≤ n) {p : Fin n} (hp : (p : ℕ) < j) :
    R.result p = R.state j p :=
  R.state_stable hj le_rfl hp

theorem result_eq_succ (t : Fin n) : R.result t = R.state ((t : ℕ) + 1) t :=
  R.result_eq t.isLt (Nat.lt_succ_self _)

theorem result_injective : Function.Injective R.result := (R.inv_state n le_rfl).2

/-- An item not collected before step `t` is at some position `s ≥ t` at the start of
step `t`, i.e. it is available. -/
theorem exists_pos_of_available {t c : Fin n} (hc' : ∀ p : Fin n, p < t → R.result p ≠ c) :
    ∃ s : Fin n, t ≤ s ∧ R.state t s = c := by
  obtain ⟨-, hinj⟩ := R.inv_state t t.isLt.le
  obtain ⟨s, hs⟩ := Finite.surjective_of_injective hinj c
  by_cases hst : s < t
  · exact absurd (R.result_eq t.isLt.le hst ▸ hs) (hc' s hst)
  · exact ⟨s, not_lt.mp hst, hs⟩

/-- An item `c ≥ t` that is not collected before step `t` is at its home position at the
start of step `t`. -/
theorem home_of_available {t c : Fin n} (hc : t ≤ c)
    (hc' : ∀ p : Fin n, p < t → R.result p ≠ c) : R.state t c = c := by
  obtain ⟨hinv, -⟩ := R.inv_state t t.isLt.le
  obtain ⟨s, hts, hs⟩ := R.exists_pos_of_available hc'
  rcases hinv s hts with h1 | h1
  · rw [← hs, h1]; exact h1
  · rw [hs] at h1; exact absurd hc (not_le.mpr h1)

/-! ## The algorithmic inequalities -/

/-- (M'): at a step `t` with `π(t) ≠ t`, the collected item is a maximizer among all items
not collected before `t` (without a swap, the occupant `π(t) = t` would be kept). -/
theorem le_of_ne {t c : Fin n} (ht : R.result t ≠ t) (hc' : ∀ p : Fin n, p < t → R.result p ≠ c) :
    S c t ≤ S (R.result t) t := by
  obtain ⟨q, htq, hq⟩ := R.exists_pos_of_available hc'
  have hres := R.result_eq_succ t
  obtain ⟨s', -, hmax, -, hY⟩ := R.step t
  have hcq := hmax q htq
  rw [hq] at hcq
  rw [hY] at hres
  split_ifs at hres with hcond
  · simp only [Function.comp_apply, Equiv.swap_apply_left] at hres
    rw [hres]; exact hcq
  · push_neg at hcond
    exact absurd (hres.trans hcond.2) ht

/-- (A): at an as-scheduled step `t`, `c(t) ≤ δ · t(t)` for every item `c` not collected
before `t`. -/
theorem ineq_A (hδ : 1 ≤ δ) {t c : Fin n} (hA : R.result t = t)
    (hc' : ∀ p : Fin n, p < t → R.result p ≠ c) : S c t ≤ δ * S t t := by
  obtain ⟨q, htq, hq⟩ := R.exists_pos_of_available hc'
  have hres := R.result_eq_succ t
  obtain ⟨s', -, hmax, -, hY⟩ := R.step t
  have hcq := hmax q htq
  rw [hq] at hcq
  rw [hY, hA] at hres
  split_ifs at hres with hcond
  · -- a swap collects item `t` as the maximizer
    simp only [Function.comp_apply, Equiv.swap_apply_left] at hres
    rw [← hres] at hcq
    nlinarith [S.nonneg t t]
  · -- no swap: the occupant is item `t`, and the maximizer beats it by at most `δ`
    push_neg at hcond
    have h1 := hcond.1
    rw [hcond.2] at h1
    exact hcq.trans h1

/-- (P): at a step `t` with `π(t) ≠ t` at which item `t` is available, `δ · t(t) ≤ π(t)(t)`
(a swap occurs, and item `t` is the occupant). -/
theorem ineq_P {t : Fin n} (ht : R.result t ≠ t) (hav : ∀ p : Fin n, p < t → R.result p ≠ t) :
    δ * S t t ≤ S (R.result t) t := by
  have hhome := R.home_of_available le_rfl hav
  have hres := R.result_eq_succ t
  obtain ⟨s', -, -, -, hY⟩ := R.step t
  rw [hY] at hres
  split_ifs at hres with hcond
  · simp only [Function.comp_apply, Equiv.swap_apply_left] at hres
    rw [hhome] at hcond
    rcases hcond with h | h
    · rw [hres]; exact h.le
    · exact absurd rfl h
  · rw [hres, hhome] at ht; exact absurd rfl ht

/-- (A) at every step `t`: an item `c` not collected before `t` satisfies
`c(t) ≤ δ · v_t` (from `ineq_A` at as-scheduled steps and (M') elsewhere). -/
theorem le_mul_of_available (hδ : 1 ≤ δ) {t c : Fin n}
    (hc' : ∀ p : Fin n, p < t → R.result p ≠ c) : S c t ≤ δ * S (R.result t) t := by
  by_cases hA : R.result t = t
  · rw [hA]; exact R.ineq_A hδ hA hc'
  · exact (R.le_of_ne hA hc').trans (le_mul_of_one_le_left (S.nonneg _ _) hδ)

/-- `lem:PMA`: the result of `δ`-SwapGreedy satisfies the algorithmic inequalities. -/
def toGreedy (hδ : 1 ≤ δ) : Greedy δ S where
  result := R.result
  result_injective := R.result_injective
  ineq_A {_ c _} hc' hts := (S.antitone c hts).trans (R.le_mul_of_available hδ hc')
  ineq_M {_ c _} hM hc' hts := (S.antitone c hts).trans (R.le_of_ne hM hc')
  ineq_P {t} hP := R.ineq_P (hP t le_rfl) fun p hp => hP p hp.le

end Run

end SwapGreedy
