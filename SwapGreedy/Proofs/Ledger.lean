import SwapGreedy.Proofs.Components
import SwapGreedy.Proofs.Greedy
import SwapGreedy.Proofs.Splitting

/-!
# The ledger

Section *Components and Transfers* of `latex/swap_greedy.tex`: `ω`, `Φ_C` and `lem:ledger`,
for a schedule `G : Greedy δ S` satisfying the algorithmic inequalities.

The stopping step `k` of the paper is `l + 1` for the last step `l : Fin n` of the prefix
(steps are 0-indexed), so the comparison schedule is `σ : Fin (l + 1) ↪ Fin n` and step
`t : Fin (l + 1)` is step `Fin.castLE l.isLt t` of `Fin n`. The component inequality
`eq:charging_scheme` is `LedgerIneq c ρ G σ C` for an `η = c`-optimal identity and the
target ratio `ρ` (the paper's `λ̂`); `lem:ledger` holds for every `σ`, optimal or not.
-/

namespace SwapGreedy

open Finset Classical

variable {n : ℕ} {δ ρ : ℝ} {S : Instance n} {l : Fin n}

theorem castLE_le (t : Fin (l + 1)) : Fin.castLE l.isLt t ≤ l :=
  Fin.le_def.mpr (Nat.lt_succ_iff.mp t.isLt)

namespace Greedy

/-- `ω = max({i(k) | i ∉ SG[k]} ∪ {0})`. -/
noncomputable def ω (G : Greedy δ S) (l : Fin n) : ℝ :=
  (univ.filter fun i : Fin n => ∀ t : Fin n, t ≤ l → G.result t ≠ i).fold max 0
    (fun i => S i l)

/-- `v_t = SG(t)(t)`, the value collected at step `t`. -/
def v (G : Greedy δ S) (t : Fin (l + 1)) : ℝ :=
  S (G.result (Fin.castLE l.isLt t)) (Fin.castLE l.isLt t)

/-- The steps `SG[k]⁻¹(I_C)` collecting an item of `C`. -/
noncomputable abbrev coll (G : Greedy δ S) (σ : Fin (l + 1) ↪ Fin n) (C : Component σ) :
    Finset (Fin (l + 1)) :=
  univ.filter fun t => IsItem σ C (G.result (Fin.castLE l.isLt t))

/-- `Φ_C = ∑_{t ∈ SG[k]⁻¹(I_C)} (v_t - ω) - ∑_{t ∈ T_C} (v_t - ω)`. -/
noncomputable def Φ (G : Greedy δ S) (σ : Fin (l + 1) ↪ Fin n) (C : Component σ) : ℝ :=
  ∑ t ∈ G.coll σ C, (G.v t - G.ω l) - ∑ t ∈ steps σ C, (G.v t - G.ω l)

end Greedy

/-- `∑_{t ∈ T_C} OPT_k(t)(t)` for the comparison schedule `σ`. -/
noncomputable def dem (S : Instance n) (σ : Fin (l + 1) ↪ Fin n) (C : Component σ) : ℝ :=
  ∑ t ∈ steps σ C, S (σ t) (Fin.castLE l.isLt t)

/-- `eq:charging_scheme` for the component `C`, with `η = c` and `λ̂ = ρ`. -/
def LedgerIneq (c ρ : ℝ) (G : Greedy δ S) (σ : Fin (l + 1) ↪ Fin n) (C : Component σ) : Prop :=
  dem S σ C ≤ c * (ρ * ∑ t ∈ steps σ C, G.v t + G.Φ σ C)

namespace Greedy

variable (G : Greedy δ S)

theorem ω_nonneg (l : Fin n) : 0 ≤ G.ω l := (le_fold_max _).mpr (Or.inl le_rfl)

/-- An item not collected in the first `k` steps competes in the definition of `ω`. -/
theorem le_ω {j : Fin n} (hj : ∀ t : Fin n, t ≤ l → G.result t ≠ j) : S j l ≤ G.ω l :=
  (le_fold_max _).mpr (Or.inr ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩, le_rfl⟩)

/-- `ω` can be used as the right-hand side of (M): `ω ≤ v_u` for `u ≤ k` with `SG(u) ≠ u`. -/
theorem ω_le {u : Fin n} (hul : u ≤ l) (hu : G.result u ≠ u) : G.ω l ≤ S (G.result u) u := by
  refine (fold_max_le _).mpr ⟨S.nonneg _ _, fun i hi => ?_⟩
  simp only [mem_filter, mem_univ, true_and] at hi
  exact G.ineq_M hu (fun p hp => hi p (hp.le.trans hul)) hul

/-- `ω` can be used as the right-hand side of (A): `ω ≤ δ · v_u` for `u ≤ k`. -/
theorem ω_le_δ_mul (hδ : 1 ≤ δ) {u : Fin n} (hul : u ≤ l) :
    G.ω l ≤ δ * S (G.result u) u := by
  refine (fold_max_le _).mpr ⟨mul_nonneg (zero_le_one.trans hδ) (S.nonneg _ _),
    fun i hi => ?_⟩
  simp only [mem_filter, mem_univ, true_and] at hi
  exact G.ineq_A (fun p hp => hi p (hp.le.trans hul)) hul

theorem v_sub_ω_nonneg {t : Fin (l + 1)}
    (ht : G.result (Fin.castLE l.isLt t) ≠ Fin.castLE l.isLt t) : 0 ≤ G.v t - G.ω l :=
  sub_nonneg.mpr (G.ω_le (castLE_le t) ht)

/-- `lem:ledger`: if every component satisfies `eq:charging_scheme`, then
`f_k(σ) ≤ c · ρ · f_k(SG)`. -/
theorem ledger {c : ℝ} (hc : 0 ≤ c) (σ : Fin (l + 1) ↪ Fin n)
    (H : ∀ C, LedgerIneq c ρ G σ C) :
    value S l.isLt σ ≤ c * ρ * value S l.isLt (G.result ∘ Fin.castLE l.isLt) := by
  set ι := Fin.castLE l.isLt
  set x : Fin (l + 1) → ℝ := fun t => G.v t - G.ω l
  have hdem : ∑ C, dem S σ C = value S l.isLt σ := sum_steps _
  have hv : ∑ C, ∑ t ∈ steps σ C, G.v t = value S l.isLt (G.result ∘ ι) := sum_steps _
  have hB : ∑ C, ∑ t ∈ steps σ C, x t = ∑ t, x t := sum_steps _
  -- every step collects an item of at most one component, and `v_t ≥ ω` if of none
  have hA : ∑ C, ∑ t ∈ G.coll σ C, x t ≤ ∑ t, x t := by
    simp only [sum_filter]
    rw [sum_comm]
    refine sum_le_sum fun t _ => ?_
    by_cases hex : ∃ C, IsItem σ C (G.result (ι t))
    · obtain ⟨C₀, hC₀⟩ := hex
      rw [sum_eq_single C₀ (fun C _ hC => if_neg fun h => hC (h.unique hC₀)) (by simp), if_pos hC₀]
    · push_neg at hex
      rw [sum_eq_zero fun C _ => if_neg (hex C)]
      have hk : l < G.result (ι t) := by
        by_contra hle
        push_neg at hle
        exact hex _ (isItem_of_lt (Nat.lt_succ_of_le hle))
      exact G.v_sub_ω_nonneg (lt_of_le_of_lt (castLE_le t) hk).ne'
  have hΦ : ∑ C, G.Φ σ C ≤ 0 := by
    have : ∑ C, G.Φ σ C = ∑ C, ∑ t ∈ G.coll σ C, x t - ∑ C, ∑ t ∈ steps σ C, x t :=
      sum_sub_distrib (fun C => ∑ t ∈ G.coll σ C, x t) (fun C => ∑ t ∈ steps σ C, x t)
    rw [this, hB]
    linarith
  calc value S l.isLt σ = ∑ C, dem S σ C := hdem.symm
    _ ≤ ∑ C, c * (ρ * ∑ t ∈ steps σ C, G.v t + G.Φ σ C) := sum_le_sum fun C _ => H C
    _ = c * (ρ * value S l.isLt (G.result ∘ ι) + ∑ C, G.Φ σ C) := by
      rw [← mul_sum, sum_add_distrib, ← mul_sum, hv]
    _ ≤ c * ρ * value S l.isLt (G.result ∘ ι) := by
      nlinarith [mul_le_mul_of_nonneg_left hΦ hc]

end Greedy

/-- A schedule `π` is `c'`-competitive if every prefix is. -/
theorem competitive_of_forall_prefix {π : Fin n → Fin n} {c' : ℝ}
    (H : ∀ (l : Fin n) (σ : Fin (l + 1) ↪ Fin n),
      value S l.isLt σ ≤ c' * value S l.isLt (π ∘ Fin.castLE l.isLt)) :
    CompetitiveSchedule S c' π := by
  intro k hk σ
  cases k with
  | zero => simp [value]
  | succ m => exact H ⟨m, hk⟩ σ

end SwapGreedy
