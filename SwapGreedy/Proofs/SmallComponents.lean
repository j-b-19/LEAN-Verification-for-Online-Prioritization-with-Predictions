import SwapGreedy.Proofs.PerComponent
import SwapGreedy.Proofs.GoldenRatio

/-!
# The remaining components and the proof of the upper bound

Section *Per-Component Analysis* of `latex/swap_greedy.tex` from *Single step components*
on (`lem:covering`, `prop:onestep`, `prop:twosteps`), and the proof of the competitive ratio
`η · λ̂` in *Proof of Main Theorems*: the weights of `prop:generic` are at least those at
`λ = φ`, which leaves the components handled by `prop:onestep` and `prop:twosteps`.
-/

namespace SwapGreedy

open Finset Classical

variable {n : ℕ} {δ : ℝ} {S : Instance n} {l : Fin n}

/-! ## Components -/

/-- A fixed point `σ t = t` is a component of its own. -/
theorem steps_eq_singleton_of_adj_self {k : ℕ} {σ : Fin k ↪ Fin n} {C : Component σ} {t : Fin k}
    (ht : t ∈ steps σ C) (h : adj σ t t) : steps σ C = {t} := by
  have key : ∀ a b, Relation.EqvGen (adj σ) a b → (a = t ↔ b = t) := by
    intro a b hab
    induction hab with
    | rel a b hab =>
      constructor
      · intro hat; subst hat; exact (adj_functional h hab).symm
      · intro hbt; subst hbt; exact σ.injective (Fin.ext (hab.trans h.symm))
    | refl => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  ext x
  simp only [mem_steps, mem_singleton]
  constructor
  · intro hx
    exact (key x t (Quotient.exact (hx.trans (mem_steps.mp ht).symm))).mpr rfl
  · rintro rfl; exact mem_steps.mp ht

/-- The item `e_C > k` of a component is `OPT_k(t)` for a step `t` of the component. -/
theorem exists_apply_eq_of_isItem {k : ℕ} {σ : Fin k ↪ Fin n} {C : Component σ} {j : Fin n}
    (hj : IsItem σ C j) (hjk : k ≤ (j : ℕ)) : ∃ t ∈ steps σ C, σ t = j := by
  obtain ⟨t, htC, h | h⟩ := hj
  · exact absurd h (by have := t.isLt; omega)
  · exact ⟨t, mem_steps.mpr htC, h⟩

namespace Greedy

variable (G : Greedy δ S) {σ : Fin (l + 1) ↪ Fin n} {C : Component σ}

/-- A sum over `SG[k]⁻¹(I_C)`, indexed by the items of `C` collected in the first `k` steps. -/
theorem sum_coll_eq (g : Fin n → ℝ) :
    ∑ t ∈ G.coll σ C, g (G.result (Fin.castLE l.isLt t)) =
      ∑ c ∈ (univ.filter (IsItem σ C)).filter (fun c => G.collTime c ≤ l), g c := by
  have hinj : Set.InjOn (fun t => G.result (Fin.castLE l.isLt t)) ↑(G.coll σ C) :=
    (G.result_injective.comp (Fin.castLE_injective l.isLt)).injOn
  rw [← sum_image hinj]
  congr 1
  ext c
  simp only [coll, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ht, by rw [G.collTime_result]; exact castLE_le t⟩
  · rintro ⟨hc, hcl⟩
    have hι : Fin.castLE l.isLt ⟨G.collTime c, Nat.lt_succ_of_le hcl⟩ = G.collTime c := rfl
    refine ⟨⟨G.collTime c, Nat.lt_succ_of_le hcl⟩, ?_, ?_⟩ <;> rw [hι, G.result_collTime]
    exact hc

/-- `Φ_C` with its first sum indexed by the items of `C` collected in the first `k` steps. -/
theorem Φ_eq :
    G.Φ σ C =
      ∑ c ∈ (univ.filter (IsItem σ C)).filter (fun c => G.collTime c ≤ l),
          (S c (G.collTime c) - G.ω l) -
        ∑ t ∈ steps σ C, (G.v t - G.ω l) := by
  rw [← G.sum_coll_eq (fun c => S c (G.collTime c) - G.ω l)]
  simp only [Φ, coll, G.collTime_result, v]

/-! ## `lem:covering` -/

/-- The term `1_{e ∈ SG[k]} · (e(t_e) - ω)` of `lem:covering`. -/
noncomputable def bracket (l : Fin n) (c : Fin n) : ℝ :=
  if G.collTime c ≤ l then S c (G.collTime c) - G.ω l else 0

variable {G}

/-- The bracket is non-negative for items `e > k`, by (M) at step `t_e`. -/
theorem bracket_nonneg {c : Fin n} (hc : l < c) : 0 ≤ G.bracket l c := by
  unfold bracket
  split_ifs with h
  · have := G.ω_le h (by rw [G.result_collTime]; exact (h.trans_lt hc).ne')
    rw [G.result_collTime] at this
    exact sub_nonneg.mpr this
  · exact le_rfl

/-- `lem:covering`: for a step `t ≤ k` and an item `e > k`,
`e(t) ≤ λ · v_t + 1_{e ∈ SG[k]} · (e(t_e) - ω)`. -/
theorem covering (hδ : 1 ≤ δ) {t c : Fin n} (ht : t ≤ l) (hc : l < c) :
    S c t ≤ δ * S (G.result t) t + G.bracket l c := by
  have hω := G.ω_le_δ_mul hδ ht
  have hB := bracket_nonneg (G := G) hc
  by_cases hct : G.collTime c < t
  · -- `e ∈ SG[t-1]`: by (D) and (A)
    have hbr : G.bracket l c = S c (G.collTime c) - G.ω l := if_pos (hct.le.trans ht)
    have := S.antitone c hct.le
    linarith
  · -- `e ∉ SG[t-1]`: (A)
    have := G.ineq_A (G.available_iff.mpr (not_lt.mp hct)) le_rfl
    linarith

/-! ## `prop:onestep` -/

/-- `x ≤ c · y` for `c ≥ 1` if `0 ≤ x ≤ y`. -/
theorem le_mul_of_le_of_nonneg {x y c : ℝ} (hc : 1 ≤ c) (h0 : 0 ≤ x) (h : x ≤ y) :
    x ≤ c * y := by nlinarith

/-- `prop:onestep`: a component with a single step `t ∉ P_C`, items `{t, e}` and
`OPT_k(t) = e > k` satisfies `eq:charging_scheme`. -/
theorem onestep (hδ : 1 ≤ δ) {c : ℝ} (hc : 1 ≤ c) {t : Fin (l + 1)}
    (hT : steps σ C = {t}) {j : Fin n} (hj : l < j)
    (hI : univ.filter (IsItem σ C) = {Fin.castLE l.isLt t, j}) (hσ : σ t = j)
    (hAM : G.collTime (Fin.castLE l.isLt t) ≤ Fin.castLE l.isLt t) :
    LedgerIneq c (lamHat δ) G σ C := by
  set r := G.collTime (Fin.castLE l.isLt t)
  have hne : Fin.castLE l.isLt t ≠ j := ((castLE_le t).trans_lt hj).ne
  have hrl : r ≤ l := hAM.trans (castLE_le t)
  -- `v_r ≥ v_t`: equal if `r = t`, and by (M) at step `r` otherwise
  have hvr : G.v t ≤ S (Fin.castLE l.isLt t) r := by
    rcases hAM.lt_or_eq with hlt | heq
    · have hr : G.result r = Fin.castLE l.isLt t := G.result_collTime _
      have hM := G.ineq_M (t := r) (c := G.result (Fin.castLE l.isLt t)) (s := Fin.castLE l.isLt t)
        (by rw [hr]; exact hlt.ne')
        (fun p hp hpe => (hp.trans hlt).ne (G.result_injective hpe)) hlt.le
      rw [hr] at hM
      exact hM
    · have hA : G.result (Fin.castLE l.isLt t) = Fin.castLE l.isLt t := G.collTime_eq_iff.mp heq
      show S (G.result (Fin.castLE l.isLt t)) (Fin.castLE l.isLt t) ≤ S (Fin.castLE l.isLt t) r
      rw [hA, heq]
  have hcov := covering (G := G) hδ (castLE_le t) hj
  have hB := bracket_nonneg (G := G) hj
  have hdem : dem S σ C = S j (Fin.castLE l.isLt t) := by simp [dem, hT, hσ]
  have hv : ∑ u ∈ steps σ C, G.v u = G.v t := by simp [hT]
  have hΦ : G.Φ σ C = (S (Fin.castLE l.isLt t) r - G.ω l) + G.bracket l j - (G.v t - G.ω l) := by
    rw [G.Φ_eq, hI, hT, sum_singleton, sum_filter, sum_pair hne, if_pos hrl]
    rfl
  unfold LedgerIneq
  rw [hdem, hv, hΦ]
  have hvt : G.v t = S (G.result (Fin.castLE l.isLt t)) (Fin.castLE l.isLt t) := rfl
  rw [← hvt] at hcov
  refine le_mul_of_le_of_nonneg hc (S.nonneg _ _) ?_
  have hδρ : δ * G.v t ≤ lamHat δ * G.v t := mul_le_mul_of_nonneg_right (le_lamHat δ) (S.nonneg _ _)
  linarith

/-! ## `prop:twosteps` -/

/-- The computation of Case 2 of `prop:twosteps`, with `X = e(s)`, `Y = s(t)`, `Jj = e(e)`,
`v_s`, `v_t` and `B = Φ_C`: split `X + Y` with the weights `(λ - 1)/λ` and `1/λ`, apply
`ineq:S` to the second part and `lem:covering` to `X` and `Jj`. -/
theorem twosteps_arith (hδ : 1 ≤ δ) {X Y vs vt Jj B c : ℝ} (hc : 1 ≤ c)
    (hX : 0 ≤ X) (hY : 0 ≤ Y) (hvs : 0 ≤ vs) (hvt : 0 ≤ vt)
    (h1 : Y ≤ vs) (h2 : X ≤ δ * vs + B) (h3 : Jj ≤ δ * vt + B)
    (h5 : X + Y ≤ c * (vs + (vt + Jj))) :
    X + Y ≤ c * (lamHat δ * (vs + vt) + B) := by
  have hδ0 : 0 < δ := by linarith
  set a := (δ - 1) / δ with ha
  set b := 1 / δ with hb
  have hab : a + b = 1 := by rw [ha, hb]; field_simp; ring
  have ha0 : 0 ≤ a := div_nonneg (by linarith) hδ0.le
  have hb0 : 0 ≤ b := div_nonneg zero_le_one hδ0.le
  have haδ : a * δ = δ - 1 := by rw [ha]; field_simp
  have hbδ : b * δ = 1 := by rw [hb]; field_simp
  -- `X + Y ≤ c · (a (X + Y) + b (v_s + v_t + e(e)))`, by `ineq:S` and `η ≥ 1`
  have hsplit : X + Y ≤ c * (a * (X + Y) + b * (vs + (vt + Jj))) := by
    have e1 : b * (X + Y) ≤ b * (c * (vs + (vt + Jj))) := mul_le_mul_of_nonneg_left h5 hb0
    have e2 : a * (X + Y) ≤ c * (a * (X + Y)) :=
      le_mul_of_one_le_left (mul_nonneg ha0 (add_nonneg hX hY)) hc
    nlinarith
  -- `eq:2step_Component_proof_goal`: `a X + b e(e) ≤ (λ - 1) v_s + v_t + Φ_C`
  have hgoal : a * X + b * Jj ≤ (δ - 1) * vs + vt + B := by
    have e1 : a * X ≤ a * (δ * vs + B) := mul_le_mul_of_nonneg_left h2 ha0
    have e2 : b * Jj ≤ b * (δ * vt + B) := mul_le_mul_of_nonneg_left h3 hb0
    have e3 : a * (δ * vs + B) + b * (δ * vt + B) = (δ - 1) * vs + vt + B := by
      linear_combination vs * haδ + vt * hbδ + B * hab
    linarith
  -- (D) for `Y`, and `λ v_s + (1 + λ)/λ · v_t ≤ λ̂ (v_s + v_t)`
  have hY' : a * Y ≤ a * vs := mul_le_mul_of_nonneg_left h1 ha0
  have hl1 : δ * vs ≤ lamHat δ * vs := mul_le_mul_of_nonneg_right (le_lamHat δ) hvs
  have hl2 : (1 + b) * vt ≤ lamHat δ * vt :=
    mul_le_mul_of_nonneg_right (by rw [hb]; exact one_add_inv_le_lamHat δ) hvt
  have hin : a * (X + Y) + b * (vs + (vt + Jj)) ≤ lamHat δ * (vs + vt) + B := by
    have : a * vs + b * vs + b * vt + ((δ - 1) * vs + vt + B) = δ * vs + (1 + b) * vt + B := by
      linear_combination vs * hab
    nlinarith
  exact hsplit.trans (mul_le_mul_of_nonneg_left hin (zero_le_one.trans hc))

/-- `prop:twosteps`: a component with `(|A_C|, |M_C|, |P_C|) = (2, 0, 0)`, i.e. two
as-scheduled steps `s < t` and items `{s, t, e}` with `e > k`, satisfies
`eq:charging_scheme`. -/
theorem twosteps (hδ : 1 ≤ δ) {c : ℝ} (hc : 1 ≤ c) (hloc : EtaOptimal S c)
    {s t : Fin (l + 1)} (hst : s < t)
    (hT : steps σ C = {s, t}) {j : Fin n} (hj : l < j)
    (hI : univ.filter (IsItem σ C) = {Fin.castLE l.isLt s, Fin.castLE l.isLt t, j})
    (hs : G.result (Fin.castLE l.isLt s) = Fin.castLE l.isLt s)
    (ht : G.result (Fin.castLE l.isLt t) = Fin.castLE l.isLt t) :
    LedgerIneq c (lamHat δ) G σ C := by
  have hst' : Fin.castLE l.isLt s < Fin.castLE l.isLt t := Fin.lt_def.mpr hst
  have hne : s ≠ t := hst.ne
  have hsne : Fin.castLE l.isLt s ≠ Fin.castLE l.isLt t := hst'.ne
  have hsj : Fin.castLE l.isLt s ≠ j := ((castLE_le s).trans_lt hj).ne
  have htj : Fin.castLE l.isLt t ≠ j := ((castLE_le t).trans_lt hj).ne
  have hsT : s ∈ steps σ C := by rw [hT]; exact mem_insert_self _ _
  have htT : t ∈ steps σ C := by rw [hT]; exact mem_insert_of_mem (mem_singleton_self _)
  have hitem : ∀ x, IsItem σ C x →
      x = Fin.castLE l.isLt s ∨ x = Fin.castLE l.isLt t ∨ x = j := fun x hx => by
    have : x ∈ univ.filter (IsItem σ C) := mem_filter.mpr ⟨mem_univ _, hx⟩
    simpa [hI] using this
  -- the pieces of `eq:twostep_goal`
  have hdem : dem S σ C = S (σ s) (Fin.castLE l.isLt s) + S (σ t) (Fin.castLE l.isLt t) := by
    simp [dem, hT, sum_pair hne]
  have hv : ∑ u ∈ steps σ C, G.v u =
      S (Fin.castLE l.isLt s) (Fin.castLE l.isLt s) +
        S (Fin.castLE l.isLt t) (Fin.castLE l.isLt t) := by
    simp [hT, sum_pair hne, v, hs, ht]
  have hΦ : G.Φ σ C = G.bracket l j := by
    rw [G.Φ_eq, hI, hT, sum_pair hne, sum_filter, sum_insert (by simp [hsne, hsj]),
      sum_pair htj, G.collTime_eq_iff.mpr hs, G.collTime_eq_iff.mpr ht, if_pos (castLE_le s),
      if_pos (castLE_le t)]
    simp only [v, hs, ht]
    unfold bracket
    ring
  have hB := bracket_nonneg (G := G) hj
  have hsplit := dem_le_sum_items (l := l) (σ := σ) (C := C) hloc
  rw [hI, sum_insert (by simp [hsne, hsj]), sum_pair htj] at hsplit
  unfold LedgerIneq
  rw [hv, hΦ]
  -- neither step is a fixed point, so `OPT_k` maps `(s, t)` to `(t, e)` or to `(e, s)`
  have hfix : ∀ u ∈ steps σ C, σ u ≠ Fin.castLE l.isLt u := fun u hu hσu => by
    have hu' : steps σ C = {u} := steps_eq_singleton_of_adj_self hu (by simp [adj, hσu])
    rw [hu'] at hsT htT
    exact hne ((mem_singleton.mp hsT).trans (mem_singleton.mp htT).symm)
  have hjI : IsItem σ C j := (mem_filter.mp (by rw [hI]; simp : j ∈ univ.filter (IsItem σ C))).2
  obtain ⟨u, huT, hσu⟩ := exists_apply_eq_of_isItem hjI hj
  rw [hT, mem_insert, mem_singleton] at huT
  rcases huT with rfl | rfl
  · -- Case `(OPT_k(s), OPT_k(t)) = (e, s)`
    rcases hitem _ (isItem_apply htT) with hσt | hσt | hσt
    · rw [hdem, hσu, hσt] at hsplit ⊢
      have h1 := S.antitone (Fin.castLE l.isLt u) hst'.le
      have h2 := covering (G := G) hδ (castLE_le u) hj
      have h3 := covering (G := G) hδ (castLE_le t) hj
      have h4 := S.antitone j ((castLE_le t).trans hj.le)
      rw [hs] at h2
      rw [ht] at h3
      exact twosteps_arith hδ hc (S.nonneg _ _) (S.nonneg _ _) (S.nonneg _ _) (S.nonneg _ _)
        h1 h2 (h4.trans h3) hsplit
    · exact absurd hσt (hfix t htT)
    · exact absurd (σ.injective (hσu.trans hσt.symm)) hne
  · -- Case `(OPT_k(s), OPT_k(t)) = (t, e)`: (A) at `s` and `lem:covering` at `t`
    rcases hitem _ (isItem_apply hsT) with hσs | hσs | hσs
    · exact absurd hσs (hfix s hsT)
    · rw [hdem, hσu, hσs]
      have hA := G.ineq_A (t := Fin.castLE l.isLt s) (c := Fin.castLE l.isLt u)
        (s := Fin.castLE l.isLt s)
        (G.available_iff.mpr (by rw [G.collTime_eq_iff.mpr ht]; exact hst'.le)) le_rfl
      rw [hs] at hA
      have hcov := covering (G := G) hδ (castLE_le u) hj
      rw [ht] at hcov
      refine le_mul_of_le_of_nonneg hc (add_nonneg (S.nonneg _ _) (S.nonneg _ _)) ?_
      have h1 : δ * S (Fin.castLE l.isLt s) (Fin.castLE l.isLt s) ≤
          lamHat δ * S (Fin.castLE l.isLt s) (Fin.castLE l.isLt s) :=
        mul_le_mul_of_nonneg_right (le_lamHat δ) (S.nonneg _ _)
      have h2 : δ * S (Fin.castLE l.isLt u) (Fin.castLE l.isLt u) ≤
          lamHat δ * S (Fin.castLE l.isLt u) (Fin.castLE l.isLt u) :=
        mul_le_mul_of_nonneg_right (le_lamHat δ) (S.nonneg _ _)
      linarith
    · exact absurd (σ.injective (hσs.trans hσu.symm)) hne

end Greedy

/-! ## Proof of the competitive ratio `η · λ̂` -/

/-- The weights of `prop:generic` are at least those at `λ = φ`: `(λ̂ - 1)/λ ≥ 1/φ²` and
`λ̂ - 1 ≥ 1/φ` (for `λ ≥ φ`, `λ̂ = λ`; for `λ ≤ φ`, `λ̂ = (1 + λ)/λ`). -/
theorem weights_ge_φ (hδ : 1 ≤ δ) : 1 / φ ^ 2 ≤ (lamHat δ - 1) / δ ∧ 1 / φ ≤ lamHat δ - 1 := by
  have hδ0 : 0 < δ := by linarith
  have hφ := φ_pos
  have hsq := φ_sq
  have hsum := inv_φ_sq_add_inv_φ
  rcases le_total φ δ with hφδ | hδφ
  · -- `λ̂ = λ`, and `(λ - 1)/λ = 1 - 1/λ ≥ 1 - 1/φ = 1/φ²`
    have hle : 1 + 1 / δ ≤ δ := by
      rw [← sub_nonneg]
      have : δ - (1 + 1 / δ) = (δ ^ 2 - δ - 1) / δ := by field_simp; ring
      rw [this]
      exact div_nonneg (by nlinarith) hδ0.le
    have hl : lamHat δ = δ := max_eq_left hle
    rw [hl]
    have hinv : 1 / δ ≤ 1 / φ := one_div_le_one_div_of_le hφ hφδ
    refine ⟨?_, ?_⟩
    · have : (δ - 1) / δ = 1 - 1 / δ := by field_simp
      rw [this]; linarith
    · have : 1 / φ = φ - 1 := by field_simp; nlinarith
      linarith
  · -- `λ̂ = (1 + λ)/λ`, so the weights are `1/λ²` and `1/λ`
    have hle : δ ≤ 1 + 1 / δ := by
      rw [← sub_nonneg]
      have : 1 + 1 / δ - δ = (φ - δ) * (δ + φ - 1) / δ := by
        field_simp; linear_combination (-1 : ℝ) * hsq
      rw [this]
      exact div_nonneg (mul_nonneg (by linarith) (by linarith [one_le_φ])) hδ0.le
    have hl : lamHat δ = 1 + 1 / δ := max_eq_right hle
    rw [hl]
    have hinv : 1 / φ ≤ 1 / δ := one_div_le_one_div_of_le hδ0 hδφ
    refine ⟨?_, by linarith⟩
    have : (1 + 1 / δ - 1) / δ = 1 / δ ^ 2 := by field_simp; ring
    rw [this]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hδ0.le hδφ 2)

/-- At `λ = φ`, the weights `|A_C|/φ² + |M_C|/φ + |P_C|` are at least `1` except for
`|P_C| = 0` and `(|A_C|, |M_C|) ∈ {(1, 0), (0, 1), (2, 0)}` (a component has a step). -/
theorem one_le_weights_φ {a m p : ℕ} (h0 : 0 < a + m + p)
    (hsmall : ¬ (p = 0 ∧ ((a = 1 ∧ m = 0) ∨ (a = 0 ∧ m = 1) ∨ (a = 2 ∧ m = 0)))) :
    (1 : ℝ) ≤ a * (1 / φ ^ 2) + m * (1 / φ) + p := by
  have hφ := φ_pos
  have hsum := inv_φ_sq_add_inv_φ
  have hA : 0 ≤ 1 / φ ^ 2 := div_nonneg zero_le_one (sq_nonneg _)
  have hM : 0 ≤ 1 / φ := div_nonneg zero_le_one hφ.le
  -- three steps of `A_C`, two of `M_C`, or one of each suffice
  have h3 : (1 : ℝ) ≤ 3 * (1 / φ ^ 2) := by
    rw [← mul_div_assoc, le_div_iff₀ (pow_pos hφ 2), one_mul, φ_sq]; linarith [φ_le_two]
  have h2 : (1 : ℝ) ≤ 2 * (1 / φ) := by
    rw [← mul_div_assoc, le_div_iff₀ hφ, one_mul]; linarith [φ_le_two]
  have ha0 : (0 : ℝ) ≤ a * (1 / φ ^ 2) := mul_nonneg (Nat.cast_nonneg _) hA
  have hm0 : (0 : ℝ) ≤ m * (1 / φ) := mul_nonneg (Nat.cast_nonneg _) hM
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp only [true_and, Nat.cast_zero, add_zero] at hsmall ⊢
    by_cases ha3 : 3 ≤ a
    · have : (3 : ℝ) ≤ a := by exact_mod_cast ha3
      nlinarith [mul_nonneg (sub_nonneg.mpr this) hA]
    by_cases hm2 : 2 ≤ m
    · have : (2 : ℝ) ≤ m := by exact_mod_cast hm2
      nlinarith [mul_nonneg (sub_nonneg.mpr this) hM]
    by_cases ham : 1 ≤ a ∧ 1 ≤ m
    · have h1 : (1 : ℝ) ≤ a := by exact_mod_cast ham.1
      have h2 : (1 : ℝ) ≤ m := by exact_mod_cast ham.2
      nlinarith [mul_nonneg (sub_nonneg.mpr h1) hA, mul_nonneg (sub_nonneg.mpr h2) hM]
    · exfalso; omega
  · have : (1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith

namespace Greedy

variable (G : Greedy δ S)

/-- The components left after `prop:generic` satisfy `eq:charging_scheme`, by
`prop:onestep` (`(|A_C|, |M_C|) ∈ {(1, 0), (0, 1)}`) and `prop:twosteps` (`(2, 0)`). -/
theorem small_components (hδ : 1 ≤ δ) {c : ℝ} (hc : 1 ≤ c) (hloc : EtaOptimal S c)
    (σ : Fin (l + 1) ↪ Fin n) (C : Component σ) (hout : (outer σ C).Nonempty)
    (hP : G.stepsP σ C = ∅)
    (hcases : (G.stepsA σ C).card = 1 ∧ (G.stepsM σ C).card = 0 ∨
      (G.stepsA σ C).card = 0 ∧ (G.stepsM σ C).card = 1 ∨
      (G.stepsA σ C).card = 2 ∧ (G.stepsM σ C).card = 0) :
    LedgerIneq c (lamHat δ) G σ C := by
  -- the item `e_C > k`
  obtain ⟨j, hjk, hj⟩ : ∃ j : Fin n, l < j ∧
      ∀ x, IsItem σ C x ↔ (∃ t ∈ steps σ C, (t : ℕ) = x) ∨ x = j := by
    rcases component_items C with h | ⟨j, hjk, hj⟩
    · obtain ⟨x, hx⟩ := hout
      obtain ⟨hxI, hxk⟩ := mem_outer.mp hx
      exact absurd (h x hxI) (not_lt.mpr hxk)
    · exact ⟨j, hjk, hj⟩
  have hjI : IsItem σ C j := (hj j).mpr (Or.inr rfl)
  have hcast : ∀ (t : Fin (l + 1)) (x : Fin n), (t : ℕ) = x ↔ x = Fin.castLE l.isLt t :=
    fun t x => by rw [Fin.ext_iff, Fin.val_castLE, eq_comm]
  have hcard := card_steps_eq (G := G) (C := C)
  rw [hP, card_empty] at hcard
  have hAsub : G.stepsA σ C ⊆ steps σ C := filter_subset _ _
  have hMsub : G.stepsM σ C ⊆ steps σ C := filter_subset _ _
  -- a single step `t ∉ P_C`
  have hone : ∀ t, steps σ C = {t} →
      G.collTime (Fin.castLE l.isLt t) ≤ Fin.castLE l.isLt t → LedgerIneq c (lamHat δ) G σ C :=
    fun t hT hAM => by
      obtain ⟨u, huT, hσu⟩ := exists_apply_eq_of_isItem hjI hjk
      rw [hT, mem_singleton] at huT
      subst huT
      refine G.onestep hδ hc hT hjk ?_ hσu hAM
      ext x
      simp only [mem_filter, mem_univ, true_and, hj, hT, mem_singleton, exists_eq_left,
        mem_insert, hcast]
  rcases hcases with ⟨hA, hM⟩ | ⟨hA, hM⟩ | ⟨hA, hM⟩
  · -- `(|A_C|, |M_C|) = (1, 0)`
    rw [hA, hM] at hcard
    obtain ⟨t, hT⟩ := card_eq_one.mp hcard
    have hAeq : G.stepsA σ C = steps σ C := eq_of_subset_of_card_le hAsub (by omega)
    have htA : t ∈ G.stepsA σ C := by rw [hAeq, hT]; exact mem_singleton_self t
    exact hone t hT (mem_stepsA.mp htA).2.le
  · -- `(|A_C|, |M_C|) = (0, 1)`
    rw [hA, hM] at hcard
    obtain ⟨t, hT⟩ := card_eq_one.mp hcard
    have hMeq : G.stepsM σ C = steps σ C := eq_of_subset_of_card_le hMsub (by omega)
    have htM : t ∈ G.stepsM σ C := by rw [hMeq, hT]; exact mem_singleton_self t
    exact hone t hT (mem_stepsM.mp htM).2.le
  · -- `(|A_C|, |M_C|) = (2, 0)`
    rw [hA, hM] at hcard
    have hAeq : G.stepsA σ C = steps σ C := eq_of_subset_of_card_le hAsub (by omega)
    obtain ⟨x, y, hxy, hT⟩ := card_eq_two.mp hcard
    have hres : ∀ z ∈ steps σ C, G.result (Fin.castLE l.isLt z) = Fin.castLE l.isLt z :=
      fun z hz => by rw [← hAeq] at hz; exact (mem_filter.mp hz).2
    have hI : univ.filter (IsItem σ C) = {Fin.castLE l.isLt x, Fin.castLE l.isLt y, j} := by
      ext z
      simp only [mem_filter, mem_univ, true_and, hj, hT, mem_singleton, mem_insert, hcast,
        exists_eq_or_imp, exists_eq_left, or_assoc]
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · exact G.twosteps hδ hc hloc hlt hT hjk hI
        (hres x (by rw [hT]; simp)) (hres y (by rw [hT]; simp))
    · rw [pair_comm] at hT
      rw [insert_comm] at hI
      exact G.twosteps hδ hc hloc hlt hT hjk hI
        (hres y (by rw [hT]; simp)) (hres x (by rw [hT]; simp))

/-- The competitive ratio `η · λ̂` of `thmUpper` for the prefix of length `k = l + 1`: every
component satisfies `eq:charging_scheme`, by `prop:generic` with the weights at `φ` or by
`small_components`, so `lem:ledger` applies. -/
theorem prefix_le (hδ : 1 ≤ δ) {c : ℝ} (hc : 1 ≤ c) (hloc : EtaOptimal S c)
    (σ : Fin (l + 1) ↪ Fin n) :
    value S l.isLt σ ≤ c * lamHat δ * value S l.isLt (G.result ∘ Fin.castLE l.isLt) := by
  refine G.ledger (zero_le_one.trans hc) σ fun C => ?_
  by_cases hsmall : (outer σ C).Nonempty ∧ G.stepsP σ C = ∅ ∧
      ((G.stepsA σ C).card = 1 ∧ (G.stepsM σ C).card = 0 ∨
        (G.stepsA σ C).card = 0 ∧ (G.stepsM σ C).card = 1 ∨
        (G.stepsA σ C).card = 2 ∧ (G.stepsM σ C).card = 0)
  · exact G.small_components hδ hc hloc σ C hsmall.1 hsmall.2.1 hsmall.2.2
  · refine G.generic hδ hc hloc ?_
    obtain ⟨hwA, hwM⟩ := weights_ge_φ hδ
    have hφw : (G.stepsA σ C).card * (1 / φ ^ 2) + (G.stepsM σ C).card * (1 / φ) +
        ((G.stepsP σ C).card : ℝ) ≤
        (G.stepsA σ C).card * ((lamHat δ - 1) / δ) + (G.stepsM σ C).card * (lamHat δ - 1) +
          (G.stepsP σ C).card := by
      gcongr
    have hnn : (0 : ℝ) ≤ (G.stepsA σ C).card * (1 / φ ^ 2) + (G.stepsM σ C).card * (1 / φ) +
        (G.stepsP σ C).card :=
      add_nonneg (add_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg zero_le_one (sq_nonneg _)))
        (mul_nonneg (Nat.cast_nonneg _) (div_nonneg zero_le_one φ_pos.le))) (Nat.cast_nonneg _)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (card_outer_le_one C) with h0 | h1
    · rw [h0, Nat.cast_zero]; exact hnn.trans hφw
    · rw [h1, Nat.cast_one]
      have hne : (outer σ C).Nonempty := card_pos.mp (by rw [h1]; exact one_pos)
      have hT : 0 < (steps σ C).card := by
        obtain ⟨t, ht⟩ := Quotient.exists_rep C
        exact card_pos.mpr ⟨t, mem_steps.mpr ht⟩
      rw [card_steps_eq (G := G)] at hT
      exact (one_le_weights_φ hT fun hs => hsmall ⟨hne, card_eq_zero.mp hs.1, hs.2⟩).trans hφw

end Greedy

end SwapGreedy
