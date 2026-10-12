import SwapGreedy.Proofs.Splitting
import Mathlib.Data.Fintype.Quotient
import Mathlib.Logic.Relation

/-!
# The component graph

Section 6 of `latex/swap_greedy.tex`, paragraph *The component graph*, and the part
of `lem:structure` that is needed without cycle-freeness (`component_items`).

For a schedule `σ` of length `k` (the paper's `π⋆_k`), the graph `G` has the steps `Fin k`
and the items `Fin n` as vertices, edges `(t, t)` and edges `(t, σ t)`. Two steps lie in
the same component iff they are related by the equivalence closure of `adj σ`, where
`adj σ t t'` means that `σ t` is the home item of step `t'`. Components are the classes of
this equivalence relation; the item set `I_C` consists of the items adjacent to a step
of `C`.

For a `c`-optimal identity with `c > 1`, cycles cannot be removed without loss, so they are
kept and handled as components with `I_C = T_C` (`component_items`, `outer`, `card_outer_le_one`).
-/

namespace SwapGreedy

open Finset Classical

variable {n k : ℕ}

/-- Step `t` is adjacent to step `t'` if `σ` collects the home item of `t'` at step `t`. -/
def adj (σ : Fin k ↪ Fin n) (t t' : Fin k) : Prop := (σ t : ℕ) = t'

/-- The equivalence relation "in the same component". -/
def compSetoid (σ : Fin k ↪ Fin n) : Setoid (Fin k) := Relation.EqvGen.setoid (adj σ)

/-- The components of `G` that contain a step. -/
abbrev Component (σ : Fin k ↪ Fin n) := Quotient (compSetoid σ)

noncomputable instance (σ : Fin k ↪ Fin n) : Fintype (Component σ) := Quotient.fintype _

/-- The component of step `t`. -/
def comp (σ : Fin k ↪ Fin n) (t : Fin k) : Component σ := Quotient.mk _ t

/-- The step set `T_C`. -/
noncomputable def steps (σ : Fin k ↪ Fin n) (C : Component σ) : Finset (Fin k) :=
  univ.filter (comp σ · = C)

/-- `c ∈ I_C`: the item `c` is adjacent to a step of `C`. -/
def IsItem (σ : Fin k ↪ Fin n) (C : Component σ) (c : Fin n) : Prop :=
  ∃ t, comp σ t = C ∧ ((t : ℕ) = c ∨ σ t = c)

variable {σ : Fin k ↪ Fin n}

theorem mem_steps {C : Component σ} {t : Fin k} : t ∈ steps σ C ↔ comp σ t = C := by
  simp [steps]

theorem comp_eq_of_adj {t t' : Fin k} (h : adj σ t t') : comp σ t = comp σ t' :=
  Quotient.sound (Relation.EqvGen.rel _ _ h)

theorem adj_functional {t t₁ t₂ : Fin k} (h₁ : adj σ t t₁) (h₂ : adj σ t t₂) : t₁ = t₂ :=
  Fin.ext (h₁.symm.trans h₂)

/-- The item sets of distinct components are disjoint. -/
theorem IsItem.unique {C C' : Component σ} {c : Fin n} (h : IsItem σ C c) (h' : IsItem σ C' c) :
    C = C' := by
  obtain ⟨t, rfl, ht⟩ := h
  obtain ⟨t', rfl, ht'⟩ := h'
  rcases ht with ht | ht <;> rcases ht' with ht' | ht'
  · exact congrArg _ (Fin.ext (ht.trans ht'.symm))
  · exact (comp_eq_of_adj (show adj σ t' t by simp [adj, ht', ht])).symm
  · exact comp_eq_of_adj (show adj σ t t' by simp [adj, ht', ht])
  · exact congrArg _ (σ.injective (ht.trans ht'.symm))

/-- Every item `c < k` is an item of the component of step `c`. -/
theorem isItem_of_lt {c : Fin n} (hc : (c : ℕ) < k) : IsItem σ (comp σ ⟨c, hc⟩) c :=
  ⟨⟨c, hc⟩, rfl, Or.inl rfl⟩

/-- The home item of a step of `C` is an item of `C`. -/
theorem isItem_castLE (hk : k ≤ n) {C : Component σ} {t : Fin k} (ht : t ∈ steps σ C) :
    IsItem σ C (Fin.castLE hk t) :=
  ⟨t, mem_steps.mp ht, Or.inl rfl⟩

/-- The item `σ t` of a step `t` of `C` is an item of `C`. -/
theorem isItem_apply {C : Component σ} {t : Fin k} (ht : t ∈ steps σ C) : IsItem σ C (σ t) :=
  ⟨t, mem_steps.mp ht, Or.inr rfl⟩

/-- An item `c < k` of `C` is (the home item of) a step of `C`. -/
theorem mem_steps_of_isItem {C : Component σ} {c : Fin n} (hc : IsItem σ C c) (h : (c : ℕ) < k) :
    ⟨c, h⟩ ∈ steps σ C := by
  obtain ⟨t, htC, ht | ht⟩ := hc
  · rw [mem_steps, ← htC]; congr 1; exact Fin.ext ht.symm
  · rw [mem_steps, ← htC]
    exact (comp_eq_of_adj (show adj σ t ⟨c, h⟩ from by simp [adj, ht])).symm

/-- The step sets of the components partition the steps. -/
theorem sum_steps (f : Fin k → ℝ) : ∑ C : Component σ, ∑ t ∈ steps σ C, f t = ∑ t, f t :=
  sum_fiberwise univ (comp σ) f

/-! ## `lem:structure` -/

/-- The items of `C` outside `[k]`, i.e. `I_C \ T_C` (as a set of items, `T_C ⊆ [k]`). -/
noncomputable def outer (σ : Fin k ↪ Fin n) (C : Component σ) : Finset (Fin n) :=
  univ.filter fun c => IsItem σ C c ∧ k ≤ (c : ℕ)

theorem mem_outer {C : Component σ} {c : Fin n} :
    c ∈ outer σ C ↔ IsItem σ C c ∧ k ≤ (c : ℕ) := by
  simp [outer]

/-- `lem:structure` without the cycle-freeness assumption: either all items of `C` are steps
of `C` (`C` is a fixed point or a cycle), or `C` has exactly one item `j ≥ k`, and its items
are its steps together with `j` (`C` is a path). -/
theorem component_items (C : Component σ) :
    (∀ c, IsItem σ C c → (c : ℕ) < k) ∨
    (∃ j : Fin n, k ≤ (j : ℕ) ∧
      ∀ c, IsItem σ C c ↔ (∃ t ∈ steps σ C, (t : ℕ) = c) ∨ c = j) := by
  by_cases hend : ∃ e, comp σ e = C ∧ k ≤ (σ e : ℕ)
  · obtain ⟨e, heC, he⟩ := hend
    -- every step of `C` reaches the end `e` by following `adj σ`
    have hreach : ∀ x y, Relation.EqvGen (adj σ) x y →
        (Relation.ReflTransGen (adj σ) x e ↔ Relation.ReflTransGen (adj σ) y e) := by
      intro x y hxy
      induction hxy with
      | rel x y hxy =>
        refine ⟨fun hx => ?_, fun hy => Relation.ReflTransGen.head hxy hy⟩
        rcases hx.cases_head with rfl | ⟨c, hxc, hc⟩
        · exact absurd (show (σ x : ℕ) < k from hxy ▸ y.isLt) (not_lt.mpr he)
        · exact adj_functional hxc hxy ▸ hc
      | refl => exact Iff.rfl
      | symm x y _ ih => exact ih.symm
      | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    have hunique : ∀ t, comp σ t = C → k ≤ (σ t : ℕ) → t = e := fun t htC ht => by
      have hte : Relation.EqvGen (adj σ) t e := Quotient.exact (htC.trans heC.symm)
      rcases ((hreach t e hte).mpr Relation.ReflTransGen.refl).cases_head with h | ⟨c, htc, -⟩
      · exact h
      · exact absurd (show (σ t : ℕ) < k from htc ▸ c.isLt) (not_lt.mpr ht)
    refine Or.inr ⟨σ e, he, fun c => ⟨?_, ?_⟩⟩
    · rintro ⟨t, htC, ht | ht⟩
      · exact Or.inl ⟨t, mem_steps.mpr htC, ht⟩
      · by_cases hlt : (σ t : ℕ) < k
        · refine Or.inl ⟨⟨σ t, hlt⟩, mem_steps.mpr ?_, by simp [ht]⟩
          exact (comp_eq_of_adj (show adj σ t ⟨σ t, hlt⟩ from rfl)).symm.trans htC
        · exact Or.inr (by rw [← ht, hunique t htC (not_lt.mp hlt)])
    · rintro (⟨t, ht, htc⟩ | rfl)
      · exact ⟨t, mem_steps.mp ht, Or.inl htc⟩
      · exact ⟨e, heC, Or.inr rfl⟩
  · push_neg at hend
    refine Or.inl fun c hc => ?_
    obtain ⟨t, htC, ht | ht⟩ := hc
    · rw [← ht]; exact t.isLt
    · rw [← ht]; exact hend t htC

/-- A component has at most one item outside `[k]`. -/
theorem card_outer_le_one (C : Component σ) : (outer σ C).card ≤ 1 := by
  rcases component_items C with h | ⟨j, -, hj⟩
  · rw [card_eq_zero.mpr]
    · exact zero_le_one
    · ext c
      simp only [mem_outer, Finset.notMem_empty, iff_false, not_and, not_le]
      exact h c
  · refine card_le_one.mpr fun a ha b hb => ?_
    have key : ∀ c ∈ outer σ C, c = j := fun c hc => by
      obtain ⟨hc, hck⟩ := mem_outer.mp hc
      rcases (hj c).mp hc with ⟨t, -, ht⟩ | rfl
      · exact absurd (ht ▸ t.isLt) (not_lt.mpr hck)
      · rfl
    rw [key a ha, key b hb]

end SwapGreedy
