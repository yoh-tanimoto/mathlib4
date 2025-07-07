/-
Copyright (c) 2022 Jesse Reimann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Reimann, Kalle Kytölä, Yoh Tanimoto
-/
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.Sets.Compacts
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.Topology.UrysohnsLemma


#align_import measure_theory.integral.riesz_markov_kakutani from "leanprover-community/mathlib"@"b2ff9a3d7a15fd5b0f060b135421d6a89a999c2f"

/-!
#  Riesz–Markov–Kakutani representation theorem

This file will prove different versions of the Riesz-Markov-Kakutani representation theorem.
The theorem is first proven for compact spaces, from which the statements about linear functionals
on bounded continuous functions or compactly supported functions on locally compact spaces follow.

To make use of the existing API, the measure is constructed from a content `λ` on the
compact subsets of the space X, rather than the usual construction of open sets in the literature.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/


noncomputable section

open BoundedContinuousFunction NNReal ENNReal

open Set Function TopologicalSpace

variable {X : Type*} [TopologicalSpace X]
variable (Λ : (X →ᵇ ℝ≥0) →ₗ[ℝ≥0] ℝ≥0)

/-! ### Construction of the content: -/


/-- Given a positive linear functional Λ on X, for `K ⊆ X` compact define
`λ(K) = inf {Λf | 1≤f on K}`. When X is a compact Hausdorff space, this will be shown to be a
content, and will be shown to agree with the Riesz measure on the compact subsets `K ⊆ X`. -/
def rieszContentAux : Compacts X → ℝ≥0 := fun K =>
  sInf (Λ '' { f : X →ᵇ ℝ≥0 | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x })
#align riesz_content_aux rieszContentAux

section RieszMonotone

/-- For any compact subset `K ⊆ X`, there exist some bounded continuous nonnegative
functions f on X such that `f ≥ 1` on K. -/
theorem rieszContentAux_image_nonempty (K : Compacts X) :
    (Λ '' { f : X →ᵇ ℝ≥0 | ∀ x ∈ K, (1 : ℝ≥0) ≤ f x }).Nonempty := by
  rw [image_nonempty]
  use (1 : X →ᵇ ℝ≥0)
  intro x _
  simp only [BoundedContinuousFunction.coe_one, Pi.one_apply]; rfl
#align riesz_content_aux_image_nonempty rieszContentAux_image_nonempty

/-- Riesz content λ (associated with a positive linear functional Λ) is
monotone: if `K₁ ⊆ K₂` are compact subsets in X, then `λ(K₁) ≤ λ(K₂)`. -/
theorem rieszContentAux_mono {K₁ K₂ : Compacts X} (h : K₁ ≤ K₂) :
    rieszContentAux Λ K₁ ≤ rieszContentAux Λ K₂ :=
  csInf_le_csInf (OrderBot.bddBelow _) (rieszContentAux_image_nonempty Λ K₂)
    (image_subset Λ (setOf_subset_setOf.mpr fun _ f_hyp x x_in_K₁ => f_hyp x (h x_in_K₁)))
#align riesz_content_aux_mono rieszContentAux_mono

end RieszMonotone

section RieszSubadditive

/-- Any bounded continuous nonnegative f such that `f ≥ 1` on K gives an upper bound on the
content of K; namely `λ(K) ≤ Λ f`. -/
theorem rieszContentAux_le {K : Compacts X} {f : X →ᵇ ℝ≥0} (h : ∀ x ∈ K, (1 : ℝ≥0) ≤ f x) :
    rieszContentAux Λ K ≤ Λ f :=
  csInf_le (OrderBot.bddBelow _) ⟨f, ⟨h, rfl⟩⟩
#align riesz_content_aux_le rieszContentAux_le

/-- The Riesz content can be approximated arbitrarily well by evaluating the positive linear
functional on test functions: for any `ε > 0`, there exists a bounded continuous nonnegative
function f on X such that `f ≥ 1` on K and such that `λ(K) ≤ Λ f < λ(K) + ε`. -/
theorem exists_lt_rieszContentAux_add_pos (K : Compacts X) {ε : ℝ≥0} (εpos : 0 < ε) :
    ∃ f : X →ᵇ ℝ≥0, (∀ x ∈ K, (1 : ℝ≥0) ≤ f x) ∧ Λ f < rieszContentAux Λ K + ε := by
  --choose a test function `f` s.t. `Λf = α < λ(K) + ε`
  obtain ⟨α, ⟨⟨f, f_hyp⟩, α_hyp⟩⟩ :=
    exists_lt_of_csInf_lt (rieszContentAux_image_nonempty Λ K)
      (lt_add_of_pos_right (rieszContentAux Λ K) εpos)
  refine' ⟨f, f_hyp.left, _⟩
  rw [f_hyp.right]
  exact α_hyp
#align exists_lt_riesz_content_aux_add_pos exists_lt_rieszContentAux_add_pos

/-- The Riesz content λ associated to a given positive linear functional Λ is
finitely subadditive: `λ(K₁ ∪ K₂) ≤ λ(K₁) + λ(K₂)` for any compact subsets `K₁, K₂ ⊆ X`. -/
theorem rieszContentAux_sup_le {K1 K2 : Compacts X} :
    rieszContentAux Λ (K1 ⊔ K2) ≤ rieszContentAux Λ K1 + rieszContentAux Λ K2 := by
  apply NNReal.le_of_forall_pos_le_add
  intro ε εpos
  --get test functions s.t. `λ(Ki) ≤ Λfi ≤ λ(Ki) + ε/2, i=1,2`
  obtain ⟨f1, f_test_function_K1⟩ := exists_lt_rieszContentAux_add_pos Λ K1 (half_pos εpos)
  obtain ⟨f2, f_test_function_K2⟩ := exists_lt_rieszContentAux_add_pos Λ K2 (half_pos εpos)
  --let `f := f1 + f2` test function for the content of `K`
  have f_test_function_union : ∀ x ∈ K1 ⊔ K2, (1 : ℝ≥0) ≤ (f1 + f2) x := by
    rintro x (x_in_K1 | x_in_K2)
    · exact le_add_right (f_test_function_K1.left x x_in_K1)
    · exact le_add_left (f_test_function_K2.left x x_in_K2)
  --use that `Λf` is an upper bound for `λ(K1⊔K2)`
  apply (rieszContentAux_le Λ f_test_function_union).trans (le_of_lt _)
  rw [map_add]
  --use that `Λfi` are lower bounds for `λ(Ki) + ε/2`
  apply lt_of_lt_of_le (_root_.add_lt_add f_test_function_K1.right f_test_function_K2.right)
    (le_of_eq _)
  rw [add_assoc, add_comm (ε / 2), add_assoc, add_halves ε, add_assoc]
#align riesz_content_aux_sup_le rieszContentAux_sup_le

end RieszSubadditive

section RieszAdditive

def toBCF_of_Icc (g : C(X, ℝ)) (hg : ∀ (x : X), 0 ≤ g x ∧ g x ≤ 1) : X →ᵇ ℝ≥0 :=
  ⟨⟨ fun x => ⟨g x, (hg x).1⟩,
      by sorry⟩,
      by
    use 1
    intro x y
    simp only
    rw [NNReal.dist_eq]
    simp only [coe_mk]
    rw [abs_le]
    simp only [neg_le_sub_iff_le_add, tsub_le_iff_right]
    constructor
    · rw [add_comm]
      exact le_add_of_le_of_nonneg (hg y).2 (hg x).1
    · exact le_add_of_le_of_nonneg (hg x).2 (hg y).1⟩

def toBCF_of_one_sub_Icc (g₀ : X →ᵇ ℝ≥0) (hg₀ : ∀ (x : X), g₀ x ≤ 1) : X →ᵇ ℝ≥0 :=
  ⟨⟨  fun x => ⟨1 - g₀ x, sub_nonneg.mpr (hg₀ x)⟩,
      by sorry⟩,
      by
    use 1
    intro x y
    simp only
    rw [NNReal.dist_eq]
    simp only [coe_mk, sub_sub_sub_cancel_left]
    rw [abs_le]
    simp only [neg_le_sub_iff_le_add, tsub_le_iff_right]
    constructor
    · rw [add_comm]
      apply le_add_of_le_of_nonneg (NNReal.coe_le_one.mpr (hg₀ x))
      simp only [zero_le_coe]
    · apply le_add_of_le_of_nonneg (NNReal.coe_le_one.mpr (hg₀ y))
      simp only [zero_le_coe]⟩

variable (f g : X →ᵇ ℝ≥0)
#check f * g


theorem rieszContentAux_eq_add [T2Space X] [LocallyCompactSpace X] [RegularSpace X] {K₁ K₂ : Compacts X} (h : Disjoint K₁ K₂) :
    rieszContentAux Λ (K₁ ⊔ K₂) = rieszContentAux Λ K₁ + rieszContentAux Λ K₂ := by
  apply le_antisymm
  · exact rieszContentAux_sup_le Λ
  · apply le_csInf
    · exact rieszContentAux_image_nonempty Λ (K₁ ⊔ K₂)
    · intro b hb
      obtain ⟨f, hf⟩ := hb
      simp only [mem_setOf_eq] at hf
      have hDisjoint : Disjoint K₁.carrier K₂.carrier := by
        rw [disjoint_iff]
        rw [disjoint_iff] at h
        simp only [inf_eq_inter, bot_eq_empty]
        simp only [Compacts.carrier_eq_coe]
        rw [← TopologicalSpace.Compacts.coe_inf]
        rw [← Compacts.carrier_eq_coe]
        rw [h]
        exact rfl
      obtain ⟨g, hg⟩ := exists_continuous_zero_one_of_isCompact K₁.isCompact'
        (IsCompact.isClosed K₂.isCompact') hDisjoint
      simp only [Compacts.carrier_eq_coe, mem_Icc] at hg
      set g₀ := toBCF_of_Icc g hg.2.2 with hg₀
      set g₁ := toBCF_of_one_sub_Icc g₀ (fun x => (hg.2.2 x).2) with hg₁

      have h1 : rieszContentAux Λ K₁ ≤ Λ (f * g₁) := by
        apply csInf_le (rieszContentAux_image_BddBelow Λ hΛ K₁)
        simp only [mem_image, mem_setOf_eq]
        use f * (1 - g)
        constructor
        constructor
        exact HasCompactSupport.mul_right hf.1.1
        constructor
        · intro x
          simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply]
          exact mul_nonneg (hf.1.2.1 x) (unitInterval.one_minus_nonneg ⟨(g x), hg.2.2 x⟩)
        · intro x hx
          simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply]
          have hgx : g x = 0 := by
            rw [hg.1 hx]
            simp only [Pi.zero_apply]
          rw [hgx]
          simp only [sub_zero, mul_one, ge_iff_le]
          exact hf.1.2.2 x ((Set.mem_union x K₁ K₂).mpr (Or.inl hx))
        · rfl
      have h2 : rieszContentAux Λ K₂ ≤ Λ (f * g) := by
        apply csInf_le (rieszContentAux_image_BddBelow Λ hΛ K₂)
        simp only [mem_image, mem_setOf_eq]
        use f * g
        constructor
        constructor
        exact HasCompactSupport.mul_right hf.1.1
        constructor
        · intro x
          simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply]
          exact mul_nonneg (hf.1.2.1 x) (hg.2.2 x).1
        · intro x hx
          simp only [ContinuousMap.mul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply]
          have hgx : g x = 1 := by
            rw [hg.2.1 hx]
            simp only [Pi.one_apply]
          rw [hgx]
          simp only [sub_zero, mul_one, ge_iff_le]
          exact hf.1.2.2 x ((Set.mem_union x K₁ K₂).mpr (Or.inr hx))
        · rfl
      have hb : b = Λ (f * (1 - g) + f * g) := by
        ring_nf
        exact (hf.2).symm
      rw [hb]
      simp only [map_add, ge_iff_le]
      exact add_le_add h1 h2

end RieszAdditive

variable [T2Space X] [LocallyCompactSpace X] [RegularSpace X]

def rieszContent : MeasureTheory.Content X where
  toFun := rieszContentAux Λ
  mono' := by
    intro K₁ K₂ h
    exact rieszContentAux_mono Λ h
  sup_disjoint' := by
    intro K₁ K₂ hDisjoint _ _
    have : Disjoint K₁ K₂ := by
        rw [disjoint_iff]
        rw [disjoint_iff] at hDisjoint
        simp only [inf_eq_inter, bot_eq_empty] at hDisjoint
        apply TopologicalSpace.Compacts.ext
        simp only [Compacts.coe_inf, Compacts.coe_bot]
        exact hDisjoint
    exact rieszContentAux_eq_add Λ this
  sup_le' := by
    intro K₁ K₂
    exact rieszContentAux_sup_le Λ
