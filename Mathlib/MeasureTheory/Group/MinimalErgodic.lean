/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Group.LpAction
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Order.Filter.EventuallyConst

/-!
-/

open Function Set Filter Topology MulOpposite
open scoped Pointwise ENNReal

namespace MeasureTheory

variable {G : Type _}
  [Group G] [TopologicalSpace G] [TopologicalGroup G] [CompactSpace G] [NormalSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {μ : MeasureTheory.Measure G} [μ.WeaklyRegular] [μ.IsHaarMeasure]

attribute [local instance] CompactSpace.isFiniteMeasure in
-- Do not use this lemma. It is generalized below
theorem Lp_one.eq_const_of_forall_dense_smulRight_eq (f : G →₁[μ] ℝ) {s : Set G} (hd : Dense s)
    (hf : ∀ a ∈ s, op a • f = f) : f = Lp.const 1 μ (⨍ x, f x ∂μ) := by
  haveI := Fact.mk ENNReal.one_ne_top
  -- have : ContinuousSMul Gᵐᵒᵖ (G →₁[μ] ℝ) := inferInstance
  replace hf : ∀ a : G, op a • f = f := fun a ↦
    closure_minimal hf (isClosed_eq (continuous_op.smul continuous_const) continuous_const) (hd a)
  replace hf : ∀ a : G, (f <| a • ·) =ᵐ[μ] f := fun a ↦
    (Lp.coeFn_smulRight (op a) _).symm.trans (by rw [hf])
  rw [← dist_le_zero, L1.dist_eq_integral_dist]
  calc
    ∫ a, dist (f a) (Lp.const 1 μ (⨍ x, f x ∂μ) a) ∂μ = ∫ a, ‖f a - ⨍ x, f x ∂μ‖ ∂μ :=
      integral_congr_ae <| (Lp.coeFn_const 1 μ (⨍ x, f x ∂μ)).mono fun x hx ↦ by
        simp only [hx, Function.const, dist_eq_norm]
    _ ≤ _ := _

open MulOpposite in
/-- If a set in a compact topological group is a.e. invariant under left multiplications by a
elements from a dense set, then it has either measure zero or full measure. -/
theorem NullMeasurableSet.aeConst_of_forall_dense_smul_ae_eq {s t : Set G} (hs : Dense s)
    (htm₀ : NullMeasurableSet t μ) (ht : ∀ a ∈ s, a • t =ᵐ[μ] t) :
    EventuallyConst t μ.ae := by
  -- Step 1: WLOG, `t` is Borel measurable
  -- TODO: redefine `indicatorConstLp` for null-measurable sets and get rid of this step
  wlog htm : MeasurableSet t generalizing t
  · rcases htm₀ with ⟨t', ht'm, htt'⟩
    refine EventuallyConst.congr (this ht'm.nullMeasurableSet (fun a ha ↦ ?_) ht'm) htt'.symm
    refine EventuallyEq.trans ?_ ((ht _ ha).trans htt')
    -- TODO: Add `smul_ae_eq`
    simp only [← preimage_smul_inv]
    exact (measurePreserving_smul _ _).quasiMeasurePreserving.preimage_ae_eq htt'.symm
  -- Step 2: Reformulate in terms of indicator of `t` as an element of `L¹`
  haveI : IsFiniteMeasure μ := CompactSpace.isFiniteMeasure
  set f : Lp ℝ 1 μ := indicatorConstLp 1 htm (measure_ne_top _ _) 1
  have hf : ∀ a ∈ s, op a • f = f := fun a ha ↦ by
    simp only [Lp.smulRight_def, Lp.indicatorConstLp_compMeasurePreserving, unop_op,
      preimage_smul]
    refine (Memℒp.toLp_eq_toLp_iff _ _).2 (indicator_eventuallyEq (EventuallyEq.refl _ _) ?_)
    exact inv_smul_ae_eq_self (ht a ha)
  -- Step 3: apply theorem about `L¹`
  have hfc : EventuallyConst f μ.ae
  · rcases Lp_one.eq_const_of_forall_dense_smulRight_eq f hs hf with ⟨c, hc⟩
    exact ⟨c, hc.symm ▸ Lp.coeFn_const _ _ _⟩
  exact .of_indicator_const (one_ne_zero (α := ℝ)) (hfc.congr indicatorConstLp_coeFn)
