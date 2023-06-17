/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.Average

/-!
-/

open Function Set Filter Topology MeasureTheory

variable {G E : Type _}
  [Group G] [TopologicalSpace G] [TopologicalGroup G] [CompactSpace G] [NormalSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {μ : MeasureTheory.Measure G} [μ.WeaklyRegular] [μ.IsHaarMeasure]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem L1.eq_average_of_dense_eq_comp_const_mul {f : G →₁[μ] E} {s : Set G} (hd : Dense s)
    (hsf : ∀ a ∈ s, f =ᵐ[μ] (f <| a * ·)) :
    f =ᵐ[μ] const G (⨍ x, f x ∂μ) := by
  

theorem Integrable.ae_eq_average_of_dense_ae_eq_comp_const_mul {f : G → E}
    (hf : Integrable f μ) {s : Set G} (hd : Dense s) (hsf : ∀ a ∈ s, f =ᵐ[μ] (f <| a * ·)) :
    f =ᵐ[μ] const G (⨍ x, f x ∂μ) := by
  -- have := hf.exists_boundedContinuous_integral_sub_le
  
  -- wlog hf' : ∃ f' : G →₁[μ] E, f = f' generalizing f
  -- · calc
  --     f =ᵐ[μ] hf.toL1 f := hf.coeFn_toL1.symm
  --     _ =ᵐ[μ] const G (⨍ x, hf.toL1 f x ∂μ) := by
  --       refine this (AEEqFun.integrable_iff_mem_L1.2 (hf.toL1 _).2) (fun a ha ↦ ?_) ⟨_, rfl⟩
  --       calc
  --         hf.toL1 f =ᵐ[μ] f := hf.coeFn_toL1
  --         _ =ᵐ[μ] (f <| a * ·) := hsf a ha
  --         _ =ᵐ[μ] (hf.toL1 f <| a * ·) :=
  --           (measurePreserving_mul_left μ a).quasiMeasurePreserving.ae hf.coeFn_toL1.symm
  --     _ = const G (⨍ x, f x ∂μ) := congr_arg _ <| average_congr hf.coeFn_toL1
  -- rcases hf' with ⟨f, rfl⟩; clear hf
