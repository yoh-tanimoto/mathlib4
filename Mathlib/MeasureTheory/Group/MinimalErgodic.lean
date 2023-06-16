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

theorem Integrable.ae_eq_average_of_dense_ae_eq_comp_const_mul {f : G → E}
    (hf : Integrable f μ) {s : Set G} (hd : Dense s) (hsf : ∀ g ∈ s, f =ᵐ[μ] (f <| g * ·)) :
    f =ᵐ[μ] const G (⨍ x, f x ∂μ) := by
  wlog hf' : ∃ f' : G →₁[μ] E, f = f' generalizing f
  · calc
      f =ᵐ[μ] hf.toL1 f := hf.coeFn_toL1.symm
      _ =ᵐ[μ] _ := _
