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

@[to_additive]
theorem Filter.EventuallyEq.of_mulIndicator_const {α β : Type _} [One β] {l : Filter α} {c : β}
    (hc : c ≠ 1) {s t : Set α} (h : s.mulIndicator (fun _ ↦ c) =ᶠ[l] t.mulIndicator fun _ ↦ c) :
    s =ᶠ[l] t := by
  have : ∀ s : Set α, s.mulIndicator (fun _ ↦ c) ⁻¹' {c} = s := fun s ↦ by
    rw [mulIndicator_preimage_of_not_mem, preimage_const_of_mem (mem_singleton _), univ_inter]
    exact hc.symm
  simpa only [this] using h.preimage {c}

variable {G E : Type _}
  [Group G] [TopologicalSpace G] [TopologicalGroup G] [CompactSpace G] [NormalSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {μ : MeasureTheory.Measure G} [μ.WeaklyRegular] [μ.IsHaarMeasure]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

