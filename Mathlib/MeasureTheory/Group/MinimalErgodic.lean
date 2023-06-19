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

open Function Set Filter Topology

namespace MeasureTheory

variable {G : Type _}
  [Group G] [TopologicalSpace G] [TopologicalGroup G] [CompactSpace G] [NormalSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {μ : MeasureTheory.Measure G} [μ.WeaklyRegular] [μ.IsHaarMeasure]

/-- If a set in a compact topological group is a.e. invariant under left multiplications by a
elements from a dense set, then it has either measure zero or full measure. -/
theorem ae_eq_empty_or_univ_of_forall_dense_smul_ae_eq {s t : Set G} (hs : Dense s)
    (htm : NullMeasurableSet t μ) (ht : ∀ a ∈ s, a • t =ᵐ[μ] t) :
    t =ᵐ[μ] (∅ : Set G) ∨ t =ᵐ[μ] univ := by
  
