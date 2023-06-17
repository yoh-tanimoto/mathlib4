/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Separation
import Mathlib.Order.Filter.CountableInter

open Filter Set Topology TopologicalSpace

variable {α X : Type _} [TopologicalSpace X] [T0Space X] [SecondCountableTopology X]
  {f g : α → X} {l : Filter α} [CountableInterFilter l]

theorem Filter.EventuallyEq.of_forall_open_mem_iff
    (h : ∀ U : Set X, IsOpen U → ∀ᶠ x in l, f x ∈ U ↔ g x ∈ U) : f =ᶠ[l] g :=
  have H : ∀ U ∈ countableBasis X, ∀ᶠ x in l, f x ∈ U ↔ g x ∈ U := fun U hU ↦
    h U (isOpen_of_mem_countableBasis hU)
  ((eventually_countable_ball <| countable_countableBasis _).2 H).mono fun _ ↦
    (isBasis_countableBasis X).eq_iff.mpr

theorem Filter.eventuallyEq_iff_forall_open_mem_iff :
    f =ᶠ[l] g ↔ ∀ U : Set X, IsOpen U → ∀ᶠ x in l, f x ∈ U ↔ g x ∈ U :=
  ⟨fun h U _ ↦ h.mono fun x hx ↦ by rw [hx], .of_forall_open_mem_iff⟩

theorem Filter.eventuallyEq_iff_forall_open_preimage :
    f =ᶠ[l] g ↔ ∀ U : Set X, IsOpen U → f ⁻¹' U =ᶠ[l] g ⁻¹' U :=
  eventuallyEq_iff_forall_open_mem_iff.trans <| by simp only [eventuallyEq_set, mem_preimage]

alias Filter.eventuallyEq_iff_forall_open_preimage ↔ _ Filter.EventuallyEq.of_forall_open_preimage
