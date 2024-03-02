import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Function.Support
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.ContinuousFunction.CocompactMap
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousFunction.ZeroAtInfty
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner

open ZeroAtInfty Filter Urysohns

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
 [T2Space X] [MeasurableSpace X] [BorelSpace X]

variable (mu : MeasureTheory.Measure X)
variable (f : C₀(X, ℂ))
#check ∫ (x : X), f x ∂mu

theorem RMK (Λ : C₀(X, ℂ) → ℂ) : Continuous Λ ∧ (∀ (f : C₀(X, ℂ)) (x : X), ((f x).re ≥ 0 ∧ (f x).im = 0) → ((Λ f).re ≥ 0 ∧ (Λ f).im = 0)) →
 ∃ (μ : MeasureTheory.Measure X), (∀ (f : C₀(X, ℂ)), ∫ (x : X), f x ∂μ = Λ f) := by
 sorry
