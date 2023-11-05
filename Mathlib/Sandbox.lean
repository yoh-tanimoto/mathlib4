import Mathlib.MeasureTheory.Constructions.Prod.Basic

open MeasureTheory

theorem MeasureTheory.Measure.prod_noAtoms_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SigmaFinite ν] [NoAtoms μ] :
    NoAtoms (Measure.prod μ ν) := by
  refine NoAtoms.mk (fun x => ?_)
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, measure_singleton, zero_mul]

theorem MeasureTheory.Measure.prod_noAtoms_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SigmaFinite ν] [NoAtoms ν] :
    NoAtoms (Measure.prod μ ν) := by
  refine NoAtoms.mk (fun x => ?_)
  rw [← Set.singleton_prod_singleton, Measure.prod_prod, measure_singleton (μ := ν), mul_zero]

instance MeasureTheory.Measure.prod_noAtoms' {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SigmaFinite ν] [NoAtoms μ] [NoAtoms ν] :
    NoAtoms (Measure.prod μ ν) := MeasureTheory.Measure.prod_noAtoms_fst

