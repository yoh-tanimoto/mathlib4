import Mathlib.MeasureTheory.Group.FundamentalDomain

open MeasureTheory MeasureTheory.Measure

@[to_additive]
theorem MeasureTheory.IsFundamentalDomain.measure_ne_zero
    {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] (s : Set α)
    {μ : Measure α} [MeasurableSpace G] [MeasurableSMul G α] [Countable G]
    [SMulInvariantMeasure G α μ] (hμ : μ ≠ 0)
    (h : IsFundamentalDomain G s μ) :
    μ s ≠ 0 := by
  have hc := measure_univ_pos.mpr hμ
  contrapose! hc
  rw [← measure_congr h.iUnion_smul_ae_eq]
  refine le_trans (measure_iUnion_le _) ?_
  simp_rw [measure_smul, hc, tsum_zero, le_refl]

