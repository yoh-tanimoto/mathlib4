import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Function.LpSpace

open MulOpposite
open scoped ENNReal Pointwise Topology

namespace MeasureTheory

namespace Lp

variable {M G X E : Type _}
  [MeasurableSpace X] {μ : MeasureTheory.Measure X}
  [Monoid M] [MeasurableSpace M] [MulAction M X] [MeasurableSMul M X] [SMulInvariantMeasure M X μ]
  [Group G] [MeasurableSpace G] [MulAction G X] [MeasurableSMul G X] [SMulInvariantMeasure G X μ]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {p : ℝ≥0∞}

@[to_additive]
instance smulRight : SMul Mᵐᵒᵖ (Lp E p μ) where
  smul c f := Lp.compMeasurePreserving (c.unop • · : X → X) (measurePreserving_smul _ μ) f

@[to_additive]
theorem smulRight_def (c : Mᵐᵒᵖ) (f : Lp E p μ) :
    c • f = Lp.compMeasurePreserving (c.unop • · : X → X) (measurePreserving_smul _ μ) f :=
  rfl

@[to_additive]
instance rightMulAction : MulAction Mᵐᵒᵖ (Lp E p μ) where
  one_smul f := by
    simp_rw [smulRight_def, unop_one, one_smul]
    apply compMeasurePreserving_id_apply
  mul_smul c₁ c₂ f := by
    simp only [smulRight_def, compMeasurePreserving_compMeasurePreserving, (· ∘ ·), smul_smul, unop_mul]

instance [TopologicalSpace G] [TopologicalGroup G] [BorelSpace G] [Fact (1 ≤ p)] :
    ContinuousSMul Gᵐᵒᵖ (Lp E p μ) where
  continuous_smul := by
    refine (opHomeomorph.prodCongr (Homeomorph.refl _)).comp_continuous_iff'.1 ?_
    -- rintro ⟨⟨g⟩, f⟩
    -- simp only [smulRight_def, ContinuousAt, unop]
    

-- TODO: What should be the additive version? Not yet defined `AddDistribAddAction`?
instance rightDistribMulAction : DistribMulAction Mᵐᵒᵖ (Lp E p μ) where
  smul_zero _ := map_zero (compMeasurePreserving _ _)
  smul_add _ := map_add (compMeasurePreserving _ _)

-- theorem smulRight_indicatorConstLp_smul {s : Set X} (hs : MeasurableSet s) (hsμ : μ s ≠ ∞) (c : E) (g : G) :
--     MulOpposite.op g • indicatorConstLp p hs hsμ c =
--       indicatorConstLp p (s := g⁻¹ • s) _ (by rwa [measure_smul]) c  := _

end Lp    

end MeasureTheory
