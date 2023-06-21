import Mathlib.MeasureTheory.Group.Action
import Mathlib.MeasureTheory.Function.ContinuousMapDense

open MulOpposite
open scoped ENNReal Pointwise Topology

namespace MeasureTheory

namespace Lp

variable {X E : Type _}
  [MeasurableSpace X] {μ : MeasureTheory.Measure X}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {p : ℝ≥0∞}

section MeasurableSMul

variable {M : Type _}
  [Monoid M] [MeasurableSpace M] [MulAction M X] [MeasurableSMul M X] [SMulInvariantMeasure M X μ]

@[to_additive]
instance smulRight : SMul Mᵐᵒᵖ (Lp E p μ) where
  smul c f := Lp.compMeasurePreserving (c.unop • · : X → X) (measurePreserving_smul _ μ) f

@[to_additive]
theorem smulRight_def (c : Mᵐᵒᵖ) (f : Lp E p μ) :
    c • f = Lp.compMeasurePreserving (c.unop • · : X → X) (measurePreserving_smul _ μ) f :=
  rfl

@[to_additive]
theorem coeFn_smulRight (c : Mᵐᵒᵖ) (f : Lp E p μ) : c • f =ᵐ[μ] (f <| c.unop • ·) :=
  Lp.coeFn_compMeasurePreserving _ _

@[to_additive]
instance rightMulAction : MulAction Mᵐᵒᵖ (Lp E p μ) where
  one_smul f := by
    simp_rw [smulRight_def, unop_one, one_smul]
    apply compMeasurePreserving_id_apply
  mul_smul c₁ c₂ f := by
    simp only [smulRight_def, compMeasurePreserving_compMeasurePreserving, (· ∘ ·), smul_smul, unop_mul]

@[to_additive]
instance isometric_smulRight [Fact (1 ≤ p)] : IsometricSMul Mᵐᵒᵖ (Lp E p μ) :=
  ⟨fun _ ↦ Lp.compMeasurePreserving_isometry _⟩

-- TODO: why `inferInstance` fails?
@[to_additive]
instance [Fact (1 ≤ p)] : ContinuousConstSMul Mᵐᵒᵖ (Lp E p μ) :=
  IsometricSMul.to_continuousConstSMul _ _

-- TODO: What should be the additive version? Not yet defined `AddDistribAddAction`?
instance rightDistribMulAction : DistribMulAction Mᵐᵒᵖ (Lp E p μ) where
  smul_zero _ := map_zero (compMeasurePreserving _ _)
  smul_add _ := map_add (compMeasurePreserving _ _)

end MeasurableSMul

section ContinuousSMul

variable {M : Type _}
  [Monoid M] [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [MulAction M X] [TopologicalSpace X] [NormalSpace X] [BorelSpace X] [ContinuousSMul M X]
  [CompactSpace X] [SecondCountableTopologyEither X E] [SMulInvariantMeasure M X μ]
  [IsFiniteMeasure μ] [μ.WeaklyRegular] [Fact (1 ≤ p)] [hp : Fact (p ≠ ∞)]

instance : ContinuousSMul Mᵐᵒᵖ (Lp E p μ) where
  continuous_smul := by
    refine ((Homeomorph.prodComm _ _).trans <|
      opHomeomorph.prodCongr (Homeomorph.refl _)).comp_continuous_iff'.1 ?_
    apply continuous_prod_of_dense_continuous_lipschitzWith _ 1
      (ContinuousMap.toLp_denseRange E μ hp.out ℝ)
    · rintro _ ⟨f, rfl⟩
      have : Continuous (fun c : M ↦ f.comp ⟨(c • · : X → X), continuous_const_smul c⟩) :=
        f.continuous_comp.comp (ContinuousMap.mk _ continuous_smul).curry.continuous
      exact (ContinuousMap.toLp p μ ℝ).continuous.comp this
    · intro c
      dsimp
      exact (isometry_smul _ (op c)).lipschitz

end ContinuousSMul

end Lp    

end MeasureTheory
