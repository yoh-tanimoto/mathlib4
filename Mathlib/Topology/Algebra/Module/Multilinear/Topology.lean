/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.Topology.Algebra.Module.StrongTopology

open scoped Topology UniformConvergence

namespace ContinuousMultilinearMap

variable {𝕜 ι : Type*} {E : ι → Type*} {F : Type*}
  [NormedField 𝕜]
  [∀ i, TopologicalSpace (E i)] [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)]
  [AddCommGroup F] [Module 𝕜 F]

/-- An auxiliary definition used to define topology on `ContinuousMultilinearMap 𝕜 E F`. -/
def toUniformOnFun [TopologicalSpace F] (f : ContinuousMultilinearMap 𝕜 E F) :
    (∀ i, E i) →ᵤ[{s | Bornology.IsVonNBounded 𝕜 s}] F :=
  ⇑f

@[simp]
lemma toUniofrmOnFun_toFun [TopologicalSpace F] (f : ContinuousMultilinearMap 𝕜 E F) :
    UniformOnFun.toFun _ f.toUniformOnFun = f :=
  rfl

instance topologicalSpace [TopologicalSpace F] [TopologicalAddGroup F] :
    TopologicalSpace (ContinuousMultilinearMap 𝕜 E F) :=
  letI := TopologicalAddGroup.toUniformSpace F
  .induced toUniformOnFun <| UniformOnFun.topologicalSpace ..

instance [UniformSpace F] [UniformAddGroup F] : UniformSpace (ContinuousMultilinearMap 𝕜 E F) :=
  .replaceTopology (.comap toUniformOnFun <| UniformOnFun.uniformSpace ..) <| by
    rw [topologicalSpace, UniformAddGroup.toUniformSpace_eq]; rfl

lemma uniformEmbedding_toUniformOnFun [UniformSpace F] [UniformAddGroup F] :
    UniformEmbedding (toUniformOnFun : ContinuousMultilinearMap 𝕜 E F → _) :=
  ⟨⟨rfl⟩, FunLike.coe_injective⟩

lemma embedding_toUniformOnFun [UniformSpace F] [UniformAddGroup F] :
    Embedding (toUniformOnFun : ContinuousMultilinearMap 𝕜 E F → _) :=
  uniformEmbedding_toUniformOnFun.embedding

instance [UniformSpace F] [UniformAddGroup F] : UniformAddGroup (ContinuousMultilinearMap 𝕜 E F) :=
  let φ : ContinuousMultilinearMap 𝕜 E F →+ (∀ i, E i) →ᵤ[{s | Bornology.IsVonNBounded 𝕜 s}] F :=
    { toFun := toUniformOnFun, map_add' := fun _ _ ↦ rfl, map_zero' := rfl }
  uniformEmbedding_toUniformOnFun.uniformAddGroup φ

instance [TopologicalSpace F] [TopologicalAddGroup F] :
    TopologicalAddGroup (ContinuousMultilinearMap 𝕜 E F) :=
  letI := TopologicalAddGroup.toUniformSpace F
  haveI := comm_topologicalAddGroup_is_uniform (G := F)
  inferInstance

instance {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F]
    [UniformSpace F] [UniformAddGroup F] [ContinuousConstSMul M F] :
    UniformContinuousConstSMul M (ContinuousMultilinearMap 𝕜 E F) :=
  haveI := uniformContinuousConstSMul_of_continuousConstSMul M F
  uniformEmbedding_toUniformOnFun.toUniformInducing.uniformContinuousConstSMul fun _ _ ↦ rfl

instance {M : Type*} [Monoid M] [DistribMulAction M F] [SMulCommClass 𝕜 M F]
    [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousConstSMul M F] :
    ContinuousConstSMul M (ContinuousMultilinearMap 𝕜 E F) :=
  letI := TopologicalAddGroup.toUniformSpace F
  haveI := comm_topologicalAddGroup_is_uniform (G := F)
  inferInstance

instance [TopologicalSpace F] [TopologicalAddGroup F] [ContinuousSMul 𝕜 F] :
    ContinuousSMul 𝕜 (ContinuousMultilinearMap 𝕜 E F) := by
  letI := TopologicalAddGroup.toUniformSpace F
  haveI := comm_topologicalAddGroup_is_uniform (G := F)
  let φ : ContinuousMultilinearMap 𝕜 E F →ₗ[𝕜] (∀ i, E i) →ᵤ[{s | Bornology.IsVonNBounded 𝕜 s}] F :=
    { toFun := toUniformOnFun, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  refine UniformOnFun.continuousSMul_induced_of_image_bounded _ _ _ _ ?_ ?_ φ
    embedding_toUniformOnFun.toInducing fun f u hu ↦ ?_
  · exact ⟨∅, Bornology.isVonNBounded_empty _ _⟩
  · exact (directedOn_of_sup_mem fun _ _ => Bornology.IsVonNBounded.union)
  · exact hu.image _
-- UniformOnFun.continuousSMul_induced_of_image_bounded
end ContinuousMultilinearMap
