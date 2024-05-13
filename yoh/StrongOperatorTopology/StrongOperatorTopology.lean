/-
Copyright (c) 2021 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yoh Tanimoto
-/
import Mathlib.Analysis.NormedSpace.Dual
import Mathlib.Analysis.NormedSpace.Star.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.Subalgebra
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.LinearAlgebra.BilinearMap
/-!
# Weak dual topology

This file defines the weak topology given two vector spaces `E` and `F` over a commutative semiring
`𝕜` and a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`. The weak topology on `E` is the coarsest topology
such that for all `y : F` every map `fun x => B x y` is continuous.

In the case that `F = E →L[𝕜] 𝕜` and `B` being the canonical pairing, we obtain the weak-* topology,
`WeakDual 𝕜 E := (E →L[𝕜] 𝕜)`. Interchanging the arguments in the bilinear form yields the
weak topology `WeakSpace 𝕜 E := E`.

## Main definitions

The main definitions are the types `WeakBilin B` for the general case and the two special cases
`WeakDual 𝕜 E` and `WeakSpace 𝕜 E` with the respective topology instances on it.

* Given `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, the type `WeakBilin B` is a type synonym for `E`.
* The instance `WeakBilin.instTopologicalSpace` is the weak topology induced by the bilinear form
  `B`.
* `WeakDual 𝕜 E` is a type synonym for `Dual 𝕜 E` (when the latter is defined): both are equal to
  the type `E →L[𝕜] 𝕜` of continuous linear maps from a module `E` over `𝕜` to the ring `𝕜`.
* The instance `WeakDual.instTopologicalSpace` is the weak-* topology on `WeakDual 𝕜 E`, i.e., the
  coarsest topology making the evaluation maps at all `z : E` continuous.
* `WeakSpace 𝕜 E` is a type synonym for `E` (when the latter is defined).
* The instance `WeakSpace.instTopologicalSpace` is the weak topology on `E`, i.e., the
  coarsest topology such that all `v : dual 𝕜 E` remain continuous.

## Main results

We establish that `WeakBilin B` has the following structure:
* `WeakBilin.instContinuousAdd`: The addition in `WeakBilin B` is continuous.
* `WeakBilin.instContinuousSMul`: The scalar multiplication in `WeakBilin B` is continuous.

We prove the following results characterizing the weak topology:
* `eval_continuous`: For any `y : F`, the evaluation mapping `fun x => B x y` is continuous.
* `continuous_of_continuous_eval`: For a mapping to `WeakBilin B` to be continuous,
  it suffices that its compositions with pairing with `B` at all points `y : F` is continuous.
* `tendsto_iff_forall_eval_tendsto`: Convergence in `WeakBilin B` can be characterized
  in terms of convergence of the evaluations at all points `y : F`.

## Notations

No new notation is introduced.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

weak-star, weak dual, duality

-/


noncomputable section

open Filter

open Topology

variable {α 𝕜 𝕝 R E F M : Type*}

section StrongOperatorTopology

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

namespace StrongOperatorTopology

def B_SOT (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] := (H →L[ℂ] H)

instance instTopologicalSpace : TopologicalSpace (B_SOT H) :=
  TopologicalSpace.induced (fun (x : H →L[ℂ] H) (v : H) => x v) Pi.topologicalSpace

#check B_SOT H

instance instAddCommMonoid [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
  AddCommMonoid (B_SOT H) := ContinuousLinearMap.addCommMonoid

instance instModule [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
  Module ℂ (B_SOT H) := ContinuousLinearMap.module

instance instAddCommGroup [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
  AddCommGroup (B_SOT H) := ContinuousLinearMap.addCommGroup

-- take instances from Mathlib.Analysis.InnerProductSpace.Adjoint

-- instance topologicalAddGroup [NormedAddCommGroup H] [InnerProductSpace ℂ H] :
--   TopologicalAddGroup B_SOT H :=



-- variable (x y : B_SOT H)
-- example : (x + y).toLinearMap = x.toLinearMap + y.toLinearMap := by
--   exact rfl

-- example : (x + y).toFun = x.toFun + y.toFun := by
--   exact rfl

-- instance (priority := 100) instModule' [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommGroup E]
--     [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [m : Module 𝕝 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
--     Module 𝕝 (WeakBilin B) := m
-- #align weak_bilin.module' WeakBilin.instModule'

-- instance instIsScalarTower [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommGroup E] [Module 𝕜 E]
--     [AddCommGroup F] [Module 𝕜 F] [SMul 𝕝 𝕜] [Module 𝕝 E] [s : IsScalarTower 𝕝 𝕜 E]
--     (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : IsScalarTower 𝕝 𝕜 (WeakBilin B) := s

-- section Semiring

-- variable [TopologicalSpace 𝕜] [CommSemiring 𝕜]
-- variable [AddCommMonoid E] [Module 𝕜 E]
-- variable [AddCommMonoid F] [Module 𝕜 F]
-- variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

-- instance instTopologicalSpace : TopologicalSpace (WeakBilin B) :=
--   TopologicalSpace.induced (fun x y => B x y) Pi.topologicalSpace

-- /-- The coercion `(fun x y => B x y) : E → (F → 𝕜)` is continuous. -/
-- theorem coeFn_continuous : Continuous fun (x : WeakBilin B) y => B x y :=
--   continuous_induced_dom
-- #align weak_bilin.coe_fn_continuous WeakBilin.coeFn_continuous

-- theorem eval_continuous (y : F) : Continuous fun x : WeakBilin B => B x y :=
--   (continuous_pi_iff.mp (coeFn_continuous B)) y
-- #align weak_bilin.eval_continuous WeakBilin.eval_continuous

-- theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakBilin B}
--     (h : ∀ y, Continuous fun a => B (g a) y) : Continuous g :=
--   continuous_induced_rng.2 (continuous_pi_iff.mpr h)
-- #align weak_bilin.continuous_of_continuous_eval WeakBilin.continuous_of_continuous_eval

-- /-- The coercion `(fun x y => B x y) : E → (F → 𝕜)` is an embedding. -/
-- theorem embedding {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (hB : Function.Injective B) :
--     Embedding fun (x : WeakBilin B) y => B x y :=
--   Function.Injective.embedding_induced <| LinearMap.coe_injective.comp hB
-- #align weak_bilin.embedding WeakBilin.embedding

-- theorem tendsto_iff_forall_eval_tendsto {l : Filter α} {f : α → WeakBilin B} {x : WeakBilin B}
--     (hB : Function.Injective B) :
--     Tendsto f l (𝓝 x) ↔ ∀ y, Tendsto (fun i => B (f i) y) l (𝓝 (B x y)) := by
--   rw [← tendsto_pi_nhds, Embedding.tendsto_nhds_iff (embedding hB)]
--   rfl
-- #align weak_bilin.tendsto_iff_forall_eval_tendsto WeakBilin.tendsto_iff_forall_eval_tendsto

-- /-- Addition in `WeakBilin B` is continuous. -/
-- instance instContinuousAdd [ContinuousAdd 𝕜] : ContinuousAdd (WeakBilin B) := by
--   refine' ⟨continuous_induced_rng.2 _⟩
--   refine'
--     cast (congr_arg _ _)
--       (((coeFn_continuous B).comp continuous_fst).add ((coeFn_continuous B).comp continuous_snd))
--   ext
--   simp only [Function.comp_apply, Pi.add_apply, map_add, LinearMap.add_apply]

-- /-- Scalar multiplication by `𝕜` on `WeakBilin B` is continuous. -/
-- instance instContinuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 (WeakBilin B) := by
--   refine' ⟨continuous_induced_rng.2 _⟩
--   refine' cast (congr_arg _ _) (continuous_fst.smul ((coeFn_continuous B).comp continuous_snd))
--   ext
--   simp only [Function.comp_apply, Pi.smul_apply, LinearMap.map_smulₛₗ, RingHom.id_apply,
--     LinearMap.smul_apply]

-- end Semiring

-- section Ring

-- variable [TopologicalSpace 𝕜] [CommRing 𝕜]
-- variable [AddCommGroup E] [Module 𝕜 E]
-- variable [AddCommGroup F] [Module 𝕜 F]


-- variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

-- /-- `WeakBilin B` is a `TopologicalAddGroup`, meaning that addition and negation are
-- continuous. -/
-- instance instTopologicalAddGroup [ContinuousAdd 𝕜] : TopologicalAddGroup (WeakBilin B) where
--   toContinuousAdd := by infer_instance
--   continuous_neg := by
--     refine' continuous_induced_rng.2 (continuous_pi_iff.mpr fun y => _)
--     refine' cast (congr_arg _ _) (eval_continuous B (-y))
--     ext x
--     simp only [map_neg, Function.comp_apply, LinearMap.neg_apply]

-- end Ring

-- end WeakBilin

-- end WeakTopology

-- section WeakStarTopology

-- /-- The canonical pairing of a vector space and its topological dual. -/
-- def topDualPairing (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [AddCommMonoid E]
--     [Module 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 𝕜] : (E →L[𝕜] 𝕜) →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
--   ContinuousLinearMap.coeLM 𝕜
-- #align top_dual_pairing topDualPairing

-- variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
-- variable [ContinuousConstSMul 𝕜 𝕜]
-- variable [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

-- theorem topDualPairing_apply (v : E →L[𝕜] 𝕜) (x : E) : topDualPairing 𝕜 E v x = v x :=
--   rfl
-- #align dual_pairing_apply topDualPairing_apply

-- /-- The weak star topology is the topology coarsest topology on `E →L[𝕜] 𝕜` such that all
-- functionals `fun v => v x` are continuous. -/
-- def WeakDual (𝕜 E : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
--     [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
--   WeakBilin (topDualPairing 𝕜 E)
-- #align weak_dual WeakDual

-- namespace WeakDual

-- -- Porting note: the next four instances should be derived from the definition
-- instance instAddCommMonoid : AddCommMonoid (WeakDual 𝕜 E) :=
--   WeakBilin.instAddCommMonoid (topDualPairing 𝕜 E)

-- instance instModule : Module 𝕜 (WeakDual 𝕜 E) :=
--   WeakBilin.instModule (topDualPairing 𝕜 E)

-- instance instTopologicalSpace : TopologicalSpace (WeakDual 𝕜 E) :=
--   WeakBilin.instTopologicalSpace (topDualPairing 𝕜 E)

-- instance instContinuousAdd : ContinuousAdd (WeakDual 𝕜 E) :=
--   WeakBilin.instContinuousAdd (topDualPairing 𝕜 E)

-- instance instInhabited : Inhabited (WeakDual 𝕜 E) :=
--   ContinuousLinearMap.inhabited

-- instance instFunLike : FunLike (WeakDual 𝕜 E) E 𝕜 :=
--   ContinuousLinearMap.funLike

-- instance instContinuousLinearMapClass : ContinuousLinearMapClass (WeakDual 𝕜 E) 𝕜 E 𝕜 :=
--   ContinuousLinearMap.continuousSemilinearMapClass
-- #align weak_dual.weak_dual.continuous_linear_map_class WeakDual.instContinuousLinearMapClass

-- /-- Helper instance for when there's too many metavariables to apply `DFunLike.hasCoeToFun`
-- directly. -/
-- instance : CoeFun (WeakDual 𝕜 E) fun _ => E → 𝕜 :=
--   DFunLike.hasCoeToFun

-- /-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
-- multiplication on `𝕜`, then it acts on `WeakDual 𝕜 E`. -/
-- instance instMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
--     [ContinuousConstSMul M 𝕜] : MulAction M (WeakDual 𝕜 E) :=
--   ContinuousLinearMap.mulAction

-- /-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
-- multiplication on `𝕜`, then it acts distributively on `WeakDual 𝕜 E`. -/
-- instance instDistribMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
--     [ContinuousConstSMul M 𝕜] : DistribMulAction M (WeakDual 𝕜 E) :=
--   ContinuousLinearMap.distribMulAction

-- /-- If `𝕜` is a topological module over a semiring `R` and scalar multiplication commutes with the
-- multiplication on `𝕜`, then `WeakDual 𝕜 E` is a module over `R`. -/
-- instance instModule' (R) [Semiring R] [Module R 𝕜] [SMulCommClass 𝕜 R 𝕜] [ContinuousConstSMul R 𝕜] :
--     Module R (WeakDual 𝕜 E) :=
--   ContinuousLinearMap.module
-- #align weak_dual.module' WeakDual.instModule'

-- instance instContinuousConstSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
--     [ContinuousConstSMul M 𝕜] : ContinuousConstSMul M (WeakDual 𝕜 E) :=
--   ⟨fun m =>
--     continuous_induced_rng.2 <| (WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).const_smul m⟩

-- /-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
-- multiplication on `𝕜`, then it continuously acts on `WeakDual 𝕜 E`. -/
-- instance instContinuousSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
--     [TopologicalSpace M] [ContinuousSMul M 𝕜] : ContinuousSMul M (WeakDual 𝕜 E) :=
--   ⟨continuous_induced_rng.2 <|
--       continuous_fst.smul ((WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).comp continuous_snd)⟩

-- theorem coeFn_continuous : Continuous fun (x : WeakDual 𝕜 E) y => x y :=
--   continuous_induced_dom
-- #align weak_dual.coe_fn_continuous WeakDual.coeFn_continuous

-- theorem eval_continuous (y : E) : Continuous fun x : WeakDual 𝕜 E => x y :=
--   continuous_pi_iff.mp coeFn_continuous y
-- #align weak_dual.eval_continuous WeakDual.eval_continuous

-- theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakDual 𝕜 E}
--     (h : ∀ y, Continuous fun a => (g a) y) : Continuous g :=
--   continuous_induced_rng.2 (continuous_pi_iff.mpr h)
-- #align weak_dual.continuous_of_continuous_eval WeakDual.continuous_of_continuous_eval

-- instance instT2Space [T2Space 𝕜] : T2Space (WeakDual 𝕜 E) :=
--   Embedding.t2Space <|
--     WeakBilin.embedding <|
--       show Function.Injective (topDualPairing 𝕜 E) from ContinuousLinearMap.coe_injective

-- end WeakDual

-- /-- The weak topology is the topology coarsest topology on `E` such that all functionals
-- `fun x => v x` are continuous. -/
-- def WeakSpace (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
--     [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
--   WeakBilin (topDualPairing 𝕜 E).flip
-- #align weak_space WeakSpace

-- namespace WeakSpace

-- -- Porting note: the next four instances should be derived from the definition
-- instance instAddCommMonoid : AddCommMonoid (WeakSpace 𝕜 E) :=
--   WeakBilin.instAddCommMonoid (topDualPairing 𝕜 E).flip

-- instance instModule : Module 𝕜 (WeakSpace 𝕜 E) :=
--   WeakBilin.instModule (topDualPairing 𝕜 E).flip

-- instance instTopologicalSpace : TopologicalSpace (WeakSpace 𝕜 E) :=
--   WeakBilin.instTopologicalSpace (topDualPairing 𝕜 E).flip

-- instance instContinuousAdd : ContinuousAdd (WeakSpace 𝕜 E) :=
--   WeakBilin.instContinuousAdd (topDualPairing 𝕜 E).flip

-- variable [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]

-- /-- A continuous linear map from `E` to `F` is still continuous when `E` and `F` are equipped with
-- their weak topologies. -/
-- def map (f : E →L[𝕜] F) : WeakSpace 𝕜 E →L[𝕜] WeakSpace 𝕜 F :=
--   { f with
--     cont :=
--       WeakBilin.continuous_of_continuous_eval _ fun l => WeakBilin.eval_continuous _ (l ∘L f) }
-- #align weak_space.map WeakSpace.map

-- theorem map_apply (f : E →L[𝕜] F) (x : E) : WeakSpace.map f x = f x :=
--   rfl
-- #align weak_space.map_apply WeakSpace.map_apply

-- @[simp]
-- theorem coe_map (f : E →L[𝕜] F) : (WeakSpace.map f : E → F) = f :=
--   rfl
-- #align weak_space.coe_map WeakSpace.coe_map

-- end WeakSpace

-- variable (𝕜 E) in
-- /-- There is a canonical map `E → WeakSpace 𝕜 E` (the "identity"
-- mapping). It is a linear equivalence. -/
-- def toWeakSpace : E ≃ₗ[𝕜] WeakSpace 𝕜 E := LinearEquiv.refl 𝕜 E

-- variable (𝕜 E) in
-- /-- For a topological vector space `E`, "identity mapping" `E → WeakSpace 𝕜 E` is continuous.
-- This definition implements it as a continuous linear map. -/
-- def continuousLinearMapToWeakSpace : E →L[𝕜] WeakSpace 𝕜 E where
--   __ := toWeakSpace 𝕜 E
--   cont := by
--     apply WeakBilin.continuous_of_continuous_eval
--     exact ContinuousLinearMap.continuous

-- variable (𝕜 E) in
-- @[simp]
-- theorem continuousLinearMapToWeakSpace_eq_toWeakSpace (x : E) :
--     continuousLinearMapToWeakSpace 𝕜 E x = toWeakSpace 𝕜 E x := by rfl

-- theorem continuousLinearMapToWeakSpace_bijective :
--     Function.Bijective (continuousLinearMapToWeakSpace 𝕜 E) :=
--   (toWeakSpace 𝕜 E).bijective

-- /-- The canonical map from `WeakSpace 𝕜 E` to `E` is an open map. -/
-- theorem isOpenMap_toWeakSpace_symm : IsOpenMap (toWeakSpace 𝕜 E).symm :=
--   IsOpenMap.of_inverse (continuousLinearMapToWeakSpace 𝕜 E).cont
--     (toWeakSpace 𝕜 E).left_inv (toWeakSpace 𝕜 E).right_inv

-- /-- A set in `E` which is open in the weak topology is open. -/
-- theorem WeakSpace.isOpen_of_isOpen (V : Set E)
--     (hV : IsOpen ((continuousLinearMapToWeakSpace 𝕜 E) '' V : Set (WeakSpace 𝕜 E))) : IsOpen V := by
--   simpa [Set.image_image] using isOpenMap_toWeakSpace_symm _ hV

-- theorem tendsto_iff_forall_eval_tendsto_topDualPairing {l : Filter α} {f : α → WeakDual 𝕜 E}
--     {x : WeakDual 𝕜 E} :
--     Tendsto f l (𝓝 x) ↔
--       ∀ y, Tendsto (fun i => topDualPairing 𝕜 E (f i) y) l (𝓝 (topDualPairing 𝕜 E x y)) :=
--   WeakBilin.tendsto_iff_forall_eval_tendsto _ ContinuousLinearMap.coe_injective
-- #align tendsto_iff_forall_eval_tendsto_top_dual_pairing tendsto_iff_forall_eval_tendsto_topDualPairing

end StrongOperatorTopology
