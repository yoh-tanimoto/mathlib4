import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.LinearAlgebra.BilinearMap

noncomputable section

open Filter

open Topology

variable {α 𝕜 𝕝 R E F M : Type*}

section WeakTopology

/-- The space `E` equipped with the weak topology induced by the bilinear form `B`. -/
@[nolint unusedArguments]
def WeakBilin [CommSemiring 𝕜] [AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F] [Module 𝕜 F]
    (_ : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) := E
#align weak_bilin WeakBilin

namespace WeakBilin

-- Porting note: the next two instances should be derived from the definition
instance instAddCommMonoid [CommSemiring 𝕜] [a : AddCommMonoid E] [Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : AddCommMonoid (WeakBilin B) := a

instance instModule [CommSemiring 𝕜] [AddCommMonoid E] [m : Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : Module 𝕜 (WeakBilin B) := m

instance instAddCommGroup [CommSemiring 𝕜] [a : AddCommGroup E] [Module 𝕜 E] [AddCommMonoid F]
    [Module 𝕜 F] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : AddCommGroup (WeakBilin B) := a

instance (priority := 100) instModule' [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommGroup E]
    [Module 𝕜 E] [AddCommGroup F] [Module 𝕜 F] [m : Module 𝕝 E] (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) :
    Module 𝕝 (WeakBilin B) := m
#align weak_bilin.module' WeakBilin.instModule'

instance instIsScalarTower [CommSemiring 𝕜] [CommSemiring 𝕝] [AddCommGroup E] [Module 𝕜 E]
    [AddCommGroup F] [Module 𝕜 F] [SMul 𝕝 𝕜] [Module 𝕝 E] [s : IsScalarTower 𝕝 𝕜 E]
    (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) : IsScalarTower 𝕝 𝕜 (WeakBilin B) := s

section Semiring

variable [TopologicalSpace 𝕜] [CommSemiring 𝕜]

variable [AddCommMonoid E] [Module 𝕜 E]

variable [AddCommMonoid F] [Module 𝕜 F]

variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

instance instTopologicalSpace : TopologicalSpace (WeakBilin B) :=
  TopologicalSpace.induced (fun x y => B x y) Pi.topologicalSpace

/-- The coercion `(fun x y => B x y) : E → (F → 𝕜)` is continuous. -/
theorem coeFn_continuous : Continuous fun (x : WeakBilin B) y => B x y :=
  continuous_induced_dom
#align weak_bilin.coe_fn_continuous WeakBilin.coeFn_continuous

theorem eval_continuous (y : F) : Continuous fun x : WeakBilin B => B x y :=
  (continuous_pi_iff.mp (coeFn_continuous B)) y
#align weak_bilin.eval_continuous WeakBilin.eval_continuous

theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakBilin B}
    (h : ∀ y, Continuous fun a => B (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)
#align weak_bilin.continuous_of_continuous_eval WeakBilin.continuous_of_continuous_eval

/-- The coercion `(fun x y => B x y) : E → (F → 𝕜)` is an embedding. -/
theorem embedding {B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜} (hB : Function.Injective B) :
    Embedding fun (x : WeakBilin B) y => B x y :=
  Function.Injective.embedding_induced <| LinearMap.coe_injective.comp hB
#align weak_bilin.embedding WeakBilin.embedding

theorem tendsto_iff_forall_eval_tendsto {l : Filter α} {f : α → WeakBilin B} {x : WeakBilin B}
    (hB : Function.Injective B) :
    Tendsto f l (𝓝 x) ↔ ∀ y, Tendsto (fun i => B (f i) y) l (𝓝 (B x y)) := by
  rw [← tendsto_pi_nhds, Embedding.tendsto_nhds_iff (embedding hB)]
  rfl
#align weak_bilin.tendsto_iff_forall_eval_tendsto WeakBilin.tendsto_iff_forall_eval_tendsto

/-- Addition in `WeakBilin B` is continuous. -/
instance instContinuousAdd [ContinuousAdd 𝕜] : ContinuousAdd (WeakBilin B) := by
  refine' ⟨continuous_induced_rng.2 _⟩
  refine'
    cast (congr_arg _ _)
      (((coeFn_continuous B).comp continuous_fst).add ((coeFn_continuous B).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.add_apply, map_add, LinearMap.add_apply]

/-- Scalar multiplication by `𝕜` on `WeakBilin B` is continuous. -/
instance instContinuousSMul [ContinuousSMul 𝕜 𝕜] : ContinuousSMul 𝕜 (WeakBilin B) := by
  refine' ⟨continuous_induced_rng.2 _⟩
  refine' cast (congr_arg _ _) (continuous_fst.smul ((coeFn_continuous B).comp continuous_snd))
  ext
  simp only [Function.comp_apply, Pi.smul_apply, LinearMap.map_smulₛₗ, RingHom.id_apply,
    LinearMap.smul_apply]

end Semiring

section Ring

variable [TopologicalSpace 𝕜] [CommRing 𝕜]

variable [AddCommGroup E] [Module 𝕜 E]

variable [AddCommGroup F] [Module 𝕜 F]


variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- `WeakBilin B` is a `TopologicalAddGroup`, meaning that addition and negation are
continuous. -/
instance instTopologicalAddGroup [ContinuousAdd 𝕜] : TopologicalAddGroup (WeakBilin B) where
  toContinuousAdd := by infer_instance
  continuous_neg := by
    refine' continuous_induced_rng.2 (continuous_pi_iff.mpr fun y => _)
    refine' cast (congr_arg _ _) (eval_continuous B (-y))
    ext x
    simp only [map_neg, Function.comp_apply, LinearMap.neg_apply]

end Ring

end WeakBilin

end WeakTopology

section WeakStarTopology

/-- The canonical pairing of a vector space and its topological dual. -/
def topDualPairing (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] [TopologicalSpace E] [ContinuousConstSMul 𝕜 𝕜] : (E →L[𝕜] 𝕜) →ₗ[𝕜] E →ₗ[𝕜] 𝕜 :=
  ContinuousLinearMap.coeLM 𝕜
#align top_dual_pairing topDualPairing

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]

variable [ContinuousConstSMul 𝕜 𝕜]

variable [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E]

theorem topDualPairing_apply (v : E →L[𝕜] 𝕜) (x : E) : topDualPairing 𝕜 E v x = v x :=
  rfl
#align dual_pairing_apply topDualPairing_apply

/-- The weak star topology is the topology coarsest topology on `E →L[𝕜] 𝕜` such that all
functionals `fun v => v x` are continuous. -/
def WeakDual (𝕜 E : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E)
#align weak_dual WeakDual

namespace WeakDual

-- Porting note: the next four instances should be derived from the definition
instance instAddCommMonoid : AddCommMonoid (WeakDual 𝕜 E) :=
  WeakBilin.instAddCommMonoid (topDualPairing 𝕜 E)

instance instModule : Module 𝕜 (WeakDual 𝕜 E) :=
  WeakBilin.instModule (topDualPairing 𝕜 E)

instance instTopologicalSpace : TopologicalSpace (WeakDual 𝕜 E) :=
  WeakBilin.instTopologicalSpace (topDualPairing 𝕜 E)

instance instContinuousAdd : ContinuousAdd (WeakDual 𝕜 E) :=
  WeakBilin.instContinuousAdd (topDualPairing 𝕜 E)

instance instInhabited : Inhabited (WeakDual 𝕜 E) :=
  ContinuousLinearMap.inhabited

instance instFunLike : FunLike (WeakDual 𝕜 E) E 𝕜 :=
  ContinuousLinearMap.funLike

instance instContinuousLinearMapClass : ContinuousLinearMapClass (WeakDual 𝕜 E) 𝕜 E 𝕜 :=
  ContinuousLinearMap.continuousSemilinearMapClass
#align weak_dual.weak_dual.continuous_linear_map_class WeakDual.instContinuousLinearMapClass

/-- Helper instance for when there's too many metavariables to apply `DFunLike.hasCoeToFun`
directly. -/
instance : CoeFun (WeakDual 𝕜 E) fun _ => E → 𝕜 :=
  DFunLike.hasCoeToFun

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts on `WeakDual 𝕜 E`. -/
instance instMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : MulAction M (WeakDual 𝕜 E) :=
  ContinuousLinearMap.mulAction

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it acts distributively on `WeakDual 𝕜 E`. -/
instance instDistribMulAction (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : DistribMulAction M (WeakDual 𝕜 E) :=
  ContinuousLinearMap.distribMulAction

/-- If `𝕜` is a topological module over a semiring `R` and scalar multiplication commutes with the
multiplication on `𝕜`, then `WeakDual 𝕜 E` is a module over `R`. -/
instance instModule' (R) [Semiring R] [Module R 𝕜] [SMulCommClass 𝕜 R 𝕜] [ContinuousConstSMul R 𝕜] :
    Module R (WeakDual 𝕜 E) :=
  ContinuousLinearMap.module
#align weak_dual.module' WeakDual.instModule'

instance instContinuousConstSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [ContinuousConstSMul M 𝕜] : ContinuousConstSMul M (WeakDual 𝕜 E) :=
  ⟨fun m =>
    continuous_induced_rng.2 <| (WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).const_smul m⟩

/-- If a monoid `M` distributively continuously acts on `𝕜` and this action commutes with
multiplication on `𝕜`, then it continuously acts on `WeakDual 𝕜 E`. -/
instance instContinuousSMul (M) [Monoid M] [DistribMulAction M 𝕜] [SMulCommClass 𝕜 M 𝕜]
    [TopologicalSpace M] [ContinuousSMul M 𝕜] : ContinuousSMul M (WeakDual 𝕜 E) :=
  ⟨continuous_induced_rng.2 <|
      continuous_fst.smul ((WeakBilin.coeFn_continuous (topDualPairing 𝕜 E)).comp continuous_snd)⟩

theorem coeFn_continuous : Continuous fun (x : WeakDual 𝕜 E) y => x y :=
  continuous_induced_dom
#align weak_dual.coe_fn_continuous WeakDual.coeFn_continuous

theorem eval_continuous (y : E) : Continuous fun x : WeakDual 𝕜 E => x y :=
  continuous_pi_iff.mp coeFn_continuous y
#align weak_dual.eval_continuous WeakDual.eval_continuous

theorem continuous_of_continuous_eval [TopologicalSpace α] {g : α → WeakDual 𝕜 E}
    (h : ∀ y, Continuous fun a => (g a) y) : Continuous g :=
  continuous_induced_rng.2 (continuous_pi_iff.mpr h)
#align weak_dual.continuous_of_continuous_eval WeakDual.continuous_of_continuous_eval

instance instT2Space [T2Space 𝕜] : T2Space (WeakDual 𝕜 E) :=
  Embedding.t2Space <|
    WeakBilin.embedding <|
      show Function.Injective (topDualPairing 𝕜 E) from ContinuousLinearMap.coe_injective

end WeakDual

/-- The weak topology is the topology coarsest topology on `E` such that all functionals
`fun x => v x` are continuous. -/
def WeakSpace (𝕜 E) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [AddCommMonoid E] [Module 𝕜 E] [TopologicalSpace E] :=
  WeakBilin (topDualPairing 𝕜 E).flip
#align weak_space WeakSpace

namespace WeakSpace

-- Porting note: the next four instances should be derived from the definition
instance instAddCommMonoid : AddCommMonoid (WeakSpace 𝕜 E) :=
  WeakBilin.instAddCommMonoid (topDualPairing 𝕜 E).flip

instance instModule : Module 𝕜 (WeakSpace 𝕜 E) :=
  WeakBilin.instModule (topDualPairing 𝕜 E).flip

instance instTopologicalSpace : TopologicalSpace (WeakSpace 𝕜 E) :=
  WeakBilin.instTopologicalSpace (topDualPairing 𝕜 E).flip

instance instContinuousAdd : ContinuousAdd (WeakSpace 𝕜 E) :=
  WeakBilin.instContinuousAdd (topDualPairing 𝕜 E).flip

variable [AddCommMonoid F] [Module 𝕜 F] [TopologicalSpace F]

/-- A continuous linear map from `E` to `F` is still continuous when `E` and `F` are equipped with
their weak topologies. -/
def map (f : E →L[𝕜] F) : WeakSpace 𝕜 E →L[𝕜] WeakSpace 𝕜 F :=
  { f with
    cont :=
      WeakBilin.continuous_of_continuous_eval _ fun l => WeakBilin.eval_continuous _ (l ∘L f) }
#align weak_space.map WeakSpace.map

theorem map_apply (f : E →L[𝕜] F) (x : E) : WeakSpace.map f x = f x :=
  rfl
#align weak_space.map_apply WeakSpace.map_apply

@[simp]
theorem coe_map (f : E →L[𝕜] F) : (WeakSpace.map f : E → F) = f :=
  rfl
#align weak_space.coe_map WeakSpace.coe_map

def toWeakSpace : E ≃ₗ[𝕜] WeakSpace 𝕜 E :=
  LinearEquiv.refl 𝕜 E

def toOriginalSpace : WeakSpace 𝕜 E ≃ₗ[𝕜] E :=
  toWeakSpace.symm

variable (x : E) (U : Set E)
#check toWeakSpace x
#check toWeakSpace U

theorem isOpen_of_isOpen_WeakSpace (U : Set E) :
    IsOpen[(WeakSpace.instTopologicalSpace : TopologicalSpace (WeakSpace 𝕜 E))]
    (id U : Set (WeakSpace 𝕜 E)) → IsOpen U := by
  intro hU
  apply Continuous.le_induced _ U hU
  refine continuous_pi ?h.h
  intro y
  exact ContinuousLinearMap.continuous y

theorem tendsto_WeakSpace_of_tendsto
    {α : Type*} {l : Filter α} {f : α → E} {p : E} (hf : Tendsto f l (nhds p)) :
    Tendsto (fun x ↦ (id (f x) : (WeakSpace 𝕜 E))) l (nhds (p : (WeakSpace 𝕜 E))) := by
  refine tendsto_nhds.mpr ?_
  intro U hpU hU
  rw [tendsto_nhds] at hf
  exact hf (id U : Set E) (isOpen_of_isOpen_WeakSpace (id U : Set E) hpU) hU

theorem eval_tendsto_of_tendsto
    {α : Type*} {l : Filter α} {f : α → E} {p : E} (hf : Tendsto f l (nhds p)) :
    ∀ (y : E →L[𝕜] 𝕜), Tendsto (fun x => y (f x)) l (nhds (y p)) := by
  intro y
  exact Tendsto.comp (Continuous.tendsto (ContinuousLinearMap.continuous y) p) hf

end WeakSpace
