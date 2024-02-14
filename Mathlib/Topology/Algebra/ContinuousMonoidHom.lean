/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Topology.Algebra.Equicontinuity
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.ContinuousFunction.Algebra
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.Covering
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.UniformSpace.Equicontinuity

#align_import topology.algebra.continuous_monoid_hom from "leanprover-community/mathlib"@"6ca1a09bc9aa75824bf97388c9e3b441fc4ccf3f"

/-!

# Continuous Monoid Homs

This file defines the space of continuous homomorphisms between two topological groups.

## Main definitions

* `ContinuousMonoidHom A B`: The continuous homomorphisms `A →* B`.
* `ContinuousAddMonoidHom A B`: The continuous additive homomorphisms `A →+ B`.
-/


open Pointwise Function

variable (F A B C D E : Type*) [Monoid A] [Monoid B] [Monoid C] [Monoid D] [CommGroup E]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
  [TopologicalSpace E] [TopologicalGroup E]

/-- The type of continuous additive monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : ContinuousAddMonoidHom A B)`,
you should parametrize over `(F : Type*) [ContinuousAddMonoidHomClass F A B] (f : F)`.

When you extend this structure, make sure to extend `ContinuousAddMonoidHomClass`. -/
structure ContinuousAddMonoidHom (A B : Type*) [AddMonoid A] [AddMonoid B] [TopologicalSpace A]
  [TopologicalSpace B] extends A →+ B where
  /-- Proof of continuity of the Hom. -/
  continuous_toFun : @Continuous A B _ _ toFun
#align continuous_add_monoid_hom ContinuousAddMonoidHom

/-- The type of continuous monoid homomorphisms from `A` to `B`.

When possible, instead of parametrizing results over `(f : ContinuousMonoidHom A B)`,
you should parametrize over `(F : Type*) [ContinuousMonoidHomClass F A B] (f : F)`.

When you extend this structure, make sure to extend `ContinuousAddMonoidHomClass`. -/
@[to_additive "The type of continuous additive monoid homomorphisms from `A` to `B`."]
structure ContinuousMonoidHom extends A →* B where
  /-- Proof of continuity of the Hom. -/
  continuous_toFun : @Continuous A B _ _ toFun
#align continuous_monoid_hom ContinuousMonoidHom

section

/-- `ContinuousAddMonoidHomClass F A B` states that `F` is a type of continuous additive monoid
homomorphisms.

You should also extend this typeclass when you extend `ContinuousAddMonoidHom`. -/
-- porting note : Changed A B to outParam to help synthesizing order
class ContinuousAddMonoidHomClass (A B : outParam (Type*)) [AddMonoid A] [AddMonoid B]
    [TopologicalSpace A] [TopologicalSpace B] [FunLike F A B]
    extends AddMonoidHomClass F A B : Prop where
  /-- Proof of the continuity of the map. -/
  map_continuous (f : F) : Continuous f
#align continuous_add_monoid_hom_class ContinuousAddMonoidHomClass

/-- `ContinuousMonoidHomClass F A B` states that `F` is a type of continuous additive monoid
homomorphisms.

You should also extend this typeclass when you extend `ContinuousMonoidHom`. -/
-- porting note : Changed A B to outParam to help synthesizing order
@[to_additive]
class ContinuousMonoidHomClass (A B : outParam (Type*)) [Monoid A] [Monoid B]
    [TopologicalSpace A] [TopologicalSpace B] [FunLike F A B]
    extends MonoidHomClass F A B : Prop where
  /-- Proof of the continuity of the map. -/
  map_continuous (f : F) : Continuous f
#align continuous_monoid_hom_class ContinuousMonoidHomClass

end

/-- Reinterpret a `ContinuousMonoidHom` as a `MonoidHom`. -/
add_decl_doc ContinuousMonoidHom.toMonoidHom

/-- Reinterpret a `ContinuousAddMonoidHom` as an `AddMonoidHom`. -/
add_decl_doc ContinuousAddMonoidHom.toAddMonoidHom

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) ContinuousMonoidHomClass.toContinuousMapClass
    [FunLike F A B] [ContinuousMonoidHomClass F A B] : ContinuousMapClass F A B :=
  { ‹ContinuousMonoidHomClass F A B› with }
#align continuous_monoid_hom_class.to_continuous_map_class ContinuousMonoidHomClass.toContinuousMapClass
#align continuous_add_monoid_hom_class.to_continuous_map_class ContinuousAddMonoidHomClass.toContinuousMapClass

namespace ContinuousMonoidHom

variable {A B C D E}

@[to_additive]
instance ContinuousMonoidHom.funLike :
    FunLike (ContinuousMonoidHom A B) A B where
  coe f := f.toFun
  coe_injective' f g h := by
    obtain ⟨⟨⟨ _ , _ ⟩, _⟩, _⟩ := f
    obtain ⟨⟨⟨ _ , _ ⟩, _⟩, _⟩ := g
    congr

@[to_additive]
instance ContinuousMonoidHom.ContinuousMonoidHomClass :
    ContinuousMonoidHomClass (ContinuousMonoidHom A B) A B where
  map_mul f := f.map_mul'
  map_one f := f.map_one'
  map_continuous f := f.continuous_toFun

@[to_additive (attr := ext)]
theorem ext {f g : ContinuousMonoidHom A B} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h
#align continuous_monoid_hom.ext ContinuousMonoidHom.ext
#align continuous_add_monoid_hom.ext ContinuousAddMonoidHom.ext

/-- Reinterpret a `ContinuousMonoidHom` as a `ContinuousMap`. -/
@[to_additive "Reinterpret a `ContinuousAddMonoidHom` as a `ContinuousMap`."]
def toContinuousMap (f : ContinuousMonoidHom A B) : C(A, B) :=
  { f with }
#align continuous_monoid_hom.to_continuous_map ContinuousMonoidHom.toContinuousMap
#align continuous_add_monoid_hom.to_continuous_map ContinuousAddMonoidHom.toContinuousMap

@[to_additive]
theorem toContinuousMap_injective : Injective (toContinuousMap : _ → C(A, B)) := fun f g h =>
  ext <| by convert DFunLike.ext_iff.1 h
#align continuous_monoid_hom.to_continuous_map_injective ContinuousMonoidHom.toContinuousMap_injective
#align continuous_add_monoid_hom.to_continuous_map_injective ContinuousAddMonoidHom.toContinuousMap_injective

-- porting note: Removed simps because given definition is not a constructor application
/-- Construct a `ContinuousMonoidHom` from a `Continuous` `MonoidHom`. -/
@[to_additive "Construct a `ContinuousAddMonoidHom` from a `Continuous` `AddMonoidHom`."]
def mk' (f : A →* B) (hf : Continuous f) : ContinuousMonoidHom A B :=
  { f with continuous_toFun := (hf : Continuous f.toFun)}
#align continuous_monoid_hom.mk' ContinuousMonoidHom.mk'
#align continuous_add_monoid_hom.mk' ContinuousAddMonoidHom.mk'

/-- Composition of two continuous homomorphisms. -/
@[to_additive (attr := simps!) "Composition of two continuous homomorphisms."]
def comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) : ContinuousMonoidHom A C :=
  mk' (g.toMonoidHom.comp f.toMonoidHom) (g.continuous_toFun.comp f.continuous_toFun)
#align continuous_monoid_hom.comp ContinuousMonoidHom.comp
#align continuous_add_monoid_hom.comp ContinuousAddMonoidHom.comp

/-- Product of two continuous homomorphisms on the same space. -/
@[to_additive (attr := simps!) "Product of two continuous homomorphisms on the same space."]
def prod (f : ContinuousMonoidHom A B) (g : ContinuousMonoidHom A C) :
    ContinuousMonoidHom A (B × C) :=
  mk' (f.toMonoidHom.prod g.toMonoidHom) (f.continuous_toFun.prod_mk g.continuous_toFun)
#align continuous_monoid_hom.prod ContinuousMonoidHom.prod
#align continuous_add_monoid_hom.sum ContinuousAddMonoidHom.sum

/-- Product of two continuous homomorphisms on different spaces. -/
@[to_additive (attr := simps!) "Product of two continuous homomorphisms on different spaces."]
def prod_map (f : ContinuousMonoidHom A C) (g : ContinuousMonoidHom B D) :
    ContinuousMonoidHom (A × B) (C × D) :=
  mk' (f.toMonoidHom.prodMap g.toMonoidHom) (f.continuous_toFun.prod_map g.continuous_toFun)
#align continuous_monoid_hom.prod_map ContinuousMonoidHom.prod_map
#align continuous_add_monoid_hom.sum_map ContinuousAddMonoidHom.sum_map

variable (A B C D E)

/-- The trivial continuous homomorphism. -/
@[to_additive (attr := simps!) "The trivial continuous homomorphism."]
def one : ContinuousMonoidHom A B :=
  mk' 1 continuous_const
#align continuous_monoid_hom.one ContinuousMonoidHom.one
#align continuous_add_monoid_hom.zero ContinuousAddMonoidHom.zero

@[to_additive]
instance : Inhabited (ContinuousMonoidHom A B) :=
  ⟨one A B⟩

/-- The identity continuous homomorphism. -/
@[to_additive (attr := simps!) "The identity continuous homomorphism."]
def id : ContinuousMonoidHom A A :=
  mk' (MonoidHom.id A) continuous_id
#align continuous_monoid_hom.id ContinuousMonoidHom.id
#align continuous_add_monoid_hom.id ContinuousAddMonoidHom.id

/-- The continuous homomorphism given by projection onto the first factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by projection onto the first factor."]
def fst : ContinuousMonoidHom (A × B) A :=
  mk' (MonoidHom.fst A B) continuous_fst
#align continuous_monoid_hom.fst ContinuousMonoidHom.fst
#align continuous_add_monoid_hom.fst ContinuousAddMonoidHom.fst

/-- The continuous homomorphism given by projection onto the second factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by projection onto the second factor."]
def snd : ContinuousMonoidHom (A × B) B :=
  mk' (MonoidHom.snd A B) continuous_snd
#align continuous_monoid_hom.snd ContinuousMonoidHom.snd
#align continuous_add_monoid_hom.snd ContinuousAddMonoidHom.snd

/-- The continuous homomorphism given by inclusion of the first factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by inclusion of the first factor."]
def inl : ContinuousMonoidHom A (A × B) :=
  prod (id A) (one A B)
#align continuous_monoid_hom.inl ContinuousMonoidHom.inl
#align continuous_add_monoid_hom.inl ContinuousAddMonoidHom.inl

/-- The continuous homomorphism given by inclusion of the second factor. -/
@[to_additive (attr := simps!)
  "The continuous homomorphism given by inclusion of the second factor."]
def inr : ContinuousMonoidHom B (A × B) :=
  prod (one B A) (id B)
#align continuous_monoid_hom.inr ContinuousMonoidHom.inr
#align continuous_add_monoid_hom.inr ContinuousAddMonoidHom.inr

/-- The continuous homomorphism given by the diagonal embedding. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by the diagonal embedding."]
def diag : ContinuousMonoidHom A (A × A) :=
  prod (id A) (id A)
#align continuous_monoid_hom.diag ContinuousMonoidHom.diag
#align continuous_add_monoid_hom.diag ContinuousAddMonoidHom.diag

/-- The continuous homomorphism given by swapping components. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by swapping components."]
def swap : ContinuousMonoidHom (A × B) (B × A) :=
  prod (snd A B) (fst A B)
#align continuous_monoid_hom.swap ContinuousMonoidHom.swap
#align continuous_add_monoid_hom.swap ContinuousAddMonoidHom.swap

/-- The continuous homomorphism given by multiplication. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by addition."]
def mul : ContinuousMonoidHom (E × E) E :=
  mk' mulMonoidHom continuous_mul
#align continuous_monoid_hom.mul ContinuousMonoidHom.mul
#align continuous_add_monoid_hom.add ContinuousAddMonoidHom.add

/-- The continuous homomorphism given by inversion. -/
@[to_additive (attr := simps!) "The continuous homomorphism given by negation."]
def inv : ContinuousMonoidHom E E :=
  mk' invMonoidHom continuous_inv
#align continuous_monoid_hom.inv ContinuousMonoidHom.inv
#align continuous_add_monoid_hom.neg ContinuousAddMonoidHom.neg

variable {A B C D E}

/-- Coproduct of two continuous homomorphisms to the same space. -/
@[to_additive (attr := simps!) "Coproduct of two continuous homomorphisms to the same space."]
def coprod (f : ContinuousMonoidHom A E) (g : ContinuousMonoidHom B E) :
    ContinuousMonoidHom (A × B) E :=
  (mul E).comp (f.prod_map g)
#align continuous_monoid_hom.coprod ContinuousMonoidHom.coprod
#align continuous_add_monoid_hom.coprod ContinuousAddMonoidHom.coprod

@[to_additive]
instance : CommGroup (ContinuousMonoidHom A E) where
  mul f g := (mul E).comp (f.prod g)
  mul_comm f g := ext fun x => mul_comm (f x) (g x)
  mul_assoc f g h := ext fun x => mul_assoc (f x) (g x) (h x)
  one := one A E
  one_mul f := ext fun x => one_mul (f x)
  mul_one f := ext fun x => mul_one (f x)
  inv f := (inv E).comp f
  mul_left_inv f := ext fun x => mul_left_inv (f x)

@[to_additive]
instance : TopologicalSpace (ContinuousMonoidHom A B) :=
  TopologicalSpace.induced toContinuousMap ContinuousMap.compactOpen

variable (A B C D E)

@[to_additive]
theorem inducing_toContinuousMap : Inducing (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) :=
  ⟨rfl⟩
#align continuous_monoid_hom.inducing_to_continuous_map ContinuousMonoidHom.inducing_toContinuousMap
#align continuous_add_monoid_hom.inducing_to_continuous_map ContinuousAddMonoidHom.inducing_toContinuousMap

@[to_additive]
theorem embedding_toContinuousMap :
    Embedding (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) :=
  ⟨inducing_toContinuousMap A B, toContinuousMap_injective⟩
#align continuous_monoid_hom.embedding_to_continuous_map ContinuousMonoidHom.embedding_toContinuousMap
#align continuous_add_monoid_hom.embedding_to_continuous_map ContinuousAddMonoidHom.embedding_toContinuousMap

@[to_additive]
lemma range_toContinuousMap :
    Set.range (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) =
      {f : C(A, B) | f 1 = 1 ∧ ∀ x y, f (x * y) = f x * f y} := by
  refine Set.Subset.antisymm (Set.range_subset_iff.2 fun f ↦ ⟨map_one f, map_mul f⟩) ?_
  rintro f ⟨h1, hmul⟩
  exact ⟨{ f with map_one' := h1, map_mul' := hmul }, rfl⟩

@[to_additive]
theorem closedEmbedding_toContinuousMap [ContinuousMul B] [T2Space B] :
    ClosedEmbedding (toContinuousMap : ContinuousMonoidHom A B → C(A, B)) where
  toEmbedding := embedding_toContinuousMap A B
  closed_range := by
    simp only [range_toContinuousMap, Set.setOf_and, Set.setOf_forall]
    refine .inter (isClosed_singleton.preimage (ContinuousMap.continuous_eval_const 1)) <|
      isClosed_iInter fun x ↦ isClosed_iInter fun y ↦ ?_
    exact isClosed_eq (ContinuousMap.continuous_eval_const (x * y)) <|
      .mul (ContinuousMap.continuous_eval_const x) (ContinuousMap.continuous_eval_const y)
#align continuous_monoid_hom.closed_embedding_to_continuous_map ContinuousMonoidHom.closedEmbedding_toContinuousMap
#align continuous_add_monoid_hom.closed_embedding_to_continuous_map ContinuousAddMonoidHom.closedEmbedding_toContinuousMap

variable {A B C D E}

@[to_additive]
instance [T2Space B] : T2Space (ContinuousMonoidHom A B) :=
  (embedding_toContinuousMap A B).t2Space

@[to_additive]
instance : TopologicalGroup (ContinuousMonoidHom A E) :=
  let hi := inducing_toContinuousMap A E
  let hc := hi.continuous
  { continuous_mul := hi.continuous_iff.mpr (continuous_mul.comp (Continuous.prod_map hc hc))
    continuous_inv := hi.continuous_iff.mpr (continuous_inv.comp hc) }

@[to_additive]
theorem continuous_of_continuous_uncurry {A : Type*} [TopologicalSpace A]
    (f : A → ContinuousMonoidHom B C) (h : Continuous (Function.uncurry fun x y => f x y)) :
    Continuous f :=
  (inducing_toContinuousMap _ _).continuous_iff.mpr
    (ContinuousMap.continuous_of_continuous_uncurry _ h)
#align continuous_monoid_hom.continuous_of_continuous_uncurry ContinuousMonoidHom.continuous_of_continuous_uncurry
#align continuous_add_monoid_hom.continuous_of_continuous_uncurry ContinuousAddMonoidHom.continuous_of_continuous_uncurry

@[to_additive]
theorem continuous_comp [LocallyCompactSpace B] :
    Continuous fun f : ContinuousMonoidHom A B × ContinuousMonoidHom B C => f.2.comp f.1 :=
  (inducing_toContinuousMap A C).continuous_iff.2 <|
    ContinuousMap.continuous_comp'.comp
      ((inducing_toContinuousMap A B).prod_map (inducing_toContinuousMap B C)).continuous
#align continuous_monoid_hom.continuous_comp ContinuousMonoidHom.continuous_comp
#align continuous_add_monoid_hom.continuous_comp ContinuousAddMonoidHom.continuous_comp

@[to_additive]
theorem continuous_comp_left (f : ContinuousMonoidHom A B) :
    Continuous fun g : ContinuousMonoidHom B C => g.comp f :=
  (inducing_toContinuousMap A C).continuous_iff.2 <|
    f.toContinuousMap.continuous_comp_left.comp (inducing_toContinuousMap B C).continuous
#align continuous_monoid_hom.continuous_comp_left ContinuousMonoidHom.continuous_comp_left
#align continuous_add_monoid_hom.continuous_comp_left ContinuousAddMonoidHom.continuous_comp_left

@[to_additive]
theorem continuous_comp_right (f : ContinuousMonoidHom B C) :
    Continuous fun g : ContinuousMonoidHom A B => f.comp g :=
  (inducing_toContinuousMap A C).continuous_iff.2 <|
    f.toContinuousMap.continuous_comp.comp (inducing_toContinuousMap A B).continuous
#align continuous_monoid_hom.continuous_comp_right ContinuousMonoidHom.continuous_comp_right
#align continuous_add_monoid_hom.continuous_comp_right ContinuousAddMonoidHom.continuous_comp_right

variable (E)

/-- `ContinuousMonoidHom _ f` is a functor. -/
@[to_additive "`ContinuousAddMonoidHom _ f` is a functor."]
def compLeft (f : ContinuousMonoidHom A B) :
    ContinuousMonoidHom (ContinuousMonoidHom B E) (ContinuousMonoidHom A E) where
  toFun g := g.comp f
  map_one' := rfl
  map_mul' _g _h := rfl
  continuous_toFun := f.continuous_comp_left
#align continuous_monoid_hom.comp_left ContinuousMonoidHom.compLeft
#align continuous_add_monoid_hom.comp_left ContinuousAddMonoidHom.compLeft

variable (A) {E}

/-- `ContinuousMonoidHom f _` is a functor. -/
@[to_additive "`ContinuousAddMonoidHom f _` is a functor."]
def compRight {B : Type*} [CommGroup B] [TopologicalSpace B] [TopologicalGroup B]
    (f : ContinuousMonoidHom B E) :
    ContinuousMonoidHom (ContinuousMonoidHom A B) (ContinuousMonoidHom A E) where
  toFun g := f.comp g
  map_one' := ext fun _a => map_one f
  map_mul' g h := ext fun a => map_mul f (g a) (h a)
  continuous_toFun := f.continuous_comp_right
#align continuous_monoid_hom.comp_right ContinuousMonoidHom.compRight
#align continuous_add_monoid_hom.comp_right ContinuousAddMonoidHom.compRight

variable (E)

-- better proof in tb_ascoli branch
theorem arzela_ascoli {X Y : Type*} [TopologicalSpace X] [UniformSpace Y] [CompactSpace Y]
    (S : Set C(X, Y)) (hS1 : IsCompact (ContinuousMap.toFun '' S))
    (hS2 : Equicontinuous ((↑) : S → X → Y)) :
    IsCompact S := by
  suffices : Inducing (Equiv.Set.image (↑) S FunLike.coe_injective)
  · rw [isCompact_iff_compactSpace] at hS1 ⊢
    exact (Equiv.toHomeomorphOfInducing _ this).symm.compactSpace
  rw [inducing_subtype_val.inducing_iff, inducing_iff_nhds]
  refine' fun ϕ ↦ le_antisymm (Filter.map_le_iff_le_comap.mp
    (ContinuousMap.continuous_coe.comp continuous_subtype_val).continuousAt) _
  rw [inducing_subtype_val.nhds_eq_comap ϕ, ← Filter.map_le_iff_le_comap]
  conv_rhs => rw [TopologicalSpace.nhds_generateFrom]
  simp only [le_iInf_iff]
  rintro - ⟨hg, K, hK, U, hU, rfl⟩
  obtain ⟨V, hV, hV'⟩ := Disjoint.exists_uniform_thickening (hK.image ϕ.1.2) hU.isClosed_compl
    (disjoint_compl_right_iff.mpr hg)
  obtain ⟨W, hW, hW₀, hWV⟩ := comp_comp_symm_mem_uniformity_sets hV
  obtain ⟨t, -, htW⟩ := hK.elim_nhds_subcover
    (fun x ↦ {x' | ∀ ψ : S, ((ψ : X → Y) x, (ψ : X → Y) x') ∈ W}) (fun x _ ↦ hS2 x W hW)
  rw [Filter.le_principal_iff, Filter.mem_map]
  refine' ⟨⋂ x ∈ t, {ψ | (ϕ.1 x, ψ x) ∈ W}, _, _⟩
  · rw [Filter.biInter_finset_mem]
    rintro x -
    rw [nhds_pi, Filter.mem_pi]
    refine' ⟨{x}, Set.finite_singleton x, fun i ↦ {y | (ϕ.1 i, y) ∈ W}, fun _ ↦ _, by simp⟩
    rw [nhds_eq_comap_uniformity, Filter.mem_comap]
    exact ⟨W, hW, fun _ x ↦ x⟩
  · rintro ψ h - ⟨x, hx, rfl⟩
    simp only [Set.mem_preimage, Set.mem_iInter] at h
    specialize htW hx
    simp only [Set.mem_iUnion] at htW
    obtain ⟨x', hx', h'⟩ := htW
    contrapose! hV'
    simp only [Set.not_disjoint_iff, Set.mem_iUnion]
    refine' ⟨ψ.1 x, _, ⟨ψ.1 x, hV', UniformSpace.mem_ball_self (ψ.1 x) hV⟩⟩
    exact ⟨ϕ.1 x, ⟨x, hx, rfl⟩, hWV ⟨ψ.1 x', ⟨ϕ.1 x', hW₀.mk_mem_comm.mp (h' ϕ), h x' hx'⟩, h' ψ⟩⟩

open BoundedContinuousFunction

theorem MonoidHom.isClosed_range (X Y : Type*)
    [TopologicalSpace X] [Group X] [TopologicalGroup X]
    [TopologicalSpace Y] [Group Y] [TopologicalGroup Y] [T1Space Y] :
    IsClosed (Set.range ((↑) : (X →* Y) → (X → Y))) := by
  have key : Set.range ((↑) : (X →* Y) → (X → Y)) = ⋂ (x) (y), {f | f x * f y * (f (x * y))⁻¹ = 1}
  · ext f
    simp_rw [mul_inv_eq_one, eq_comm, Set.mem_iInter]
    exact ⟨fun ⟨g, h⟩ ↦ h ▸ map_mul g, fun h ↦ ⟨MonoidHom.mk' f h, rfl⟩⟩
  rw [key]
  exact isClosed_iInter (fun _ ↦ isClosed_iInter
    (fun _ ↦ isClosed_singleton.preimage (by continuity)))

theorem mythm {X Y : Type*}
    [TopologicalSpace X] [Group X] [TopologicalGroup X]
    [UniformSpace Y] [CommGroup Y] [UniformGroup Y] [T1Space Y] [CompactSpace Y]
    (U : Set X) (V : Set Y)
    (hUc : IsCompact U) (hVc : IsClosed V)
    (hVo : V ∈ nhds (1 : Y))
    (h : EquicontinuousAt (fun f : {f : X →* Y | U ⊆ f ⁻¹' V} ↦ (f : X → Y)) 1) :
    LocallyCompactSpace (ContinuousMonoidHom X Y) := by
  apply TopologicalSpace.PositiveCompacts.locallyCompactSpace_of_group
  let S1 : Set (X →* Y) := {f | U ⊆ f ⁻¹' V}
  let S2 : Set (ContinuousMonoidHom X Y) := {f | U ⊆ f ⁻¹' V}
  let S3 : Set C(X, Y) := (↑) '' S2
  let S4 : Set (X → Y) := (↑) '' S3
  replace h : Equicontinuous ((↑) : S1 → X → Y) := equicontinuous_of_equicontinuousAt_one _ h
  have hS : S4 = (↑) '' S1
  · ext
    constructor
    · rintro ⟨-, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨⟨f, h.continuous ⟨f, hf⟩⟩, ⟨⟨f, h.continuous ⟨f, hf⟩⟩, hf, rfl⟩, rfl⟩
  replace h : Equicontinuous ((↑) : S3 → X → Y)
  · rw [equicontinuous_iff_range, ← Set.image_eq_range] at h ⊢
    rwa [← hS] at h
  have hS2 : (interior S2).Nonempty
  · let T : Set (ContinuousMonoidHom X Y) := {f | f '' U ⊆ interior V}
    have h1 : T ⊆ S2 := fun f hf ↦ Set.image_subset_iff.mp (Set.Subset.trans hf interior_subset)
    have h2 : IsOpen T := isOpen_induced (ContinuousMap.isOpen_gen hUc isOpen_interior)
    have h3 : T.Nonempty := ⟨1, fun _ ⟨_, _, h⟩ ↦ h ▸ mem_interior_iff_mem_nhds.mpr hVo⟩
    exact h3.mono (interior_maximal h1 h2)
  suffices : IsClosed S4
  · exact ⟨⟨S2, (inducing_toContinuousMap X Y).isCompact_iff.mpr
      (arzela_ascoli S3 this.isCompact h)⟩, hS2⟩
  replace hS : S4 = Set.pi U (fun _ ↦ V) ∩ Set.range ((↑) : (X →* Y) → (X → Y))
  · rw [hS]
    ext f
    simp only [Set.mem_image, Set.mem_setOf_eq]
    exact ⟨fun ⟨g, hg, hf⟩ ↦ hf ▸ ⟨hg, g, rfl⟩, fun ⟨hg, g, hf⟩ ↦ ⟨g, hf ▸ hg, hf⟩⟩
  rw [hS]
  exact (isClosed_set_pi (fun _ _ ↦ hVc)).inter (MonoidHom.isClosed_range X Y)

theorem mythm' {X Y : Type*}
    [TopologicalSpace X] [Group X] [TopologicalGroup X] [LocallyCompactSpace X]
    [UniformSpace Y] [CommGroup Y] [UniformGroup Y] [T1Space Y] [CompactSpace Y]
    (V : ℕ → Set Y)
    (hV : ∀ {n x}, x ∈ V n → x * x ∈ V n → x ∈ V (n + 1))
    (hVc : IsClosed (V 0)) (hVo : Filter.HasBasis (nhds 1) (fun _ ↦ True) V) :
    LocallyCompactSpace (ContinuousMonoidHom X Y) := by
  obtain ⟨U0, hU0c, hU0o⟩ := exists_compact_mem_nhds (1 : X)
  let U_aux : ℕ → {S : Set X | S ∈ nhds 1} :=
    Nat.rec ⟨U0, hU0o⟩ <| fun _ S ↦ let h := exists_closed_nhds_one_inv_eq_mul_subset S.2
      ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  let U : ℕ → Set X := fun n ↦ (U_aux n).1
  have hU1 : ∀ n, U n ∈ nhds 1 := fun n ↦ (U_aux n).2
  have hU2 : ∀ n, U (n + 1) * U (n + 1) ⊆ U n :=
    fun n ↦ (Classical.choose_spec (exists_closed_nhds_one_inv_eq_mul_subset (U_aux n).2)).2.2.2
  have hU3 : ∀ n, U (n + 1) ⊆ U n :=
    fun n x hx ↦ hU2 n (mul_one x ▸ Set.mul_mem_mul hx (mem_of_mem_nhds (hU1 (n + 1))))
  apply mythm (U 0) (V 0) hU0c hVc (hVo.mem_of_mem trivial)
  rw [hVo.uniformity_of_nhds_one.equicontinuousAt_iff_right]
  refine' fun n _ ↦ Filter.eventually_iff_exists_mem.mpr ⟨U n, hU1 n, fun x hx ⟨f, hf⟩ ↦ _⟩
  rw [Set.mem_setOf_eq, map_one, div_one]
  suffices : U n ⊆ f ⁻¹' V n
  · exact this hx
  clear x hx
  induction' n with n ih
  · exact hf
  · exact fun x hx ↦ hV (ih (hU3 n hx)) (map_mul f x x ▸ ih (hU2 n (Set.mul_mem_mul hx hx)))

open Pointwise

-- PR # 7596
lemma coveringmap : IsCoveringMap expMapCircle := sorry

lemma basis0 :
    Filter.HasBasis (nhds (0 : ℝ)) (fun _ ↦ True) (fun n : ℕ ↦ Set.Icc (- (n + 1 : ℝ)⁻¹) (n + 1 : ℝ)⁻¹) := by
  have key := nhds_basis_zero_abs_sub_lt ℝ
  have : ∀ ε : ℝ, {b | |b| < ε} = Set.Ioo (-ε) ε
  · simp [Set.ext_iff, abs_lt]
  simp only [this] at key
  refine' key.to_hasBasis (fun ε hε ↦ _) (fun n _ ↦ ⟨(n + 1)⁻¹, by positivity, Set.Ioo_subset_Icc_self⟩)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  rw [one_div] at hn
  exact ⟨n, trivial, Set.Icc_subset_Ioo (neg_lt_neg hn) hn⟩

lemma basis1 :
    Filter.HasBasis (nhds (0 : ℝ)) (fun _ ↦ True) (fun n : ℕ ↦ Set.Icc (-(2 ^ n : ℝ)⁻¹) (2 ^ n : ℝ)⁻¹) := by
  have h1 : ∀ n : ℕ, (2 ^ n : ℝ)⁻¹ ≤ (n + 1 : ℝ)⁻¹ := fun n ↦
    inv_le_inv_of_le (by positivity) (mod_cast Nat.lt_two_pow n)
  have h2 : ∀ n, 0 < (2 ^ n : ℝ)⁻¹ := fun n ↦ by positivity
  refine' basis0.to_subset _ _
  · exact fun n _ ↦ Set.Icc_subset_Icc (neg_le_neg (h1 n)) (h1 n)
  · exact fun n _ ↦ Icc_mem_nhds (neg_neg_of_pos (h2 n)) (h2 n)

lemma smul_Icc {a b c : ℝ} (ha : 0 < a) : a • Set.Icc b c = Set.Icc (a • b) (a • c) := by
  ext x
  simp [Set.mem_smul_set]
  refine' ⟨_, fun ⟨h1, h2⟩ ↦ ⟨x / a,
    ⟨(le_div_iff' ha).mpr h1, (div_le_iff' ha).mpr h2⟩, mul_div_cancel' x ha.ne'⟩⟩
  rintro ⟨y, ⟨h1, h2⟩, rfl⟩
  exact ⟨(mul_le_mul_left ha).mpr h1, (mul_le_mul_left ha).mpr h2⟩

instance : UniformGroup circle := by
  convert topologicalGroup_is_uniform_of_compactSpace circle
  exact unique_uniformity_of_compact rfl rfl

instance {X : Type*} [TopologicalSpace X] [Group X] [TopologicalGroup X] [LocallyCompactSpace X] :
    LocallyCompactSpace (ContinuousMonoidHom X circle) := by
  let Vn : ℕ → Set circle := fun n ↦ expMapCircle '' Set.Icc (-(2 ^ n : ℝ)⁻¹) (2 ^ n : ℝ)⁻¹
  have key0 : Filter.HasBasis (nhds 1) (fun _ ↦ True) Vn
  · rw [← expMapCircle_zero, ← coveringmap.isLocalHomeomorph.map_nhds_eq 0]
    exact basis1.map expMapCircle
  refine' mythm' Vn _ (isCompact_Icc.image coveringmap.continuous).isClosed key0
  intro n x h2 h1
  have h3 : ∀ t, t < Real.pi → Set.Icc (-t) t ⊆ Set.Ioc (-Real.pi) Real.pi
  · intro t ht
    by_cases h : -t ≤ t
    · exact (Set.Icc_subset_Ioc_iff h).mpr ⟨neg_lt_neg ht, ht.le⟩
    · rw [Set.Icc_eq_empty h]
      apply Set.empty_subset
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpow : (2 ^ n : ℝ)⁻¹ ≤ 1 := inv_le_one (one_le_pow_of_one_le one_le_two n)
  have h3 : x ∈ Vn (n + 1)
  · obtain ⟨s, hs, h1⟩ := h1
    obtain ⟨t, ht, h2⟩ := h2
    refine' ⟨t, _, h2⟩
    rw [← h2, ← expMapCircle_add] at h1
    have := (Set.Icc_add_Icc_subset _ _ _ _ (Set.add_mem_add ht ht))
    rw [← neg_add] at this
    have key := invOn_arg_expMapCircle.1.injOn (h3 _ ?_ hs) (h3 _ ?_ this) h1
    rw [key] at hs
    rw [← two_smul ℝ, ← Set.mem_inv_smul_set_iff₀, smul_Icc, smul_neg, ← smul_inv₀,
        smul_eq_mul, ← pow_succ] at hs
    exact hs
    · exact inv_pos.mpr two_pos
    · exact two_ne_zero
    · linarith
    · linarith
  exact h3

end ContinuousMonoidHom

/-- The Pontryagin dual of `A` is the group of continuous homomorphism `A → circle`. -/
def PontryaginDual :=
  ContinuousMonoidHom A circle
#align pontryagin_dual PontryaginDual

-- porting note: `deriving` doesn't derive these instances
instance : TopologicalSpace (PontryaginDual A) :=
  (inferInstance : TopologicalSpace (ContinuousMonoidHom A circle))

instance : T2Space (PontryaginDual A) :=
  (inferInstance : T2Space (ContinuousMonoidHom A circle))

instance {X : Type*} [Group X] [TopologicalSpace X] [TopologicalGroup X] [LocallyCompactSpace X] :
    LocallyCompactSpace (PontryaginDual X) :=
  (inferInstance : LocallyCompactSpace (ContinuousMonoidHom X circle))

-- porting note: instance is now noncomputable
noncomputable instance : CommGroup (PontryaginDual A) :=
  (inferInstance : CommGroup (ContinuousMonoidHom A circle))

instance : TopologicalGroup (PontryaginDual A) :=
  (inferInstance : TopologicalGroup (ContinuousMonoidHom A circle))

-- porting note: instance is now noncomputable
noncomputable instance : Inhabited (PontryaginDual A) :=
  (inferInstance : Inhabited (ContinuousMonoidHom A circle))


variable {A B C D E}

namespace PontryaginDual

open ContinuousMonoidHom

instance : FunLike (PontryaginDual A) A circle :=
  ContinuousMonoidHom.funLike

noncomputable instance : ContinuousMonoidHomClass (PontryaginDual A) A circle :=
  ContinuousMonoidHom.ContinuousMonoidHomClass

/-- `PontryaginDual` is a functor. -/
noncomputable def map (f : ContinuousMonoidHom A B) :
    ContinuousMonoidHom (PontryaginDual B) (PontryaginDual A) :=
  f.compLeft circle
#align pontryagin_dual.map PontryaginDual.map

@[simp]
theorem map_apply (f : ContinuousMonoidHom A B) (x : PontryaginDual B) (y : A) :
    map f x y = x (f y) :=
  rfl
#align pontryagin_dual.map_apply PontryaginDual.map_apply

@[simp]
theorem map_one : map (one A B) = one (PontryaginDual B) (PontryaginDual A) :=
  ext fun x => ext (fun _y => OneHomClass.map_one x)
#align pontryagin_dual.map_one PontryaginDual.map_one

@[simp]
theorem map_comp (g : ContinuousMonoidHom B C) (f : ContinuousMonoidHom A B) :
    map (comp g f) = ContinuousMonoidHom.comp (map f) (map g) :=
  ext fun _x => ext fun _y => rfl
#align pontryagin_dual.map_comp PontryaginDual.map_comp


@[simp]
nonrec theorem map_mul (f g : ContinuousMonoidHom A E) : map (f * g) = map f * map g :=
  ext fun x => ext fun y => map_mul x (f y) (g y)
#align pontryagin_dual.map_mul PontryaginDual.map_mul

variable (A B C D E)

/-- `ContinuousMonoidHom.dual` as a `ContinuousMonoidHom`. -/
noncomputable def mapHom [LocallyCompactSpace E] :
    ContinuousMonoidHom (ContinuousMonoidHom A E)
      (ContinuousMonoidHom (PontryaginDual E) (PontryaginDual A)) where
  toFun := map
  map_one' := map_one
  map_mul' := map_mul
  continuous_toFun := continuous_of_continuous_uncurry _ continuous_comp
#align pontryagin_dual.map_hom PontryaginDual.mapHom

end PontryaginDual
