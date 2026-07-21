/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Toroidal lattices

Basic definitions for toroidal lattices used in renormalization-group arguments.
-/

@[expose] public section

/-- The `d`-dimensional continuum torus of side length `L ^ M`.

This is a wrapper around its coordinate representation so that geometric structures, such as a
metric, can be chosen independently of the canonical instances on the coordinate space.
-/
@[ext]
structure ContinuumTorus (d L M : ℕ) where
  /-- The coordinates of a point in the continuum torus. -/
  coords : Fin d → AddCircle ((L : ℝ) ^ M)

namespace ContinuumTorus

/-- The equivalence between the continuum torus and its coordinate representation. -/
def equiv (d L M : ℕ) :
    ContinuumTorus d L M ≃ (Fin d → AddCircle ((L : ℝ) ^ M)) where
  toFun := coords
  invFun := .mk
  left_inv _ := rfl
  right_inv _ := rfl

instance (d L M : ℕ) : AddCommGroup (ContinuumTorus d L M) :=
  (equiv d L M).addCommGroup

/-- The additive equivalence between the continuum torus and its coordinate representation. -/
def addEquiv (d L M : ℕ) :
    ContinuumTorus d L M ≃+ (Fin d → AddCircle ((L : ℝ) ^ M)) where
  __ := equiv d L M
  map_add' _ _ := rfl

/-- The point of the circle of period `L ^ M` representing one lattice spacing at scale `N`. -/
noncomputable def meshPoint (L M N : ℕ) : AddCircle ((L : ℝ) ^ M) :=
  (((L : ℝ) ^ M / (L ^ (M + N) : ℕ) : ℝ) : AddCircle ((L : ℝ) ^ M))

/-- A lattice spacing at scale `N` is an integral multiple of a lattice spacing at a finer scale. -/
theorem meshPoint_eq_nsmul_meshPoint {L M N N' : ℕ} (hL : 0 < L) (hNN' : N ≤ N') :
    meshPoint L M N = L ^ (N' - N) • meshPoint L M N' := by
  rw [meshPoint, meshPoint, ← AddCircle.coe_nsmul]
  congr 1
  norm_cast
  have hExp : M + N' = (N' - N) + (M + N) := by omega
  rw [hExp, pow_add]
  simp only [nsmul_eq_mul]
  field_simp
  norm_cast
  simp [pow_add, mul_assoc, mul_comm]

/-- The one-dimensional lattice of mesh size `L⁻ᴺ` in the circle of period `L ^ M`. -/
noncomputable def circleLattice (L M N : ℕ) : AddSubgroup (AddCircle ((L : ℝ) ^ M)) :=
  AddSubgroup.zmultiples (meshPoint L M N)

/-- The one-dimensional lattices form an increasing family as the scale becomes finer. -/
theorem circleLattice_mono {L M N N' : ℕ} (hL : 0 < L) (hNN' : N ≤ N') :
    circleLattice L M N ≤ circleLattice L M N' := by
  rw [circleLattice, circleLattice, AddSubgroup.zmultiples_le,
    meshPoint_eq_nsmul_meshPoint hL hNN']
  exact AddSubgroup.nsmul_mem_zmultiples _ _

/-- The one-dimensional lattice is additively equivalent to the corresponding cyclic group. -/
noncomputable def circleLatticeAddEquiv (L M N : ℕ) (hL : 0 < L) :
    circleLattice L M N ≃+ ZMod (L ^ (M + N)) := by
  letI : Fact (0 < (L : ℝ) ^ M) := ⟨pow_pos (Nat.cast_pos.2 hL) M⟩
  let g : circleLattice L M N :=
    ⟨meshPoint L M N, AddSubgroup.mem_zmultiples (meshPoint L M N)⟩
  have hg : ∀ x : circleLattice L M N, x ∈ AddSubgroup.zmultiples g := by
    rintro ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := hx
    exact ⟨n, rfl⟩
  have horder : addOrderOf (meshPoint L M N) = L ^ (M + N) := by
    simpa only [meshPoint] using
      (AddCircle.addOrderOf_period_div (p := (L : ℝ) ^ M) (n := L ^ (M + N))
        (pow_pos hL (M + N)))
  have hcard : Nat.card (circleLattice L M N) = L ^ (M + N) := by
    rw [circleLattice, Nat.card_zmultiples, horder]
  exact (zmodAddEquivOfGenerator hg hcard).symm

/-- The lattice `T⁻ᴺ_M` of mesh size `L⁻ᴺ` as an additive subgroup of the continuum torus. -/
noncomputable def discreteTorus (d L M N : ℕ) : AddSubgroup (ContinuumTorus d L M) :=
  (AddSubgroup.pi Set.univ fun _ ↦ circleLattice L M N).comap
    (addEquiv d L M).toAddMonoidHom

/-- The discrete tori form an increasing family of subgroups as the scale becomes finer. -/
theorem discreteTorus_mono {d L M N N' : ℕ} (hL : 0 < L) (hNN' : N ≤ N') :
    discreteTorus d L M N ≤ discreteTorus d L M N' := by
  apply AddSubgroup.comap_mono
  intro x hx i hi
  exact circleLattice_mono hL hNN' (hx i hi)

/-- The discrete tori are monotone in the ultraviolet cutoff. -/
theorem monotone_discreteTorus (d L M : ℕ) (hL : 0 < L) :
    Monotone (discreteTorus d L M) :=
  fun _ _ ↦ discreteTorus_mono hL

/-- The canonical inclusion of a discrete torus into a finer discrete torus. -/
noncomputable def discreteTorusInclusion {d L M N N' : ℕ} (hL : 0 < L) (hNN' : N ≤ N') :
    discreteTorus d L M N →+ discreteTorus d L M N' :=
  AddSubgroup.inclusion (discreteTorus_mono hL hNN')

/-- A coordinatewise product subgroup is additively equivalent to the product of its coordinate
subgroups. -/
def piCircleLatticeAddEquiv (d L M N : ℕ) :
    (AddSubgroup.pi Set.univ fun _ : Fin d ↦ circleLattice L M N) ≃+
      (Fin d → circleLattice L M N) where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
  invFun x := ⟨fun i ↦ x i, fun i _ ↦ (x i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The discrete torus is additively equivalent to the product of its one-dimensional coordinate
lattices. -/
noncomputable def discreteTorusAddEquivPiCircleLattice (d L M N : ℕ) :
    discreteTorus d L M N ≃+ (Fin d → circleLattice L M N) := by
  let H := AddSubgroup.pi Set.univ fun _ : Fin d ↦ circleLattice L M N
  let f := (addEquiv d L M).toAddMonoidHom
  let e : H.comap f ≃+ H := AddEquiv.ofBijective (f.addSubgroupComap H) <| by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact (addEquiv d L M).injective (congrArg Subtype.val hxy)
    · exact f.addSubgroupComap_surjective_of_surjective H (addEquiv d L M).surjective
  exact e.trans (piCircleLatticeAddEquiv d L M N)

/-- The lattice `T⁻ᴺ_M` is additively equivalent to a product of `d` copies of
`ZMod (L ^ (M + N))`. -/
noncomputable def discreteTorusAddEquivPiZMod (d L M N : ℕ) (hL : 0 < L) :
    discreteTorus d L M N ≃+ (Fin d → ZMod (L ^ (M + N))) :=
  (discreteTorusAddEquivPiCircleLattice d L M N).trans <|
    AddEquiv.piCongrRight fun _ ↦ circleLatticeAddEquiv L M N hL

/-- The renormalization-group lattice `T⁻ᵏ_(M + N - k)`. -/
noncomputable def renormalizationTorus (d L M N k : ℕ) :
    AddSubgroup (ContinuumTorus d L (M + N - k)) :=
  discreteTorus d L (M + N - k) k

/-- For `k ≤ N`, the renormalization-group lattice `T⁻ᵏ_(M + N - k)` is additively equivalent
to a product of `d` copies of `ZMod (L ^ (M + N))`. -/
noncomputable def renormalizationTorusAddEquivPiZMod (d L M N k : ℕ) (hL : 0 < L) (hk : k ≤ N) :
    renormalizationTorus d L M N k ≃+ (Fin d → ZMod (L ^ (M + N))) :=
  (discreteTorusAddEquivPiZMod d L (M + N - k) k hL).trans <|
    AddEquiv.piCongrRight fun _ ↦ (ZMod.ringEquivCongr <| congrArg (L ^ ·) <|
      Nat.sub_add_cancel (hk.trans <| Nat.le_add_left N M)).toAddEquiv

end ContinuumTorus
