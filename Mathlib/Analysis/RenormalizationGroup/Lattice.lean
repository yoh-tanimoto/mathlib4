/-
Copyright (c) 2026 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.Module.Pi
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
  coord : Fin d → AddCircle ((L : ℝ) ^ M)

namespace ContinuumTorus

variable (d L M N : ℕ)

/-- The equivalence between the continuum torus and its coordinate representation. -/
def toPi :
    ContinuumTorus d L M ≃ (Fin d → AddCircle ((L : ℝ) ^ M)) where
  toFun := coord
  invFun := .mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : AddCommGroup (ContinuumTorus d L M) :=
  (toPi d L M).addCommGroup

/-- The additive equivalence between the continuum torus and its coordinate representation. -/
def addToPi :
    ContinuumTorus d L M ≃+ (Fin d → AddCircle ((L : ℝ) ^ M)) where
  __ := toPi d L M
  map_add' _ _ := rfl

/-- The point of the circle of period `L ^ M` representing one lattice spacing at scale `N`. -/
noncomputable abbrev latticeSpacing : AddCircle ((L : ℝ) ^ M) :=
  ((1 / (L ^ N) : ℝ) : AddCircle ((L : ℝ) ^ M))

/-- A lattice spacing at scale `N` is an integral multiple of a lattice spacing at a finer scale. -/
theorem latticeSpacing_eq_nsmul_latticeSpacing {L M N N' : ℕ} (hL : 0 < L)
    (hNN' : N ≤ N') :
    latticeSpacing L M N = L ^ (N' - N) • latticeSpacing L M N' := by
  rw [latticeSpacing, latticeSpacing, ← AddCircle.coe_nsmul]
  congr 1
  norm_cast
  simp only [nsmul_eq_mul]
  field_simp
  norm_cast
  rw [← pow_add]
  congr 1
  omega

/-- The one-dimensional lattice of mesh size `L⁻ᴺ` in the circle of period `L ^ M`. -/
noncomputable def discreteCircle : AddSubgroup (AddCircle ((L : ℝ) ^ M)) :=
  AddSubgroup.zmultiples (latticeSpacing L M N)

/-- The one-dimensional lattices form an increasing family as the scale becomes finer. -/
theorem discreteCircle_mono {L M N N' : ℕ} (hL : 0 < L) (hNN' : N ≤ N') :
    discreteCircle L M N ≤ discreteCircle L M N' := by
  rw [discreteCircle, discreteCircle, AddSubgroup.zmultiples_le,
    latticeSpacing_eq_nsmul_latticeSpacing hL hNN']
  exact AddSubgroup.nsmul_mem_zmultiples _ _

/-- The one-dimensional lattice is additively equivalent to the corresponding cyclic group. -/
noncomputable def discreteCircleAddEquiv (hL : 0 < L) :
    discreteCircle L M N ≃+ ZMod (L ^ (M + N)) := by
  letI : Fact (0 < (L : ℝ) ^ M) := ⟨pow_pos (Nat.cast_pos.2 hL) M⟩
  let g : discreteCircle L M N :=
    ⟨latticeSpacing L M N, AddSubgroup.mem_zmultiples (latticeSpacing L M N)⟩
  have hg : ∀ x : discreteCircle L M N, x ∈ AddSubgroup.zmultiples g := by
    rintro ⟨x, hx⟩
    obtain ⟨n, rfl⟩ := hx
    exact ⟨n, rfl⟩
  have horder : addOrderOf (latticeSpacing L M N) = L ^ (M + N) := by
    rw [latticeSpacing]
    have hmesh :
        (1 / (L ^ N) : ℝ) = (L : ℝ) ^ M / (L ^ (M + N) : ℕ) := by
      norm_cast
      rw [pow_add]
      field_simp
      norm_cast
      exact Nat.mul_comm _ _
    rw [hmesh]
    exact AddCircle.addOrderOf_period_div (p := (L : ℝ) ^ M) (n := L ^ (M + N))
      (pow_pos hL (M + N))
  have hcard : Nat.card (discreteCircle L M N) = L ^ (M + N) := by
    rw [discreteCircle, Nat.card_zmultiples, horder]
  exact (zmodAddEquivOfGenerator hg hcard).symm

/-- The lattice `T⁻ᴺ_M` of mesh size `L⁻ᴺ` as an additive subgroup of the continuum torus. -/
noncomputable def discreteTorus : AddSubgroup (ContinuumTorus d L M) :=
  (AddSubgroup.pi Set.univ fun _ ↦ discreteCircle L M N).comap
    (addToPi d L M).toAddMonoidHom

/-- The `i`-th coordinate of a point in the discrete torus. -/
def discreteTorus.coord (x : discreteTorus d L M N) (i : Fin d) :
    discreteCircle L M N := ⟨x.1.coord i, x.2 i (Set.mem_univ i)⟩

/-- The discrete tori form an increasing family of subgroups as the scale becomes finer. -/
theorem discreteTorus_mono {d L M N N' : ℕ} (hL : 0 < L) (hNN' : N ≤ N') :
    discreteTorus d L M N ≤ discreteTorus d L M N' := by
  apply AddSubgroup.comap_mono
  intro x hx i hi
  exact discreteCircle_mono hL hNN' (hx i hi)

/-- The discrete tori are monotone in the ultraviolet cutoff. -/
theorem monotone_discreteTorus (hL : 0 < L) :
    Monotone (discreteTorus d L M) :=
  fun _ _ ↦ discreteTorus_mono hL

/-- The canonical inclusion of a discrete torus into a finer discrete torus. -/
noncomputable def discreteTorusInclusion {d L M N N' : ℕ} (hL : 0 < L) (hNN' : N ≤ N') :
    discreteTorus d L M N →+ discreteTorus d L M N' :=
  AddSubgroup.inclusion (discreteTorus_mono hL hNN')

/-- A coordinatewise product subgroup is additively equivalent to the product of its coordinate
subgroups. -/
def pidiscreteCircleAddEquiv :
    (AddSubgroup.pi Set.univ fun _ : Fin d ↦ discreteCircle L M N) ≃+
      (Fin d → discreteCircle L M N) where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ i)⟩
  invFun x := ⟨fun i ↦ x i, fun i _ ↦ (x i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The discrete torus is additively equivalent to the product of its one-dimensional coordinate
lattices. -/
noncomputable def discreteTorusAddEquivPidiscreteCircle :
    discreteTorus d L M N ≃+ (Fin d → discreteCircle L M N) where
  toFun x := discreteTorus.coord d L M N x
  invFun x := ⟨⟨fun i ↦ x i⟩, fun i _ ↦ (x i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The lattice `T⁻ᴺ_M` is additively equivalent to a product of `d` copies of
`ZMod (L ^ (M + N))`. -/
noncomputable def discreteTorusAddEquivPiZMod (hL : 0 < L) :
    discreteTorus d L M N ≃+ (Fin d → ZMod (L ^ (M + N))) :=
  (discreteTorusAddEquivPidiscreteCircle d L M N).trans <|
    AddEquiv.piCongrRight fun _ ↦ discreteCircleAddEquiv L M N hL

/-- The renormalization-group lattice `T⁻ᵏ_(M + N - k)`. -/
noncomputable def renormalizationTorus (k : ℕ) :
    AddSubgroup (ContinuumTorus d L (M + N - k)) :=
  discreteTorus d L (M + N - k) k

/-- For `k ≤ N`, the renormalization-group lattice `T⁻ᵏ_(M + N - k)` is additively equivalent
to a product of `d` copies of `ZMod (L ^ (M + N))`. -/
noncomputable def renormalizationTorusAddEquivPiZMod (k : ℕ) (hL : 0 < L) (hk : k ≤ N) :
    renormalizationTorus d L M N k ≃+ (Fin d → ZMod (L ^ (M + N))) :=
  (discreteTorusAddEquivPiZMod d L (M + N - k) k hL).trans <|
    AddEquiv.piCongrRight fun _ ↦ (ZMod.ringEquivCongr <| congrArg (L ^ ·) <|
      Nat.sub_add_cancel (hk.trans <| Nat.le_add_left N M)).toAddEquiv

end ContinuumTorus

section LatticeField

open ContinuumTorus
variable (d L M N : ℕ)

/-- A scalar field on the discrete torus. -/
def LatticeField := discreteTorus d L M N → ℝ

instance : AddCommGroup (LatticeField d L M N) :=
  inferInstanceAs (AddCommGroup (discreteTorus d L M N → ℝ))

instance : Module ℝ (LatticeField d L M N) :=
  Pi.module (discreteTorus d L M N) (fun _ ↦ ℝ) ℝ

end LatticeField
