import Mathlib
import Mathlib.Yoh.Lattice.Defs

-- Temporary goal: define lattice as a `AddSubgroup` of `(Fin d) → AddCircle L ^ M`,
-- showing that it is isomorphic to `(Fin d) → ZMod L ^ (M + N)`
-- together with `LatticeEmbedding` as `AddGroupHom`


open Polynomial Filter QuotientAddGroup Submodule MeasureTheory MeasureTheory.Measure
  NNReal BigOperators

class ParameterSet where
  d : ℕ
  L : ℕ
  M : ℕ
  N : ℕ

variable {d' : SpaceDimension} {L' : RGStepL}
  (M' : SideLength) (N' : LatticeSpacing)

export ParameterSet (d L M N)

variable [ps : ParameterSet] {μb gc : ℝ}

#check d

class OneLtL : Prop where
  out : 1 < L

variable [hL : @OneLtL ps]

instance : Fact (0 < (L ^ M : ℝ)) :=
    Fact.mk (by
      rw [← Nat.cast_pow]
      exact Nat.cast_pos'.mpr (pow_pos (lt_trans zero_lt_one hL.out) M))

instance : NeZero L := NeZero.of_gt hL.out

noncomputable section PeriodicLattice

abbrev ContinuousTorus := (Fin d) → (AddCircle (L ^ M : ℝ))

def FineBasisVector (i : Fin d) : ContinuousTorus := (fun j => if i = j then (1 / N : ℝ) else 0)

def ScaledBasisVector (k : Fin N) (i : Fin d) :
    ContinuousTorus := (fun j => if i = j then (k / N : ℝ) else 0)

def FineBasis : Set ContinuousTorus :=
  Set.range (fun (i : Fin d) => FineBasisVector i)

def ScaledBasis (k : Fin N) : Set ContinuousTorus :=
  Set.range (fun (i : Fin d) => ScaledBasisVector k i)

def ScaledInfiniteLattice1d (p : ℝ) :=
  AddSubgroup.map ((LinearMap.lsmul ℝ ℝ p : ℝ →+ ℝ).comp (Int.castAddHom ℝ)) (⊤ : AddSubgroup ℤ)

lemma ScaledInfiniteLattice1d_eq (p : ℝ) :
    ScaledInfiniteLattice1d p = AddSubgroup.zmultiples p := by
  ext x
  rw [ScaledInfiniteLattice1d, AddSubgroup.mem_map, AddSubgroup.mem_zmultiples_iff]
  simp only [AddSubgroup.mem_top, AddMonoidHom.coe_comp, AddMonoidHom.coe_coe, Int.coe_castAddHom,
    Function.comp_apply, LinearMap.lsmul_apply, smul_eq_mul, true_and, zsmul_eq_mul]
  constructor
  · intro h
    obtain ⟨q, hq⟩ := h
    use q
    rw [← hq]
    exact Int.cast_comm q p
  · intro h
    obtain ⟨q, hq⟩ := h
    use q
    rw [← hq]
    exact Eq.symm (Int.cast_comm q p)

def ScaledPeriodicLattice1d (k : Fin N) :=
  AddSubgroup.map (QuotientAddGroup.mk' (AddSubgroup.zmultiples (L ^ M : ℝ)))
    (ScaledInfiniteLattice1d (1 / (L ^ (N - k) : ℝ)))

lemma ScaledPeriodicLattice1d_eq_Submodule_span (k : Fin N) :
    ScaledPeriodicLattice1d k =
    AddSubgroup.zmultiples
    ((QuotientAddGroup.mk' (AddSubgroup.zmultiples (L ^ M : ℝ))) (1 / (L ^ (N - k) : ℝ))) := by
  ext x
  simp only [one_div, mk'_apply]
  constructor
  · intro h
    obtain ⟨y, hy⟩ := AddSubgroup.mem_map.mp h
    simp only [one_div, mk'_apply] at hy
    rw [ScaledInfiniteLattice1d_eq] at hy
    rw [← hy.right]
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp hy.left
    rw [AddSubgroup.mem_zmultiples_iff]
    use m
    rw [← hm]
    simp
  · intro h
    obtain ⟨m, hm⟩ := AddSubgroup.mem_zmultiples_iff.mp h
    rw [ScaledPeriodicLattice1d]
    simp only [one_div, AddSubgroup.mem_map, mk'_apply]
    use m • (L ^ (N - k) : ℝ )⁻¹
    refine ⟨?_, hm⟩
    rw [ScaledInfiniteLattice1d_eq]
    simp

def ScaledLattice (k : Fin N) := Submodule.span ℤ (ScaledBasis k)

abbrev ScaledLattice' (k : Fin N) := (Fin d) → ScaledPeriodicLattice1d k

section QuotientGroupPi

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)] {NG : (i : ι) → Subgroup (G i)}
  [nnormal : ∀ i, (NG i).Normal]

-- #synth (Subgroup.pi Set.univ NG).Normal fails

@[to_additive]
instance Subgroup_normal : (Subgroup.pi Set.univ NG).Normal :=
  { conj_mem := fun n hn g i hi => Subgroup.Normal.conj_mem (nnormal i) (n i) (hn i hi) (g i) }

#synth (Subgroup.pi Set.univ NG).Normal

-- missing Pi.mulEquiv? cf. Pi.monoidHom
-- missing the canonical iso between the groups below

#synth Group ((i : ι) → (G i) ⧸ (NG i))
#synth Group (((i : ι) → (G i)) ⧸ (Subgroup.pi Set.univ NG))


end QuotientGroupPi

section QuotientAddGroupPi

variable {ι : Type*} {G : ι → Type*} [∀ i, AddCommGroup (G i)] {NG : (i : ι) → AddSubgroup (G i)}

#synth (AddSubgroup.pi Set.univ NG).Normal

end QuotientAddGroupPi


def ScaledLattice.component (k : Fin N) (x : ScaledLattice k) (j : Fin d) :
    Set.Ioc (0 : ℝ) (0 + L ^ M) :=
  AddCircle.equivIoc (L ^ M : ℝ) 0 (x.val j)

lemma mem_ScaledLattice_iff (k : Fin N) (x : ContinuousTorus) : x ∈ ScaledLattice k ↔
    ∀ j, ∃ (m : ℕ), AddCircle.equivIoc (L ^ M : ℝ) 0 (x j) = (m / L ^ N : ℝ) := by
  constructor
  · intro h j
    sorry
  · sorry

def FineLattice := AddSubgroup.closure FineBasis

lemma ScaledBasisVector_in_ScaledLattice {k : Fin N} {i : Fin d} :
    ScaledBasisVector k i ∈ ScaledLattice k := Submodule.mem_span_of_mem (Set.mem_range_self _)

lemma FineBasisVector_in_FineLattice {i : Fin d} : FineBasisVector i ∈ FineLattice :=
  AddSubgroup.mem_closure_of_mem (Set.mem_range_self _)

abbrev FineLattice' {L' : RGStepL} (M' : SideLength) (N' : LatticeSpacing) :=
  (Fin d') → Fin (L' ^ (M' + N'))

variable (x : FineLattice) (j : Fin d)

noncomputable def shiftOne {k : Fin N} (i : Fin d) : ScaledLattice k → ScaledLattice k :=
  fun x => x + ⟨(ScaledBasisVector k i), ScaledBasisVector_in_ScaledLattice⟩

noncomputable def shiftOne' (n : Fin d') : @FineLattice' d' L' M' N' → @FineLattice' d' L' M' N' :=
  fun x => fun m => if m = n then x m else x m + 1

end PeriodicLattice

noncomputable section LatticeField

abbrev ScaledLatticeField (k : Fin N) := ScaledLattice k → ℝ

abbrev LatticeField := FineLattice → ℝ

abbrev LatticeField' {M' : SideLength} {N' : LatticeSpacing} := @FineLattice' d' L' M' N' → ℝ

variable (ϕ : LatticeField) (x : FineLattice)

def scaledFieldNorm {k : Fin N} (ϕ : ScaledLatticeField k) : ℝ :=
  (∫ (x : ScaledLattice k), (ϕ x) ^ 2 ∂count) / L ^ (d * (N - k))

def fieldNorm (ϕ : LatticeField) : ℝ :=
  (∫ (x : FineLattice), (ϕ x) ^ 2 ∂count) / L ^ (d * N)

def fieldNorm' {M' : SideLength} {N' : LatticeSpacing} (ϕ : @LatticeField' d' L' M' N') : ℝ :=
  (∫ (x : @FineLattice' d' L' M' N'), (ϕ x) ^ 2 ∂count) / L' ^ (d' * N')

def partialDeriv {k : Fin N} (i : Fin d) :
    ScaledLatticeField k → ScaledLatticeField k :=
  fun ϕ => fun x => (ϕ (shiftOne i x) - ϕ x) / L ^ (N - k)

def partialDeriv' {M' : SideLength} {N' : LatticeSpacing} (n : Fin d') :
    @LatticeField' d' L' M' N' → @LatticeField' d' L' M' N' :=
  fun ϕ => fun x => (ϕ (shiftOne' M' N' n x) - ϕ x) / L' ^ N'

def LatticeEmbedding {k₁ k₂ : Fin N} (h : k₁ < k₂) :
    ScaledLattice k₂ → ScaledLattice k₁ :=
  fun x => ⟨fun (j : Fin d) => ((x : ContinuousTorus) j : AddCircle (L ^ M : ℝ)), by sorry⟩
-- need to show that `x` in a finer lattice is in the ℤ-span of coarser lattice basis.
-- maybe I should construct API to take components
-- look around Mathlib.Analysis.Fourier.ZMod, Mathlib.Topology.Instances.AddCircle.Real
-- and develop APIs
-- make an isomorphism between this and Mathlib.Data.ZMod.Basic

def LatticeEmbedding' {M' : SideLength} {N₁ N₂ : LatticeSpacing} (h : N₁ < N₂) :
    @FineLattice' d' L' M' N₁ → @FineLattice' d' L' M' N₂ :=
  fun x => fun n => Fin.ofNat (L' ^ (M' + N₂)) (x n * (L' ^ (N₂ - N₁)))

end LatticeField

section Weight

abbrev FieldWeight' {M' : SideLength} {N' : LatticeSpacing} := @LatticeField' d' L' M' N'  → ℝ≥0

noncomputable def blockAveraging' {M' : SideLength} {N' : LatticeSpacing} :
    @LatticeField' d' L' M' (N' + 1) → @LatticeField' d' L' M' N' :=
  fun ϕ => fun x =>
    ∑ x' ∈ {s : @FineLattice' d' L' M' (N' + 1) | ∀ n, s n < L'},
      ϕ (fun n => (LatticeEmbedding' (lt_add_one N') x n) + x' n
        - (Fin.ofNat (L' ^ (M' + (N' + 1))) (L' / 2 : ℕ))) / L' ^ d'

lemma pow_sub_one_le' : L' ^ (M' + N') ≤ L' ^ (M' + (N' + 1)) := by
  apply Nat.pow_le_pow_of_le hL.out
  simp

noncomputable def blockConstant' {M' : SideLength} {N' : LatticeSpacing} :
    @LatticeField' d' L' M' N' → @LatticeField' d' L' M' (N' + 1) :=
  fun ϕ => fun x => ϕ (fun n => (Fin.ofNat (L' ^ (M' + N')) (((x n : ℕ)+ L' / (2 : ℕ)) / L')))

@[simp]
lemma blockConstant_apply' {M' : SideLength} {N' : LatticeSpacing} (ϕ : @LatticeField' d' L' M' N')
    (x : @FineLattice' d' L' M' (N' + 1)) :
    blockConstant' ϕ x = ϕ (fun n => Fin.ofNat (L' ^ (M' + N')) (((x n : ℕ)+ L' / (2 : ℕ)) / L')) := by
  rfl

lemma blockAC_eq_id' {M' : SideLength} {N' : LatticeSpacing} :
    @blockAveraging' d' L' _ M' N' ∘ @blockConstant' d' L' _ M' N' = id := by
  ext ϕ x
  simp only [Function.comp_apply, id_eq]
  sorry

end Weight


section FreeFlow

noncomputable def HFree' {M' : SideLength} {N' : LatticeSpacing} (ϕ : @LatticeField' d' L' M' N')
  {μb : ℝ} : ℝ :=
  Real.exp (- ((∑ n, fieldNorm' (partialDeriv' n ϕ)) + μb * fieldNorm' ϕ) / 2)

noncomputable def freePartitionFunction' : ℝ :=
  ∫ (ϕ : @LatticeField' d' L' M' N'), Real.exp (@HFree' d' L' _ M' N' ϕ μb) ∂count

-- multivariate Gaussian Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

#check freePartitionFunction' M' N'

end FreeFlow
