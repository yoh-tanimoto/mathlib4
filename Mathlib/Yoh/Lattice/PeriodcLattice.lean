import Mathlib
import Mathlib.Yoh.Lattice.Defs

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

variable [ParameterSet] {μb gc : ℝ}

#check d

class OneLtL : Prop where
  out : 1 < L'

variable [hL : @OneLtL L']

instance : NeZero L' := NeZero.of_gt hL.out

noncomputable section PeriodicLattice

abbrev ContinuousTorus := (Fin d) → (AddCircle (L : ℝ))

def FineBasisVector (i : Fin d) : ContinuousTorus := (fun j => if i = j then (1 / N : ℝ) else 0)

def ScaledBasisVector (k : Fin N) (i : Fin d) :
    ContinuousTorus := (fun j => if i = j then (k / N : ℝ) else 0)

def FineBasis : Set ContinuousTorus :=
  Set.range (fun (i : Fin d) => FineBasisVector i)

def ScaledBasis (k : Fin N) : Set ContinuousTorus :=
  Set.range (fun (i : Fin d) => ScaledBasisVector k i)

def ScaledInfiniteLattice (p : ℝ) :=
  AddSubgroup.map ((LinearMap.lsmul ℝ ℝ p : ℝ →+ ℝ).comp (Int.castAddHom ℝ)) (⊤ : AddSubgroup ℤ)

lemma ScaledInfiniteLattice_eq (p : ℝ) : ScaledInfiniteLattice p = AddSubgroup.closure {p} := by
  ext x
  rw [ScaledInfiniteLattice, AddSubgroup.mem_map, AddSubgroup.mem_closure_singleton]
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


def ScaledLattice (k : Fin N) := Submodule.span ℤ (ScaledBasis k)

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
  sorry
--  fun x => fun j => ⟨(x : ContinuousTorus) j, by sorry⟩
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
