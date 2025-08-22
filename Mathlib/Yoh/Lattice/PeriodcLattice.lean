import Mathlib
import Mathlib.Yoh.Lattice.Defs

open Polynomial Filter QuotientAddGroup Submodule MeasureTheory MeasureTheory.Measure
  NNReal BigOperators

variable {d : SpaceDimension} {L : RGStepL}
  (M : SideLength) (N : LatticeSpacing)

variable {μb gc : ℝ}

class OneLtL : Prop where
  out : 1 < L

variable [hL : @OneLtL L]

instance : NeZero L := NeZero.of_gt hL.out

section PeriodicLattice

abbrev FineLattice {L : RGStepL} (M : SideLength) (N : LatticeSpacing) :=
  (Fin d) → Fin (L ^ (M + N))

noncomputable def shiftOne (n : Fin d) : @FineLattice d L M N → @FineLattice d L M N :=
  fun x => fun m => if m = n then x m else x m + 1

end PeriodicLattice

section LatticeField

abbrev LatticeField {M : SideLength} {N : LatticeSpacing} := @FineLattice d L M N → ℝ

variable (ϕ : LatticeField) (x : FineLattice M N)

noncomputable def fieldNorm {M : SideLength} {N : LatticeSpacing} (ϕ : @LatticeField d L M N) : ℝ :=
  (∫ (x : @FineLattice d L M N), (ϕ x) ^ 2 ∂count) / L ^ (d * N)

noncomputable def partialDeriv {M : SideLength} {N : LatticeSpacing} (n : Fin d) :
    @LatticeField d L M N → @LatticeField d L M N :=
  fun ϕ => fun x => (ϕ (shiftOne M N n x) - ϕ x) / L ^ N

noncomputable def LatticeEmbedding {M : SideLength} {N₁ N₂ : LatticeSpacing} (h : N₁ < N₂) :
    @FineLattice d L M N₁ → @FineLattice d L M N₂ :=
  fun x => fun n => Fin.ofNat (L ^ (M + N₂)) (x n * (L ^ (N₂ - N₁)))

end LatticeField

section Weight

variable (x' : @FineLattice d L M (N - 1)) (x : @FineLattice d L M N) (n : Fin d)

abbrev FieldWeight {M : SideLength} {N : LatticeSpacing} := @LatticeField d L M N  → ℝ≥0

noncomputable def blockAveraging {M : SideLength} {N : LatticeSpacing} :
    @LatticeField d L M (N + 1) → @LatticeField d L M N :=
  fun ϕ => fun x =>
    ∑ x' ∈ {s : @FineLattice d L M (N + 1) | ∀ n, s n < L},
      ϕ (fun n => (LatticeEmbedding (lt_add_one N) x n) + x' n
        - (Fin.ofNat (L ^ (M + (N + 1))) (L / 2 : ℕ))) / L ^ d

lemma pow_sub_one_le : L ^ (M + N) ≤ L ^ (M + (N + 1)) := by
  apply Nat.pow_le_pow_of_le hL.out
  simp

noncomputable def blockConstant {M : SideLength} {N : LatticeSpacing} :
    @LatticeField d L M N → @LatticeField d L M (N + 1) :=
  fun ϕ => fun x => ϕ (fun n => (Fin.ofNat (L ^ (M + N)) (((x n : ℕ)+ L / (2 : ℕ)) / L)))

@[simp]
lemma blockConstant_apply {M : SideLength} {N : LatticeSpacing} (ϕ : @LatticeField d L M N)
    (x : @FineLattice d L M (N + 1)) :
    blockConstant ϕ x = ϕ (fun n => Fin.ofNat (L ^ (M + N)) (((x n : ℕ)+ L / (2 : ℕ)) / L)) := by
  rfl

lemma blockAC_eq_id {M : SideLength} {N : LatticeSpacing} :
    @blockAveraging d L _ M N ∘ @blockConstant d L _ M N= id := by
  ext ϕ x
  simp only [Function.comp_apply, id_eq]

end Weight


section FreeFlow

noncomputable def HFree {M : SideLength} {N : LatticeSpacing} (ϕ : @LatticeField d L M N )
  {μb : ℝ} : ℝ :=
  Real.exp (- ((∑ n, fieldNorm (partialDeriv n ϕ)) + μb * fieldNorm ϕ) / 2)

noncomputable def freePartitionFunction : ℝ :=
  ∫ (ϕ : @LatticeField d L M N), Real.exp (@HFree d L _ M N ϕ μb) ∂count


#check freePartitionFunction M N

end FreeFlow
