import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.FieldTheory.Adjoin

open FiniteDimensional IntermediateField Polynomial

variable (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem aux1 (α : E) : F⟮α⟯ = ⊤ ↔ (minpoly F α).natDegree = finrank F E := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← adjoin.finrank (isIntegral_of_finite F α), h, ← finrank_top F E]
    rfl
  · refine IntermediateField.eq_of_le_of_finrank_eq le_top ?_
    rw [adjoin.finrank (isIntegral_of_finite F α), h, ← finrank_top]
    rfl

variable [IsSeparable F E] (A : Type*) [Field A] [IsAlgClosed A] [Algebra F A]

theorem aux2 (α : E) : F⟮α⟯ = ⊤ ↔ ∀ φ ψ : E →ₐ[F] A, φ α = ψ α → φ = ψ := by
  classical
  rw [aux1, ← Polynomial.card_rootSet_eq_natDegree (K := A) (IsSeparable.separable F α)
    (IsAlgClosed.splits_codomain (minpoly F α)), ← AlgHom.card F E A, ← Set.toFinset_card]
  simp_rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly A
    (Algebra.isAlgebraic_of_finite F E) α]
  rw [Fintype.card, Set.toFinset_range, Finset.card_image_iff, Finset.coe_univ,
    ← Set.injective_iff_injOn_univ]
  rfl

theorem aux3 (hA: Algebra.IsAlgebraic F A) (α : E) (φ : E →ₐ[F] A) :
    F⟮α⟯ = ⊤ ↔ ∀ ψ : E →ₐ[F] A, φ α = ψ α → φ = ψ := by
  rw [aux2 F A]
  refine ⟨fun h ψ =>  h φ ψ, fun h φ₀ ψ₀ h_eq => ?_⟩
  have : ∃ σ : A →ₐ[F] A, σ (φ₀ α) = φ α := by
    have t1 := Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly A hA (φ₀ α)
    have t2 := iff_of_eq (congr_arg (φ α ∈ ·) t1)
    dsimp at t2
    rw [Set.mem_range] at t2
    rw [t2]
    rw [mem_rootSet]
    refine ⟨?_, ?_⟩
    · refine minpoly.ne_zero ?_
      refine isAlgebraic_iff_isIntegral.mp (hA (φ₀ α))
    · rw [aeval_algHom_apply]
      rw [_root_.map_eq_zero]
      letI : Algebra E A := φ₀.toAlgebra
      have : IsScalarTower F E A := by
        refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
        have := RingHom.algebraMap_toAlgebra φ₀.toRingHom
        rw [this]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
      have : Function.Injective (algebraMap E A) := by
        exact NoZeroSMulDivisors.algebraMap_injective E A
      have t3 := minpoly.algebraMap_eq (A := F) this α
      have t4 : φ₀ α = algebraMap E A α := rfl
      rw [t4, t3]
      exact minpoly.aeval F α
  obtain ⟨σ, hσ⟩ := this
  have t1 : φ = AlgHom.comp σ φ₀ := by
    apply h
    exact hσ.symm
  have t2 : φ = AlgHom.comp σ ψ₀ := by
    apply h
    rw [AlgHom.coe_comp, Function.comp_apply, ← h_eq, hσ]
  ext x
  apply RingHom.injective σ.toRingHom
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  erw [AlgHom.congr_fun t1.symm x, AlgHom.congr_fun t2.symm x]

def subclosure : IntermediateField F A := by
  let S : Set A := { x : A | IsAlgebraic F x }
  exact IntermediateField.adjoin F S

theorem mem_subclosure {x : A} (h : IsAlgebraic F x) : x ∈ subclosure F A := by
  apply Subfield.subset_closure
  refine Set.mem_union_right _ ?_
  exact h

theorem isalgclosure.subclosure : IsAlgClosure F (subclosure F A) := by
  refine IsAlgClosure.mk ?_ ?_
  ·
    sorry
  · refine isAlgebraic_adjoin ?_
    sorry


theorem aux4 (α : E) (φ : E →ₐ[F] A) :
    F⟮α⟯ = ⊤ ↔ ∀ ψ : E →ₐ[F] A, φ α = ψ α → φ = ψ := by
  let K := subclosure F A
  have :=  isalgclosure.subclosure F A
  have hK_alg : Algebra.IsAlgebraic F K := (isalgclosure.subclosure F A).algebraic
  have hK_mem : ∀ (ψ : E →ₐ[F] A) (x : E), ψ x ∈ K := by
    intro ψ x
    refine mem_subclosure F A ?_
    have : IsAlgebraic F x := isAlgebraic_of_finite F x
    exact isAlgebraic_algHom_of_isAlgebraic ψ this
  let res : (E →ₐ[F] A) → (E →ₐ[F] K) := by
    exact fun ψ => AlgHom.codRestrict ψ K.toSubalgebra (hK_mem ψ)
  rw [aux2 F A]
  refine ⟨fun h ψ =>  h φ ψ, fun h φ₀ ψ₀ h_eq => ?_⟩
  have : ∃ σ : K →ₐ[F] A, σ (⟨φ₀ α, hK_mem _ _⟩) = φ α := by
    have t1 := Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly A hK_alg ⟨φ₀ α, hK_mem _ _⟩
    have t2 := iff_of_eq (congr_arg (φ α ∈ ·) t1)
    dsimp at t2
    rw [Set.mem_range] at t2
    rw [t2]
    rw [mem_rootSet]
    refine ⟨?_, ?_⟩
    · refine minpoly.ne_zero ?_
      refine isAlgebraic_iff_isIntegral.mp (hK_alg _)
    · rw [aeval_algHom_apply]
      rw [_root_.map_eq_zero]
      letI : Algebra E K := (res φ₀).toAlgebra
      have : IsScalarTower F E K := by
        refine IsScalarTower.of_algebraMap_eq (fun x => ?_)
        have := RingHom.algebraMap_toAlgebra (res φ₀).toRingHom
        erw [this]
        simp [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
        rw [@AlgHomClass.commutes]
      have : Function.Injective (algebraMap E K) := by
        exact NoZeroSMulDivisors.algebraMap_injective E K
      have t3 := minpoly.algebraMap_eq (A := F) this α
      have t4 : φ₀ α = algebraMap E K α := rfl
      simp_rw [t4]
      rw [t3]
      exact minpoly.aeval F α
  obtain ⟨σ, hσ⟩ := this
  have t1 : φ = AlgHom.comp σ (res φ₀) := by
    apply h
    exact hσ.symm
  have t2 : φ = AlgHom.comp σ (res ψ₀) := by
    apply h
    rw [← hσ, AlgHom.coe_comp, Function.comp_apply]
    congr 2
  ext x
  have := RingHom.injective σ.toRingHom
  have t0 : σ (res φ₀ x) = σ (res ψ₀ x) := by
    rw [t1] at t2
    have := AlgHom.congr_fun t2 x
    exact this
  have := this t0
  dsimp at this
  rw [@Subtype.mk_eq_mk] at this
  exact this
