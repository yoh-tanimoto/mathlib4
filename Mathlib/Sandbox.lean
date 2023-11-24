import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.FieldTheory.Adjoin

open FiniteDimensional IntermediateField Polynomial Algebra

variable (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem Field.primitive_element_of_natDegree_eq (α : E) :
    F⟮α⟯ = ⊤ ↔ (minpoly F α).natDegree = finrank F E := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← adjoin.finrank (IsIntegral.of_finite F α), h, ← finrank_top F E]
    rfl
  · refine eq_of_le_of_finrank_eq le_top ?_
    rw [adjoin.finrank (IsIntegral.of_finite F α), h, ← finrank_top]
    rfl

theorem Field.primitive_element_of_degree_eq (α : E) :
    F⟮α⟯ = ⊤ ↔ (minpoly F α).degree = finrank F E := by
  sorry

variable [IsSeparable F E] (A : Type*) [Field A] [IsAlgClosed A] [Algebra F A]

theorem Field.primitive_element_of_algHom_eval_pairwise_ne (α : E) :
    F⟮α⟯ = ⊤ ↔ ∀ φ ψ : E →ₐ[F] A, φ ≠ ψ → φ α ≠ ψ α := by
  classical
  rw [primitive_element_of_natDegree_eq, ← card_rootSet_eq_natDegree (K := A)
    (IsSeparable.separable F α) (IsAlgClosed.splits_codomain (minpoly F α)),
    ← AlgHom.card F E A, ← Set.toFinset_card]
  simp_rw [← IsAlgebraic.range_eval_eq_rootSet_minpoly A (Algebra.IsAlgebraic.of_finite F E) α,
    not_imp_not]
  rw [Fintype.card, Set.toFinset_range, Finset.card_image_iff, Finset.coe_univ,
    ← Set.injective_iff_injOn_univ]
  rfl

theorem Field.primitive_element_of_algHom_eval_ne (α : E) (φ : E →ₐ[F] A) :
    F⟮α⟯ = ⊤ ↔ ∀ ψ : E →ₐ[F] A, φ ≠ ψ → φ α ≠ ψ α := by
  let K := IntermediateField.adjoin F (⋃ ψ : E →ₐ[F] A, Set.range ψ)
  have hK_alg : Algebra.IsAlgebraic F K := by
    refine isAlgebraic_adjoin fun a ha => IsAlgebraic.isIntegral ?_
    obtain ⟨ψ, x, rfl⟩ := Set.mem_iUnion.mp ha
    exact (IsAlgebraic.of_finite F x).algHom ψ
  have hK_mem : ∀ (ψ : E →ₐ[F] A) (x : E), ψ x ∈ K := fun ψ x => by
    refine Subfield.subset_closure (Set.mem_union_right _ ?_)
    exact Set.mem_iUnion.mpr ⟨ψ, Set.mem_range_self x⟩
  let res : (E →ₐ[F] A) → (E →ₐ[F] K) := fun ψ => AlgHom.codRestrict ψ K.toSubalgebra (hK_mem ψ)
  rw [Field.primitive_element_of_algHom_eval_pairwise_ne F A]
  refine ⟨fun h ψ =>  h φ ψ, fun h φ₀ ψ₀ => ?_⟩
  rsuffices ⟨σ, hσ⟩ : ∃ σ : K →ₐ[F] A, σ (⟨φ₀ α, hK_mem _ _⟩) = φ α
  · simp_rw [not_imp_not] at h ⊢
    intro h_eq
    suffices res φ₀ = res ψ₀ by
      ext x
      exact Subtype.mk_eq_mk.mp (AlgHom.congr_fun this x)
    have hφ₁ : φ = AlgHom.comp σ (res φ₀) := h (AlgHom.comp σ (res φ₀)) hσ.symm
    have hφ₂ : φ = AlgHom.comp σ (res ψ₀) := by
      apply h
      rw [← hσ, AlgHom.coe_comp, Function.comp_apply]
      congr 2
    ext1 x
    exact RingHom.injective σ.toRingHom <| AlgHom.congr_fun (hφ₁.symm.trans hφ₂) x
  refine IntermediateField.exists_algHom_of_splits_of_aeval ?_ ?_
  · exact fun x => ⟨IsAlgebraic.isIntegral (hK_alg x), IsAlgClosed.splits_codomain (minpoly F x)⟩
  · rw [aeval_algHom_apply, _root_.map_eq_zero]
    convert minpoly.aeval F α
    letI : Algebra E K := (res φ₀).toAlgebra
    refine minpoly.algebraMap_eq ?_ α
    exact NoZeroSMulDivisors.algebraMap_injective E K
