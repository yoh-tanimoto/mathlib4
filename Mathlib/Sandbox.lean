import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.FieldTheory.Adjoin

open FiniteDimensional IntermediateField Polynomial Algebra Set

variable (F : Type*) {E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem Field.primitive_element_of_minpoly_natDegree_eq (α : E) :
    F⟮α⟯ = ⊤ ↔ (minpoly F α).natDegree = finrank F E := by
  rw [← adjoin.finrank (IsIntegral.of_finite F α), ← finrank_top F E]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact congr_arg (fun K : IntermediateField F E => finrank F K) h
  · exact eq_of_le_of_finrank_eq le_top h

theorem Field.primitive_element_of_minpoly_degree_eq (α : E) :
    F⟮α⟯ = ⊤ ↔ (minpoly F α).degree = finrank F E := by
  rw [degree_eq_iff_natDegree_eq, primitive_element_of_minpoly_natDegree_eq]
  exact minpoly.ne_zero_of_finite F α

variable [IsSeparable F E] (A : Type*) [Field A] [IsAlgClosed A] [Algebra F A]

theorem Field.primitive_element_of_algHom_eval_pairwise_ne (α : E) :
    F⟮α⟯ = ⊤ ↔ ∀ φ ψ : E →ₐ[F] A, φ ≠ ψ → φ α ≠ ψ α := by
  classical
  simp_rw [primitive_element_of_minpoly_natDegree_eq, ← card_rootSet_eq_natDegree (K := A)
    (IsSeparable.separable F α) (IsAlgClosed.splits_codomain (minpoly F α)), ← toFinset_card,
    ← IsAlgebraic.range_eval_eq_rootSet_minpoly A (Algebra.IsAlgebraic.of_finite F E) α,
    ← AlgHom.card F E A, not_imp_not, Fintype.card, toFinset_range, Finset.card_image_iff,
    Finset.coe_univ, ← injective_iff_injOn_univ, Function.Injective]

theorem Field.primitive_element_of_algHom_eval_ne (α : E) (φ : E →ₐ[F] A) :
    F⟮α⟯ = ⊤ ↔ ∀ ψ : E →ₐ[F] A, φ ≠ ψ → φ α ≠ ψ α := by
  rw [Field.primitive_element_of_algHom_eval_pairwise_ne F A]
  refine ⟨fun h ψ =>  h φ ψ, fun h φ₀ ψ₀ => ?_⟩
  let K := IntermediateField.adjoin F (⋃ ν : E →ₐ[F] A, Set.range ν)
  have hK_mem : ∀ (ψ : E →ₐ[F] A) (x : E), ψ x ∈ K := fun ψ x =>
    Subfield.subset_closure (mem_union_right _ (mem_iUnion.mpr ⟨ψ, mem_range_self x⟩))
  let res : (E →ₐ[F] A) → (E →ₐ[F] K) := fun ψ => AlgHom.codRestrict ψ K.toSubalgebra (hK_mem ψ)
  rsuffices ⟨σ, hσ⟩ : ∃ σ : K →ₐ[F] A, σ (⟨φ₀ α, hK_mem _ _⟩) = φ α
  · contrapose!
    intro h'
    suffices res φ₀ = res ψ₀ by
      ext x
      exact Subtype.mk_eq_mk.mp (AlgHom.congr_fun this x)
    have eq₁ : φ = AlgHom.comp σ (res φ₀) := not_imp_not.mp (h (AlgHom.comp σ (res φ₀))) hσ.symm
    have eq₂ : φ = AlgHom.comp σ (res ψ₀) := by
      refine not_imp_not.mp (h (AlgHom.comp σ (res ψ₀))) ?_
      simp_rw [← hσ, h']
      rfl
    ext1 x
    exact (RingHom.injective σ.toRingHom) <| AlgHom.congr_fun (eq₁.symm.trans eq₂) x
  refine IntermediateField.exists_algHom_of_splits_of_aeval ?_ ?_
  · refine fun x => ⟨IsAlgebraic.isIntegral ?_, IsAlgClosed.splits_codomain (minpoly F x)⟩
    refine (isAlgebraic_adjoin fun a ha => IsAlgebraic.isIntegral ?_) x
    obtain ⟨ψ, x, rfl⟩ := Set.mem_iUnion.mp ha
    exact (IsAlgebraic.of_finite F x).algHom ψ
  · rw [aeval_algHom_apply, _root_.map_eq_zero]
    convert minpoly.aeval F α
    letI : Algebra E K := (res φ₀).toAlgebra
    refine minpoly.algebraMap_eq ?_ α
    exact NoZeroSMulDivisors.algebraMap_injective E K
