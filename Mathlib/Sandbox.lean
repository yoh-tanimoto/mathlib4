import Mathlib.NumberTheory.NumberField.Discriminant
import Mathlib.RingTheory.Discriminant

section discr

variable (K : Type*) {L₁ L₂ E : Type*} (E : Type*) [Field K] [Field L₁] [Field L₂] [Field E]
  [Algebra K L₁] [Algebra K L₂] [Algebra K E] [Module.Finite K L₁] [IsAlgClosed E]
  [IsSeparable K L₁]

theorem Algebra.discr_eq_discr_of_algEquiv {ι : Type*} [DecidableEq ι] [Fintype ι] (b : ι → L₁)
    (e : ι ≃ (L₁ →ₐ[K] E)) (f : L₁ ≃ₐ[K] L₂) : Algebra.discr K b = Algebra.discr K (f ∘ b) := by
  have : Module.Finite K L₂ := Module.Finite.equiv f.toLinearEquiv
  have : IsSeparable K L₂ := IsSeparable.of_algHom K L₁ f.symm
  apply (NoZeroSMulDivisors.algebraMap_injective K E)
  let s : (L₁ →ₐ[K] E) ≃ (L₂ →ₐ[K] E) := f.arrowCongr AlgEquiv.refl
  let e' : ι ≃ (L₂ →ₐ[K] E) := e.trans s
  rw [Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two _ _ _ e,
    Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two _ _ _ e']
  congr
  ext
  simp [Algebra.embeddingsMatrixReindex]

end discr

section integral_closure

variable {R A S : Type*} [CommRing R] [CommRing A] [CommRing S] [Algebra R A] [Algebra R S]

def integralClosure_algHom_restrict (f : A →ₐ[R] S) :
    integralClosure R A →ₐ[R] integralClosure R S :=
  (f.restrictDomain (integralClosure R A)).codRestrict (integralClosure R S) (fun ⟨_, h⟩ => h.map f)

@[simp]
theorem integralClosure_coe_algHom_restrict (f : A →ₐ[R] S) (x : integralClosure R A) :
    (integralClosure_algHom_restrict f x : S) = f (x : A) := rfl

noncomputable def integralClosure_algEquiv_restrict (f : A ≃ₐ[R] S) :
    integralClosure R A ≃ₐ[R] integralClosure R S := by
  refine AlgEquiv.ofBijective (integralClosure_algHom_restrict f) ⟨?_, ?_⟩
  · erw [AlgHom.injective_codRestrict]
    exact (EquivLike.injective f).comp Subtype.val_injective
  · rintro ⟨y, hy⟩
    exact ⟨⟨f.symm y, hy.map f.symm⟩, by rw [Subtype.mk_eq_mk]; simp⟩

@[simp]
theorem integralClosure_coe_algEquiv_restrict (f : A ≃ₐ[R] S) (x : integralClosure R A) :
    (integralClosure_algEquiv_restrict f x : S) = f (x : A) := rfl

end integral_closure

section integral_basis

open NumberField nonZeroDivisors

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] (f : K ≃ₐ[ℚ] L)

theorem discr_eq_discr_of_algEquiv : discr K = discr L := by
  let f₀ : 𝓞 K ≃ₗ[ℤ] 𝓞 L := (integralClosure_algEquiv_restrict (f.restrictScalars ℤ)).toLinearEquiv
  let e : Module.Free.ChooseBasisIndex ℤ (𝓞 K) ≃ (K →ₐ[ℚ] ℂ) := by
    refine Fintype.equivOfCardEq ?_
    rw [← FiniteDimensional.finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank, AlgHom.card]
  rw [← Rat.intCast_inj, coe_discr, Algebra.discr_eq_discr_of_algEquiv ℚ ℂ (integralBasis K) e f,
    ← discr_eq_discr _ ((RingOfIntegers.basis K).map f₀)]
  change _ = algebraMap ℤ ℚ _
  rw [← Algebra.discr_localizationLocalization ℤ ℤ⁰ L]
  congr
  ext
  simp only [Function.comp_apply, integralBasis_apply, Basis.localizationLocalization_apply,
    Basis.map_apply]
  rfl

end integral_basis
