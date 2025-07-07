import Mathlib

open Complex

variable  (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
-- `E` is a complex Hilbert space
(θ : E →ₗ[ℝ] E) -- `θ` is a real linear map on `E`
(hθinv : θ ∘ θ = id) -- `θ` is an involution
(hθal : ∀ (α : ℂ), ∀ (v : E), θ (α • v) = conjCLE α • (θ v)) -- `θ` is antilinear
(hθau : ∀ (v w : E), ⟪v, θ w⟫_ℂ = ⟪w, θ v⟫_ℂ) -- `θ^* = θ`
(Eₚ : Subspace ℂ E) (hEₚ: IsClosed Eₚ) -- `Eₚ` is a closed complex subspace of `E`
(hRP : ∀ (v : E), v ∈ Eₚ → 0 ≤ (⟪v, θ v⟫_ℂ).re) -- reflection positive

-- todo: show that the completion of Eₚ with respect to `⟪v, θ v⟫_ℂ` is `InnerProductSpace`
-- cf. Mathlib.Analysis.NormedSpace.Completion
