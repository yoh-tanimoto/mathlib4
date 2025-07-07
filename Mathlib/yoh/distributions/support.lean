import Mathlib

abbrev R2 : Type := EuclideanSpace ℝ (Fin 2)

open Set TopologicalSpace Classical Function

namespace Distribution

abbrev SchwartzDist : Type := SchwartzMap R2 ℝ →L[ℝ] ℝ

variable (ϕ : SchwartzDist)
#check ϕ
-- ϕ is a distribution

/-- For a Schwartz distribution `ϕ`, we say that a set `X` is an open annihilation set
if `X` is open and `ϕ f = 0` for any test function `f` with `tsupport f ⊆ X`. -/
def IsOpenAnnihilationSet : SchwartzDist → (Set R2) → Prop :=
  fun ϕ X => if IsOpen X ∧ ∀ (f : SchwartzMap R2 ℝ), tsupport f ⊆ X → ϕ f = 0 then true else false

lemma isOpenAnnihilationSet_iff_zero {ϕ : SchwartzDist} {X : Set R2} (hX : IsOpen X) :
    IsOpenAnnihilationSet ϕ X ↔ ∀ (f : SchwartzMap R2 ℝ), tsupport f ⊆ X → ϕ f = 0 := by
  constructor
  · intro h f hf
    rw [IsOpenAnnihilationSet] at h
    simp only [ite_eq_left_iff, not_and, not_forall, exists_prop, imp_false, not_exists, not_not]
      at h
    exact h.2 f hf
  · intro h
    rw [IsOpenAnnihilationSet]
    simp only [ite_eq_left_iff, not_and, not_forall, exists_prop, imp_false, not_exists, not_not]
    exact ⟨hX, h⟩
  done

/-- If `X` is an open annihilation set, then it is open. -/
lemma isOpenAnnihilationSet (X : Set R2) : (IsOpenAnnihilationSet ϕ X) → IsOpen X := by
  rw [IsOpenAnnihilationSet]
  intro h
  simp only [ite_eq_left_iff, not_and, not_forall, exists_prop, imp_false] at h
  exact h.1

/-- The (topological) support of a distribution `ϕ` is the complement of the union of all open
annihilation sets. -/
def tsupport : SchwartzDist → Set R2 :=
  fun ϕ => (⋃₀ IsOpenAnnihilationSet ϕ)ᶜ

/-- The support of a distribution `ϕ' is closed. -/
lemma isClosed_tsupport {ϕ : SchwartzDist} : IsClosed (tsupport ϕ) := by
  rw [tsupport, isClosed_compl_iff]
  apply isOpen_sUnion
  exact fun t a => isOpenAnnihilationSet ϕ t a

lemma isOpenAnnihilationSet_compl_tsupport {ϕ : SchwartzDist} :
    IsOpenAnnihilationSet ϕ (tsupport ϕ)ᶜ  := by
  rw [IsOpenAnnihilationSet]
  simp only [isOpen_compl_iff, ite_eq_left_iff, not_and, not_forall, exists_prop, imp_false,
    not_exists, not_not]
  constructor
  · exact isClosed_tsupport
  · intro f hf
    sorry
-- need that f can be written as a sum of test functions
-- supported in open annihilation sets.
-- need LocallyCompactSpace for the vector space?

theorem eq_zero_of_disjoint_tsupport_tsupport {ϕ : SchwartzDist} {f : SchwartzMap R2 ℝ} :
    Disjoint (tsupport ϕ) (_root_.tsupport f) → ϕ f = 0 := by
  intro h
  rw [← Set.subset_compl_iff_disjoint_left] at h
  apply (isOpenAnnihilationSet_iff_zero (isOpen_compl_iff.mpr isClosed_tsupport)).mp
  exact isOpenAnnihilationSet_compl_tsupport
  exact h
  done

-- theorem Function.mem_support x ∈ Function.support f ↔ f x ≠ 0
-- theorem Function.support_subset_iff Function.support f ⊆ s ↔ ∀ (x : α), f x ≠ 0 → x ∈ s
-- theorem tsupport_eq_empty_iff
-- thelrem if Disjoint (tsupport ϕ) (tsupport f) then ϕ f = 0

-- theorem tsupport_add, smul
