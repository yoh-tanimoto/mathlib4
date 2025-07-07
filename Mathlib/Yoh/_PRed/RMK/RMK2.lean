import LeanCopilot
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Function.Support
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Topology.ContinuousFunction.CocompactMap
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousFunction.ZeroAtInfty
import Mathlib.Topology.Sets.Compacts
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Integral.Bochner

noncomputable section

open BoundedContinuousFunction NNReal ENNReal

open Set Function TopologicalSpace

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [NormalSpace X] [T2Space X]
variable (Λ : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) (hΛ : ∀ (f : X →ᵇ ℝ), 0 ≤ f → 0 ≤ Λ f)

lemma Λ_mono {f g : X →ᵇ ℝ} (h : f ≤ g) : Λ f ≤ Λ g := by
  have : 0 ≤ g - f := by exact sub_nonneg.mpr h
  calc Λ f ≤ Λ f + Λ (g - f) := by exact le_add_of_nonneg_right (hΛ (g - f) this)
  _ = Λ (f + (g - f)) := by rw [← LinearMap.map_add Λ f (g - f)]
  _ = Λ g := by simp only [add_sub_cancel]


-- /-! ### Construction of the content: -/

/-- Given a positive linear functional Λ on X, for `V ⊆ X` open define
-- `λ(K) = sup {Λf | 0 ≤ f ≤ 1 and supp f ⊆ V}`. -/
def rieszContentAux' : Opens X → ℝ≥0∞ := fun V =>
  sSup ((fun (x : ℝ) => ENNReal.ofReal x) ''
    (Λ '' ({ f : X →ᵇ ℝ | IsCompact (tsupport f.1) ∧ (tsupport f.1) ⊆ (V : Set X) ∧ ∀ x : X, 0 ≤ f.1 x ∧ f.1 x ≤ 1})))

section RieszMonotone

/-- For any pair of open subsets `V₁ ⊆ V₂`, it holds that Λ V₁ ≤ Λ V₂. -/
theorem rieszContentAux'_image_nonempty (V : Opens X) :
    ((fun (x : ℝ) => ENNReal.ofReal x) ''
    (Λ '' { f : X →ᵇ ℝ | IsCompact (tsupport f.1) ∧ (tsupport f.1) ⊆ V ∧ ∀ x : X, 0 ≤ f.1 x ∧ f.1 x ≤ 1})).Nonempty := by
  rw [image_nonempty, image_nonempty]
  use (0 : X →ᵇ ℝ)
  simp only [coe_to_continuous_fun, mem_setOf_eq, BoundedContinuousFunction.coe_zero, Pi.zero_apply,
    le_refl, zero_le_one, and_self, implies_true, and_true]
  unfold tsupport
  rw [Function.support_zero', closure_empty]
  constructor
  · simp only [isCompact_empty]
  · exact Set.empty_subset _
  done

/-- rieszContentAux' is monotone on open sets. -/
lemma rieszContentAux'_mono {V₁ V₂ : Opens X} (h : V₁ ≤ V₂) :
    rieszContentAux' Λ V₁ ≤ rieszContentAux' Λ V₂ := by
  apply sSup_le_sSup
  rw [← Set.image_comp, ← Set.image_comp]
  apply Set.image_subset
  intro f
  simp only [coe_to_continuous_fun, mem_setOf_eq, and_imp]
  intro hfcp hf hfx
  constructor
  · exact hfcp
  constructor
  · intro x hx
    exact (mem_of_subset_of_mem (fun ⦃a⦄ a_1 => h (hf a_1)) hx)
  · exact hfx
  done


/-- For any subset E of X, we define rieszContent' Λ E to be the inf of
riesContent' V such that E ⊆ V. -/
def rieszContent' : Set X → ℝ≥0∞ := fun E  =>
  sInf (rieszContentAux' Λ '' { V : Opens X | E ⊆ V })

/-- rieszContent' is monotone. -/
lemma rieszContent'_mono {E₁ E₂ : Set X} (h : E₁ ⊆ E₂) : rieszContent' Λ E₁ ≤ rieszContent' Λ E₂ := by
  apply sInf_le_sInf
  apply Set.image_subset
  intro V
  simp only [mem_setOf_eq]
  exact fun a ⦃a_1⦄ a_2 => a (h a_2)

/-- rieszContent' coincides with rieszContentAux' on open sets. -/
lemma rieszContent'_eq_rieszContentAux'_open (V : Opens X) :
    rieszContent' Λ V = rieszContentAux' Λ V := by
  apply le_antisymm
  apply sInf_le_of_le
  use V
  simp only [SetLike.coe_subset_coe, mem_setOf_eq, le_refl, true_and]
  rfl
  exact rieszContentAux'_mono Λ fun ⦃a⦄ a => a
  apply le_sInf
  intro x hx
  simp only [SetLike.coe_subset_coe, mem_image, mem_setOf_eq] at hx
  obtain ⟨V', hV'⟩ := hx
  rw [← hV'.2]
  exact rieszContentAux'_mono Λ hV'.1

def M_F (Λ : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) : Set (Set X) := {E : Set X | rieszContent' Λ E < ∞
  ∧ rieszContent' Λ E = sSup (rieszContent' Λ '' {K : Set X | IsCompact K ∧ K ⊆ E })}

def M (Λ : (X →ᵇ ℝ) →ₗ[ℝ] ℝ) : Set (Set X) :=
  {E : Set X | ∀ (K : Set X), IsCompact K → (E ∩ K) ∈ M_F Λ}

-- P.42 of Rudin "Real and Complex analysis"
-- Continue with "Proof that μ and M have the required properties"

lemma in_M_F_of_rieszContent'_zero {E : Set X} (h : rieszContent' Λ E = 0) : E ∈ M_F Λ := by
  constructor
  · rw [h]
    simp only [zero_lt_top]
  · apply le_antisymm
    rw [h]
    simp only [zero_le]
    apply sSup_le
    intro b hb
    obtain ⟨K, hK⟩ := hb
    rw [← hK.2]
    exact rieszContent'_mono Λ (Set.mem_setOf.mp hK.1).2

lemma in_M_of_rieszContent'_zero {E : Set X} (h : rieszContent' Λ E = 0) : E ∈ M Λ := by
  intro K _
  have : rieszContent' Λ (E ∩ K) = 0 := by
    apply le_antisymm
    rw [← h]
    exact rieszContent'_mono Λ (Set.inter_subset_left E K)
    exact zero_le (rieszContent' Λ (E ∩ K))
  constructor
  · rw [this]
    exact zero_lt_top
  · apply le_antisymm
    rw [this]
    exact zero_le (sSup (rieszContent' Λ '' {K_1 | IsCompact K_1 ∧ K_1 ⊆ E ∩ K}))
    apply sSup_le
    intro x hx
    obtain ⟨E', hE'⟩ := hx
    rw [← hE'.2]
    exact rieszContent'_mono Λ hE'.1.2


-- to mathlib UrysohnsLemma?

open BigOperators

lemma exists_tsupport_one_of_isOpen_isClosed [NormalSpace X] {s t : Set X}
    (hs : IsOpen s) (ht : IsClosed t) (hst : t ⊆ s) : ∃ f : C(X, ℝ), tsupport f ⊆ s ∧ EqOn f 1 t
    ∧ ∀ x, f x ∈ Icc (0 : ℝ) 1 := by
    obtain ⟨U, V, hUV⟩ := normal_separation (IsOpen.isClosed_compl hs) ht
      (HasSubset.Subset.disjoint_compl_left hst)
    have : Disjoint (closure U) t := by
      apply le_compl_iff_disjoint_right.mp
      apply _root_.subset_trans _ (Set.compl_subset_compl.mpr hUV.2.2.2.1)
      apply (IsClosed.closure_subset_iff (IsOpen.isClosed_compl hUV.2.1)).mpr
      exact Set.subset_compl_iff_disjoint_right.mpr hUV.2.2.2.2
    obtain ⟨f, hf⟩ := exists_continuous_zero_one_of_isClosed isClosed_closure ht this
    use f
    constructor
    · apply _root_.subset_trans _ (Set.compl_subset_comm.mp hUV.2.2.1)
      rw [← IsClosed.closure_eq (IsOpen.isClosed_compl hUV.1)]
      apply closure_mono
      rw [Set.subset_compl_iff_disjoint_left, Function.disjoint_support_iff]
      exact Set.EqOn.mono subset_closure hf.1
    · exact hf.2

open Classical

lemma exists_forall_tsupport_iUnion_one_iUnion_of_isOpen_isClosed [NormalSpace X] [T2Space X]
    [LocallyCompactSpace X] {n : ℕ} {t : Set X} {s : Fin n → Set X}
    (hs : ∀ (i : Fin n), IsOpen (s i))
    (ht : IsClosed t) (htcp : IsCompact t) (hst : t ⊆ ⋃ i, s i) :
    ∃ f : Fin n → C(X, ℝ), (∀ (i : Fin n), tsupport (f i) ⊆ s i) ∧ EqOn (∑ i, f i) 1 t
    ∧ ∀ (i : Fin n), ∀ (x : X), f i x ∈ Icc (0 : ℝ) 1 := by
  sorry

/-- The Riesz content μ associated to a given positive linear functional Λ is
finitely subadditive for open sets : `μ (V₁ ∪ V₂) ≤ μ(V₁) + μ(V₂)`. -/
lemma rieszContentAux'_sup_le (V₁ V₂ : Opens X) :
    rieszContentAux' Λ (V₁ ⊔ V₂) ≤ rieszContentAux' Λ V₁ + rieszContentAux' Λ V₂ := by
  apply sSup_le
  set V : Fin 2 → Opens X := fun i => if i = 0 then V₁ else V₂ with hV
  have isOpenV : ∀ (i : Fin 2), IsOpen (V i).carrier := by
    intro i
    by_cases hi : i = 0
    · rw [hV]
      simp only [Fin.isValue, Opens.carrier_eq_coe]
      rw [if_pos hi]
      exact V₁.2
    · rw [hV]
      simp only [Fin.isValue, Opens.carrier_eq_coe]
      rw [if_neg hi]
      exact V₂.2
  have hUnion : V₁.carrier ∪ V₂.carrier = ⋃ i, (V i).carrier := by
    ext x
    constructor
    · intro hx
      rcases hx with h1 | h2
      sorry
      sorry
    · sorry
  intro a ha
  obtain ⟨b, hb⟩ := ha
  obtain ⟨g, hg⟩ := hb.1
  simp only [coe_to_continuous_fun, Opens.coe_sup, mem_setOf_eq] at hg
  have : (V₁ : Set X) ∪ (V₂ : Set X) = V₁.carrier ∪ V₂.carrier := by
    simp only [Opens.carrier_eq_coe]
  rw [this, hUnion] at hg -- coersion is different from .carrier
  obtain ⟨f, hf⟩ := exists_forall_tsupport_iUnion_one_iUnion_of_isOpen_isClosed isOpenV
    (isClosed_tsupport g) hg.1.1 hg.1.2.1
  sorry




-- to mathlib NEEReal??

lemma sInf_diff_singleton_eq_sInf {s : Set ENNReal} {b : ENNReal} (h : ∃ (a : ENNReal), a ∈ s ∧ a < b)
    : sInf (s \ {b}) = sInf s := by
  apply le_antisymm
  apply sInf_le_sInf_of_forall_exists_le
  intro x hxins
  obtain ⟨a, ha⟩ := h
  by_cases hx : x = b
  · use a
    constructor
    · constructor
      · exact ha.1
      · simp only [mem_singleton_iff]
        exact ne_of_lt ha.2
    · rw [hx]
      exact le_of_lt ha.2
  · use x
    constructor
    · constructor
      exact hxins
      simp only [mem_singleton_iff]
      exact hx
    · exact Preorder.le_refl x
  exact sInf_le_sInf (Set.diff_subset _ _)

lemma ENNReal.toNNReal_sInf' {s : Set ℝ≥0∞} (hs : ∃ (r : ℝ≥0∞), r ∈ s ∧ r ≠ ⊤) :
    (sInf s).toNNReal = sInf (ENNReal.toNNReal '' (s \ {⊤})) := by
  rw [← ENNReal.toNNReal_sInf]
  have : sInf (s \ ({⊤} : Set ℝ≥0∞)) = sInf s := by
    apply sInf_diff_singleton_eq_sInf
    obtain ⟨r, hr⟩ := hs
    use r
    constructor
    · exact hr.1
    · exact Ne.lt_top hr.2
  rw [← this]
  intro x hx
  exact (Set.mem_diff_singleton.mp hx).right

lemma toReal_eq_toReal_toNNReal (x : ℝ≥0∞) : x.toReal = (x.toNNReal).toReal := by
  exact rfl

lemma NNReal.bddBelow (s : Set ℝ≥0) : BddBelow s := by
  exact OrderBot.bddBelow s

lemma toReal_sInf_eq_sInf_toReal {s : Set ℝ≥0} (hs : Set.Nonempty s) :
    (sInf s).toReal = sInf (toReal '' s) := by
  apply le_antisymm
  have : ∀ (b : ℝ), b ∈ (toReal '' s) → (sInf s).toReal ≤ b := by
    intro b hb
    obtain ⟨a, ha⟩ := hb
    rw [← ha.2]
    simp only [NNReal.coe_le_coe]
    apply csInf_le (OrderBot.bddBelow s) ha.1
  exact le_csInf (Set.image_nonempty.mpr hs) this
  rw [(csInf_le_iff (NNReal.bddBelow_coe s) (Set.image_nonempty.mpr hs))]
  intro b hb
  rw [mem_lowerBounds] at hb
  by_cases hbnonneg : 0 ≤ b
  rw [(Real.coe_toNNReal b hbnonneg).symm, NNReal.coe_le_coe]
  apply le_csInf hs
  intro b1 hb1
  exact Real.toNNReal_le_iff_le_coe.mpr (hb b1.toReal (Set.mem_image_of_mem toReal hb1))
  push_neg at hbnonneg
  exact le_of_lt (lt_of_lt_of_le hbnonneg zero_le_coe)

lemma toReal_sInf_eq_sInf_toReal' {s : Set ℝ≥0∞} (hs : ∃ (r : ℝ≥0∞), r ∈ s ∧ r ≠ ⊤) :
    (sInf (s \ {⊤})).toReal = sInf (ENNReal.toReal '' (s \ {⊤})) := by
  obtain ⟨r, hr⟩ := hs
  apply le_antisymm
  have hble : ∀ (b : ℝ), b ∈ (ENNReal.toReal '' (s \ {⊤})) → (sInf (s \ {⊤})).toReal ≤ b := by
    intro b hb
    obtain ⟨a, ha⟩ := hb
    rw [← ha.2, ENNReal.toReal_le_toReal]
    exact sInf_le ha.1
    simp only [sInf_diff_singleton_top, ne_eq, sInf_eq_top, not_forall, exists_prop]
    use r
    exact (Set.mem_diff_singleton.mp ha.1).2
  apply (le_csInf_iff _ _).mpr hble
  use 0
  intro x hx
  obtain ⟨y, hy⟩ := hx
  rw [← hy.2]
  exact ENNReal.toReal_nonneg
  use r.toReal
  exact mem_image_of_mem ENNReal.toReal hr
  apply (csInf_le_iff _ _).mpr
  intro b hb
  rw [@mem_lowerBounds] at hb
  by_cases hbnonneg : 0 ≤ b
  rw [← ENNReal.toReal_ofReal hbnonneg, ENNReal.toReal_le_toReal]
  apply (le_csInf_iff _ _).mpr
  intro y hy
  rw [← ENNReal.ofReal_toReal_eq_iff.mpr (Set.mem_diff_singleton.mp hy).2]
  simp only [toReal_nonneg, ofReal_le_ofReal_iff]
  exact (hb y.toReal) (Set.mem_image_of_mem ENNReal.toReal hy)
  exact OrderBot.bddBelow (s \ {⊤})
  exact nonempty_of_mem hr
  exact ofReal_ne_top
  simp only [sInf_diff_singleton_top, ne_eq, sInf_eq_top, not_forall, exists_prop]
  use r
  push_neg at hbnonneg
  exact le_of_lt (lt_of_lt_of_le hbnonneg zero_le_coe)
  use 0
  intro x hx
  obtain ⟨y, hy⟩ := hx
  rw [← hy.2]
  exact ENNReal.toReal_nonneg
  use r.toReal
  exact mem_image_of_mem ENNReal.toReal hr

lemma ex_in_add_pos_lt {s : Set ℝ≥0∞} (hsinf : sInf s < ⊤) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ (a : ℝ≥0), ENNReal.ofNNReal a ∈ s ∧ a < ENNReal.toNNReal (sInf s) + ε := by
  have : ∃ (x : ℝ≥0∞), x ∈ s ∧ x ≠ ⊤ := by
    by_contra! h
    have : ⊤ ≤ sInf s := by
      apply le_sInf
      intro x hx
      exact eq_top_iff.mp (h x hx)
    exact LT.lt.false (lt_of_le_of_lt this hsinf)
  have : Set.Nonempty (ENNReal.toReal '' (s \ {⊤})) := by
    simp only [image_nonempty]
    obtain ⟨x, hx⟩ := this
    use x
    constructor
    · exact hx.1
    · exact not_mem_of_mem_diff hx
  obtain ⟨a, ha⟩ := Real.lt_sInf_add_pos this hε
  obtain ⟨b, hb⟩ := ha.1
  use b.toNNReal
  have hbnottop : b ≠ ⊤ := by
    exact (Set.mem_diff_singleton.mpr hb.1).2
  constructor
  · rw [ENNReal.coe_toNNReal (Set.mem_diff_singleton.mpr hb.1).2]
    exact ((Set.mem_diff b).mp hb.1).1
  · have : ∃ (r : ℝ≥0∞), r ∈ s ∧ r ≠ ⊤ := by
      use b
      constructor
      · exact ((Set.mem_diff b).mp hb.1).1
      · exact hbnottop
    rw [ENNReal.toNNReal_sInf' this, ← NNReal.coe_lt_coe]
    rw [← toReal_eq_toReal_toNNReal b, hb.2]
    simp
    rw [← ENNReal.toNNReal_sInf' this, ← toReal_eq_toReal_toNNReal (sInf s)]
    rw [← sInf_diff_singleton_eq_sInf (sInf_lt_iff.mp hsinf), toReal_sInf_eq_sInf_toReal']
    exact ha.2
    use b
    constructor
    · exact ((Set.mem_diff b).mp hb.1).1
    · exact hbnottop

lemma ex_in_add_pos_lt' {s : Set ℝ≥0∞} (hsinf : sInf s < ⊤) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ (a : ℝ≥0), ENNReal.ofNNReal a ∈ s ∧ ENNReal.ofNNReal a < (sInf s) + ε := by
  obtain ⟨a, ha⟩ := ex_in_add_pos_lt hsinf ε hε
  use a
  have : sInf s ≠ ⊤ := by
    exact LT.lt.ne_top hsinf
  constructor
  · exact ha.1
  · rw [← ENNReal.coe_toNNReal this]
    rw [← ENNReal.coe_add, ENNReal.coe_lt_coe]
    exact ha.2



/-- The Riesz content can be approximated arbitrarily well from outside by open sets. -/
lemma exists_lt_rieszContent'_add_pos {E : Set X} {ε : ℝ≥0} (εpos : 0 < ε) :
    ∃ (V : Opens X), E ⊆ (V : Set X) ∧ rieszContent' Λ V ≤ rieszContent' Λ E + ε := by
  by_cases hinf : rieszContent' Λ E = ∞
  · use ⊤
    constructor
    exact le_top
    rw [hinf]
    exact sup_eq_left.mp rfl
  · obtain ⟨b, hb⟩ := ex_in_add_pos_lt' (Ne.lt_top hinf) ε εpos
    obtain ⟨V, hV⟩ := hb.1
    use V
    constructor
    exact Set.mem_setOf.mp hV.1
    rw [rieszContent'_eq_rieszContentAux'_open Λ V, hV.2]
    apply le_of_lt
    exact hb.2



open ZeroAtInfty

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
 [T2Space X] [MeasurableSpace X] [BorelSpace X]


theorem RMK (Λ : C₀(X, ℂ) → ℂ) : Continuous Λ ∧ (∀ (f : C₀(X, ℂ)) (x : X), ((f x).re ≥ 0 ∧ (f x).im = 0) → ((Λ f).re ≥ 0 ∧ (Λ f).im = 0)) →
 ∃ (μ : MeasureTheory.Measure X), (∀ (f : C₀(X, ℂ)), ∫ (x : X), f x ∂μ = Λ f) := by
 sorry
