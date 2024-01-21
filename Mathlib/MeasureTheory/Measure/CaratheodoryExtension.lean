import Mathlib.Data.Finite.Card
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.AddContent
import Mathlib.MeasureTheory.Measure.Trim

open Finset Set MeasureTheory Order

open scoped Classical BigOperators NNReal Topology ENNReal MeasureTheory

namespace MeasureTheory

variable {α : Type _} {C : Set (Set α)} {s : Set α}

lemma OuterMeasure.isCaratheodory_partialSups {m : OuterMeasure α} {s : ℕ → Set α}
    (h : ∀ i, m.IsCaratheodory (s i)) (i : ℕ) :
    m.IsCaratheodory (partialSups s i) := by
  induction' i with i hi
  · rw [partialSups_zero]; exact h 0
  rw [partialSups_succ]
  exact m.isCaratheodory_union hi (h (i + 1))

lemma OuterMeasure.isCaratheodory_disjointed {m : OuterMeasure α} {s : ℕ → Set α}
    (h : ∀ i, m.IsCaratheodory (s i)) (i : ℕ) :
    m.IsCaratheodory (disjointed s i) := by
  induction' i with i _
  · rw [disjointed_zero]; exact h 0
  rw [disjointed_succ, diff_eq]
  refine m.isCaratheodory_inter (h (i + 1)) (m.isCaratheodory_compl ?_)
  exact isCaratheodory_partialSups h i

lemma OuterMeasure.isCaratheodory_iUnion {m : OuterMeasure α} {s : ℕ → Set α}
    (h : ∀ i, m.IsCaratheodory (s i)) :
    m.IsCaratheodory (⋃ i, s i) := by
  rw [← iUnion_disjointed]
  exact OuterMeasure.isCaratheodory_iUnion_nat m (isCaratheodory_disjointed h)
    (disjoint_disjointed _)

/-- Same as the definition of `OuterMeasure.ofFunction`, except that the sets in the infimum
belong to `C`. -/
lemma OuterMeasure.ofFunction_eq_iInf_mem (m : Set α → ℝ≥0∞) (m_empty : m ∅ = 0)
    (m_top : ∀ s ∉ C, m s = ∞) (s : Set α) :
    OuterMeasure.ofFunction m m_empty s =
      ⨅ (f : ℕ → Set α) (_ : ∀ i, f i ∈ C) (_ : s ⊆ ⋃ i, f i), ∑' i, m (f i) := by
  rw [OuterMeasure.ofFunction_apply]
  apply le_antisymm
  · refine le_iInf fun f ↦ le_iInf fun _ ↦ le_iInf fun h ↦ iInf₂_le _ ?_
    exact h
  · simp_rw [le_iInf_iff]
    refine fun f hf_subset ↦ iInf_le_of_le f ?_
    by_cases hf : ∀ i, f i ∈ C
    · exact iInf_le_of_le hf (iInf_le_of_le hf_subset le_rfl)
    · simp only [hf, not_false_eq_true, iInf_neg, top_le_iff]
      push_neg at hf
      obtain ⟨i, hfi_not_mem⟩ := hf
      exact ENNReal.tsum_eq_top_of_eq_top ⟨i, m_top _ hfi_not_mem⟩

lemma inducedOuterMeasure_eq_iInf_mem (hC : ∅ ∈ C) (m : ∀ s : Set α, s ∈ C → ℝ≥0∞)
    (m_empty : m ∅ hC = 0) (s : Set α) :
    inducedOuterMeasure m hC m_empty s =
      ⨅ (f : ℕ → Set α) (hf : ∀ i, f i ∈ C) (_ : s ⊆ ⋃ i, f i), ∑' i, m (f i) (hf i) := by
  rw [inducedOuterMeasure,
    OuterMeasure.ofFunction_eq_iInf_mem (extend m) _ fun s ↦ extend_eq_top m]
  simp_rw [← extend_eq m]

lemma OuterMeasure.ofFunction_eq_of_mono_of_subadditive (hC : IsPiSystem C) (hC_empty : ∅ ∈ C)
    (m : Set α → ℝ≥0∞) (m_empty : m ∅ = 0)
    (m_mono : ∀ ⦃s t : Set α⦄ (_hs : s ∈ C) (_ht : t ∈ C), s ⊆ t → m s ≤ m t)
    (m_iUnion_le : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : ⋃ i, f i ∈ C),
        m (⋃ i, f i) ≤ ∑' i, m (f i))
    (m_top : ∀ s ∉ C, m s = ∞) (hs : s ∈ C) :
    OuterMeasure.ofFunction m m_empty s = m s := by
  refine le_antisymm (OuterMeasure.ofFunction_le s) ?_
  rw [ofFunction_eq_iInf_mem m m_empty m_top]
  refine le_iInf fun f ↦ le_iInf fun hf ↦ le_iInf fun hs_subset ↦ ?_
  have h_mem : ∀ i, s ∩ f i ∈ C := by
    intro i
    by_cases h_empty : s ∩ f i = ∅
    · rwa [h_empty]
    · refine hC s hs (f i) (hf i) ?_
      rwa [Set.nonempty_iff_ne_empty]
  calc
    m s = m (s ∩ ⋃ i, f i) := by rw [inter_eq_self_of_subset_left hs_subset]
    _ = m (⋃ i, s ∩ f i) := by rw [inter_iUnion]
    _ ≤ ∑' i, m (s ∩ f i) := by
      refine m_iUnion_le h_mem ?_
      rwa [← inter_iUnion, inter_eq_self_of_subset_left hs_subset]
    _ ≤ ∑' i, m (f i) := by
      refine tsum_le_tsum (fun i ↦ ?_) ENNReal.summable ENNReal.summable
      refine m_mono (h_mem i) (hf i) (Set.inter_subset_right _ _)

lemma OuterMeasure.ofFunction_addContent_eq (hC : IsSetSemiring C) (m : AddContent C)
    (m_iUnion_le : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : ⋃ i, f i ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i))
    (m_top : ∀ s ∉ C, m s = ∞) (hs : s ∈ C) :
    OuterMeasure.ofFunction m addContent_empty s = m s :=
  OuterMeasure.ofFunction_eq_of_mono_of_subadditive hC.isPiSystem hC.empty_mem m addContent_empty
    (fun _ _ ↦ addContent_mono hC) m_iUnion_le m_top hs

lemma OuterMeasure.ofFunction_extend_addContent_eq (hC : IsSetSemiring C) (m : AddContent C)
    (m_iUnion_le : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : ⋃ i, f i ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i)) (hs : s ∈ C) :
    OuterMeasure.ofFunction (extend (fun s _ ↦ m s))
      (extend_empty hC.empty_mem addContent_empty) s = m s := by
  refine (OuterMeasure.ofFunction_eq_of_mono_of_subadditive hC.isPiSystem hC.empty_mem _
    ?_ ?_ ?_ ?_ hs).trans ?_
  · intro s t hs ht hst
    rw [extend_eq (fun s _ ↦ m s) hs, extend_eq (fun s _ ↦ m s) ht]
    exact addContent_mono hC hs ht hst
  · intro f hf hf_Union
    rw [extend_eq (fun s _ ↦ m s) hf_Union]
    refine (m_iUnion_le hf hf_Union).trans_eq ?_
    congr with i
    rw [extend_eq (fun s _ ↦ m s) (hf i)]
  · exact fun s hs ↦ extend_eq_top _ hs
  · rw [extend_eq (fun s _ ↦ m s) hs]

lemma inducedOuterMeasure_addContent_eq_of_subadditive (hC : IsSetSemiring C) (m : AddContent C)
    (m_iUnion_le : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : ⋃ i, f i ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i))
    (hs : s ∈ C) :
    inducedOuterMeasure (fun s _ ↦ m s) hC.empty_mem addContent_empty s = m s := by
  rw [inducedOuterMeasure, OuterMeasure.ofFunction_extend_addContent_eq hC _ m_iUnion_le hs]

def equivRangeFin (n : ℕ) : Finset.range n ≃ Fin n  where
  toFun := fun j ↦ ⟨j, Finset.mem_range.mp j.2⟩
  invFun := fun j ↦ ⟨j, Finset.mem_range.mpr j.2⟩
  left_inv := fun j ↦ by simp only [Subtype.coe_mk, Fin.eta]
  right_inv := fun j ↦ by simp only [Fin.val_mk, Subtype.coe_eta]

lemma isCaratheodory_ofFunction_addContent_of_mem (hC : IsSetSemiring C) (m : AddContent C)
    (m_top : ∀ s ∉ C, m s = ∞) (hs : s ∈ C) :
    (OuterMeasure.ofFunction m addContent_empty).IsCaratheodory s := by
  rw [OuterMeasure.isCaratheodory_iff_le']
  intro t
  conv_rhs => rw [OuterMeasure.ofFunction_eq_iInf_mem _ addContent_empty m_top]
  refine le_iInf fun f ↦ le_iInf fun hf ↦ le_iInf fun hf_subset ↦ ?_
  -- ⊢ OuterMeasure.ofFunction m _ (t ∩ s) + OuterMeasure.ofFunction m _ (t \ s) ≤ ∑' i, m (f i)
  let A : ℕ → Finset (Set α) := fun i ↦ hC.diffFinset (hf i) (hC.inter_mem _ (hf i) _ hs)
  have h_diff_eq_sUnion : ∀ i, f i \ s = ⋃₀ A i := by
    intro i
    simp only
    rw [IsSetSemiring.sUnion_diffFinset, Set.inter_comm, diff_inter_self_eq_diff]
  have h_m_eq : ∀ i, m (f i) = m (f i ∩ s) + ∑ u in A i, m u := by
    intro i
    rw [addContent_eq_add_diffFinset_of_subset hC (hf i) (hC.inter_mem _ (hf i) _ hs)
        (inter_subset_left _ _)]
  simp_rw [h_m_eq]
  rw [tsum_add ENNReal.summable ENNReal.summable]
  refine add_le_add ?_ ?_
  · -- ⊢ OuterMeasure.ofFunction m _ (t ∩ s) ≤ ∑' i, m (f i ∩ s)
    refine iInf_le_of_le (fun i ↦ f i ∩ s) (iInf_le_of_le ?_ le_rfl)
    rw [← iUnion_inter]
    exact Set.inter_subset_inter_left _ hf_subset
  · -- ⊢ OuterMeasure.ofFunction m _ (t \ s) ≤ ∑' i, ∑ u in A i, m u
    let e : ℕ ≃ ℕ × ℕ := (Denumerable.eqv (ℕ × ℕ)).symm
    let g' : ℕ × ℕ → Set α := fun n ↦
      if h : n.2 < (A n.1).card then (A n.1).ordered ⟨n.2, h⟩ else ∅
    suffices h_sum_sum : ∑' i, ∑ u in A i, m u = ∑' n, m (g' (e n)) by
      have h_Union : (⋃ i, g' (e i)) = (⋃ i, f i) \ s := by
        rw [iUnion_diff, ← biUnion_range]
        simp only [Equiv.range_eq_univ, Set.mem_univ, iUnion_true, iUnion_dite,
          iUnion_empty, Set.union_empty, h_diff_eq_sUnion]
        ext1 x
        simp_rw [← iUnion_ordered, mem_iUnion]
        simp only [Prod.exists]
        constructor
        · rintro ⟨a, b, h, h_mem⟩
          exact ⟨a, ⟨b, h⟩, h_mem⟩
        · rintro ⟨a, ⟨b, h⟩, h_mem⟩
          exact ⟨a, b, h, h_mem⟩
      rw [h_sum_sum]
      refine iInf_le_of_le _ (iInf_le_of_le ?_ le_rfl)
      rw [h_Union]
      exact diff_subset_diff hf_subset subset_rfl
    have h1 : ∀ i, ∑ u in A i, m u = ∑' n, m (g' ⟨i, n⟩) := by
      intro i
      rw [← sum_ordered]
      let e_range_fin : Finset.range (A i).card ≃ Fin (A i).card := equivRangeFin (A i).card
      rw [Fintype.sum_equiv e_range_fin.symm (fun j ↦ m (Finset.ordered (A i) j)) fun j ↦
          m (Finset.ordered (A i) (e_range_fin j))]
      swap; · simp [Equiv.symm_apply_apply]
      have : ∑' n, m (g' (i, n)) =
          ∑' n : ((Finset.range (A i).card : Finset ℕ) : Set ℕ), m (g' (i, n)) := by
        rw [tsum_subtype ((Finset.range (A i).card : Finset ℕ) : Set ℕ) fun n ↦ m (g' (i, n))]
        congr with n
        simp only [Set.indicator_apply]
        by_cases h_lt : n ∈ ((Finset.range (A i).card : Finset ℕ) : Set ℕ)
        · simp only [h_lt, mem_setOf_eq, if_true]
        · have : ¬ (i, n).snd < (A (i, n).fst).card := by
            simpa only [coe_range, Set.mem_Iio] using h_lt
          simp only at h_lt this
          simp only [h_lt, mem_setOf_eq, if_false, this, not_false_iff, dif_neg, addContent_empty]
      rw [this, Finset.tsum_subtype' (Finset.range (A i).card) fun n ↦ m (g' (i, n))]
      rw [← Finset.sum_coe_sort (Finset.range (A i).card)]
      congr with j
      simp only
      rw [dif_pos (Finset.mem_range.mp j.2)]
      congr
    simp_rw [h1]
    rw [(_ : ∑' (i : ℕ) (n : ℕ), m (g' (i, n)) = ∑' n : ℕ × ℕ, m (g' n))]
    swap; · rw [ENNReal.tsum_prod']
    rw [← @tsum_range _ _ _ _ _ _ e (fun n ↦ m (g' n)) e.injective, Equiv.range_eq_univ,
      tsum_subtype (univ : Set (ℕ × ℕ)) fun n ↦ m (g' n)]
    simp_rw [indicator_univ]

lemma isCaratheodory_inducedOuterMeasure_addContent_of_mem (hC : IsSetSemiring C) (m : AddContent C)
    (hs : s ∈ C) :
    (inducedOuterMeasure (fun s _ ↦ m s) hC.empty_mem addContent_empty).IsCaratheodory s := by
  refine isCaratheodory_ofFunction_addContent_of_mem hC
    (extendContent hC.empty_mem (fun s _ ↦ m s) addContent_empty ?_)
    (fun _ ↦ extendContent_eq_top hC.empty_mem (fun s _ ↦ m s) addContent_empty ?_) hs <;>
    · intro I h_ss h_disj h_mem
      simp only [univ_eq_attach, sum_attach]
      exact addContent_sUnion h_ss h_disj h_mem

/-- A measure defined from a sub-additive content on a semi-ring of sets. This is a measure on a
Carathéodory σ-algebra. For a measure on another σ-algebra generated by the semi-ring of sets, see
`MeasureTheory.Measure.ofAddContent`. -/
noncomputable def Measure.ofAddContentCaratheodory (hC : IsSetSemiring C) (m : AddContent C)
    (m_iUnion_le : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : ⋃ i, f i ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i)) :
    @Measure α
      (inducedOuterMeasure (fun s _ ↦ m s) hC.empty_mem addContent_empty).caratheodory := by
  let M := inducedOuterMeasure (fun s _ ↦ m s) hC.empty_mem addContent_empty
  letI : MeasurableSpace α := M.caratheodory
  exact { M with
    m_iUnion := fun f hf hd ↦ OuterMeasure.iUnion_eq_of_caratheodory _ hf hd
    trimmed := by
      refine le_antisymm ?_ (OuterMeasure.le_trim _)
      refine (le_inducedOuterMeasure (P0 := hC.empty_mem) (m0 := addContent_empty)).mpr
        fun s hs ↦ ?_
      have hs_meas : MeasurableSet[M.caratheodory] s :=
        isCaratheodory_inducedOuterMeasure_addContent_of_mem hC m hs
      rw [OuterMeasure.trim_eq _ hs_meas,
        inducedOuterMeasure_addContent_eq_of_subadditive hC m m_iUnion_le hs] }

lemma Measure.ofAddContentCaratheodory_eq_inducedOuterMeasure (hC : IsSetSemiring C)
    (m : AddContent C)
    (m_iUnion_le : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : ⋃ i, f i ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i))
    (s : Set α) :
    Measure.ofAddContentCaratheodory hC m m_iUnion_le s
      = inducedOuterMeasure (fun s _ ↦ m s) hC.empty_mem addContent_empty s := rfl

lemma Measure.ofAddContentCaratheodory_eq (hC : IsSetSemiring C) (m : AddContent C)
    (m_iUnion_le : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : ⋃ i, f i ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i))
    (hs : s ∈ C) :
    Measure.ofAddContentCaratheodory hC m m_iUnion_le s = m s :=
  inducedOuterMeasure_addContent_eq_of_subadditive hC m m_iUnion_le hs

lemma isCaratheodory_generateFrom (hC : IsSetSemiring C) (m : AddContent C)
    (s : Set α) (hs : MeasurableSet[MeasurableSpace.generateFrom C] s) :
    (inducedOuterMeasure (fun s _ ↦ m s) hC.empty_mem addContent_empty).IsCaratheodory s := by
  apply MeasurableSpace.generateFrom_induction
  · exact fun _ ↦ isCaratheodory_inducedOuterMeasure_addContent_of_mem hC m
  · exact OuterMeasure.isCaratheodory_empty _
  · exact fun _ ↦ OuterMeasure.isCaratheodory_compl _
  · exact fun _ ↦ OuterMeasure.isCaratheodory_iUnion
  · exact hs

/-- A measure defined from a sub-additive content on a semi-ring of sets that generates the
σ-algebra. This is the measure given by the **Carathéodory extension theorem**. -/
noncomputable def Measure.ofAddContent [mα : MeasurableSpace α] (hC : IsSetSemiring C)
    (hC_gen : MeasurableSpace.generateFrom C = mα) (m : AddContent C)
    (m_iUnion_le : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : ⋃ i, f i ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i)) :
    Measure α :=
  Measure.trim (Measure.ofAddContentCaratheodory hC m m_iUnion_le)
    (by rw [← hC_gen]; exact isCaratheodory_generateFrom hC m)

/-- On the semi-ring of sets used in its definition, the measure `Measure.ofAddContent` is equal to
the content. -/
lemma Measure.ofAddContent_eq [mα : MeasurableSpace α] (hC : IsSetSemiring C)
    (hC_gen : MeasurableSpace.generateFrom C = mα) (m : AddContent C)
    (m_iUnion_le : ∀ ⦃f : ℕ → Set α⦄ (_hf : ∀ i, f i ∈ C) (_hf_Union : ⋃ i, f i ∈ C),
      m (⋃ i, f i) ≤ ∑' i, m (f i))
    (hs : s ∈ C) :
    Measure.ofAddContent hC hC_gen m m_iUnion_le s = m s := by
  rw [Measure.ofAddContent, trim_measurableSet_eq]
  · exact Measure.ofAddContentCaratheodory_eq hC m m_iUnion_le hs
  · rw [← hC_gen]
    exact MeasurableSpace.measurableSet_generateFrom hs

end MeasureTheory
