import Mathlib.Tactic
import TopologicalEntropy.ENNRealLog
import TopologicalEntropy.ERealDiv
import TopologicalEntropy.InvariantSubset
import TopologicalEntropy.RefinedUniformity
import TopologicalEntropy.UniformityFilter
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.UniformSpace.Basic

namespace RefinedCover

open InvariantSubset RefinedUniformity UniformSpace


/-- Given a uniform neighborhood U, an integer n and a subset F, a subset s is a (n, U)-cover 
(i.e. a refined cover) of F if any orbit of length n in F is U-shadowed by an orbit of length n 
of a point in s.--/
def IsRefinedCoverOf {X : Type _} (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) (s : Set X) :
  Prop :=
F ⊆ ⋃ x : s, ball x (refinedUni T U n)

theorem RefinedCoverOf.mono_space {X : Type _} {T : X → X} {F G : Set X} (F_sub_G : F ⊆ G)
{U : Set (X × X)} {n : ℕ} {s : Set X} (h : IsRefinedCoverOf T G U n s) :
  IsRefinedCoverOf T F U n s :=
Set.Subset.trans F_sub_G h

theorem RefinedCoverOf.mono_time {X : Type _} {T : X → X} {F : Set X} {U : Set (X × X)} {m n : ℕ}
(m_le_n : m ≤ n) {s : Set X} (h : IsRefinedCoverOf T F U n s) :
  IsRefinedCoverOf T F U m s :=
by
  apply @Set.Subset.trans X F _ (⋃ x : s, ball x (refinedUni T U m)) h
  apply Set.iUnion_mono
  intro x
  exact ball_mono (RefinedUniformity.mono_time T U m_le_n) x

theorem RefinedCoverOf.mono_uni {X : Type _} {T : X → X} {F : Set X} {U V : Set (X × X)}
(U_sub_V : U ⊆ V) {n : ℕ} {s : Set X} (h : IsRefinedCoverOf T F U n s) :
  IsRefinedCoverOf T F V n s :=
by
  apply @Set.Subset.trans X F _ (⋃ x : s, ball x (refinedUni T V n)) h
  apply Set.iUnion_mono
  intro x
  exact ball_mono (RefinedUniformity.mono_uni T U_sub_V n) x

@[simp]
theorem RefinedCoverOf.of_empty {X : Type _} {T : X → X} {U : Set (X × X)} {n : ℕ} :
  IsRefinedCoverOf T ∅ U n ∅ := 
by simp only [IsRefinedCoverOf, Set.empty_subset]

theorem RefinedCoverOf.of_nonempty {X : Type _} {T : X → X} {F : Set X} (hF : F.Nonempty)
{U : Set (X × X)} {n : ℕ} {s : Set X} (h : IsRefinedCoverOf T F U n s) :
  s.Nonempty :=
by
  cases' Set.nonempty_iUnion.1 (Set.Nonempty.mono h hF) with x hx
  use x
  exact Subtype.coe_prop x

theorem RefinedCoverOf.init_time {X : Type _} (T : X → X) (F : Set X) (U : Set (X × X)) {s : Set X}
(s_nonempty : s.Nonempty) :
  IsRefinedCoverOf T F U 0 s :=
by
  simp [IsRefinedCoverOf, refinedUni, ball]
  cases' s_nonempty with x x_in_s
  apply Set.subset_iUnion_of_subset x
  exact Set.subset_iUnion_of_subset x_in_s (Set.subset_univ F)

theorem RefinedCoverOf.iterate {X : Type _} {T : X → X} {F : Set X} (F_inv : IsInvariant T F)
{U V : Set (X × X)} (V_symm : SymmetricRel V) (V_comp_U : compRel V V ⊆ U) {m : ℕ} (n : ℕ)
{s : Finset X} (hs : IsRefinedCoverOf T F V m s) :
  ∃ t : Finset X, IsRefinedCoverOf T F U (m * n) t ∧ t.card ≤ s.card ^ n :=
by
  rcases F.eq_empty_or_nonempty with (rfl | F_nonempty)
  · clear hs V_symm V_comp_U V F_inv
    use ∅
    simp
  haveI : Nonempty X :=
    Set.nonempty_iff_univ_nonempty.2 (Set.Nonempty.mono (Set.subset_univ F) F_nonempty)
  have s_nonempty := RefinedCoverOf.of_nonempty F_nonempty hs
  cases' F_nonempty with x x_in_F
  rcases m.eq_zero_or_pos with (rfl | m_pos)
  · use {x}
    simp
    constructor
    · exact RefinedCoverOf.init_time T F U (Set.singleton_nonempty x)
    · have := Nat.one_le_of_lt (Finset.Nonempty.card_pos s_nonempty)
      exact one_le_pow_of_one_le' this n
  have :
    ∀ β : Finset.range n → s, ∃ y : X,
      (⋂ k : Finset.range n, T^[m * k] ⁻¹' ball (β k) (refinedUni T V m)) ⊆
        ball y (refinedUni T U (m * n)) :=
    by
    intro t
    by_cases inter_nonempty :
      (⋂ k : Finset.range n, T^[m * k] ⁻¹' ball (t k) (refinedUni T V m)).Nonempty
    swap
    · rw [Set.not_nonempty_iff_eq_empty] at inter_nonempty 
      rw [inter_nonempty]
      use x
      exact Set.empty_subset _
    cases' inter_nonempty with y y_in_inter
    use y
    intro z z_in_inter
    simp [refinedUni, ball, -Set.preimage_iterate_eq]
    simp [refinedUni, ball, -Set.preimage_iterate_eq] at z_in_inter 
    intro k k_lt_mn
    have kdivm_lt_n : k / m < n := Nat.div_lt_of_lt_mul k_lt_mn
    specialize z_in_inter (k / m) (Finset.mem_range.2 kdivm_lt_n) (k % m) (Nat.mod_lt k m_pos)
    rw [prod_map_ite T T (k % m)] at z_in_inter 
    simp at z_in_inter 
    rw [← Function.iterate_add_apply T (k % m) (m * (k / m)), Nat.mod_add_div k m] at z_in_inter 
    simp [refinedUni, ball, -Set.preimage_iterate_eq] at y_in_inter 
    specialize y_in_inter (k / m) (Finset.mem_range.2 kdivm_lt_n) (k % m) (Nat.mod_lt k m_pos)
    rw [prod_map_ite T T (k % m)] at y_in_inter 
    simp at y_in_inter 
    rw [← Function.iterate_add_apply T (k % m) (m * (k / m)), Nat.mod_add_div k m] at y_in_inter 
    rw [prod_map_ite T T k]
    simp
    apply V_comp_U
    exact mem_comp_of_mem_ball V_symm y_in_inter z_in_inter
  choose! refined_cover h_refined_cover using this
  classical
  let sn := Set.range refined_cover
  haveI := Set.fintypeRange refined_cover
  use sn.toFinset
  apply And.intro
  · intro y y_in_F
    have key : ∀ k : Finset.range n, ∃ z : s, y ∈ T^[m * k] ⁻¹' ball z (refinedUni T V m) :=
      by
      intro k
      have := hs (iter_of_inv_in_inv' F_inv (m * k) y_in_F)
      simp at this 
      rcases this with ⟨z, ⟨z_in_s, hz⟩⟩
      use ⟨z, z_in_s⟩
      exact hz
    rw [Finset.coe_nonempty] at s_nonempty 
    haveI : Nonempty s := Finset.Nonempty.coe_sort s_nonempty
    choose! t ht using key
    specialize h_refined_cover t
    simp
    simp [-Set.preimage_iterate_eq] at ht
    use t
    apply h_refined_cover
    simp [ht, -Set.preimage_iterate_eq]
  · rw [Set.toFinset_card]
    apply le_trans (Fintype.card_range_le refined_cover)
    simp

theorem RefinedCoverOf.iterate' {X : Type _} {T : X → X} {F : Set X} (F_inv : IsInvariant T F)
    {U V : Set (X × X)} (V_symm : SymmetricRel V) (V_comp_U : compRel V V ⊆ U) {m : ℕ}
    (m_pos : 0 < m) (n : ℕ) {s : Finset X} (hs : IsRefinedCoverOf T F V m s) :
    ∃ t : Finset X, IsRefinedCoverOf T F U n t ∧ t.card ≤ s.card ^ (n / m + 1) :=
  by
  cases' RefinedCoverOf.iterate F_inv V_symm V_comp_U (n / m + 1) hs with t ht
  use t
  exact ⟨RefinedCoverOf.mono_time (le_of_lt (Nat.lt_mul_div_succ n m_pos)) ht.1, ht.2⟩

/-- We can always find a (n, U)-refined cover of a compact subspace. 
If `T` is assumed continuous, this statement can be proved quickly by covering `F` 
by refined subsets, which are in this case open, and extracting a finite subcover. 
We bypass this condition, using the comparatively complex lemma `RefinedCoverOf.iterate`.-/
theorem RefinedCoverOf.exists {X : Type _} [UniformSpace X] {T : X → X} {F : Set X}
(F_inv : IsInvariant T F) (F_compact : IsCompact F) {U : Set (X × X)} (U_uni : U ∈ uniformity X)
(n : ℕ) :
  ∃ s : Finset X, IsRefinedCoverOf T F U n s :=
by
  rcases comp_symm_mem_uniformity_sets U_uni with ⟨V, V_uni, ⟨V_symm, V_comp_U⟩⟩
  let open_cover := fun x : X => ball x V
  have :=
    IsCompact.elim_nhds_subcover F_compact open_cover fun (x : X) _ =>
      ball_mem_nhds x V_uni
  rcases this with ⟨s, _, s_cover⟩
  have : IsRefinedCoverOf T F V 1 s := by
    intro x x_in_F
    specialize s_cover x_in_F
    simp at s_cover 
    rcases s_cover with ⟨y, y_in_s, x_in_By⟩
    simp [refinedUni]
    use y, y_in_s
    exact x_in_By
  rcases RefinedCoverOf.iterate F_inv V_symm V_comp_U n this with ⟨t, t_refined_cover, t_card⟩
  rw [one_mul n] at t_refined_cover 
  use t
  exact t_refined_cover

/--
The cardinals of all finite (n,U)-refined cover of F, mapped into ℕ∞ to get closure under Inf.--/
def RefinedCoverOf.cardinals {X : Type _} (T : X → X) (F : Set X) (U : Set (X × X)) (n : ℕ) :
    Set ℕ∞ :=
  {k : ℕ∞ | ∃ s : Finset X, (s.card : ℕ∞) = k ∧ IsRefinedCoverOf T F U n s}

theorem RefinedCoverOf.cardinals.nonempty {X : Type _} [UniformSpace X] {T : X → X} {F : Set X}
(F_inv : IsInvariant T F) (F_compact : IsCompact F) {U : Set (X × X)} (U_uni : U ∈ uniformity X) 
(n : ℕ) :
  (RefinedCoverOf.cardinals T F U n).Nonempty :=
by
  have := RefinedCoverOf.exists F_inv F_compact U_uni n
  cases' this with t ht
  use t.card, t
  simp only [ht, eq_self_iff_true, and_self_iff]

/-- The smallest cardinal of a (n,U)-refined cover of F. Takes values in ℕ∞, and is infinite 
if and only if F admits no finite refined cover.--/
noncomputable def refinedCoverMincard {X : Type _} (T : X → X) (F : Set X) (U : Set (X × X))
    (n : ℕ) : ℕ∞ :=
  sInf (RefinedCoverOf.cardinals T F U n)

theorem refinedCoverMincard.is_finite_iff {X : Type _} (T : X → X) (F : Set X) (U : Set (X × X))
    (n : ℕ) :
    refinedCoverMincard T F U n < ⊤ ↔
      ∃ s : Finset X, (s.card : ℕ∞) = refinedCoverMincard T F U n ∧ IsRefinedCoverOf T F U n s :=
  by
  constructor
  · intro finite_mincard
    have :=
      (not_iff_not.2 (@sInf_eq_top _ _ (RefinedCoverOf.cardinals T F U n))).1
        (ne_of_lt finite_mincard)
    push_neg at this 
    rcases this with ⟨k, ⟨k_cover_card, _⟩⟩
    exact csInf_mem (Set.nonempty_of_mem k_cover_card)
  · rintro ⟨s, ⟨s_mincard, _⟩⟩
    rw [← s_mincard]
    exact WithTop.coe_lt_top s.card

theorem refinedCoverMincard.le {X : Type _} {T : X → X} {F : Set X} {U : Set (X × X)} {n : ℕ}
{s : Finset X} (h : IsRefinedCoverOf T F U n s) :
  refinedCoverMincard T F U n ≤ s.card :=
by
  apply @sInf_le ℕ∞ _ _ _
  simp [RefinedCoverOf.cardinals]
  use s
  simp only [h, eq_self_iff_true, and_self_iff]

theorem refinedCoverMincard.exists {X : Type _} [UniformSpace X] {T : X → X} {F : Set X}
(F_inv : IsInvariant T F) (F_compact : IsCompact F) {U : Set (X × X)} (U_uni : U ∈ uniformity X) (n : ℕ) :
  ∃ s : Finset X, (s.card : ℕ∞) = refinedCoverMincard T F U n ∧ IsRefinedCoverOf T F U n s :=
csInf_mem (RefinedCoverOf.cardinals.nonempty F_inv F_compact U_uni n)

theorem refinedCoverMincard.mono_space {X : Type _} (T : X → X) {F G : Set X} (F_sub_G : F ⊆ G)
(U : Set (X × X)) (n : ℕ) :
  refinedCoverMincard T F U n ≤ refinedCoverMincard T G U n :=
by
  apply @sInf_le_sInf _ _ (RefinedCoverOf.cardinals T G U n) (RefinedCoverOf.cardinals T F U n)
  rintro k ⟨s, s_card_k, s_cover⟩
  use s
  exact ⟨s_card_k, RefinedCoverOf.mono_space F_sub_G s_cover⟩

theorem refinedCoverMincard.mono_time {X : Type _} (T : X → X) (F : Set X) (U : Set (X × X))
{m n : ℕ} (m_le_n : m ≤ n) :
  refinedCoverMincard T F U m ≤ refinedCoverMincard T F U n :=
by
  apply @sInf_le_sInf _ _ (RefinedCoverOf.cardinals T F U n) (RefinedCoverOf.cardinals T F U m)
  rintro k ⟨s, s_card_k, s_cover⟩
  use s
  exact ⟨s_card_k, RefinedCoverOf.mono_time m_le_n s_cover⟩

theorem refinedCoverMincard.mono_uni {X : Type _} (T : X → X) (F : Set X) {U V : Set (X × X)}
(U_sub_V : U ⊆ V) (n : ℕ) :
  refinedCoverMincard T F V n ≤ refinedCoverMincard T F U n :=
by
  apply @sInf_le_sInf _ _ (RefinedCoverOf.cardinals T F U n) (RefinedCoverOf.cardinals T F V n)
  rintro k ⟨s, s_card_k, s_cover⟩
  use s
  exact ⟨s_card_k, RefinedCoverOf.mono_uni U_sub_V s_cover⟩

@[simp]
theorem refinedCoverMincard.of_empty {X : Type _} {T : X → X} {U : Set (X × X)} {n : ℕ} :
  refinedCoverMincard T ∅ U n = 0 :=
by
  apply le_antisymm
  · apply @sInf_le ℕ∞ _
    use ∅
    simp [IsRefinedCoverOf]
  · exact zero_le (refinedCoverMincard T ∅ U n)

theorem refinedCoverMincard.empty_iff_zero {X : Type _} (T : X → X) (F : Set X) (U : Set (X × X))
(n : ℕ) :
  F = ∅ ↔ refinedCoverMincard T F U n = 0 :=
by
  apply Iff.intro
  · intro F_empty
    rw [F_empty]
    exact refinedCoverMincard.of_empty
  · intro zero_cover
    have := refinedCoverMincard.is_finite_iff T F U n
    rw [zero_cover] at this 
    simp [IsRefinedCoverOf] at this 
    exact Set.eq_empty_iff_forall_not_mem.2 this

theorem refinedCoverMincard.of_nonempty {X : Type _} (T : X → X) (F : Set X) (U : Set (X × X))
(n : ℕ) :
  F.Nonempty ↔ 1 ≤ refinedCoverMincard T F U n :=
by
  rw [ENat.one_le_iff_ne_zero, Set.nonempty_iff_ne_empty, Ne.def, Ne.def]
  apply not_iff_not.2
  exact refinedCoverMincard.empty_iff_zero T F U n

theorem refinedCoverMincard.init_eq_one {X : Type _} (T : X → X) {F : Set X}
(F_nonempty : F.Nonempty) (U : Set (X × X)) :
  refinedCoverMincard T F U 0 = 1 :=
by
  cases' F_nonempty with x x_in_F
  apply le_antisymm
  · apply @sInf_le ℕ∞ _ (RefinedCoverOf.cardinals T F U 0) (1 : ℕ∞)
    use {x}
    simp
    exact RefinedCoverOf.init_time T F U (Set.singleton_nonempty x)
  · apply @le_sInf ℕ∞ _ (RefinedCoverOf.cardinals T F U 0) (1 : ℕ∞)
    rintro k ⟨s, s_card_k, s_cover⟩
    rw [← s_card_k]; clear s_card_k; norm_cast
    apply Finset.Nonempty.card_pos
    rcases Set.mem_iUnion.1 (s_cover x_in_F) with ⟨⟨y, y_in_s⟩, hy⟩
    norm_cast at y_in_s
    use y
    exact y_in_s

theorem Enat.top_pow {n : ℕ} (n_pos : 0 < n) :
  (⊤ : ℕ∞)^n = ⊤ :=
by
  apply @Nat.le_induction 1 (fun m : ℕ => fun _ : 1 ≤ m => (⊤ : ℕ∞) ^ m = ⊤) (pow_one ⊤)
  · intro m _ h
    calc
      (⊤ : ℕ∞)^(m + 1) = ⊤^m * ⊤^1 := by rw [pow_add ⊤ m 1]
                     _ = ⊤ * ⊤^1   := by rw [h]
                     _ = ⊤ * ⊤     := by rw [pow_one ⊤]
                     _ = ⊤         := WithTop.top_mul_top
  · exact n_pos

theorem refinedCoverMincard.exponential_bound {X : Type _} {T : X → X} {F : Set X}
(F_inv : IsInvariant T F) {U V : Set (X × X)} (V_symm : SymmetricRel V)
(V_comp_U : compRel V V ⊆ U) (m n : ℕ) :
  refinedCoverMincard T F U (m * n) ≤ refinedCoverMincard T F V m ^ n :=
by
  rcases F.eq_empty_or_nonempty with (rfl | F_nonempty)
  · simp
  rcases n.eq_zero_or_pos with (rfl | n_pos)
  · simp [refinedCoverMincard.init_eq_one T F_nonempty U]
  by_cases h : refinedCoverMincard T F V m = ⊤
  · rw [h]
    exact le_of_le_of_eq (@le_top ℕ∞ _ _ _) (Eq.symm (Enat.top_pow n_pos))
  · replace h := lt_top_iff_ne_top.2 h
    rcases(refinedCoverMincard.is_finite_iff T F V m).1 h with ⟨s, ⟨s_mincard, s_cover⟩⟩
    rcases RefinedCoverOf.iterate F_inv V_symm V_comp_U n s_cover with ⟨t, ⟨t_cover, t_le_sn⟩⟩
    rw [← s_mincard]
    apply @le_trans ENat _ _ t.card _ _ _
    · apply sInf_le _
      use t
      simp [t_cover]
    · norm_cast

theorem refinedCoverMincard.exponential_bound' {X : Type _} {T : X → X} {F : Set X}
    (F_inv : IsInvariant T F) {U V : Set (X × X)} (V_symm : SymmetricRel V)
    (V_comp_U : compRel V V ⊆ U) {m : ℕ} (m_pos : 0 < m) (n : ℕ) :
    refinedCoverMincard T F U n ≤ refinedCoverMincard T F V m ^ (n / m + 1) :=
  by
  apply le_trans _ (refinedCoverMincard.exponential_bound F_inv V_symm V_comp_U m (n / m + 1))
  exact refinedCoverMincard.mono_time T F U (le_of_lt (Nat.lt_mul_div_succ n m_pos))

open ENNRealLog ERealDiv

theorem refinedCoverMincard.log_of_empty {X : Type _} (T : X → X) (U : Set (X × X)) (n : ℕ) :
  ENNReal.log (refinedCoverMincard T ∅ U n) = ⊥ :=
by
  rw [refinedCoverMincard.of_empty]
  norm_cast
  exact ENNReal.log_zero

theorem refinedCoverMincard.log_of_nonempty {X : Type _} (T : X → X) {F : Set X}
(F_nonempty : F.Nonempty) (U : Set (X × X)) (n : ℕ) :
  0 ≤ ENNReal.log (refinedCoverMincard T F U n) :=
by
  apply ENNReal.log_one_le_iff.1
  rw [← ENat.toENNReal_one]
  norm_cast
  exact (refinedCoverMincard.of_nonempty T F U n).1 F_nonempty

theorem refinedCoverMincard.explicit_upper_bound {X : Type _} {T : X → X} {F : Set X}
(F_inv : IsInvariant T F) {U V : Set (X × X)} (V_symm : SymmetricRel V)
(V_comp_U : compRel V V ⊆ U) (m n : ℕ) :
  ENNReal.log (refinedCoverMincard T F U (m * n)) / (n : ENNReal) ≤
    ENNReal.log (refinedCoverMincard T F V m) :=
by
  rcases n.eq_zero_or_pos with (rfl | n_pos)
  · simp
    rcases F.eq_empty_or_nonempty with (rfl | F_nonempty)
    · simp
      exact EReal.bot_div_ntop ENNReal.zero_ne_top
    · rw [refinedCoverMincard.init_eq_one T F_nonempty U]
      simp
      apply ENNReal.log_one_le_iff.1
      rw [← ENat.toENNReal_one]
      norm_cast
      exact (refinedCoverMincard.of_nonempty T F V m).1 F_nonempty
  · apply (@EReal.div_le_iff_le_mul _ _ n _ _).2
    · rw [← ENNReal.log_pow, ← ENNReal.log_le_iff_le]
      nth_rw 2 [← ENat.toENNRealRingHom_apply]
      rw [← RingHom.map_pow ENat.toENNRealRingHom _ n, ENat.toENNRealRingHom_apply]
      norm_cast
      exact refinedCoverMincard.exponential_bound F_inv V_symm V_comp_U m n
    · norm_cast
      exact Ne.symm (ne_of_lt n_pos)
    · simp

theorem refinedCoverMincard.explicit_upper_bound' {X : Type _} {T : X → X} {F : Set X}
(F_inv : IsInvariant T F) {U V : Set (X × X)} (V_symm : SymmetricRel V)
(V_comp_U : compRel V V ⊆ U) {m : ℕ} (m_pos : 0 < m) (n : ℕ) :
  ENNReal.log (refinedCoverMincard T F U n) / (n : ENNReal) ≤
    ENNReal.log (refinedCoverMincard T F V m) / (m : ENNReal) * (m / n + 1 : ENNReal) :=
by
  have m_ne_top : (m : ENNReal) ≠ ⊤ := by simp
  have n_ne_top : (n : ENNReal) ≠ ⊤ := by simp
  rcases F.eq_empty_or_nonempty with (rfl | F_nonempty)
  · simp [EReal.bot_div_ntop n_ne_top]
  rcases n.eq_zero_or_pos with (rfl | n_pos)
  · rw [refinedCoverMincard.init_eq_one T F_nonempty U, ENat.toENNReal_one, ENNReal.log_one,
      EReal.zero_div]
    apply mul_nonneg
    · apply EReal.nneg_div
      rw [← ENNReal.log_one_le_iff, ← ENat.toENNReal_one, ENat.toENNReal_le]
      exact (refinedCoverMincard.of_nonempty T F V m).1 F_nonempty
    · exact EReal.coe_ennreal_nonneg _
  have n_ne_zero : (n : ENNReal) ≠ 0 := by exact_mod_cast n_pos.ne.symm
  have m_ne_zero : (m : ENNReal) ≠ 0 := by exact_mod_cast m_pos.ne.symm
  rw [EReal.div_le_iff_le_mul n_ne_zero n_ne_top, mul_comm, mul_assoc, EReal.mul_div_right, 
    EReal.le_div_iff_mul_le m_ne_zero m_ne_top, ← EReal.coe_ennreal_mul, add_mul, 
    ENNReal.div_mul_cancel n_ne_zero n_ne_top, one_mul, mul_comm, mul_comm _ (ENNReal.toEReal _)]
  norm_cast
  repeat' rw [← ENNReal.log_pow]
  apply ENNReal.log_mono
  rw [← ENat.toENNRealRingHom_apply, ← RingHom.map_pow ENat.toENNRealRingHom _ m, ←
    RingHom.map_pow ENat.toENNRealRingHom _ (m + n), ENat.toENNRealRingHom_apply]
  norm_cast
  have key := refinedCoverMincard.mono_time T F U (le_of_lt (Nat.lt_mul_div_succ n m_pos))
  have lock := refinedCoverMincard.exponential_bound F_inv V_symm V_comp_U m (n / m + 1)
  replace key := le_trans key lock; clear lock
  replace key := @pow_le_pow_of_le_left ℕ∞ _ _ _ bot_le key m
  apply le_trans key; clear key
  rw [← pow_mul]
  apply pow_le_pow _ _
  · exact (refinedCoverMincard.of_nonempty T F V m).1 F_nonempty
  · rw [mul_comm, mul_add, mul_one, add_comm m n]
    exact add_le_add_right (Nat.mul_div_le n m) m

/-- The entropy of a uniformity neighborhood U, defined as the exponential rate of growth of the 
size of the smallest (n, U)-refined cover of F. Takes values in the space fo extended real numbers 
[-∞,+∞]. The first version uses a liminf (NB : should invert liminf and limsup).--/
noncomputable def refinedCoverEntropy {X : Type _} (T : X → X) (F : Set X) (U : Set (X × X)) :=
  Filter.atTop.liminf fun n : ℕ => ENNReal.log (refinedCoverMincard T F U n) / (n : ENNReal)

/-- The entropy of a uniformity neighborhood U, defined as the exponential rate of growth of the 
size of the smallest (n, U)-refined cover of F. Takes values in the space fo extended real numbers 
[-∞,+∞]. The second version uses a limsup (NB : should invert liminf and limsup).--/
noncomputable def refinedCoverEntropy' {X : Type _} (T : X → X) (F : Set X) (U : Set (X × X)) :=
  Filter.atTop.limsup fun n : ℕ => ENNReal.log (refinedCoverMincard T F U n) / (n : ENNReal)

theorem refinedCoverEntropy.mono_space {X : Type _} (T : X → X) {F G : Set X} (F_sub_G : F ⊆ G)
    (U : Set (X × X)) : refinedCoverEntropy T F U ≤ refinedCoverEntropy T G U :=
  by
  apply Filter.liminf_le_liminf _ _ _
  · apply Filter.eventually_of_forall _
    intro n
    apply EReal.div_left_mono _
    apply ENNReal.log_mono _
    norm_cast
    exact refinedCoverMincard.mono_space T F_sub_G U n
  · use ⊥; simp
  · use ⊤; simp

theorem refinedCoverEntropy.mono_uni {X : Type _} (T : X → X) (F : Set X) {U V : Set (X × X)}
    (U_sub_V : U ⊆ V) : refinedCoverEntropy T F V ≤ refinedCoverEntropy T F U :=
  by
  apply Filter.liminf_le_liminf _ _ _
  swap; · use ⊥; simp
  swap; · use ⊤; simp
  apply Filter.eventually_of_forall _
  intro n
  apply EReal.div_left_mono n
  apply ENNReal.log_mono
  apply ENat.toENNReal_mono
  exact refinedCoverMincard.mono_uni T F U_sub_V n

@[simp]
theorem refinedCoverEntropy.of_empty {X : Type _} {T : X → X} {U : Set (X × X)} :
  refinedCoverEntropy T ∅ U = ⊥ :=
by
  suffices h :
    (fun n : ℕ => ENNReal.log (refinedCoverMincard T ∅ U n) / (n : ENNReal)) = fun n : ℕ =>
      ⊥
  · unfold refinedCoverEntropy
    rw [h]
    exact Filter.liminf_const ⊥
  · ext1 n
    rw [refinedCoverMincard.log_of_empty T U n]
    apply EReal.bot_div_ntop
    simp

theorem refinedCoverEntropy.pos_of_nonempty {X : Type _} (T : X → X) {F : Set X}
  (F_nonempty : F.Nonempty) (U : Set (X × X)) : 0 ≤ refinedCoverEntropy T F U :=
by
  apply le_trans _ Filter.iInf_le_liminf
  apply le_iInf _
  intro n
  exact EReal.nneg_div (refinedCoverMincard.log_of_nonempty T F_nonempty U n)

theorem refinedCoverEntropy.upper_bound {X : Type _} {T : X → X} {F : Set X}
(F_inv : IsInvariant T F) {U V : Set (X × X)} (V_symm : SymmetricRel V)
(V_comp_U : compRel V V ⊆ U) {n : ℕ} (n_pos : 0 < n) :
  refinedCoverEntropy T F U ≤ ENNReal.log (refinedCoverMincard T F V n) / (n : ENNReal) :=
by
  apply Filter.liminf_le_of_frequently_le' _
  rw [Filter.frequently_atTop]
  intro N
  use N * n
  apply And.intro
  . have := Nat.mul_le_mul_left N (Nat.one_le_of_lt n_pos)
    rw [mul_one N] at this 
    exact this
  . have key := refinedCoverMincard.explicit_upper_bound F_inv V_symm V_comp_U n N
    rw [mul_comm n N] at key
    replace key := EReal.div_left_mono' n key
    rw [EReal.div_mul _ _] at key
    . simp
      exact key
    . simp
    . simp

theorem refinedCoverEntropy.explicit_upper_bound {X : Type _} {T : X → X} {F : Set X}
(F_inv : IsInvariant T F) {U V : Set (X × X)} (V_symm : SymmetricRel V)
(V_comp_U : compRel V V ⊆ U) {n : ℕ} (n_pos : 0 < n) {s : Finset X}
(h : IsRefinedCoverOf T F V n s) :
  refinedCoverEntropy T F U ≤ ENNReal.log s.card / (n : ENNReal) :=
by
  apply le_trans (refinedCoverEntropy.upper_bound F_inv V_symm V_comp_U n_pos)
  apply EReal.div_left_mono _
  apply ENNReal.log_mono _
  norm_cast
  apply sInf_le _
  use s
  simp [h]

/-lemma refined_cover_entropy.entropic_upper_bound' {X : Type*} {T : X → X} {F : set X}
(F_inv : is_invariant T F) {U V : set (X × X)} (V_symm : symmetric_rel V) 
(V_comp_U : comp_rel V V ⊆ U) {n : ℕ} (n_pos : 0 < n) :
  refined_cover_entropy' T F U 
≤ ereal.div_ennreal (ENNReal.log (refinedCoverMincard T F V n)) n :=
begin
  unfold refined_cover_entropy',
  have key := @filter.eventually_of_forall ℕ _ filter.at_top 
    (refinedCoverMincard.explicit_upper_bound' F_inv V_symm V_comp_U n_pos),
  replace key := filter.limsup_le_limsup key _ _,
  swap, { use ⊥, simp },
  swap, { use ⊤, simp },
  apply le_trans key, clear key,
  sorry,
end-/

theorem refinedCoverEntropy.finite_of_compact {X : Type _} [UniformSpace X] {T : X → X} {F : Set X}
(F_inv : IsInvariant T F) (F_compact : IsCompact F) {U : Set (X × X)} (U_uni : U ∈ uniformity X) :
  refinedCoverEntropy T F U < ⊤ :=
by
  rcases comp_symm_mem_uniformity_sets U_uni with ⟨V, V_uni, V_symm, V_comp_U⟩
  rcases refinedCoverMincard.exists F_inv F_compact V_uni 1 with ⟨s, ⟨_, s_cover⟩⟩
  apply lt_of_le_of_lt
    (refinedCoverEntropy.explicit_upper_bound F_inv V_symm V_comp_U zero_lt_one s_cover)
  simp
  rw [← ENNReal.log_lt_top_iff]
  change ((Finset.card s : ENat) : ENNReal) < ⊤
  rw [← ENat.toENNReal_top, ENat.toENNReal_lt]
  exact Ne.lt_top (ENat.coe_ne_top (Finset.card s))

/-- The entropy of T restricted to F, obtained by taking the limit when the uniformity neighborhood 
U vanishes.--/
noncomputable def coverEntropy {X : Type _} [UniformSpace X] (T : X → X) (F : Set X) :=
  UniformityFilter.smallUniformities.liminf fun U : Set (X × X) => refinedCoverEntropy T F U

theorem coverEntropy.mono_space {X : Type _} [UniformSpace X] (T : X → X) {F G : Set X}
(F_sub_G : F ⊆ G) :
  coverEntropy T F ≤ coverEntropy T G :=
by
  apply @Filter.liminf_le_liminf EReal
  . apply Filter.eventually_of_forall _
    intro U
    exact refinedCoverEntropy.mono_space T F_sub_G U
  · use ⊥; simp
  · use ⊤; simp

theorem coverEntropy.pos_of_nonempty {X : Type _} [UniformSpace X] (T : X → X) {F : Set X}
(F_nonempty : F.Nonempty) :
  0 ≤ coverEntropy T F :=
by
  apply Filter.le_liminf_of_le
  · use ⊤; simp
  . apply Filter.eventually_of_forall _
    intro U
    exact refinedCoverEntropy.pos_of_nonempty T F_nonempty U


#lint

end RefinedCover

