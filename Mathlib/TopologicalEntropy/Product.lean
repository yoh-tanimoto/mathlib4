import Mathlib.Tactic
import TopologicalEntropy.RefinedCover

--import .refined_net
--import .refined_net
namespace Product

open RefinedCover RefinedUniformity UniformSpace

/--
This defines a uniform structure on the product of two uniform spaces. Should be expanded and put into 
the library on uniform spaces.--/
def Prod.uniformity {X Y : Type _} (U : Set (X × X)) (V : Set (Y × Y)) : Set ((X × Y) × X × Y) :=
  {W : (X × Y) × X × Y | (W.1.1, W.2.1) ∈ U ∧ (W.1.2, W.2.2) ∈ V}

theorem ball_prod {X Y : Type _} (U : Set (X × X)) (V : Set (Y × Y)) (xy : X × Y) :
  ball xy (Prod.uniformity U V) = ball xy.1 U ×ˢ ball xy.2 V :=
by
  ext p
  simp [ball, Prod.uniformity]

theorem refinedUniformity_prod {X Y : Type _} (S : X → X) (T : Y → Y) (U : Set (X × X))
(V : Set (Y × Y)) (n : ℕ) :
  refinedUni (Prod.map S T) (Prod.uniformity U V) n =
    Prod.uniformity (refinedUni S U n) (refinedUni T V n) :=
by
  apply Set.Subset.antisymm
  · intro p p_in_uniformity
    simp [Prod.uniformity, refinedUni, -Set.preimage_iterate_eq]
    simp [Prod.uniformity, refinedUni, -Set.preimage_iterate_eq] at p_in_uniformity 
    apply And.intro
    · intro k k_lt_n
      simp [prod_map_ite S S k, Prod_map S^[k] S^[k]]
      specialize p_in_uniformity k k_lt_n
      simp [prod_map_ite (Prod.map S T) (Prod.map S T) k, prod_map_ite S T k] at p_in_uniformity 
      exact p_in_uniformity.1
    · intro k k_lt_n
      simp [prod_map_ite T T k, Prod_map T^[k] T^[k]]
      specialize p_in_uniformity k k_lt_n
      simp [prod_map_ite (Prod.map S T) (Prod.map S T) k, prod_map_ite S T k] at p_in_uniformity 
      exact p_in_uniformity.2
  · intro p p_in_product
    simp [Prod.uniformity, refinedUni]
    intro k k_lt_n
    simp [prod_map_ite (Prod.map S T) (Prod.map S T) k, prod_map_ite S T k]
    simp [Prod.uniformity, refinedUni, -Set.preimage_iterate_eq] at p_in_product 
    cases' p_in_product with p_in_U p_in_V
    specialize p_in_U k k_lt_n
    simp [prod_map_ite S S k] at p_in_U 
    specialize p_in_V k k_lt_n
    simp [prod_map_ite T T k] at p_in_V 
    exact ⟨p_in_U, p_in_V⟩

theorem RefinedCoverOf.product {X Y : Type _} {S : X → X} {T : Y → Y} {F : Set X} {G : Set Y}
{U : Set (X × X)} {V : Set (Y × Y)} {n : ℕ} {s : Set X} {t : Set Y}
(h_S : IsRefinedCoverOf S F U n s) (h_T : IsRefinedCoverOf T G V n t) :
  IsRefinedCoverOf (Prod.map S T) (F ×ˢ G) (Prod.uniformity U V) n (s ×ˢ t) :=
by
  unfold IsRefinedCoverOf
  rw [refinedUniformity_prod S T U V n]
  intro p p_in_FG
  specialize h_S p_in_FG.1
  simp at h_S 
  rcases h_S with ⟨x, ⟨x_in_s, p_ball_x⟩⟩
  specialize h_T p_in_FG.2
  simp at h_T 
  rcases h_T with ⟨y, ⟨y_in_t, p_ball_y⟩⟩
  rw [Set.mem_iUnion]
  use ⟨(x, y), Set.mem_prod.2 ⟨x_in_s, y_in_t⟩⟩
  simp [ball_prod]
  exact ⟨p_ball_x, p_ball_y⟩

theorem RefinedCoverOf.projection_fst {X Y : Type _} {S : X → X} {T : Y → Y} {F : Set X} {G : Set Y}
(G_nonempty : G.Nonempty) {U : Set (X × X)} {V : Set (Y × Y)} {n : ℕ} {st : Set (X × Y)}
(h_ST : IsRefinedCoverOf (Prod.map S T) (F ×ˢ G) (Prod.uniformity U V) n st) :
  IsRefinedCoverOf S F U n (Prod.fst '' st) :=
by
  replace h_ST := Set.image_subset Prod.fst h_ST
  rw [Set.fst_image_prod F G_nonempty] at h_ST 
  apply @Set.Subset.trans X F _ (⋃ x : Prod.fst '' st, ball x (refinedUni S U n)) h_ST; clear h_ST
  simp
  intro x y xy_in_st
  simp [refinedUniformity_prod S T U V n, ball_prod (refinedUni S U n) (refinedUni T V n)]
  apply Set.subset_iUnion_of_subset x
  apply Set.subset_iUnion_of_subset y
  apply Set.subset_iUnion_of_subset xy_in_st
  exact Set.prod_subset_preimage_fst (ball x (refinedUni S U n)) (ball y (refinedUni T V n))

theorem RefinedCoverOf.projection_snd {X Y : Type _} {S : X → X} {T : Y → Y} {F : Set X}
(F_nonempty : F.Nonempty) {G : Set Y} {U : Set (X × X)} {V : Set (Y × Y)} {n : ℕ}
{st : Set (X × Y)} (h_ST : IsRefinedCoverOf (Prod.map S T) (F ×ˢ G) (Prod.uniformity U V) n st) :
  IsRefinedCoverOf T G V n (Prod.snd '' st) :=
by
  replace h_ST := Set.image_subset Prod.snd h_ST
  rw [Set.snd_image_prod F_nonempty G] at h_ST 
  apply @Set.Subset.trans Y G _ (⋃ y : Prod.snd '' st, ball y (refinedUni T V n)) h_ST; clear h_ST
  simp
  intro x y xy_in_st
  simp [refinedUniformity_prod S T U V n, ball_prod (refinedUni S U n) (refinedUni T V n)]
  apply Set.subset_iUnion_of_subset y
  apply Set.subset_iUnion_of_subset x
  apply Set.subset_iUnion_of_subset xy_in_st
  exact Set.prod_subset_preimage_snd (ball x (refinedUni S U n)) (ball y (refinedUni T V n))

theorem RefinedCoverMincard.product {X Y : Type _} (S : X → X) (T : Y → Y) (F : Set X) (G : Set Y)
    (U : Set (X × X)) (V : Set (Y × Y)) (n : ℕ) :
    refinedCoverMincard (Prod.map S T) (F ×ˢ G) (Prod.uniformity U V) n ≤
      refinedCoverMincard S F U n * refinedCoverMincard T G V n :=
  by
  rcases F.eq_empty_or_nonempty with (rfl | F_nonempty)
  · simp [refinedCoverMincard.of_empty]
  rcases G.eq_empty_or_nonempty with (rfl | G_nonempty)
  · simp [refinedCoverMincard.of_empty]
  by_cases X_has_card : (RefinedCoverOf.cardinals S F U n).Nonempty; swap
  · rw [Set.not_nonempty_iff_eq_empty] at X_has_card 
    have : refinedCoverMincard S F U n = ⊤ := by 
      unfold refinedCoverMincard
      rw [X_has_card]
      simp
    rw [this]; clear this
    apply le_of_le_of_eq le_top _
    apply Eq.symm
    apply WithTop.top_mul
    exact ENat.one_le_iff_ne_zero.1 ((refinedCoverMincard.of_nonempty T G V n).1 G_nonempty)
  by_cases Y_has_card : (RefinedCoverOf.cardinals T G V n).Nonempty; swap
  · rw [Set.not_nonempty_iff_eq_empty] at Y_has_card 
    have : refinedCoverMincard T G V n = ⊤ := by
      unfold refinedCoverMincard
      rw [Y_has_card]
      simp
    rw [this]; clear this
    apply le_of_le_of_eq le_top _
    apply Eq.symm
    apply WithTop.mul_top
    exact ENat.one_le_iff_ne_zero.1 ((refinedCoverMincard.of_nonempty S F U n).1 F_nonempty)
  rcases csInf_mem X_has_card with ⟨s, ⟨s_mincard, s_cover⟩⟩; clear X_has_card
  rcases csInf_mem Y_has_card with ⟨t, ⟨t_mincard, t_cover⟩⟩; clear Y_has_card
  unfold refinedCoverMincard
  rw [← s_mincard]; clear s_mincard
  rw [← t_mincard]; clear t_mincard
  apply @sInf_le ℕ∞ _ _ (s.card * t.card)
  use s ×ˢ t
  simp
  exact RefinedCoverOf.product s_cover t_cover

/-open ENNRealLog ERealDiv-/

/-lemma refined_cover_entropy.product {X Y : Type*} (S : X → X) (T : Y → Y) (F : set X) (G : set Y) 
(U : set (X × X)) (V : set (Y × Y)) :
  refined_cover_entropy (prod.map S T) (F ×ˢ G) (Prod.uniformity U V) 
≤ (refined_cover_entropy S F U) + (refined_cover_entropy T G V) := 
begin
  sorry,
end


lemma cover_entropy.product {X Y : Type*} [uniform_space X] [uniform_space Y] (S : X → X) (T : Y → Y)
(F : set X) (G : set Y) :
  cover_entropy (prod.map S T) (F ×ˢ G) ≤ (cover_entropy S F) + (cover_entropy T G) := 
begin
  sorry,
end-/
-- Besoin de monstrer que la liminf est une lim pour que cela fonctionne. Pas évident... 
-- Changer liminf en limsup dans la définition de l'entropie cover ? 
-- Essayer les morphismes et aviser.

#lint

end Product

