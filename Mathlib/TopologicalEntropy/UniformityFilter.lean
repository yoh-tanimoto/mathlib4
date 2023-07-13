import Mathlib.Tactic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.UniformSpace.Basic

--import order.pfilter
namespace UniformityFilter

/--Shorthand for the space of uniform neighborhoods--/
notation "𝓤" => uniformity

/-- Filter of small neighborhoods in a uniform space. --/
def smallUniformities {X : Type _} [UniformSpace X] : Filter (Set (X × X))
    where
  sets := {N : Set (Set (X × X)) | ∃ U ∈ 𝓤 X, ∀ V ∈ N, V ⊆ U}
  univ_sets := by simp; use Set.univ; simp
  sets_of_superset := by simp; intro M N U _ _ _; use Set.univ; simp
  inter_sets := by
    simp; intro M N P _ _ U U_uni N_sub_U; use U, U_uni; intro V _ V_N
    exact N_sub_U V V_N

/-

/- Courtesy of Junyan Xu-/
/- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there-code-for-X.3F/topic/Filter.20on.20.28set.20X.29/near/289690942 -/

variable {X : Type*}

def filter.pfilter (F : filter X) : order.pfilter (set X) :=
⟨ { carrier := F.sets,
    lower' := λ a b h ha, F.sets_of_superset ha h,
    nonempty' := ⟨set.univ, F.univ_sets⟩,
    directed' := λ a ha b hb, ⟨order_dual.to_dual (a.of_dual ∩ b.of_dual),
      F.inter_sets ha hb, set.inter_subset_left a b, set.inter_subset_right a b⟩ } ⟩

lemma filter.generate_singleton (s : set X) :
  filter.generate {s} = filter.principal s :=
begin
  apply le_antisymm,
  { intros t h, apply filter.generate_sets.superset _ h, exact filter.generate_sets.basic rfl },
  { rw filter.sets_iff_generate, rintro _ ⟨rfl⟩, exact subset_rfl },
end

variables [preorder X] {F : set X} (hn : F.nonempty) (hd : directed_on (≥) F)
-- hn and hd together are weaker than pfilter (two of three conditions)

def filter_of_directed : filter X :=
{ sets := {T : set X | ∃ U ∈ F, ∀ V ≤ U, V ∈ T},
  univ_sets := ⟨hn.some, hn.some_mem, λ _ _, trivial⟩,
  sets_of_superset := λ s t ⟨U, hU, hs⟩ hl, ⟨U, hU, λ V hV, hl (hs V hV)⟩,
  inter_sets := λ s t ⟨U₁, hU₁, hs₁⟩ ⟨U₂, hU₂, hs₂⟩,
    let ⟨U, hU, hl₁, hl₂⟩ := hd U₁ hU₁ U₂ hU₂ in
    ⟨U, hU, λ V hV, ⟨hs₁ V (hV.trans hl₁), hs₂ V (hV.trans hl₂)⟩⟩ }

lemma mem_filter_of_directed (T : set X) :
  T ∈ filter_of_directed hn hd ↔ ∃ U ∈ F, set.Iic U ⊆ T := iff.rfl

lemma filter_of_directed_eq :
  filter_of_directed hn hd = ⨅ U ∈ F, filter.principal (set.Iic U) :=
begin
  simp_rw [← filter.generate_singleton, ← filter.generate_Union],
  apply le_antisymm,
  { rw filter.sets_iff_generate, rintro T hT,
    obtain ⟨x, hx, he⟩ := set.mem_Union₂.1 hT,
    refine (mem_filter_of_directed hn hd T).2 ⟨x, hx, he.superset⟩ },
  { rintro T hT, obtain ⟨U, hU, hl⟩ := (mem_filter_of_directed hn hd T).1 hT,
    apply filter.generate_sets.superset (filter.generate_sets.basic _) hl,
    exact set.mem_Union₂.2 ⟨U, hU, rfl⟩ },
end

lemma directed_on_univ' : directed_on (≥) F ↔ directed_on (≥) (set.univ : set F) :=
begin
  rw directed_on_univ_iff, refine ⟨λ hd, ⟨_⟩, _⟩,
  { rintro ⟨a, ha⟩ ⟨b, hb⟩,
    obtain ⟨c, hc, h⟩ := hd a ha b hb,
    exact ⟨⟨c, hc⟩, h⟩ },
  { rintro ⟨hd⟩ a ha b hb,
    obtain ⟨⟨c, hc⟩, h⟩ := hd ⟨a, ha⟩ ⟨b, hb⟩,
    exact ⟨c, hc, h⟩ },
end

lemma filter_of_directed_eq_at_bot :
  filter_of_directed (@set.univ_nonempty _ hn.to_subtype) (directed_on_univ'.1 hd) =
  filter.at_bot :=
by rw [filter_of_directed_eq, filter.at_bot, infi_univ]

def map_at_bot (F : set X) : filter X := filter.map coe (filter.at_bot : filter F)

include hn hd

lemma mem_map_at_bot (T : set X) :
  T ∈ map_at_bot F ↔ ∃ U ∈ F, set.Iic U ∩ F ⊆ T :=
begin
  sorry,
  /-dsimp [map_at_bot],
  rw [← filter_of_directed_eq_at_bot hn hd, mem_filter_of_directed],
  exact ⟨λ ⟨⟨U, hU⟩, _, h⟩, ⟨U, hU, λ V ⟨hVU, hVF⟩, @h ⟨V, hVF⟩ hVU⟩,
    λ ⟨U, hU, h⟩, ⟨⟨U, hU⟩, trivial, λ ⟨V, hVF⟩ hVU, h ⟨hVU, hVF⟩⟩⟩,-/
end

lemma map_at_bot_eq (T : set X) : map_at_bot F = filter_of_directed hn hd ⊓ filter.principal F :=
begin
  ext, rw [filter.mem_inf_principal, mem_map_at_bot hn hd, mem_filter_of_directed],
  exact exists₂_congr (λ _ _, forall_congr $ λ _, and_imp),
end

-/
#lint

end UniformityFilter

