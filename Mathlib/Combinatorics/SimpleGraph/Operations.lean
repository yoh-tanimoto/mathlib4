/-
Copyright (c) 2023 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Local graph operations

This file defines some single-graph operations that modify a finite number of vertices
and proves basic theorems about them. When the graph itself has a finite number of vertices
we also prove theorems about the number of edges in the modified graphs.

## Main definitions

* `G.replaceVertex s t` is `G` with `t` replaced by a copy of `s`,
  removing the `s-t` edge if present.
* `G.addEdge s t` is `G` with the `s-t` edge added, if that is a valid edge.
-/


open Finset

namespace SimpleGraph

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (s t : V)

section ReplaceVertex

/-- The graph formed by forgetting `t`'s neighbours and instead giving it those of `s`. The `s-t`
edge is removed if present. -/
def replaceVertex : SimpleGraph V where
  Adj v w := if v = t then if w = t then False else G.Adj s w
                      else if w = t then G.Adj v s else G.Adj v w
  symm v w := by dsimp only; split_ifs <;> simp [adj_comm]

/-- There is never an `s-t` edge in `G.replaceVertex s t`. -/
lemma not_adj_replaceVertex_same : ¬(G.replaceVertex s t).Adj s t := by simp [replaceVertex]

@[simp]
lemma replaceVertex_self : G.replaceVertex s s = G := by ext; unfold replaceVertex; aesop

variable {t}

/-- Except possibly for `t`, the neighbours of `s` in `G.replaceVertex s t` are its neighbours in
`G`. -/
lemma adj_replaceVertex_iff_of_ne_left {w : V} (hw : w ≠ t) :
    (G.replaceVertex s t).Adj s w ↔ G.Adj s w := by simp [replaceVertex, hw]

/-- Except possibly for itself, the neighbours of `t` in `G.replaceVertex s t` are the neighbours of
`s` in `G`. -/
lemma adj_replaceVertex_iff_of_ne_right {w : V} (hw : w ≠ t) :
    (G.replaceVertex s t).Adj t w ↔ G.Adj s w := by simp [replaceVertex, hw]

/-- Adjacency in `G.replaceVertex s t` which does not involve `t` is the same as that of `G`. -/
lemma adj_replaceVertex_iff_of_ne {v w : V} (hv : v ≠ t) (hw : w ≠ t) :
    (G.replaceVertex s t).Adj v w ↔ G.Adj v w := by simp [replaceVertex, hv, hw]

variable {s}

theorem edgeSet_replaceVertex_of_not_adj (hn : ¬G.Adj s t) : (G.replaceVertex s t).edgeSet =
    G.edgeSet \ G.incidenceSet t ∪ (s(·, t)) '' (G.neighborSet s) := by
  ext e; refine' e.inductionOn _
  simp only [replaceVertex, mem_edgeSet, Set.mem_union, Set.mem_diff, mk'_mem_incidenceSet_iff]
  intros; split_ifs; exacts [by simp_all, by aesop, by rw [adj_comm]; aesop, by aesop]

theorem edgeSet_replaceVertex_of_adj (ha : G.Adj s t) : (G.replaceVertex s t).edgeSet =
    (G.edgeSet \ G.incidenceSet t ∪ (s(·, t)) '' (G.neighborSet s)) \ {s(t, t)} := by
  ext e; refine' e.inductionOn _
  simp only [replaceVertex, mem_edgeSet, Set.mem_union, Set.mem_diff, mk'_mem_incidenceSet_iff]
  intros; split_ifs; exacts [by simp_all, by aesop, by rw [adj_comm]; aesop, by aesop]

variable [Fintype V] [DecidableRel G.Adj]

instance : DecidableRel (G.replaceVertex s t).Adj := by unfold replaceVertex; infer_instance

theorem edgeFinset_replaceVertex_of_not_adj (hn : ¬G.Adj s t) : (G.replaceVertex s t).edgeFinset =
    G.edgeFinset \ G.incidenceFinset t ∪ (G.neighborFinset s).image (s(·, t)) := by
  simp only [incidenceFinset, neighborFinset, ← Set.toFinset_diff, ← Set.toFinset_image,
    ← Set.toFinset_union]
  exact Set.toFinset_congr (G.edgeSet_replaceVertex_of_not_adj hn)

theorem edgeFinset_replaceVertex_of_adj (ha : G.Adj s t) : (G.replaceVertex s t).edgeFinset =
    (G.edgeFinset \ G.incidenceFinset t ∪ (G.neighborFinset s).image (s(·, t))) \ {s(t, t)} := by
  simp only [incidenceFinset, neighborFinset, ← Set.toFinset_diff, ← Set.toFinset_image,
    ← Set.toFinset_union, ← Set.toFinset_singleton]
  exact Set.toFinset_congr (G.edgeSet_replaceVertex_of_adj ha)

lemma disjoint_sdiff_neighborFinset_image :
    Disjoint (G.edgeFinset \ G.incidenceFinset t) ((G.neighborFinset s).image (s(·, t))) := by
  rw [disjoint_iff_ne]
  intro e he
  have : t ∉ e := by
    rw [mem_sdiff, mem_incidenceFinset] at he
    obtain ⟨_, h⟩ := he
    contrapose! h
    simp_all [incidenceSet]
  aesop

theorem card_edgeFinset_replaceVertex_of_not_adj (hn : ¬G.Adj s t) :
    (G.replaceVertex s t).edgeFinset.card = G.edgeFinset.card + G.degree s - G.degree t := by
  have inc : G.incidenceFinset t ⊆ G.edgeFinset := by simp [incidenceFinset, incidenceSet_subset]
  rw [G.edgeFinset_replaceVertex_of_not_adj hn,
    card_union_of_disjoint G.disjoint_sdiff_neighborFinset_image, card_sdiff inc,
    tsub_add_eq_add_tsub <| card_le_card inc, card_incidenceFinset_eq_degree]
  congr 2
  rw [card_image_of_injective, card_neighborFinset_eq_degree]
  unfold Function.Injective
  aesop

theorem card_edgeFinset_replaceVertex_of_adj (ha : G.Adj s t) :
    (G.replaceVertex s t).edgeFinset.card = G.edgeFinset.card + G.degree s - G.degree t - 1 := by
  have inc : G.incidenceFinset t ⊆ G.edgeFinset := by simp [incidenceFinset, incidenceSet_subset]
  rw [G.edgeFinset_replaceVertex_of_adj ha, card_sdiff (by simp [ha]),
    card_union_of_disjoint G.disjoint_sdiff_neighborFinset_image, card_sdiff inc,
    tsub_add_eq_add_tsub <| card_le_card inc, card_incidenceFinset_eq_degree]
  congr 2
  rw [card_image_of_injective, card_neighborFinset_eq_degree]
  unfold Function.Injective
  aesop

end ReplaceVertex

section AddEdge

/-- Given a vertex pair, add the corresponding edge to the graph's edge set if not present. -/
def addEdge : SimpleGraph V where
  Adj v w := G.Adj v w ∨ s ≠ t ∧ (s = v ∧ t = w ∨ s = w ∧ t = v)
  symm v w := by simp_rw [adj_comm]; (conv_lhs => arg 2; arg 2; rw [or_comm]); exact id

@[simp]
lemma addEdge_self : G.addEdge s s = G := by ext; simp [addEdge]

variable {s t}

lemma addEdge_of_adj (h : G.Adj s t) : G.addEdge s t = G := by
  ext
  simp only [addEdge, ne_eq, G.ne_of_adj h, not_false_eq_true, true_and, or_iff_left_iff_imp]
  rintro (_ | _) <;> simp_all [adj_comm]

variable [Fintype V] [DecidableRel G.Adj]

instance : DecidableRel (G.addEdge s t).Adj := by unfold addEdge; infer_instance

theorem edgeFinset_addEdge (hn : ¬G.Adj s t) (h : s ≠ t) :
    (G.addEdge s t).edgeFinset = G.edgeFinset.cons s(s, t) (by simp_all) := by
  ext e; refine' e.inductionOn _; unfold addEdge; aesop

theorem card_edgeFinset_addEdge (hn : ¬G.Adj s t) (h : s ≠ t) :
    (G.addEdge s t).edgeFinset.card = G.edgeFinset.card + 1 := by
  rw [G.edgeFinset_addEdge hn h, card_cons]

end AddEdge

section Restrict

variable [Fintype V] [DecidableRel G.Adj] (K : Finset V)

/-- The natural embedding from `{ x // x ∈ K }` to `V`, lifted to `Sym2`s. -/
def sym2SubtypeEmb : Sym2 { x // x ∈ K } ↪ Sym2 V where
  toFun := Sym2.map Subtype.val
  inj' a b := by refine' a.inductionOn₂ b _; simp

/-- The graph formed by retaining only those edges wholly within `K`, but keeping the
vertex set intact. -/
def restrictSubset : SimpleGraph V where
  Adj s t := G.Adj s t ∧ s ∈ K ∧ t ∈ K
  symm s t := by simp_all [adj_comm]

/-- The graph formed by retaining only those edges from `K` to `Kᶜ`. -/
def betweenSubset : SimpleGraph V where
  Adj s t := G.Adj s t ∧ ¬(s ∈ K ↔ t ∈ K)
  symm s t := by dsimp only; rw [adj_comm]; aesop

/-- The graph formed by retaining only those edges wholly within `K` and restricting
the vertex set to match. -/
def restrictSubtype : SimpleGraph K where
  Adj s t := G.Adj s t
  symm s t := by simp_all [adj_comm]

instance : DecidableRel (G.restrictSubtype K).Adj := by simp only [restrictSubtype]; infer_instance
instance : DecidableRel (G.restrictSubset K).Adj := by simp only [restrictSubset]; infer_instance
instance : DecidableRel (G.betweenSubset K).Adj := by simp only [betweenSubset]; infer_instance

theorem restrictSubset_le : G.restrictSubset K ≤ G := by
  intro a b; simp only [restrictSubset]; tauto

theorem restrictSubtype_map :
    (G.restrictSubtype K).map ⟨Subtype.val, Subtype.val_injective⟩ =
    (G.restrictSubset K) := by
  ext a b
  simp only [restrictSubtype, map_adj, Function.Embedding.coeFn_mk, Subtype.exists, exists_prop,
    restrictSubset]
  constructor <;> intro h
  · obtain ⟨_, _, _, _, _, _, _⟩ := h; aesop
  · use a, h.2.1, b, h.2.2; tauto

theorem restrictSubtype_edgeFinset_map :
    (G.restrictSubtype K).edgeFinset.map (sym2SubtypeEmb _) =
    (G.restrictSubset K).edgeFinset := by
  ext e
  refine' e.inductionOn _
  intro x y
  simp_rw [sym2SubtypeEmb, mem_map, Function.Embedding.coeFn_mk, restrictSubset, restrictSubtype,
    mem_edgeFinset, mem_edgeSet]
  constructor
  · rw [forall_exists_index]; intro a; refine' a.inductionOn _; intro u v ⟨m, q⟩
    simp only [Sym2.map_pair_eq, Sym2.eq] at q
    cases' q; aesop; rw [adj_comm]; aesop
  · simp_rw [and_imp]; intro ha mx my; use s(⟨x, mx⟩, ⟨y, my⟩); simpa using ha

theorem restrictSubtype_edgeFinset_card :
    (G.restrictSubtype K).edgeFinset.card = (G.restrictSubset K).edgeFinset.card := by
  rw [← restrictSubtype_edgeFinset_map, card_map]

theorem edgeFinset_decompose : G.edgeFinset =
    (G.restrictSubset K).edgeFinset ∪ (G.restrictSubset Kᶜ).edgeFinset ∪
    (G.betweenSubset K).edgeFinset := by
  ext e
  refine' e.inductionOn _
  intro x y
  simp_rw [mem_union, mem_edgeFinset, mem_edgeSet, restrictSubset, betweenSubset, mem_compl]
  tauto

theorem edgeFinset_decompose_card : G.edgeFinset.card =
    (G.restrictSubset K).edgeFinset.card + (G.restrictSubset Kᶜ).edgeFinset.card +
    (G.betweenSubset K).edgeFinset.card := by
  rw [G.edgeFinset_decompose K, card_union_of_disjoint, card_union_of_disjoint]
  · rw [disjoint_iff_inter_eq_empty]
    ext e; refine' e.inductionOn _; intro x y
    simp_rw [mem_inter, mem_edgeFinset, mem_edgeSet, restrictSubset, mem_compl]
    tauto
  · rw [disjoint_iff_inter_eq_empty]
    ext e; refine' e.inductionOn _; intro x y
    simp_rw [mem_inter, mem_union, mem_edgeFinset, mem_edgeSet, restrictSubset, betweenSubset,
      mem_compl]
    tauto

theorem betweenSubset_edgeFinset : (G.betweenSubset K).edgeFinset =
    Kᶜ.biUnion fun b ↦ (K.filter (G.Adj · b)).map (Sym2.congrEmb b) := by
  ext e; refine' e.inductionOn _; intro a b
  simp_rw [betweenSubset, mem_biUnion, Set.mem_toFinset, mem_edgeSet, Sym2.congrEmb, mem_map,
    mem_filter, Function.Embedding.coeFn_mk, Sym2.eq_iff, mem_compl]
  constructor
  · rw [and_imp]; intro j s; push_neg at s
    cases' s with h h
    · use b, h.2, a, ⟨h.1, j⟩; tauto
    · use a, h.1, b, ⟨h.2, j.symm⟩; tauto
  · simp only [forall_exists_index, and_imp]
    intro a' ma b' mb e q
    cases' q with h h
    · rw [h.1, h.2, adj_comm] at e; aesop
    · rw [h.1, h.2] at e; aesop

open BigOperators in
theorem betweenSubset_edgeFinset_card : (G.betweenSubset K).edgeFinset.card =
    ∑ b in Kᶜ, (K.filter (G.Adj · b)).card := by
  rw [betweenSubset_edgeFinset, card_biUnion]
  · simp
  · simp_rw [disjoint_iff_ne, mem_map, mem_filter, forall_exists_index, and_imp,
      Sym2.congrEmb, Function.Embedding.coeFn_mk]
    aesop

end Restrict
