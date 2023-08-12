-- lemma Finset.card_product_sum_left {α β : Type} [Fintype α] (r : Finset (α × β)) :
--     Finset.card r = ∑ a in α, Finset.card (r.filter (r.fst = a)) := by
--   sorry

-- instance [Field F] : IsDomain (MvPolynomial σ F) := sorry

theorem Polynomial.degree_map_eq_iff {R : Type u} {S : Type v}
  [Semiring R] [Semiring S] {f : R →+* S} (p : Polynomial R) :
    Polynomial.degree (Polynomial.map f p) = Polynomial.degree p
      ↔
    f (p.leadingCoeff) ≠ 0 := by
  -- apply degree_map_eq_of_injective
  sorry

theorem Polynomial.natDegree_map_eq_iff {R : Type u} {S : Type v}
  [Semiring R] [Semiring S] {f : R →+* S} (p : Polynomial R) :
    Polynomial.natDegree (Polynomial.map f p) = Polynomial.natDegree p
      ↔
    f (p.leadingCoeff) ≠ 0 := by
  -- TODO: seems like polynomial.map should not take a hom, but a zero to zero function
  constructor
  · sorry
  · intro h
    apply natDegree_map_of_leadingCoeff_ne_zero
    exact h
  -- sorry
