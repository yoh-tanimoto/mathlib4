import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.NormedSpace.Complemented

open Set FiniteDimensional MeasureTheory Measure Metric
open scoped Topology NNReal ENNReal

namespace Sard

noncomputable def bound (k : ℕ) (ρ : ℝ) : ℕ :=
  if k < ρ then 1 else ⌈k * (k - ρ) / ρ⌉₊ + 2

variable {k : ℕ} {ρ : ℝ}

lemma bound_of_lt (h : k < ρ) : bound k ρ = 1 := if_pos h
lemma bound_of_le (h : ρ ≤ k) : bound k ρ = ⌈k * (k - ρ) / ρ⌉₊ + 2 := if_neg h.not_lt

lemma bound_le_ceil_add_two : bound k ρ ≤ ⌈k * (k - ρ) / ρ⌉₊ + 2 := by
  unfold bound; split_ifs <;> simp [Nat.succ_le]

@[simp] lemma bound_same : bound k k = 2 := by simp [bound_of_le le_rfl]

@[simp]
lemma bound_eq_one : bound k ρ = 1 ↔ k < ρ := by simp [bound, imp_false]

lemma bound_pos (k ρ) : 0 < bound k ρ := by
  unfold bound; split_ifs <;> simp

lemma one_le_bound (k ρ) : 1 ≤ bound k ρ := bound_pos k ρ

@[simp]
lemma one_lt_bound : 1 < bound k ρ ↔ ρ ≤ k := by
  rw [(one_le_bound k ρ).lt_iff_ne, ne_comm, Ne.def, bound_eq_one, not_lt]

@[simp] lemma two_le_bound : 2 ≤ bound k ρ ↔ ρ ≤ k := one_lt_bound

@[gcongr]
lemma bound_mono_left {k l : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hkl : k ≤ l) :
    bound k ρ ≤ bound l ρ := by
  rcases lt_or_le ↑k ρ with hk | hk
  · simp only [bound_of_lt hk, one_le_bound]
  · rw [bound_of_le hk, bound_of_le (hk.trans <| Nat.mono_cast hkl)]
    gcongr
    rwa [sub_nonneg]

lemma bound_succ_succ_le (k : ℕ) (hρ : 0 < ρ) : bound (k + 1) (ρ + 1) ≤ bound k ρ := by
  rcases lt_or_le ↑k ρ with hlt | hle
  · rw [bound_of_lt hlt, bound_of_lt]; simpa
  · rw [bound_of_le hle, bound_of_le (by simpa)]
    gcongr ⌈(?_ : ℝ)⌉₊ + _
    push_cast
    simp only [add_sub_add_right_eq_sub, ← div_mul_eq_mul_div]
    gcongr ?_ * _; · rwa [sub_nonneg]
    rw [div_le_div_iff (by positivity) hρ]
    linarith

lemma le_bound_pred_pred (k : ℕ) (hρ : 1 < ρ) : bound k ρ ≤ bound (k - 1) (ρ - 1) := by
  cases k with
  | zero => simp [bound, one_pos.trans hρ, hρ]
  | succ k => simpa using bound_succ_succ_le k (sub_pos.2 hρ)

lemma le_bound_sub_nat (n : ℕ) (hρ : k < ρ) : bound n ρ ≤ bound (n - k) (ρ - k) := by
  induction k with
  | zero => simp
  | succ k ihk =>
    rw [Nat.cast_succ] at hρ
    calc
      bound n ρ ≤ bound (n - k) (ρ - k) := ihk <| by linarith
      _ ≤ bound (n - (k + 1)) (ρ - ↑(k + 1)) := by
        simp only [Nat.cast_add_one, sub_add_eq_sub_sub, ← Nat.sub_sub]
        apply le_bound_pred_pred
        rwa [lt_sub_iff_add_lt']

lemma ceil_div_lt_bound (hρ : 0 ≤ ρ) (hle : ρ ≤ k) : ⌈k / ρ⌉₊ < bound k ρ := by
  rcases hρ.eq_or_lt with rfl | hρ'; · simp [bound_pos]
  rw [bound_of_le hle, ← Nat.add_one_le_iff, ← Nat.ceil_add_one (by positivity), Nat.ceil_le]
  calc
    k / ρ + 1 ≤ k * (k - ρ) / ρ + 2 := by
      field_simp [div_le_div_right hρ']
      have : (1 : ℝ) ≤ k := by exact_mod_cast hρ'.trans_le hle
      nlinarith
    _ ≤ _ := by simp [Nat.le_ceil]

lemma floor_div_lt_bound (hρ : 0 ≤ ρ) : ⌊k / ρ⌋₊ < bound k ρ := by
  rcases lt_or_le ↑k ρ with hlt | hle
  · rw [Nat.floor_eq_zero.2]
    exacts [bound_pos _ _, (div_lt_one <| k.cast_nonneg.trans_lt hlt).2 hlt]
  · exact (Nat.floor_le_ceil _).trans_lt (ceil_div_lt_bound hρ hle)

/-- Inequality (7) from the paper. We drop the unneeded assumption `3 ≤ ν(k, ρ)`
which is equivalent to `2 * ρ ≤ k`.

`k` here is `k - 1` in the paper. -/
lemma le_bound_succ_left_add_one (hρ : 0 < ρ) :
    bound k ρ + ⌊(k + 1) / ρ⌋₊ ≤ bound (k + 1) ρ + 1 := by
  rcases lt_or_le ↑k ρ with hlt | hle
  · rw [bound_of_lt hlt, add_comm, ← Nat.cast_add_one]
    exact add_le_add (floor_div_lt_bound hρ.le).le le_rfl
  rw [bound_of_le hle, bound_of_le (hle.trans (by simp))]
  have hkρ : 0 ≤ k - ρ := sub_nonneg.2 hle
  -- Get rid of some floor/ceil functions
  calc
    ⌈k * (k - ρ) / ρ⌉₊ + 2 + ⌊(k + 1) / ρ⌋₊ = ⌈k * (k - ρ) / ρ + ⌊(k + 1) / ρ⌋₊⌉₊ + 2 := by
      rw [add_right_comm, ← Nat.ceil_add_nat]; positivity
    _ ≤ ⌈(k + 1) * (k + 1 - ρ) / ρ + 1⌉₊ + 2 := ?_
    _ ≤ ⌈↑(k + 1) * (↑(k + 1) - ρ) / ρ⌉₊ + 1 + 2 := by simp [Nat.le_ceil]
  gcongr ⌈(?_ : ℝ)⌉₊ + 2
  calc
    k * (k - ρ) / ρ + ⌊(k + 1) / ρ⌋₊ ≤ k * (k - ρ) / ρ + (k + 1) / ρ := by
      gcongr; apply Nat.floor_le; positivity
    _ ≤ (k + 1) * (k + 1 - ρ) / ρ + 1 := by
      field_simp [div_le_div_right hρ]
      nlinarith

/-- Inequality (7) from the paper. We drop the unneeded assumption `3 ≤ ν(k, ρ)`
which is equivalent to `2 * ρ ≤ k`.

`k` here is `k - 1` in the paper. -/
lemma le_bound_succ_left (hρ : 0 < ρ) :
    bound k ρ + ⌊(k + 1) / ρ⌋₊ - 1 ≤ bound (k + 1) ρ :=
  Nat.sub_le_of_le_add <| le_bound_succ_left_add_one hρ

section Prod

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Module.Finite ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace G] [BorelSpace G]
  {f : E × F → E × G} {ρ : ℝ}

lemma main_prod (hf : ContDiffAt ℝ (bound (finrank ℝ F) ρ) f 0) (hρ : 0 < ρ)
    (hf' : HasFDerivAt f (.prodMap (.id _ _) 0 : E × F →L[ℝ] E × G) 0) :
    ∃ U ∈ 𝓝[{y | (fderiv ℝ f y : E × F →ₗ[ℝ] E × G).rank = finrank ℝ E}] 0,
      μH[finrank ℝ E + ρ] (f '' U) = 0 := by
  sorry

end Prod

section HausdorffMeasure

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
  {f : E → F} {r k : ℕ} {n : ℕ∞} {ρ : ℝ} {x : E}

#check Function.RightInverse
lemma main_local (hf : ContDiffAt ℝ n f x) (hρ : 0 < ρ) (hn : bound (finrank ℝ E - r) ρ ≤ n)
    (hr : (fderiv ℝ f x : E →ₗ[ℝ] F).rank = r) :
    ∃ U ∈ 𝓝[{y | (fderiv ℝ f y : E →ₗ[ℝ] F).rank = ↑r}] x, μH[r + ρ] (f '' U) = 0 := by
  borelize E
  have hn1 : 1 ≤ n := (Nat.one_le_cast.2 <| one_le_bound _ _).trans hn
  rcases lt_or_le ↑(finrank ℝ E) (r + ρ) with hlt | hrρm
  · rcases (hf.of_le hn1).exists_lipschitzOnWith with ⟨K, s, hsx, hfs⟩
    rcases Metric.mem_nhds_iff.1 hsx with ⟨ε, hε₀, hεs⟩
    refine ⟨_, inter_mem_nhdsWithin _ (ball_mem_nhds _ hε₀), nonpos_iff_eq_zero.1 ?_⟩
    calc
      μH[r + ρ] (f '' (_ ∩ ball x ε)) ≤ μH[r + ρ] (f '' ball x ε) := by
        gcongr; apply inter_subset_right
      _ ≤ (K : ℝ≥0∞) ^ (r + ρ) * μH[r + ρ] (ball x ε) :=
        (hfs.mono hεs).hausdorffMeasure_image_le (by positivity)
      _ = 0 := by
        simp [Real.hausdorffMeasure_of_finrank_lt hlt]
  have hrm : r ≤ finrank ℝ E := Nat.cast_le.1 (le_trans (by simp [hρ.le]) hrρm)
  set f' := fderiv ℝ f x
  set E' := LinearMap.range f'
  obtain ⟨g, hg⟩ := Submodule.ClosedComplemented.of_finiteDimensional E'
  set G' := LinearMap.ker g
  set e : F ≃L[ℝ] (E' × G') := .equivOfRightInverse g E'.subtypeL hg
  -- rcases (f'.codRestrict _ (LinearMap.mem_range_self f')).exists_right_inverse_of_surjective
  --   (f' : E →ₗ[ℝ] F).range_rangeRestrict with ⟨g, hg⟩
  
end HausdorffMeasure

end Sard

open FiniteDimensional MeasureTheory Measure Sard

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

section HausdorffMeasure

variable [MeasurableSpace F] [BorelSpace F] {f : E → F} {r : ℕ} {n : ℕ∞} {ρ : ℝ}

theorem hausdorffMeasure_image_setOf_finrank_eq (hf : ContDiff ℝ n f) (hρ : 0 < ρ)
    (hn : bound (finrank ℝ E - r) ρ ≤ n) :
    μH[r + ρ] (f '' {x | (fderiv ℝ f x : E →ₗ[ℝ] F).rank = ↑r}) = 0 := by
  set s := {x | (fderiv ℝ f x : E →ₗ[ℝ] F).rank = ↑r}
  have : ∀ x ∈ s, ∃ U ∈ 𝓝[s] x, μH[r + ρ] (f '' U) = 0 := fun x hx ↦
    Sard.main_local hf.contDiffAt hρ hn hx
  choose! U hU hUμ using this
  rcases TopologicalSpace.countable_cover_nhdsWithin hU with ⟨t, hts, htc, ht⟩
  refine measure_mono_null (image_subset _ ht) ?_
  rw [image_iUnion₂]
  exact (measure_biUnion_null_iff htc).2 fun x hx ↦ hUμ _ (hts hx)

/-- Sard's Theorem -/
theorem hausdorffMeasure_image_setOf_finrank_le (hf : ContDiff ℝ n f) (hρ : 0 < ρ)
    (hn : bound (finrank ℝ E - r) ρ ≤ n) :
    μH[r + ρ] (f '' {x | (fderiv ℝ f x : E →ₗ[ℝ] F).rank ≤ ↑r}) = 0 := by
  suffices μH[r + ρ] (f '' ⋃ k ≤ r, {x | (fderiv ℝ f x : E →ₗ[ℝ] F).rank = ↑k}) = 0 by
    refine measure_mono_null (image_subset _ fun x hx ↦ ?_) this
    simp only [mem_iUnion, exists_prop]
    exact Cardinal.exists_nat_eq_of_le_nat hx
  rw [image_iUnion₂]
  refine (measure_biUnion_null_iff (Set.to_countable _)).2 fun k (hk : k ≤ r) ↦ ?_
  rcases le_iff_exists_add.1 hk with ⟨l, rfl⟩
  rw [Nat.cast_add, add_assoc]
  apply hausdorffMeasure_image_setOf_finrank_eq hf
  · positivity
  · calc
      (bound (finrank ℝ E - k) (l + ρ) : ℕ∞) ≤ bound (finrank ℝ E - k - l) (l + ρ - l) :=
        Nat.mono_cast <| le_bound_sub_nat _ <| by simpa
      _ ≤ n := by simpa [Nat.sub_sub]
