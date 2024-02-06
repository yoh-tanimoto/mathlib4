import Mathlib.Analysis.NormedSpace.Star.Spectrum
import Mathlib.Analysis.NormedSpace.Star.CFC.CFCRestricts

/-!
# Another approach with less DTT hell?
-/

section Basic

class CFC (R : Type*) {A : Type*} (p : outParam (A → Prop)) [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] where
  /-- The star algebra homomorphisms. -/
  toStarAlgHom {a} (ha : p a) : C(spectrum R a, R) →⋆ₐ[R] A
  /-- A continuous functional calculus is a closed embedding. -/
  hom_closedEmbedding {a} (ha : p a) : ClosedEmbedding <| toStarAlgHom ha
  /-- A continuous functional calculus extends the polynomial functional calculus. -/
  hom_map_id {a} (ha : p a) : toStarAlgHom ha ((ContinuousMap.id R).restrict <| spectrum R a) = a
  /-- A continuous functional calculus satisfies the spectral mapping property. -/
  hom_map_spectrum {a} (ha : p a) : ∀ f, spectrum R (toStarAlgHom ha f) = Set.range f
  /-- Predicate preserving -/
  hom_predicate_preserving {a} (ha : p a) : ∀ f, p (toStarAlgHom ha f)

structure CFCCore {R A : Type*} [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] (s : Set R) (a : A) extends C(s, R) →⋆ₐ[R] A where
  map_id' : toStarAlgHom ((ContinuousMap.id R).restrict s) = a
  map_continuous' : Continuous toStarAlgHom

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
variable [TopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
variable [Algebra R A] [CFC R p]

/- Note: since `spectrum R a` is closed, we may always extend `f : C(spectrum R a, R)` to a function
of type `C(R, R)` by the Tietze extension theorem (assuming `R` is either `ℝ`, `ℂ` or `ℝ≥0`). -/

/-- The star algebra homomorphism underlying a instance of the continuous functional calculus.
Version for continuous functions on the spectrum.

In this case, the user must supply the fact that `a` satisfies the predicate `p`, for otherwise it
may be the case that no star algebra homomorphism exists. For instance if `R := ℝ` and `a` is an
element whose spectrum (in `ℂ`) is disjoint from `ℝ`, then `spectrum ℝ a = ∅` and so there can be
no star algebra homomorphism between these spaces. -/
def cfcSpec {a : A} (ha : p a) : C(spectrum R a, R) →⋆ₐ[R] A :=
  CFC.toStarAlgHom ha

lemma cfcSpec_closedEmbedding {a : A} (ha : p a) :
    ClosedEmbedding <| (cfcSpec ha : C(spectrum R a, R) →⋆ₐ[R] A) :=
  CFC.hom_closedEmbedding ha

lemma cfcSpec_map_id {a : A} (ha : p a) :
    cfcSpec ha ((ContinuousMap.id R).restrict <| spectrum R a) = a :=
  CFC.hom_map_id ha

lemma cfcSpec_map_spectrum {a : A} (ha : p a) (f : C(spectrum R a, R)) :
    spectrum R (cfcSpec ha f) = Set.range f :=
  CFC.hom_map_spectrum ha f

lemma cfcSpec_predicate_preserving {a : A} (ha : p a) (f : C(spectrum R a, R)) :
    p (cfcSpec ha f) :=
  CFC.hom_predicate_preserving ha f

theorem cfcSpec_comp {a : A} (ha : p a) (f : C(spectrum R a, R))
    [Subsingleton (CFCCore (spectrum R (cfcSpec ha f)) (cfcSpec ha f))]
    (f' : C(spectrum R a, spectrum R (cfcSpec ha f)))
    (hff' : ∀ x, f x = f' x) (g : C(spectrum R (cfcSpec ha f), R)) :
    cfcSpec ha (g.comp f') = cfcSpec (cfcSpec_predicate_preserving ha f) g := by
  let cfc₂ : CFCCore (spectrum R (cfcSpec ha f)) (cfcSpec ha f) :=
    { toStarAlgHom := cfcSpec (cfcSpec_predicate_preserving ha f)
      map_id' := cfcSpec_map_id (cfcSpec_predicate_preserving ha f)
      map_continuous' := (cfcSpec_closedEmbedding (cfcSpec_predicate_preserving ha f)).continuous }
  let cfc₁ : CFCCore (spectrum R (cfcSpec ha f)) (cfcSpec ha f) :=
    { toStarAlgHom := (cfcSpec ha).comp <| ContinuousMap.compStarAlgHom' R R f'
      map_id' := by
        simp only [StarAlgHom.comp_apply, ContinuousMap.compStarAlgHom'_apply]
        congr
        ext x
        simp [hff']
      map_continuous' := (cfcSpec_closedEmbedding ha).continuous.comp f'.continuous_comp_left }
  have := congr_arg CFCCore.toStarAlgHom <| Subsingleton.elim cfc₁ cfc₂
  exact DFunLike.congr_fun this g

@[simps]
def ContinuousMap.evalStarAlgHom (r : R) : C(R, R) →⋆ₐ[R] R where
  toFun f := f r
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

/- In practice, we expec this to be the most useful version of the continuous functional calculus.
It is also uniquely determined (by appealing to the Stone-Weierstrass and the Tietze extension
theorems), although I haven't proven that here. -/

/-- The star algebra homomorphism underlying a instance of the continuous functional calculus.
Version for continuous functions on the full space. -/
def cfc [StarModule R A] (a : A) [DecidablePred p] : C(R, R) →⋆ₐ[R] A :=
  if ha : p a
    then (cfcSpec ha).comp <| (ContinuousMap.id R |>.restrict <| spectrum R a).compStarAlgHom' R R
    else (StarAlgHom.ofId R A).comp (ContinuousMap.evalStarAlgHom 0)

lemma cfc_def [StarModule R A] {a : A} [DecidablePred p] (ha : p a) :
    cfc a = ((cfcSpec ha).comp <| (ContinuousMap.id R |>.restrict <| spectrum R a).compStarAlgHom' R R) :=
  dif_pos ha

lemma cfc_id [StarModule R A] {a : A} [DecidablePred p] (ha : p a) :
    cfc a (ContinuousMap.id R) = a := by
  simp [cfc_def ha, cfcSpec_map_id ha]

lemma cfc_map_spectrum [StarModule R A] {a : A} [DecidablePred p] (ha : p a) (f : C(R, R)) :
    spectrum R (cfc a f) = f '' spectrum R a := by
  simp [cfc_def ha, cfcSpec_map_spectrum ha, Set.range_comp]

lemma cfc_apply [StarModule R A] {a : A} [DecidablePred p] (ha : p a) (f : C(R, R)) :
    cfc a f = cfcSpec ha (f.restrict <| spectrum R a) := by
  rw [cfc_def ha, StarAlgHom.comp_apply, ContinuousMap.compStarAlgHom'_apply]
  congr

lemma cfc_def' [StarModule R A] {a : A} [DecidablePred p] (ha : ¬ p a) :
    cfc a = (StarAlgHom.ofId R A).comp (ContinuousMap.evalStarAlgHom 0) :=
  dif_neg ha

lemma cfc_predicate_preserving [StarModule R A] {a : A} [DecidablePred p] (ha : p a) (f : C(R, R)) :
    p (cfc a f) := by
  rw [cfc_def ha]
  exact cfcSpec_predicate_preserving ha _

variable [∀ a : A, Subsingleton (CFCCore (spectrum R a) a)]

lemma cfc_comp [StarModule R A] {a : A} [DecidablePred p] (ha : p a) (f g : C(R, R)) :
    cfc a (g.comp f) = cfc (cfc a f) g := by
  simp_rw [cfc_apply ha, cfc_apply (cfcSpec_predicate_preserving ha _)]
  rw [← cfcSpec_comp ha _ _]
  rotate_right
  · exact ContinuousMap.mk _ <| (map_continuous (f.restrict (spectrum R a))).codRestrict
      fun x ↦ by rw [ContinuousMap.restrict_apply, cfcSpec_map_spectrum]; exact ⟨x, rfl⟩
  · congr
  · simp

lemma cfc_eq_of_eqOn [StarModule R A] {a : A} [DecidablePred p] (ha : p a) (f g : C(R, R))
    (hfg : (spectrum R a).EqOn f g) :
    cfc a f = cfc a g := by
  simp only [cfc_def ha, StarAlgHom.comp_apply, ContinuousMap.compStarAlgHom'_apply]
  congr! 1
  ext x
  exact hfg x.2

lemma cfc_eqOn_of_eq [StarModule R A] {a : A} [DecidablePred p] (ha : p a) (f g : C(R, R))
    (hfg : cfc a f = cfc a g) : (spectrum R a).EqOn f g := by
  simp_rw [cfc_apply ha] at hfg
  apply (cfcSpec_closedEmbedding ha).injective at hfg
  rw [← Set.restrict_eq_restrict_iff]
  congrm(⇑$(hfg))

lemma eq_algebraMap_of_spectrum_singleton [StarModule R A] {a : A} [DecidablePred p] (ha : p a)
    {r : R} (h_spec : spectrum R a = {r}) : a = algebraMap R A r := by
  simpa [cfc_id ha, AlgHomClass.commutes] using
    cfc_eq_of_eqOn ha (ContinuousMap.id R) (algebraMap R C(R, R) r) <| by rw [h_spec]; simp

lemma eq_zero_of_spectrum_eq_zero [StarModule R A] {a : A} [DecidablePred p] (ha : p a)
    (h_spec : spectrum R a = {0}) : a = 0 := by
  simpa using eq_algebraMap_of_spectrum_singleton ha h_spec

lemma eq_one_of_spectrum_eq_one [StarModule R A] {a : A} [DecidablePred p] (ha : p a)
    (h_spec : spectrum R a = {1}) : a = 1 := by
  simpa using eq_algebraMap_of_spectrum_singleton ha h_spec

/- This is a version of the continuous functional calculus for bare functions. It is most useful
when one prefers unbundled objects. For instance, the most general version of the composition
theorem is easily statable for `cfcBare`. -/
def cfcBare (a : A) (f : R → R) [DecidablePred p]
    [DecidablePred (fun x : A ↦ ContinuousOn f <| spectrum R x)] : A :=
  if h : p a ∧ ContinuousOn f (spectrum R a)
    then cfcSpec h.1 ⟨_, h.2.restrict⟩
    else 0 --algebraMap R A (f 0) -- chosen to agree with `cfc`

lemma cfcBare_apply {a : A} {f : R → R} [DecidablePred p]
    [DecidablePred (fun x : A ↦ ContinuousOn f <| spectrum R x)] (ha : p a)
    (hf : ContinuousOn f (spectrum R a)) :
    cfcBare a f = cfcSpec ha ⟨_, hf.restrict⟩ :=
  dif_pos ⟨ha, hf⟩

lemma cfcBare_apply_of_not_and {a : A} {f : R → R} [DecidablePred p]
    [DecidablePred (fun x : A ↦ ContinuousOn f <| spectrum R x)]
    (ha : ¬ (p a ∧ ContinuousOn f (spectrum R a))) :
    cfcBare a f = 0 :=
  dif_neg ha

lemma cfcBare_apply_of_not {a : A} {f : R → R} [DecidablePred p]
    [DecidablePred (fun x : A ↦ ContinuousOn f <| spectrum R x)] (ha : ¬ p a) :
    cfcBare a f = 0 :=
  dif_neg (not_and_of_not_left _ ha)

lemma cfcBare_apply_of_not' {a : A} {f : R → R} [DecidablePred p]
    [DecidablePred (fun x : A ↦ ContinuousOn f <| spectrum R x)]
    (hf : ¬ ContinuousOn f (spectrum R a)) :
    cfcBare a f = 0 :=
  dif_neg (not_and_of_not_right _ hf)

/- lemma cfc_eq_cfcBare [StarModule R A] (a : A) (f : C(R, R)) [DecidablePred p]
    [DecidablePred (fun x : A ↦ ContinuousOn f <| spectrum R x)] :
    cfc a f = cfcBare a f := by
  rw [cfc, cfcBare]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact False.elim <| h₂ ⟨h₁, f.continuous.continuousOn⟩
  · exact False.elim <| h₁ h₂.1
  · rfl-/

variable [DecidablePred p] [∀ x : A, ∀ f : R → R, Decidable (ContinuousOn f <| spectrum R x)]

lemma cfcBare_predicate_preserving {a : A} {f : R → R} (ha : p a)
    (hf : ContinuousOn f (spectrum R a)) :
    p (cfcBare a f) :=
  cfcBare_apply ha hf ▸ cfcSpec_predicate_preserving ha _

lemma cfcBare_comp {a : A} {f g : R → R} (ha : p a) (hf : ContinuousOn f (spectrum R a))
    (hg : ContinuousOn g (f '' spectrum R a)) :
    cfcBare a (g ∘ f) = cfcBare (cfcBare a f) g := by
  have := hg.comp hf <| (spectrum R a).mapsTo_image f
  have sp_eq : spectrum R (cfcSpec ha (ContinuousMap.mk _ hf.restrict)) = f '' (spectrum R a) := by
    rw [cfcSpec_map_spectrum ha]
    ext
    simp
  rw [cfcBare_apply ha this, cfcBare_apply ha hf, cfcBare_apply (cfcSpec_predicate_preserving ha _)]
  swap
  · convert hg
  · rw [← cfcSpec_comp _ _]
    rotate_left
    · exact ContinuousMap.mk _ <| hf.restrict.codRestrict fun x ↦ by rw [sp_eq]; use x.1; simp
    · exact fun _ ↦ rfl
    · congr


----- basic applications

lemma cfcBare_eq_of_eqOn {a : A} {f g : R → R} (hfg : (spectrum R a).EqOn f g) :
    cfcBare a f = cfcBare a g := by
  by_cases h : p a ∧ ContinuousOn g (spectrum R a)
  · rw [cfcBare_apply h.1 (h.2.congr hfg), cfcBare_apply h.1 h.2]
    congr
    exact Set.restrict_eq_iff.mpr hfg
  · obtain (ha | hg) := Decidable.not_and_iff_or_not _ _ |>.mp h
    · simp [cfcBare_apply_of_not ha]
    · rw [cfcBare_apply_of_not' hg, cfcBare_apply_of_not']
      exact fun hf ↦ hg (hf.congr hfg.symm)


lemma cfcBare_eqOn_of_eq {a : A} {f g : R → R} (ha : p a) (hf : ContinuousOn f (spectrum R a))
    (hg : ContinuousOn g (spectrum R a)) (h : cfcBare a f = cfcBare a g) :
    (spectrum R a).EqOn f g := by
  rw [cfcBare_apply ha hf, cfcBare_apply ha hg] at h
  have := (cfcSpec_closedEmbedding ha (R := R)).inj h
  intro x hx
  congrm($(this) ⟨x, hx⟩)

lemma cfcBare_id {a : A} (ha : p a) : cfcBare a (id : R → R) = a :=
  cfcBare_apply (R := R) ha continuousOn_id ▸ cfcSpec_map_id ha

lemma cfcBare_pow {a : A} (ha : p a) (n : ℕ) : cfcBare a (fun x : R ↦ x ^ n) = a ^ n := by
  nth_rw 2 [← cfcSpec_map_id ha (R := R)]
  rw [cfcBare_apply ha (continuous_pow n).continuousOn, ← map_pow]
  congr

lemma cfcBare_pow_comm {a : A} (ha : p a) (n : ℕ) {f : R → R}
    (hf : ContinuousOn f ((· ^ n) '' (spectrum R a))) :
    cfcBare a (fun x ↦ f (x ^ n)) = cfcBare (a ^ n) f := by
  rw [← Function.comp, cfcBare_comp ha (continuous_pow n).continuousOn hf, cfcBare_pow ha]

lemma cfcBare_smul {a : A} (ha : p a) (r : R) : cfcBare a (r * ·) = r • a := by
  nth_rw 2 [← cfcSpec_map_id ha (R := R)]
  rw [← map_smul, cfcBare_apply ha (continuous_mul_left r).continuousOn]
  congr

lemma cfcBare_smul_comm {a : A} (ha : p a) (r : R) {f : R → R}
    (hf : ContinuousOn f ((r * ·) '' (spectrum R a))) :
    cfcBare a (fun x ↦ f (r * x)) = cfcBare (r • a) f := by
  rw [← Function.comp, cfcBare_comp ha (continuous_mul_left r).continuousOn hf, cfcBare_smul ha r]

lemma cfcBare_star_map {a : A} {f : R → R} :
    cfcBare a (star f) = star (cfcBare a f) := by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · rw [cfcBare_apply h.1 h.2, ← map_star,
      cfcBare_apply h.1 (show ContinuousOn (star f) _ from h.2.star)]
    congr
  · obtain (ha | hf) := Decidable.not_and_iff_or_not _ _ |>.mp h
    · simp [cfcBare_apply_of_not ha]
    · rw [cfcBare_apply_of_not' hf, cfcBare_apply_of_not', star_zero]
      exact fun hf_star ↦ hf <| by simpa using hf_star.star

lemma cfcBare_star {a : A} (ha : p a) : cfcBare a (star : R → R) = star a := by
  nth_rw 2 [← cfcSpec_map_id ha (R := R)]
  rw [← map_star, cfcBare_apply ha continuous_star.continuousOn]
  congr

lemma cfcBare_star_comm {a : A} (ha : p a) {f : R → R}
    (hf : ContinuousOn f (star '' (spectrum R a))) :
    cfcBare a (fun x ↦ f (star x)) = cfcBare (star a) f := by
  rw [← Function.comp, cfcBare_comp ha continuous_star.continuousOn hf, cfcBare_star ha]

lemma cfcBare_mul {a : A} {f g : R → R} (hf : ContinuousOn f (spectrum R a))
    (hg : ContinuousOn g (spectrum R a)) :
    cfcBare a (f * g) = cfcBare a f * cfcBare a g := by
  by_cases ha : p a
  · rw [cfcBare_apply ha hf, cfcBare_apply ha hg, ← map_mul,
      show f * g = fun x ↦ f x * g x from rfl, cfcBare_apply ha (hf.mul hg)]
    congr
  · simp [cfcBare_apply_of_not ha]

end Basic

section Inv

variable {R A : Type*} {p : A → Prop} [Semifield R] [StarRing R] [MetricSpace R]
variable [TopologicalSemiring R] [ContinuousStar R] [HasContinuousInv₀ R] [TopologicalSpace A]
variable [Ring A] [StarRing A] [Algebra R A] [CFC R p]
variable [∀ a : A, Subsingleton (CFCCore (spectrum R a) a)]
variable [DecidablePred p] [∀ x : A, ∀ f : R → R, Decidable (ContinuousOn f <| spectrum R x)]

lemma cfcBare_inv {a : Aˣ} (ha : p a) :
    cfcBare (a : A) (fun x ↦ x⁻¹ : R → R) = a⁻¹ := by
  rw [← a.mul_left_inj, a.inv_mul]
  have : ContinuousOn (· ⁻¹) (spectrum R (a : A)) := continuousOn_inv₀.mono <| by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_not_mem R a.isUnit
  nth_rw 2 [← cfcSpec_map_id ha (R := R)]
  rw [cfcBare_apply ha this, ← map_mul]
  convert map_one (cfcSpec ha)
  all_goals try infer_instance -- after merging master, `convert` got worse
  ext x
  simp [inv_mul_cancel (fun hx ↦ spectrum.zero_not_mem R a.isUnit (hx ▸ x.2))]

lemma cfcBare_inv_comm {a : Aˣ} (ha : p a) {f : R → R}
    (hf : ContinuousOn f ((· ⁻¹) '' (spectrum R (a : A)))) :
    cfcBare (a : A) (fun x ↦ f x⁻¹) = cfcBare (↑a⁻¹ : A) f := by
  rw [← Function.comp, cfcBare_comp ha _ hf, cfcBare_inv ha]
  exact continuousOn_inv₀.mono <| by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_not_mem R a.isUnit

-- zpow

end Inv

section Neg

variable {R A : Type*} {p : A → Prop} [CommRing R] [StarRing R] [MetricSpace R]
variable [TopologicalRing R] [ContinuousStar R] [TopologicalSpace A]
variable [Ring A] [StarRing A] [Algebra R A] [CFC R p]
variable [∀ a : A, Subsingleton (CFCCore (spectrum R a) a)]
variable [DecidablePred p] [∀ x : A, ∀ f : R → R, Decidable (ContinuousOn f <| spectrum R x)]

lemma cfcBare_neg {a : A} (ha : p a) :
    cfcBare (a : A) (fun x ↦ -x : R → R) = -a := by
  apply add_right_injective a
  simp only [add_right_neg]
  nth_rw 1 [← cfcSpec_map_id ha (R := R)]
  rw [cfcBare_apply ha continuous_neg.continuousOn, ← map_add]
  convert map_zero (cfcSpec ha)
  all_goals try infer_instance -- again, `convert` is worse, maybe because of #8386
  ext
  simp

lemma cfcBare_neg_comm {a : A} (ha : p a) {f : R → R}
    (hf : ContinuousOn f ((-·) '' (spectrum R (a : A)))) :
    cfcBare (a : A) (fun x ↦ f (-x)) = cfcBare (-a) f := by
  rw [← Function.comp, cfcBare_comp ha continuous_neg.continuousOn hf, cfcBare_neg ha]

end Neg

section Restrict

variable {R S A : Type*} {p q : A → Prop}
variable [CommSemiring R] [StarRing R] [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R]
variable [CommSemiring S] [StarRing S] [MetricSpace S] [TopologicalSemiring S] [ContinuousStar S]
variable [TopologicalSpace A] [Ring A] [StarRing A] [Algebra S A] [CFC S q]
variable [Algebra R S] [Algebra R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]

-- we should be able to get rid of the compactness and isometry conditions below in favor of
-- something weaker, but they hold in the situations we care about, so we leave them for now.
@[reducible]
def cfc_of_spectrumRestricts [CompleteSpace R]
    (f : C(S, R)) (h_isom : Isometry (algebraMap R S)) (h : ∀ a, p a ↔ q a ∧ SpectrumRestricts a f)
    (h_cpct : ∀ a, q a → CompactSpace (spectrum S a)):
    CFC R p where
  toStarAlgHom {a} ha := ((h a).mp ha).2.starAlgHom (cfcSpec ((h a).mp ha).1 (R := S)) f
  hom_closedEmbedding {a} ha := by
    apply ClosedEmbedding.comp (cfcSpec_closedEmbedding ((h a).mp ha).1)
    simp only [RingHom.coe_coe, StarAlgHom.coe_toAlgHom, StarAlgHom.comp_apply,
      ContinuousMap.compStarAlgHom'_apply, ContinuousMap.compStarAlgHom_apply]
    have : CompactSpace (spectrum S a) := h_cpct a ((h a).mp ha).1
    have : CompactSpace (spectrum R a) := ((h a).mp ha).2.compactSpace
    refine Isometry.closedEmbedding ?_
    simp only [isometry_iff_dist_eq]
    refine fun g₁ g₂ ↦ le_antisymm ?_ ?_
    all_goals refine (ContinuousMap.dist_le dist_nonneg).mpr fun x ↦ ?_
    · simpa [h_isom.dist_eq] using ContinuousMap.dist_apply_le_dist _
    · obtain ⟨y, y_mem, hy⟩ : (x : R) ∈ f '' spectrum S a := ((h a).mp ha).2.image.symm ▸ x.2
      lift y to spectrum S a using y_mem
      refine le_of_eq_of_le ?_ <| ContinuousMap.dist_apply_le_dist y
      simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, StarAlgHom.ofId_apply]
      rw [h_isom.dist_eq]
      congr <;> exact Subtype.ext hy.symm
  hom_map_id {a} ha := by
    simp only [SpectrumRestricts.starAlgHom_apply]
    convert cfcSpec_map_id ((h a).mp ha).1
    ext x
    exact ((h a).mp ha).2.rightInvOn x.2
  hom_map_spectrum {a} ha g := by
    rw [SpectrumRestricts.starAlgHom_apply]
    simp only [← @spectrum.preimage_algebraMap R S, cfcSpec_map_spectrum]
    ext x
    constructor
    · rintro ⟨y, hy⟩
      have := congr_arg f hy
      simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, StarAlgHom.ofId_apply] at this
      rw [((h a).mp ha).2.left_inv _, ((h a).mp ha).2.left_inv _] at this
      exact ⟨_, this⟩
    · rintro ⟨y, rfl⟩
      rw [Set.mem_preimage]
      refine' ⟨⟨algebraMap R S y, spectrum.algebraMap_mem R S y.prop⟩, _⟩
      simp only [ContinuousMap.coe_mk, ContinuousMap.comp_apply, StarAlgHom.ofId_apply]
      congr
      exact Subtype.ext (((h a).mp ha).2.left_inv y)
  hom_predicate_preserving {a} ha g := by
    rw [h]
    refine ⟨cfcSpec_predicate_preserving _ _, ?_⟩
    refine { rightInvOn := fun s hs ↦ ?_, left_inv := ((h a).mp ha).2.left_inv }
    rw [SpectrumRestricts.starAlgHom_apply, cfcSpec_map_spectrum] at hs
    obtain ⟨r, rfl⟩ := hs
    simp [((h a).mp ha).2.left_inv _]


end Restrict
