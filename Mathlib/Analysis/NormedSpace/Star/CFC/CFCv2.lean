import Mathlib.Analysis.NormedSpace.Star.Spectrum
import Mathlib.Tactic.FunProp.Continuous
import Mathlib.Analysis.NormedSpace.Star.CFC.CFCRestricts

/-!
# Another approach with less DTT hell?
-/

section move

-- MOVE ME
lemma map_mem_unitary {F R S : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S] [FunLike F R S]
    [StarHomClass F R S] [MonoidHomClass F R S] (f : F) {r : R} (hr : r ∈ unitary R) :
    f r ∈ unitary S := by
  rw [unitary.mem_iff] at hr
  simpa [map_star, map_mul] using And.intro congr(f $(hr.1)) congr(f $(hr.2))

-- MOVE ME; also prove that it plays nice with `Units.map`
/-- The group homomorphism between unitary subgroups of star monoids induced by a star
homomorphism -/
def unitary.map {F R S : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S] [FunLike F R S]
    [StarHomClass F R S] [MonoidHomClass F R S] (f : F) :
    unitary R →* unitary S where
  toFun := Subtype.map f (fun _ ↦ map_mem_unitary f)
  map_one' := Subtype.ext <| map_one f
  map_mul' _ _ := Subtype.ext <| map_mul f _ _

-- MOVE ME
-- currently, we can't phrase this nicely because `Units.map` takes a `MonoidHom`, not a
-- `MonoidHomClass`.
lemma unitary.toUnits_comp_map {F R S : Type*} [Monoid R] [StarMul R] [Monoid S] [StarMul S]
    [FunLike F R S] [StarHomClass F R S] [MonoidHomClass F R S] (f : F) :
    unitary.toUnits.comp (unitary.map f) = (Units.map f).comp unitary.toUnits := by
  ext; rfl

end move

section Basic

class CFC (R : Type*) {A : Type*} (p : outParam (A → Prop)) [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] where
  /-- The star algebra homomorphisms. -/
  toStarAlgHom {a} (ha : p a) : C(spectrum R a, R) →⋆ₐ[R] A
  /-- A continuous functional calculus is a closed embedding. -/
  hom_closedEmbedding {a} (ha : p a) : ClosedEmbedding <| toStarAlgHom ha
  /-- A continuous functional calculus extends the polynomial functional calculus. -/
  hom_id {a} (ha : p a) : toStarAlgHom ha ((ContinuousMap.id R).restrict <| spectrum R a) = a
  /-- A continuous functional calculus satisfies the spectral mapping property. -/
  hom_map_spectrum {a} (ha : p a) : ∀ f, spectrum R (toStarAlgHom ha f) = Set.range f
  /-- Predicate preserving -/
  predicate_hom {a} (ha : p a) : ∀ f, p (toStarAlgHom ha f)

structure CFCCore {R A : Type*} [CommSemiring R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [TopologicalSpace A] [Algebra R A] (s : Set R) (a : A) extends C(s, R) →⋆ₐ[R] A where
  map_id' : toStarAlgHom ((ContinuousMap.id R).restrict s) = a
  map_continuous' : Continuous toStarAlgHom

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
variable [TopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
variable [Algebra R A] [CFC R p]

section cfcSpec

variable {a : A} (ha : p a)

/- Note: since `spectrum R a` is closed, we may always extend `f : C(spectrum R a, R)` to a function
of type `C(R, R)` by the Tietze extension theorem (assuming `R` is either `ℝ`, `ℂ` or `ℝ≥0`). -/

/-- The star algebra homomorphism underlying a instance of the continuous functional calculus.
Version for continuous functions on the spectrum.

In this case, the user must supply the fact that `a` satisfies the predicate `p`, for otherwise it
may be the case that no star algebra homomorphism exists. For instance if `R := ℝ` and `a` is an
element whose spectrum (in `ℂ`) is disjoint from `ℝ`, then `spectrum ℝ a = ∅` and so there can be
no star algebra homomorphism between these spaces. -/
def cfcSpec : C(spectrum R a, R) →⋆ₐ[R] A :=
  CFC.toStarAlgHom ha

lemma cfcSpec_closedEmbedding :
    ClosedEmbedding <| (cfcSpec ha : C(spectrum R a, R) →⋆ₐ[R] A) :=
  CFC.hom_closedEmbedding ha

lemma cfcSpec_map_id :
    cfcSpec ha ((ContinuousMap.id R).restrict <| spectrum R a) = a :=
  CFC.hom_id ha

lemma cfcSpec_map_spectrum (f : C(spectrum R a, R)) :
    spectrum R (cfcSpec ha f) = Set.range f :=
  CFC.hom_map_spectrum ha f

lemma cfcSpec_predicate (f : C(spectrum R a, R)) :
    p (cfcSpec ha f) :=
  CFC.predicate_hom ha f

theorem cfcSpec_comp (f : C(spectrum R a, R))
    [Subsingleton (CFCCore (spectrum R (cfcSpec ha f)) (cfcSpec ha f))]
    (f' : C(spectrum R a, spectrum R (cfcSpec ha f)))
    (hff' : ∀ x, f x = f' x) (g : C(spectrum R (cfcSpec ha f), R)) :
    cfcSpec ha (g.comp f') = cfcSpec (cfcSpec_predicate ha f) g := by
  let cfc₂ : CFCCore (spectrum R (cfcSpec ha f)) (cfcSpec ha f) :=
    { toStarAlgHom := cfcSpec (cfcSpec_predicate ha f)
      map_id' := cfcSpec_map_id (cfcSpec_predicate ha f)
      map_continuous' := (cfcSpec_closedEmbedding (cfcSpec_predicate ha f)).continuous }
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

end cfcSpec

/-- Evaluation of continuous maps at a point, bundled as a star algebra homomorphism. -/
@[simps]
def ContinuousMap.evalStarAlgHom (r : R) : C(R, R) →⋆ₐ[R] R where
  toFun f := f r
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl

section Bare

/- This is a version of the continuous functional calculus for bare functions. It is most useful
when one prefers unbundled objects. For instance, the most general version of the composition
theorem is easily statable for `cfcBare`. -/
noncomputable irreducible_def cfcBare (a : A) (f : R → R) : A := by
  classical
  exact if h : p a ∧ ContinuousOn f (spectrum R a)
    then cfcSpec h.1 ⟨_, h.2.restrict⟩
    else 0 -- algebraMap R A (f 0) -- chosen to agree with `cfc`

variable [∀ a : A, Subsingleton (CFCCore (spectrum R a) a)]
variable {a : A}

lemma cfcBare_apply {f : R → R} (ha : p a) (hf : ContinuousOn f (spectrum R a)) :
    cfcBare a f = cfcSpec ha ⟨_, hf.restrict⟩ := by
  rw [cfcBare_def, dif_pos ⟨ha, hf⟩]

lemma cfcBare_apply_of_not_and {f : R → R} (ha : ¬ (p a ∧ ContinuousOn f (spectrum R a))) :
    cfcBare a f = 0 := by
  rw [cfcBare_def, dif_neg ha]

lemma cfcBare_apply_of_not {f : R → R} (ha : ¬ p a) :
    cfcBare a f = 0 := by
  rw [cfcBare_def, dif_neg (not_and_of_not_left _ ha)]

lemma cfcBare_apply_of_not' {f : R → R} (hf : ¬ ContinuousOn f (spectrum R a)) :
    cfcBare a f = 0 := by
  rw [cfcBare_def, dif_neg (not_and_of_not_right _ hf)]

variable (R) in
lemma cfcBare_id (ha : p a) : cfcBare a (id : R → R) = a :=
  cfcBare_apply (R := R) ha continuousOn_id ▸ cfcSpec_map_id ha

lemma cfcBare_map_spectrum (ha : p a) {f : R → R} (hf : ContinuousOn f (spectrum R a)) :
    spectrum R (cfcBare a f) = f '' spectrum R a := by
  simp [cfcBare_apply ha hf, cfcSpec_map_spectrum ha]

lemma cfcBare_predicate {f : R → R} (ha : p a) (hf : ContinuousOn f (spectrum R a)) :
    p (cfcBare a f) :=
  cfcBare_apply ha hf ▸ cfcSpec_predicate ha _

lemma cfcBare_congr {f g : R → R} (hfg : (spectrum R a).EqOn f g) :
    cfcBare a f = cfcBare a g := by
  by_cases h : p a ∧ ContinuousOn g (spectrum R a)
  · rw [cfcBare_apply h.1 (h.2.congr hfg), cfcBare_apply h.1 h.2]
    congr
    exact Set.restrict_eq_iff.mpr hfg
  · classical
    obtain (ha | hg) := Decidable.not_and_iff_or_not _ _ |>.mp h
    · simp [cfcBare_apply_of_not ha]
    · rw [cfcBare_apply_of_not' hg, cfcBare_apply_of_not']
      exact fun hf ↦ hg (hf.congr hfg.symm)

lemma cfcBare_eqOn_of_eq {f g : R → R} (ha : p a) (hf : ContinuousOn f (spectrum R a))
    (hg : ContinuousOn g (spectrum R a)) (h : cfcBare a f = cfcBare a g) :
    (spectrum R a).EqOn f g := by
  rw [cfcBare_apply ha hf, cfcBare_apply ha hg] at h
  have := (cfcSpec_closedEmbedding ha (R := R)).inj h
  intro x hx
  congrm($(this) ⟨x, hx⟩)

variable (R) in
lemma cfcBare_map_one (ha : p a) : cfcBare a (1 : R → R) = 1 :=
  cfcBare_apply (R := R) ha continuousOn_const ▸ map_one (cfcSpec ha)

variable (R) in
lemma cfcBare_map_zero : cfcBare a (0 : R → R) = 0 := by
  by_cases ha : p a
  · exact cfcBare_apply (R := R) ha continuousOn_const ▸ map_zero (cfcSpec ha)
  · rw [cfcBare_apply_of_not ha]

lemma cfcBare_map_mul {f g : R → R} (hf : ContinuousOn f (spectrum R a))
    (hg : ContinuousOn g (spectrum R a)) :
    cfcBare a (f * g) = cfcBare a f * cfcBare a g := by
  by_cases ha : p a
  · rw [cfcBare_apply ha hf, cfcBare_apply ha hg, ← map_mul,
      cfcBare_apply ha (show ContinuousOn (f * g) _ from hf.mul hg)]
    congr
  · simp [cfcBare_apply_of_not ha]

lemma cfcBare_map_add {f g : R → R} (hf : ContinuousOn f (spectrum R a))
    (hg : ContinuousOn g (spectrum R a)) :
    cfcBare a (f + g) = cfcBare a f + cfcBare a g := by
  by_cases ha : p a
  · rw [cfcBare_apply ha hf, cfcBare_apply ha hg, ← map_add,
      cfcBare_apply ha (show ContinuousOn (f + g) _ from hf.add hg)] -- fun_prop failure? beta reduction problems?
    congr
  · simp [cfcBare_apply_of_not ha]

-- generalize to arbitrary smuls with an `IsScalarTower`?
lemma cfcBare_map_smul (r : R) {f : R → R} (hf : ContinuousOn f (spectrum R a)) :
    cfcBare a (r • f) = r • cfcBare a f := by
  by_cases ha : p a
  · rw [cfcBare_apply ha hf, ← map_smul,
      cfcBare_apply ha (show ContinuousOn (r • f) _ from hf.const_smul r)] -- fun_prop failure? beta reduction problems?
    congr
  · simp [cfcBare_apply_of_not ha]

lemma cfcBare_map_star {f : R → R} : cfcBare a (star f) = star (cfcBare a f) := by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · rw [cfcBare_apply h.1 h.2, ← map_star,
      cfcBare_apply h.1 (show ContinuousOn (star f) _ from h.2.star)]
    congr
  · classical
    obtain (ha | hf) := Decidable.not_and_iff_or_not _ _ |>.mp h
    · simp [cfcBare_apply_of_not ha]
    · rw [cfcBare_apply_of_not' hf, cfcBare_apply_of_not', star_zero]
      exact fun hf_star ↦ hf <| by simpa using hf_star.star

lemma cfcBare_pow (ha : p a) (n : ℕ) : cfcBare a (fun x : R ↦ x ^ n) = a ^ n := by
  nth_rw 2 [← cfcSpec_map_id ha (R := R)]
  rw [cfcBare_apply ha (by fun_prop), ← map_pow]
  congr

lemma cfcBare_smul (ha : p a) (r : R) : cfcBare a (r * ·) = r • a := by
  simp_rw [← smul_eq_mul]
  have := cfcBare_id ha (R := R) ▸ cfcBare_map_smul (a := a) r continuousOn_id
  exact this

attribute [fun_prop] continuous_star -- need to mark this in the correct place

lemma cfcBare_star (ha : p a) : cfcBare a (star : R → R) = star a := by
  nth_rw 2 [← cfcSpec_map_id ha (R := R)]
  rw [← map_star, cfcBare_apply ha (by fun_prop)]
  congr
lemma cfcBare_map_pow {f : R → R} (hf : ContinuousOn f (spectrum R a)) (n : ℕ) (hn : n ≠ 0) :
    cfcBare a (f ^ n) = cfcBare a f ^ n := by
  by_cases ha : p a
  · rw [cfcBare_apply ha hf, ← map_pow,
      cfcBare_apply ha (show ContinuousOn (f ^ n) _ from hf.pow n)] -- fun_prop failure?
    congr
  · simp [cfcBare_apply_of_not ha, zero_pow hn]

variable [∀ a : A, Subsingleton (CFCCore (spectrum R a) a)]

lemma cfcBare_comp {f g : R → R} (ha : p a) (hf : ContinuousOn f (spectrum R a))
    (hg : ContinuousOn g (f '' spectrum R a)) :
    cfcBare a (g ∘ f) = cfcBare (cfcBare a f) g := by
  have := hg.comp hf <| (spectrum R a).mapsTo_image f
  have sp_eq : spectrum R (cfcSpec ha (ContinuousMap.mk _ hf.restrict)) = f '' (spectrum R a) := by
    rw [cfcSpec_map_spectrum ha]
    ext
    simp
  rw [cfcBare_apply ha this, cfcBare_apply ha hf, cfcBare_apply (cfcSpec_predicate ha _)]
  swap
  · convert hg
  · rw [← cfcSpec_comp _ _]
    rotate_left
    · exact ContinuousMap.mk _ <| hf.restrict.codRestrict fun x ↦ by rw [sp_eq]; use x.1; simp
    · exact fun _ ↦ rfl
    · congr

lemma cfcBare_comp_pow (ha : p a) (n : ℕ) {f : R → R}
    (hf : ContinuousOn f ((· ^ n) '' (spectrum R a))) :
    cfcBare a (fun x ↦ f (x ^ n)) = cfcBare (a ^ n) f := by
  rw [← Function.comp, cfcBare_comp ha (by fun_prop) hf, cfcBare_pow ha]

lemma cfcBare_comp_smul (ha : p a) (r : R) {f : R → R}
    (hf : ContinuousOn f ((r * ·) '' (spectrum R a))) :
    cfcBare a (fun x ↦ f (r * x)) = cfcBare (r • a) f := by
  rw [← Function.comp, cfcBare_comp ha (by fun_prop) hf, cfcBare_smul ha r]

lemma cfcBare_comp_star (ha : p a) {f : R → R}
    (hf : ContinuousOn f (star '' (spectrum R a))) :
    cfcBare a (fun x ↦ f (star x)) = cfcBare (star a) f := by
  rw [← Function.comp, cfcBare_comp ha (by fun_prop) hf, cfcBare_star ha]

end Bare

end Basic

section Inv

variable {R A : Type*} {p : A → Prop} [Semifield R] [StarRing R] [MetricSpace R]
variable [TopologicalSemiring R] [ContinuousStar R] [HasContinuousInv₀ R] [TopologicalSpace A]
variable [Ring A] [StarRing A] [Algebra R A] [CFC R p]

lemma cfcBare_isUnit_iff {a : A} (ha : p a) {f : R → R} (hf : ContinuousOn f (spectrum R a)) :
    IsUnit (cfcBare a f) ↔ ∀ x ∈ spectrum R a, f x ≠ 0 := by
  rw [← spectrum.zero_not_mem_iff R, cfcBare_map_spectrum ha hf]
  aesop

alias ⟨_, cfcBare_isUnit⟩ := cfcBare_isUnit_iff

@[simps]
noncomputable def cfcBare_units {a : A} (ha : p a) (f : R → R)
    (hf : ContinuousOn f (spectrum R a)) (hf' : ∀ x ∈ spectrum R a, f x ≠ 0) : Aˣ where
  val := cfcBare a f
  inv := cfcBare a f⁻¹
  val_inv := by
    have : ContinuousOn (f⁻¹) (spectrum R a) := hf.inv₀ hf'
    rw [← cfcBare_map_mul hf this, ← cfcBare_map_one R ha]
    exact cfcBare_congr fun _ _ ↦ by aesop
  inv_val := by
    have : ContinuousOn (f⁻¹) (spectrum R a) := hf.inv₀ hf'
    rw [← cfcBare_map_mul this hf, ← cfcBare_map_one R ha]
    exact cfcBare_congr fun _ _ ↦ by aesop
  -- there should be an `abbrev` constructor for `Units` with the assumption that the bits commute

lemma cfcBare_units_pow {a : A} (ha : p a) (f : R → R)
    (hf : ContinuousOn f (spectrum R a)) (hf' : ∀ x ∈ spectrum R a, f x ≠ 0) (n : ℕ) :
    (cfcBare_units ha f hf hf') ^ n =
      cfcBare_units ha (f ^ n) (hf.pow n) (forall₂_imp (fun _ _ ↦ pow_ne_zero n) hf') := by
  ext
  cases n with
  | zero => simp [cfcBare_map_one R ha]
  | succ n => simp [cfcBare_map_pow (a := a) hf _ n.succ_ne_zero]

lemma cfcBare_map_inv {a : A} (ha : p a) (f : R → R) (hf : ContinuousOn f (spectrum R a))
    (hf' : ∀ x ∈ spectrum R a, f x ≠ 0) : cfcBare a f⁻¹ = Ring.inverse (cfcBare a f) := by
  rw [← val_inv_cfcBare_units ha f hf hf', ← val_cfcBare_units ha f hf hf', Ring.inverse_unit]

lemma cfcBare_inv {a : Aˣ} (ha : p a) :
    cfcBare (a : A) (fun x ↦ x⁻¹ : R → R) = a⁻¹ := by
  rw [← Ring.inverse_unit]
  convert cfcBare_map_inv ha (id : R → R) continuousOn_id ?_
  · exact (cfcBare_id R ha).symm
  · rintro x hx rfl
    exact spectrum.zero_not_mem R a.isUnit hx

variable [∀ a : A, Subsingleton (CFCCore (spectrum R a) a)]

lemma cfcBare_comp_inv {a : Aˣ} (ha : p a) {f : R → R}
    (hf : ContinuousOn f ((· ⁻¹) '' (spectrum R (a : A)))) :
    cfcBare (a : A) (fun x ↦ f x⁻¹) = cfcBare (↑a⁻¹ : A) f := by
  rw [← Function.comp, cfcBare_comp ha _ hf, cfcBare_inv ha]
  exact continuousOn_inv₀.mono <| by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_not_mem R a.isUnit

lemma cfcBare_units_zpow {a : A} (ha : p a) (f : R → R)
    (hf : ContinuousOn f (spectrum R a)) (hf' : ∀ x ∈ spectrum R a, f x ≠ 0) (n : ℤ) :
    (cfcBare_units ha f hf hf') ^ n =
      cfcBare_units ha (f ^ n) (hf.zpow₀ n (forall₂_imp (fun _ _ ↦ Or.inl) hf'))
        (forall₂_imp (fun _ _ ↦ zpow_ne_zero n) hf') := by
  cases n with
  | ofNat _ => simpa using cfcBare_units_pow ha f hf hf' _
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow]
    ext
    exact cfcBare_map_pow (hf.inv₀ hf') _ n.succ_ne_zero |>.symm

lemma cfcBare_zpow {a : Aˣ} (ha : p a) (n : ℤ) :
    cfcBare (a : A) (fun x : R ↦ x ^ n) = ↑(a ^ n) := by
  cases n with
  | ofNat n => simpa using cfcBare_pow ha n
  | negSucc n =>
    simp only [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val]
    have := cfcBare_map_pow (a := (a : A)) (f := (fun x ↦ x⁻¹ : R → R)) ?_ (n + 1) n.succ_ne_zero
    · exact this.trans <| congr($(cfcBare_inv ha) ^ (n + 1))
    · refine continuousOn_inv₀.mono (s := {0}ᶜ) fun x ↦ ?_
      simpa using spectrum.ne_zero_of_mem_of_unit

lemma cfcBare_comp_zpow {a : Aˣ} (ha : p a) {f : R → R} (n : ℤ)
    (hf : ContinuousOn f ((· ^ n) '' (spectrum R (a : A)))) :
    cfcBare (a : A) (fun x ↦ f (x ^ n)) = cfcBare (↑(a ^ n) : A) f := by
  rw [← Function.comp, cfcBare_comp ha _ hf, cfcBare_zpow ha]
  exact (continuousOn_zpow₀ n).mono <| by
    simpa only [Set.subset_compl_singleton_iff] using spectrum.zero_not_mem R a.isUnit

end Inv

section Neg

variable {R A : Type*} {p : A → Prop} [CommRing R] [StarRing R] [MetricSpace R]
variable [TopologicalRing R] [ContinuousStar R] [TopologicalSpace A]
variable [Ring A] [StarRing A] [Algebra R A] [CFC R p]
variable [∀ a : A, Subsingleton (CFCCore (spectrum R a) a)]

lemma cfcBare_map_sub {a : A} {f g : R → R} (hf : ContinuousOn f (spectrum R a))
    (hg : ContinuousOn g (spectrum R a)) :
    cfcBare a (f - g) = cfcBare a f - cfcBare a g := by
  by_cases ha : p a
  · rw [cfcBare_apply ha hf, cfcBare_apply ha hg, ← map_sub,
      cfcBare_apply ha (show ContinuousOn (f - g) _ from hf.sub hg)] -- fun_prop failure? beta reduction problems?
    congr
  · simp [cfcBare_apply_of_not ha]

lemma cfcBare_map_neg (a : A) (f : R → R) : cfcBare a (-f) = - (cfcBare a f) := by
  by_cases h : p a ∧ ContinuousOn f (spectrum R a)
  · rw [cfcBare_apply h.1 h.2, ← map_neg,
      cfcBare_apply h.1 (show ContinuousOn (-f) _ from h.2.neg)]
    congr
  · classical
    obtain (ha | hf) := Decidable.not_and_iff_or_not _ _ |>.mp h
    · simp [cfcBare_apply_of_not ha]
    · rw [cfcBare_apply_of_not' hf, cfcBare_apply_of_not', neg_zero]
      exact fun hf_neg ↦ hf <| by simpa using hf_neg.neg

lemma cfcBare_neg {a : A} (ha : p a) :
    cfcBare (a : A) (fun x ↦ -x : R → R) = -a := by
  have := cfcBare_id R ha ▸ cfcBare_map_neg a (id : R → R)
  exact this

lemma cfcBare_comp_neg {a : A} (ha : p a) {f : R → R}
    (hf : ContinuousOn f ((-·) '' (spectrum R (a : A)))) :
    cfcBare (a : A) (fun x ↦ f (-x)) = cfcBare (-a) f := by
  rw [← Function.comp, cfcBare_comp ha (by fun_prop) hf, cfcBare_neg ha]

end Neg

section cfc

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
variable [TopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A] [StarRing A]
variable [Algebra R A] [CFC R p] [StarModule R A] {a : A}

/- In practice, we expec this to be the most useful version of the continuous functional calculus.
It is also uniquely determined (by appealing to the Stone-Weierstrass and the Tietze extension
theorems), although I haven't proven that here. -/

variable (a) in
/-- The star algebra homomorphism underlying a instance of the continuous functional calculus.
Version for continuous functions on the full space. -/
noncomputable irreducible_def cfc : C(R, R) →⋆ₐ[R] A := by
  classical
  exact if ha : p a
    then (cfcSpec ha).comp <| (ContinuousMap.id R |>.restrict <| spectrum R a).compStarAlgHom' R R
    else (StarAlgHom.ofId R A).comp (ContinuousMap.evalStarAlgHom 0)

lemma cfc_dif_pos (ha : p a) :
    cfc a =
      (cfcSpec ha).comp ((ContinuousMap.id R |>.restrict <| spectrum R a).compStarAlgHom' R R) := by
  rw [cfc_def, dif_pos ha]

lemma cfc_dif_neg (ha : ¬ p a) :
    cfc a = (StarAlgHom.ofId R A).comp (ContinuousMap.evalStarAlgHom 0) := by
  rw [cfc_def, dif_neg ha]

lemma cfc_apply (ha : p a) (f : C(R, R)) : cfc a f = cfcSpec ha (f.restrict <| spectrum R a) := by
  rw [cfc_dif_pos ha, StarAlgHom.comp_apply, ContinuousMap.compStarAlgHom'_apply]
  congr

lemma cfc_eq_cfcBare [StarModule R A] {a : A} (ha : p a) (f : C(R, R)) :
    cfc a f = cfcBare a f := by
  rw [cfc_apply ha, cfcBare_apply ha (map_continuous f).continuousOn]
  congr

lemma cfc_id (ha : p a) : cfc a (ContinuousMap.id R) = a := by
  rw [cfc_apply ha, cfcSpec_map_id ha]

lemma cfc_map_spectrum (ha : p a) (f : C(R, R)) : spectrum R (cfc a f) = f '' spectrum R a := by
  simp [cfc_apply ha, cfcSpec_map_spectrum ha, Set.range_comp]

lemma cfc_predicate (ha : p a) (f : C(R, R)) : p (cfc a f) := by
  rw [cfc_apply ha]
  exact cfcSpec_predicate ha _

lemma cfc_continuous [TopologicalSemiring A] [ContinuousSMul R A] : Continuous (cfc a (R := R)) := by
  by_cases ha : p a
  · rw [cfc_dif_pos ha]
    exact cfcSpec_closedEmbedding ha |>.continuous |>.comp <| ContinuousMap.continuous_comp_left _
  · rw [cfc_dif_neg ha]
    exact continuous_algebraMap R A |>.comp <| ContinuousMap.continuous_eval_const _

-- MOVE ME
attribute [fun_prop] map_continuous

lemma cfc_congr (ha : p a) {f g : C(R, R)} (hfg : (spectrum R a).EqOn f g) :
    cfc a f = cfc a g := by
  simpa [cfc_eq_cfcBare ha] using cfcBare_congr hfg

lemma cfc_eqOn_of_eq (ha : p a) {f g : C(R, R)} (hfg : cfc a f = cfc a g) :
    (spectrum R a).EqOn f g := by
  refine cfcBare_eqOn_of_eq ha ?_ ?_ <| by simpa [cfc_eq_cfcBare ha] using hfg
  all_goals fun_prop

lemma eq_algebraMap_of_spectrum_singleton (ha : p a) {r : R} (h_spec : spectrum R a = {r}) :
    a = algebraMap R A r := by
  simpa [cfc_id ha, AlgHomClass.commutes] using
    cfc_congr ha (f := ContinuousMap.id R) (g := algebraMap R C(R, R) r) <| by rw [h_spec]; simp

lemma eq_zero_of_spectrum_eq_zero (ha : p a) (h_spec : spectrum R a = {0}) : a = 0 := by
  simpa using eq_algebraMap_of_spectrum_singleton ha h_spec

lemma eq_one_of_spectrum_eq_one (ha : p a) (h_spec : spectrum R a = {1}) : a = 1 := by
  simpa using eq_algebraMap_of_spectrum_singleton ha h_spec

-- pow, star, smul

lemma cfc_pow (ha : p a) (n : ℕ) : cfc a (.id R ^ n) = a ^ n := by
  rw [map_pow, cfc_id ha]

lemma cfc_star (ha : p a) : cfc a (star (.id R)) = star a := by
  rw [map_star, cfc_id ha]

-- generalize to other smuls
lemma cfc_smul (ha : p a) (r : R) : cfc a (r • .id R) = r • a := by
  rw [map_smul, cfc_id ha]

-- inv, zpow, neg

variable [∀ a : A, Subsingleton (CFCCore (spectrum R a) a)]

lemma cfc_comp (ha : p a) (f g : C(R, R)) : cfc a (g.comp f) = cfc (cfc a f) g := by
  simp_rw [cfc_eq_cfcBare (cfc_predicate ha f), cfc_eq_cfcBare ha, ContinuousMap.coe_comp]
  apply cfcBare_comp ha <;> fun_prop

lemma cfc_comp_pow (ha : p a) (n : ℕ) (f : C(R, R)) :
    cfc a (f.comp (.id R ^ n)) = cfc (a ^ n) f := by
  rw [cfc_comp ha, cfc_pow ha]

lemma cfc_comp_star (ha : p a) (f : C(R, R)) :
    cfc a (f.comp (star (.id R))) = cfc (star a) f := by
  rw [cfc_comp ha, cfc_star ha]

lemma cfc_comp_smul (ha : p a) (r : R) (f : C(R, R)) :
    cfc a (f.comp (r • .id R)) = cfc (r • a) f := by
  rw [cfc_comp ha, cfc_smul ha]

-- spectrum subset circle → unitary

end cfc


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
  hom_id {a} ha := by
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
  predicate_hom {a} ha g := by
    rw [h]
    refine ⟨cfcSpec_predicate _ _, ?_⟩
    refine { rightInvOn := fun s hs ↦ ?_, left_inv := ((h a).mp ha).2.left_inv }
    rw [SpectrumRestricts.starAlgHom_apply, cfcSpec_map_spectrum] at hs
    obtain ⟨r, rfl⟩ := hs
    simp [((h a).mp ha).2.left_inv _]


end Restrict
