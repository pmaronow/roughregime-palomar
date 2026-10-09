module

public import RoughRegime.AffineResponseLower
public import RoughRegime.MeasureScores
public import RoughRegime.BaselineScores
public import RoughRegime.ProductClass


@[expose] public section
/-! Parametric lower bounds in the actual localized generic model. -/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace RoughRegime.AffineResponseLower

theorem clip_eq_of_abs_le {ε t : ℝ} (ht : |t| ≤ ε) : clip ε t = t := by
  rcases abs_le.mp ht with ⟨hl, hr⟩
  simp [clip, min_eq_right hr, max_eq_right hl]

theorem clip_zero {ε : ℝ} (hε : 0 ≤ ε) : clip ε 0 = 0 :=
  clip_eq_of_abs_le (by simpa using hε)

variable {Z : Type*} [MeasurableSpace Z] (π : ProbabilityMeasure Z)

def responsePairLaw (su sv : Z → ℝ) (hsu : Measurable su) (hsv : Measurable sv)
    (ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hsmall : ε * K ≤ 1 / 4)
    (hbu : ∀ z, |su z| ≤ K) (hbv : ∀ z, |sv z| ≤ K)
    (hmu : (∫ z, su z ∂(π : Measure Z)) = 0)
    (hmv : (∫ z, sv z ∂(π : Measure Z)) = 0) (q : ℝ × ℝ) :
    GeneralTesting.DensityLaw (π : Measure Z) :=
  responseDensityLaw (π : Measure Z) su sv hsu hsv (clip ε q.1) ε K hε hK
    (clip_abs_le hε q.1) hsmall hbu hbv hmu hmv q.2

theorem responsePairLaw_zero (su sv : Z → ℝ) (hsu : Measurable su) (hsv : Measurable sv)
    (ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hsmall : ε * K ≤ 1 / 4)
    (hbu : ∀ z, |su z| ≤ K) (hbv : ∀ z, |sv z| ≤ K)
    (hmu : (∫ z, su z ∂(π : Measure Z)) = 0)
    (hmv : (∫ z, sv z ∂(π : Measure Z)) = 0) :
    (responsePairLaw π su sv hsu hsv ε K hε hK hsmall hbu hbv hmu hmv (0, 0)).probabilityMeasure = π := by
  apply Subtype.ext
  simp [responsePairLaw, responseDensityLaw, GeneralTesting.DensityLaw.probabilityMeasure,
    GeneralTesting.DensityLaw.measure, clip_zero hε]

theorem responsePairLaw_integral_continuous (su sv : Z → ℝ)
    (hsu : Measurable su) (hsv : Measurable sv)
    (ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hsmall : ε * K ≤ 1 / 4)
    (hbu : ∀ z, |su z| ≤ K) (hbv : ∀ z, |sv z| ≤ K)
    (hmu : (∫ z, su z ∂(π : Measure Z)) = 0)
    (hmv : (∫ z, sv z ∂(π : Measure Z)) = 0)
    (f : Z → ℝ) (hf : Integrable f (π : Measure Z))
    (hfu : Integrable (fun z => f z * su z) (π : Measure Z))
    (hfv : Integrable (fun z => f z * sv z) (π : Measure Z)) :
    Continuous (fun q : ℝ × ℝ => ∫ z, f z ∂
      (responsePairLaw π su sv hsu hsv ε K hε hK hsmall hbu hbv hmu hmv q).measure) := by
  have he : (fun q : ℝ × ℝ => ∫ z, f z ∂
      (responsePairLaw π su sv hsu hsv ε K hε hK hsmall hbu hbv hmu hmv q).measure) =
      fun q => (∫ z, f z ∂(π : Measure Z)) + clip ε q.1 * (∫ z, f z * su z ∂(π : Measure Z)) +
        clip ε q.2 * (∫ z, f z * sv z ∂(π : Measure Z)) := by
    funext q
    exact integral_density_affine (π : Measure Z)
      (responsePairLaw π su sv hsu hsv ε K hε hK hsmall hbu hbv hmu hmv q)
      su sv f (clip ε q.1) (clip ε q.2) (Filter.Eventually.of_forall fun _ => rfl) hf hfu hfv
  rw [he]
  unfold clip
  fun_prop

end RoughRegime.AffineResponseLower



namespace RoughRegime.Model

theorem eventually_productLaw_mem_localClass_general {I : Type*} [TopologicalSpace I]
    (i0 : I) (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π0 : ProbabilityMeasure Z) (ν : I → ProbabilityMeasure Z)
    (hν0 : ν i0 = π0) (hnd : Nondegenerate A F π0) (r : ℝ) (hr : 0 < r)
    (hD : ContinuousAt (fun t => baselineW A F (ν t)) i0)
    (hA : ContinuousAt (fun t => baselineA A F (ν t)) i0)
    (hB : ContinuousAt (fun t => baselineB A F (ν t)) i0) :
    ∀ᶠ t in 𝓝 i0, productLaw A (ν t) ∈ localClass A F π0 r := by
  obtain ⟨_, hwl, hwh, hal, hbl, _⟩ := hnd
  have hlow : ∀ᶠ t in 𝓝 i0, max A.δ A.gminus < baselineW A F (ν t) :=
    continuousAt_const.eventually_lt hD (by simpa [hν0] using hwl)
  have hhigh : ∀ᶠ t in 𝓝 i0, baselineW A F (ν t) < A.gplus :=
    hD.eventually_lt continuousAt_const (by simpa [hν0] using hwh)
  have hanorm : ∀ᶠ t in 𝓝 i0, |baselineA A F (ν t)| < A.H :=
    hA.abs.eventually_lt continuousAt_const (by simpa [hν0] using hal)
  have hbnorm : ∀ᶠ t in 𝓝 i0, |baselineB A F (ν t)| < A.H :=
    hB.abs.eventually_lt continuousAt_const (by simpa [hν0] using hbl)
  have hdnear : ∀ᶠ t in 𝓝 i0, |baselineW A F (ν t) - baselineW A F π0| < r :=
    (hD.sub continuousAt_const).abs.eventually_lt continuousAt_const (by simpa [hν0] using hr)
  have hanear : ∀ᶠ t in 𝓝 i0, |baselineA A F (ν t) - baselineA A F π0| < r :=
    (hA.sub continuousAt_const).abs.eventually_lt continuousAt_const (by simpa [hν0] using hr)
  have hbnear : ∀ᶠ t in 𝓝 i0, |baselineB A F (ν t) - baselineB A F π0| < r :=
    (hB.sub continuousAt_const).abs.eventually_lt continuousAt_const (by simpa [hν0] using hr)
  filter_upwards [hlow, hhigh, hanorm, hbnorm, hdnear, hanear, hbnear] with t hl hh ha hb hd da db
  exact productLaw_mem_localClass A F (ν t) π0 r
    ((le_max_left _ _).trans hl.le) ⟨(le_max_right _ _).trans hl.le, hh.le⟩
    ha.le hb.le hd.le da.le db.le


end RoughRegime.Model

namespace RoughRegime.AffineResponseLower

theorem responsePairLaw_eventually_localClass (A : Model.Parameters)
    {Z : Type*} [MeasurableSpace Z] (F : Model.Observables Z A)
    (π : ProbabilityMeasure Z) (hnd : Model.Nondegenerate A F π) (r : ℝ) (hr : 0 < r)
    (su sv : Z → ℝ) (hsu : Measurable su) (hsv : Measurable sv)
    (ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K) (hsmall : ε * K ≤ 1 / 4)
    (hbu : ∀ z, |su z| ≤ K) (hbv : ∀ z, |sv z| ≤ K)
    (hmu : (∫ z, su z ∂(π : Measure Z)) = 0)
    (hmv : (∫ z, sv z ∂(π : Measure Z)) = 0) :
    ∀ᶠ q : ℝ × ℝ in nhds (0, 0), Model.productLaw A
      (responsePairLaw π su sv hsu hsv ε K hε hK hsmall hbu hbv hmu hmv q).probabilityMeasure ∈
      Model.localClass A F π r := by
  let L := responsePairLaw π su sv hsu hsv ε K hε hK hsmall hbu hbv hmu hmv
  let ν := fun q => (L q).probabilityMeasure
  have hν0 : ν (0, 0) = π := responsePairLaw_zero π su sv hsu hsv ε K hε hK hsmall hbu hbv hmu hmv
  have hDb (z : Z) : |F.D z| ≤ A.M0 := by
    rw [abs_of_nonneg (F.boundD z).1]
    exact (F.boundD z).2
  have hD := score_integrable (π : Measure Z) F.D F.measurableD A.M0 hDb
  have hU := score_integrable (π : Measure Z) F.U F.measurableU A.M0 F.boundU
  have hV := score_integrable (π : Measure Z) F.V F.measurableV A.M0 F.boundV
  have hDu := bounded_score_product_integrable (π : Measure Z) F.D su F.measurableD hsu A.M0 K
    (le_of_lt A.hM0) hK hDb hbu
  have hDv := bounded_score_product_integrable (π : Measure Z) F.D sv F.measurableD hsv A.M0 K
    (le_of_lt A.hM0) hK hDb hbv
  have hUu := bounded_score_product_integrable (π : Measure Z) F.U su F.measurableU hsu A.M0 K
    (le_of_lt A.hM0) hK F.boundU hbu
  have hUv := bounded_score_product_integrable (π : Measure Z) F.U sv F.measurableU hsv A.M0 K
    (le_of_lt A.hM0) hK F.boundU hbv
  have hVu := bounded_score_product_integrable (π : Measure Z) F.V su F.measurableV hsu A.M0 K
    (le_of_lt A.hM0) hK F.boundV hbu
  have hVv := bounded_score_product_integrable (π : Measure Z) F.V sv F.measurableV hsv A.M0 K
    (le_of_lt A.hM0) hK F.boundV hbv
  have hDc := (responsePairLaw_integral_continuous π su sv hsu hsv ε K hε hK hsmall hbu hbv
    hmu hmv F.D hD hDu hDv).continuousAt (x := (0, 0))
  have hUc := (responsePairLaw_integral_continuous π su sv hsu hsv ε K hε hK hsmall hbu hbv
    hmu hmv F.U hU hUu hUv).continuousAt (x := (0, 0))
  have hVc := (responsePairLaw_integral_continuous π su sv hsu hsv ε K hε hK hsmall hbu hbv
    hmu hmv F.V hV hVu hVv).continuousAt (x := (0, 0))
  have hw : Model.baselineW A F (ν (0, 0)) ≠ 0 := by
    rw [hν0]
    exact ne_of_gt (lt_trans A.hδ ((le_max_left _ _).trans_lt hnd.2.1))
  exact Model.eventually_productLaw_mem_localClass_general (0, 0) A F π ν hν0 hnd r hr
    hDc (hUc.div hDc hw) (hVc.div hDc hw)

end RoughRegime.AffineResponseLower

namespace RoughRegime.Model

/-- The parametric lower bound in Theorem 2, under the original nondegeneracy
assumption, on every positive local radius. The true scores, actual laws,
smoothness, overlap, density bounds, and local membership are all constructed. -/
theorem localClass_parametric_rootn (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π : ProbabilityMeasure Z) (hnd : Nondegenerate A F π)
    (r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        minimaxRMSE n (target A F) (localClass A F π r) := by
  classical
  open AffineResponseLower in
  obtain ⟨su, sv, K, hsu, hsv, hK, hbu, hbv, hmu, hmv, hcases⟩ :=
    MeasureScores.nondegenerate_has_scores A F π hnd
  let ε : ℝ := 1 / (8 * (K + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsmall : ε * K ≤ 1 / 4 := by
    dsimp [ε]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  let L := AffineResponseLower.responsePairLaw π su sv hsu hsv ε K (le_of_lt hε) hK
    hsmall hbu hbv hmu hmv
  have hclass : ∀ᶠ u : ℝ in nhds 0, ∀ᶠ t : ℝ in nhds 0,
      productLaw A (L (u, t)).probabilityMeasure ∈ localClass A F π r :=
    (AffineResponseLower.responsePairLaw_eventually_localClass A F π hnd r hr su sv hsu hsv
      ε K (le_of_lt hε) hK hsmall hbu hbv hmu hmv).curry_nhds
  have hbase : 0 < ∫ z, F.D z ∂(π : Measure Z) :=
    lt_trans A.hδ ((le_max_left _ _).trans_lt hnd.2.1)
  have hU0 : (∫ z, F.U z ∂(π : Measure Z)) = baselineA A F π * ∫ z, F.D z ∂(π : Measure Z) := by
    unfold baselineA baselineW
    field_simp
  have hV0 : (∫ z, F.V z ∂(π : Measure Z)) = baselineB A F π * ∫ z, F.D z ∂(π : Measure Z) := by
    unfold baselineB baselineW
    field_simp
  have hroot : ∀ᶠ u : ℝ in nhds 0, u ≠ 0 → ∃ hu : |u| ≤ ε,
      let P := fun t => AffineResponseLower.withDesign (π : Measure Z) (cubeVolume A.d)
        (AffineResponseLower.responseDensityLaw (π : Measure Z) su sv hsu hsv u ε K
          (le_of_lt hε) hK hu hsmall hbu hbv hmu hmv t)
      ∀ (T : ProbabilityMeasure (Covariate A.d × Z) → ℝ)
        (C : Set (ProbabilityMeasure (Covariate A.d × Z))) (tstar : ℝ),
        (∀ᶠ t in nhds 0, (P t).probabilityMeasure ∈ C) →
        ((fun t => T (P t).probabilityMeasure) =ᶠ[nhds 0]
          fun t => target A F (P t).probabilityMeasure + tstar) →
        ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
          ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ minimaxRMSE n T C := by
    rcases hcases with hcross | ⟨hUV, hsame, hR⟩
    · exact AffineResponseLower.actual_target_rootn_near (π : Measure Z) A F (cubeVolume A.d)
        su sv hsu hsv ε K hε hK hsmall hbu hbv hmu hmv (baselineA A F π) (baselineB A F π)
        hbase hU0 hV0 hcross.1 hcross.2.1 hcross.2.2.1 hcross.2.2.2
    · subst sv
      exact AffineResponseLower.actual_diagonal_target_rootn_near (π : Measure Z) A F (cubeVolume A.d)
        su hsu ε K hε hK hsmall hbu hmu (baselineA A F π) hbase hUV hU0 hR
  have hgood : ∀ᶠ u : ℝ in nhdsWithin 0 ({0}ᶜ),
      u ≠ 0 ∧ (u ≠ 0 → ∃ hu : |u| ≤ ε,
        let P := fun t => AffineResponseLower.withDesign (π : Measure Z) (cubeVolume A.d)
          (AffineResponseLower.responseDensityLaw (π : Measure Z) su sv hsu hsv u ε K
            (le_of_lt hε) hK hu hsmall hbu hbv hmu hmv t)
        ∀ (T : ProbabilityMeasure (Covariate A.d × Z) → ℝ)
          (C : Set (ProbabilityMeasure (Covariate A.d × Z))) (tstar : ℝ),
          (∀ᶠ t in nhds 0, (P t).probabilityMeasure ∈ C) →
          ((fun t => T (P t).probabilityMeasure) =ᶠ[nhds 0]
            fun t => target A F (P t).probabilityMeasure + tstar) →
          ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
            ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ minimaxRMSE n T C) ∧
      (∀ᶠ t : ℝ in nhds 0, productLaw A (L (u, t)).probabilityMeasure ∈ localClass A F π r) := by
    filter_upwards [self_mem_nhdsWithin, hroot.filter_mono nhdsWithin_le_nhds,
      hclass.filter_mono nhdsWithin_le_nhds] with u hu hur huc
    exact ⟨by simpa using hu, hur, huc⟩
  obtain ⟨u, hune, hur, huc⟩ := hgood.exists
  obtain ⟨hu, hbound⟩ := hur hune
  apply hbound (target A F) (localClass A F π r) 0
  · filter_upwards [huc] with t ht
    have he : (AffineResponseLower.withDesign (π : Measure Z) (cubeVolume A.d)
        (AffineResponseLower.responseDensityLaw (π : Measure Z) su sv hsu hsv u ε K
          (le_of_lt hε) hK hu hsmall hbu hbv hmu hmv t)).probabilityMeasure =
        productLaw A (L (u, t)).probabilityMeasure := by
      apply Subtype.ext
      dsimp only [GeneralTesting.DensityLaw.probabilityMeasure, productLaw]
      rw [AffineResponseLower.withDesign_measure]
      change (cubeVolume A.d).prod ((π : Measure Z).withDensity
          (fun z => ENNReal.ofReal (1 + u * su z + AffineResponseLower.clip ε t * sv z))) =
        (cubeVolume A.d).prod ((π : Measure Z).withDensity
          (fun z => ENNReal.ofReal (1 + AffineResponseLower.clip ε u * su z +
            AffineResponseLower.clip ε t * sv z)))
      rw [AffineResponseLower.clip_eq_of_abs_le hu]
    exact he ▸ ht
  · exact Filter.Eventually.of_forall fun _ => by simp


/-- A single constant and sample threshold work uniformly for every class
containing the localized model. This is the root-n clause of Theorem 2(b). -/
theorem main_parametric_lower (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π : ProbabilityMeasure Z) (hnd : Nondegenerate A F π)
    (r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∃ n0 : ℕ, 3 ≤ n0 ∧
      ∀ C : Set (ProbabilityMeasure (Observation A Z)), localClass A F π r ⊆ C →
        ∀ n : ℕ, n0 ≤ n → ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
          minimaxRMSE n (target A F) C := by
  obtain ⟨c, hc, hn⟩ := localClass_parametric_rootn A F π hnd r hr
  obtain ⟨n1, hn1⟩ := Filter.eventually_atTop.1 hn
  refine ⟨c, hc, max 3 n1, le_max_left _ _, ?_⟩
  intro C hC n hn
  exact (hn1 n ((le_max_right _ _).trans hn)).trans
    (minimaxRMSE_mono_class n (target A F) hC)


end RoughRegime.Model
