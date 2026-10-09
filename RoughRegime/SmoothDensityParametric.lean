module

public import RoughRegime.ParametricBaselineLower
public import RoughRegime.CanonicalPartitionPPP
public import RoughRegime.ModelMainLowerConsequences


@[expose] public section
/-! Actual smooth-density subclasses retain parametric local hardness. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology ContDiff
namespace RoughRegime.Model

/-- No uniform derivative bound is placed on this density. -/
def smoothDensityClass (d : ℕ) (Z : Type*) [MeasurableSpace Z] :
    Set (ProbabilityMeasure (Covariate d×Z)) :=
  {P | ∃ p : Covariate d→ℝ, ContDiff ℝ ∞ p ∧
    (P : Measure (Covariate d×Z)).map Prod.fst=
      (cubeVolume d).withDensity (fun x => ENNReal.ofReal (p x))}

theorem productLaw_mem_smoothDensityClass (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) : productLaw A π∈smoothDensityClass A.d Z := by
  refine ⟨fun _=>1,contDiff_const,?_⟩
  change ((cubeVolume A.d).prod (π : Measure Z)).map Prod.fst=_
  simp

theorem smooth_localClass_parametric_rootn (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (π : ProbabilityMeasure Z) (hnd : Nondegenerate A F π)
    (r : ℝ) (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in Filter.atTop,
      ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤
        minimaxRMSE n (target A F) ((localClass A F π r ∩ smoothDensityClass A.d Z)) := by
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
      productLaw A (L (u, t)).probabilityMeasure ∈ (localClass A F π r ∩ smoothDensityClass A.d Z) := by
    have hc := (AffineResponseLower.responsePairLaw_eventually_localClass A F π hnd r hr su sv hsu hsv
      ε K (le_of_lt hε) hK hsmall hbu hbv hmu hmv).curry_nhds
    filter_upwards [hc] with u hu
    filter_upwards [hu] with t ht
    exact ⟨ht,productLaw_mem_smoothDensityClass A (L (u,t)).probabilityMeasure⟩
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
      (∀ᶠ t : ℝ in nhds 0, productLaw A (L (u, t)).probabilityMeasure ∈ (localClass A F π r ∩ smoothDensityClass A.d Z)) := by
    filter_upwards [self_mem_nhdsWithin, hroot.filter_mono nhdsWithin_le_nhds,
      hclass.filter_mono nhdsWithin_le_nhds] with u hu hur huc
    exact ⟨by simpa using hu, hur, huc⟩
  obtain ⟨u, hune, hur, huc⟩ := hgood.exists
  obtain ⟨hu, hbound⟩ := hur hune
  apply hbound (target A F) ((localClass A F π r ∩ smoothDensityClass A.d Z)) 0
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



end RoughRegime.Model
