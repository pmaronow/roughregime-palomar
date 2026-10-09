module

public import RoughRegime.AffineResponseLower
public import RoughRegime.AffinePathUniform


@[expose] public section
/-! Proposition15(b)'s constant is fixed at the chosen nonzero u before all
containing classes, target parameters, and additive offsets. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.AffineResponseLower
set_option backward.isDefEq.respectTransparency false
variable {Z : Type*} [MeasurableSpace Z] (π : Measure Z) [IsProbabilityMeasure π]

theorem response_path_uniform_minimax (η : Measure (Model.Covariate d))
    [IsProbabilityMeasure η] (su sv : Z→ℝ) (hsu : Measurable su) (hsv : Measurable sv)
    (u ε K : ℝ) (hε : 0<ε) (hK : 0 ≤ K) (hu : |u| ≤ ε) (hsmall : ε*K ≤ 1/4)
    (hbu : ∀z,|su z| ≤ K) (hbv : ∀z,|sv z| ≤ K)
    (hmu : (∫z,su z ∂π)=0) (hmv : (∫z,sv z ∂π)=0)
    (G : ℝ→ℝ) (D : ℝ) (hG : HasDerivAt G D 0) (hD : D≠0) :
    let P := fun t=>withDesign π η
      (responseDensityLaw π su sv hsu hsv u ε K hε.le hK hu hsmall hbu hbv hmu hmv t)
    ∃ c : ℝ,0<c ∧
      ∀ (T : ProbabilityMeasure (Model.Covariate d×Z)→ℝ)
        (C : Set (ProbabilityMeasure (Model.Covariate d×Z))) (tstar : ℝ),
        (∀ᶠ t in nhds 0,(P t).probabilityMeasure∈C) →
        ((fun t=>T (P t).probabilityMeasure) =ᶠ[nhds 0] fun t=>G t+tstar) →
        ∀ᶠ n : ℕ in atTop,
          ENNReal.ofReal (c*(n:ℝ)^(-(1/2:ℝ))) ≤ Model.minimaxRMSE n T C := by
  dsimp only
  let P := fun t=>withDesign π η
    (responseDensityLaw π su sv hsu hsv u ε K hε.le hK hu hsmall hbu hbv hmu hmv t)
  have hdens : ∀t∈Ioo (-ε) ε,(P t).density =ᵐ[η.prod π]
      fun x=>(1+u*su x.2)+t*sv x.2 := by
    intro t ht
    exact ae_of_all _ (fun x=>by
      change 1+u*su x.2+clip ε t*sv x.2=_
      rw [clip_eq ht])
  have hpos : ∀t∈Ioo (-ε) ε,∀ᵐ x ∂η.prod π,(1/2:ℝ) ≤ (1+u*su x.2)+t*sv x.2 := by
    intro t ht
    exact ae_of_all _ (fun x=>by
      simpa only [clip_eq ht] using
        affine_density_lower su sv u ε K t hε.le hK hu hsmall hbu hbv x.2)
  exact LowerMeasure.affine_path_uniform_rootn P (fun x=>1+u*su x.2) (fun x=>sv x.2)
    G (-ε) ε D (1/2) K ⟨by linarith,hε⟩ hG hD (by norm_num) hK hdens hpos
    (ae_of_all _ (fun x=>hbv x.2))

theorem actual_target_rootn_near_uniform (A : Model.Parameters) (F : Model.Observables Z A)
    (η : Measure (Model.Covariate A.d)) [IsProbabilityMeasure η]
    (su sv : Z → ℝ) (hsu : Measurable su) (hsv : Measurable sv)
    (ε K : ℝ) (hε : 0 < ε) (hK : 0 ≤ K) (hsmall : ε * K ≤ 1 / 4)
    (hbu : ∀ z, |su z| ≤ K) (hbv : ∀ z, |sv z| ≤ K)
    (hmu : (∫ z, su z ∂π) = 0) (hmv : (∫ z, sv z ∂π) = 0)
    (a0 b0 : ℝ) (hbase : 0 < ∫ z, F.D z ∂π)
    (hU0 : (∫ z, F.U z ∂π) = a0 * ∫ z, F.D z ∂π)
    (hV0 : (∫ z, F.V z ∂π) = b0 * ∫ z, F.D z ∂π)
    (hRu : (∫ z, (F.U z - a0 * F.D z) * su z ∂π) = 1)
    (hRv : (∫ z, (F.U z - a0 * F.D z) * sv z ∂π) = 0)
    (hSu : (∫ z, (F.V z - b0 * F.D z) * su z ∂π) = 0)
    (hSv : (∫ z, (F.V z - b0 * F.D z) * sv z ∂π) = 1) :
    ∀ᶠ u : ℝ in nhds 0, u ≠ 0 → ∃ hu : |u| ≤ ε,
      let P := fun t => withDesign π η
        (responseDensityLaw π su sv hsu hsv u ε K (le_of_lt hε) hK hu hsmall hbu hbv hmu hmv t)
      ∃ c : ℝ, 0 < c ∧
      ∀ (T : ProbabilityMeasure (Model.Covariate A.d × Z) → ℝ)
        (C : Set (ProbabilityMeasure (Model.Covariate A.d × Z))) (tstar : ℝ),
        (∀ᶠ t in nhds 0, (P t).probabilityMeasure ∈ C) →
        ((fun t => T (P t).probabilityMeasure) =ᶠ[nhds 0]
          fun t => Model.target A F (P t).probabilityMeasure + tstar) →
        ∀ᶠ n : ℕ in Filter.atTop,
          ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ Model.minimaxRMSE n T C := by
  let c0 := (∫ z, F.W z ∂π) + F.lam * (a0 * b0 * ∫ z, F.D z ∂π)
  let cu := (∫ z, F.W z * su z ∂π) +
    F.lam * (a0 * b0 * (∫ z, F.D z * su z ∂π) + b0)
  let cv := (∫ z, F.W z * sv z ∂π) +
    F.lam * (a0 * b0 * (∫ z, F.D z * sv z ∂π) + a0)
  let w0 := ∫ z, F.D z ∂π
  let du := ∫ z, F.D z * su z ∂π
  let dv := ∫ z, F.D z * sv z ∂π
  have hw0 : w0 ≠ 0 := ne_of_gt hbase
  have hden : ∀ᶠ u : ℝ in nhds 0, w0 + du * u ≠ 0 := by
    have hc : ContinuousAt (fun u : ℝ => w0 + du * u) 0 := by fun_prop
    exact hc.eventually_ne (by simpa using hw0)
  have hslope := Applications.localIntegrand_nonzero_slope_near c0 cu cv F.lam w0 du dv
    F.hlam hw0
  have hu_near : ∀ᶠ u : ℝ in nhds 0, |u| ≤ ε := by
    filter_upwards [Ioo_mem_nhds (by linarith : -ε < (0 : ℝ)) hε] with u hu
    exact abs_le.mpr ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  filter_upwards [hden, hslope, hu_near] with u hdu hsu' hu
  intro hune
  refine ⟨hu, ?_⟩
  dsimp only
  let L := fun t => responseDensityLaw π su sv hsu hsv u ε K (le_of_lt hε) hK hu
    hsmall hbu hbv hmu hmv t
  let P := fun t => withDesign π η (L t)
  have hrepr : (fun t => Model.target A F (P t).probabilityMeasure) =ᶠ[nhds 0]
      fun t => Applications.localIntegrand c0 cu cv F.lam w0 du dv u t := by
    filter_upwards [Ioo_mem_nhds (by linarith : -ε < (0 : ℝ)) hε] with t ht
    have hLd : (L t).density =ᵐ[π] fun z => 1 + u * su z + t * sv z :=
      Filter.Eventually.of_forall fun z => by
        change 1 + u * su z + clip ε t * sv z = _
        rw [clip_eq ht]
    have hLl : ∀ᵐ z ∂π, (1 / 2 : ℝ) ≤ (L t).density z :=
      Filter.Eventually.of_forall fun z =>
        affine_density_lower su sv u ε K t (le_of_lt hε) hK hu hsmall hbu hbv z
    exact model_target_response_affine π A F η (L t) su sv hsu hsv K hK hbu hbv
      u t a0 b0 hbase hLd hLl hU0 hV0 hRu hRv hSu hSv
  have hG := Applications.localIntegrand_v_hasDerivAt c0 cu cv F.lam w0 du dv u hdu
  have hD : cv + F.lam * u / (w0 + du * u) ≠ 0 := by
    rw [← hG.deriv]
    exact hsu' hune
  obtain ⟨c,hc,huniform⟩ := response_path_uniform_minimax π η su sv hsu hsv u ε K hε hK hu hsmall hbu hbv hmu hmv
    (fun t => Applications.localIntegrand c0 cu cv F.lam w0 du dv u t)
    (cv + F.lam * u / (w0 + du * u)) hG hD

  refine ⟨c,hc,?_⟩
  intro T C tstar hclass htarget
  have htG : (fun t => T (P t).probabilityMeasure) =ᶠ[nhds 0]
      fun t => Applications.localIntegrand c0 cu cv F.lam w0 du dv u t + tstar := by
    filter_upwards [htarget, hrepr] with t ht hr
    exact ht.trans (congrArg (fun x => x + tstar) hr)
  exact huniform T C tstar hclass htG

theorem actual_diagonal_target_rootn_near_uniform (A : Model.Parameters) (F : Model.Observables Z A)
    (η : Measure (Model.Covariate A.d)) [IsProbabilityMeasure η]
    (s : Z → ℝ) (hs : Measurable s) (ε K : ℝ)
    (hε : 0 < ε) (hK : 0 ≤ K) (hsmall : ε * K ≤ 1 / 4)
    (hb : ∀ z, |s z| ≤ K) (hm : (∫ z, s z ∂π) = 0)
    (a0 : ℝ) (hbase : 0 < ∫ z, F.D z ∂π) (hUV : F.U = F.V)
    (hU0 : (∫ z, F.U z ∂π) = a0 * ∫ z, F.D z ∂π)
    (hR : (∫ z, (F.U z - a0 * F.D z) * s z ∂π) = 1) :
    ∀ᶠ u : ℝ in nhds 0, u ≠ 0 → ∃ hu : |u| ≤ ε,
      let P := fun t => withDesign π η
        (responseDensityLaw π s s hs hs u ε K (le_of_lt hε) hK hu hsmall hb hb hm hm t)
      ∃ c : ℝ, 0 < c ∧
      ∀ (T : ProbabilityMeasure (Model.Covariate A.d × Z) → ℝ)
        (C : Set (ProbabilityMeasure (Model.Covariate A.d × Z))) (tstar : ℝ),
        (∀ᶠ t in nhds 0, (P t).probabilityMeasure ∈ C) →
        ((fun t => T (P t).probabilityMeasure) =ᶠ[nhds 0]
          fun t => Model.target A F (P t).probabilityMeasure + tstar) →
        ∀ᶠ n : ℕ in Filter.atTop,
          ENNReal.ofReal (c * (n : ℝ) ^ (-(1 / 2 : ℝ))) ≤ Model.minimaxRMSE n T C := by
  let c0 := (∫ z, F.W z ∂π) + F.lam * (a0 ^ 2 * ∫ z, F.D z ∂π)
  let c1 := (∫ z, F.W z * s z ∂π) +
    F.lam * (a0 ^ 2 * (∫ z, F.D z * s z ∂π) + 2 * a0)
  let w0 := ∫ z, F.D z ∂π
  let d1 := ∫ z, F.D z * s z ∂π
  have hw0 : w0 ≠ 0 := ne_of_gt hbase
  have hden : ∀ᶠ u : ℝ in nhds 0, w0 + d1 * u ≠ 0 := by
    have hc : ContinuousAt (fun u : ℝ => w0 + d1 * u) 0 := by fun_prop
    exact hc.eventually_ne (by simpa using hw0)
  have hslope := Applications.diagonalIntegrand_nonzero_slope_near c0 c1 c1 F.lam w0 d1 d1
    F.hlam hw0
  have hu_near : ∀ᶠ u : ℝ in nhds 0, |u| ≤ ε := by
    filter_upwards [Ioo_mem_nhds (by linarith : -ε < (0 : ℝ)) hε] with u hu
    exact abs_le.mpr ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  filter_upwards [hden, hslope, hu_near] with u hdu hsu' hu
  intro hune
  refine ⟨hu, ?_⟩
  dsimp only
  let L := fun t => responseDensityLaw π s s hs hs u ε K (le_of_lt hε) hK hu hsmall hb hb hm hm t
  let P := fun t => withDesign π η (L t)
  have hrepr : (fun t => Model.target A F (P t).probabilityMeasure) =ᶠ[nhds 0]
      fun t => Applications.diagonalIntegrand c0 c1 c1 F.lam w0 d1 d1 u t := by
    filter_upwards [Ioo_mem_nhds (by linarith : -ε < (0 : ℝ)) hε] with t ht
    have hLd : (L t).density =ᵐ[π] fun z => 1 + u * s z + t * s z :=
      Filter.Eventually.of_forall fun z => by
        change 1 + u * s z + clip ε t * s z = _
        rw [clip_eq ht]
    have hLl : ∀ᵐ z ∂π, (1 / 2 : ℝ) ≤ (L t).density z :=
      Filter.Eventually.of_forall fun z =>
        affine_density_lower s s u ε K t (le_of_lt hε) hK hu hsmall hb hb z
    exact model_target_response_diagonal π A F η (L t) s hs K hK hb
      u t a0 hbase hLd hLl hUV hU0 hR
  have hG := Applications.diagonalIntegrand_v_hasDerivAt c0 c1 c1 F.lam w0 d1 d1 u hdu
  have hD : Applications.diagonalSlope c1 F.lam w0 d1 d1 u ≠ 0 := by
    rw [← hG.deriv]
    exact hsu' hune
  obtain ⟨c,hc,huniform⟩ := response_path_uniform_minimax π η s s hs hs u ε K hε hK hu hsmall hb hb hm hm
    (fun t => Applications.diagonalIntegrand c0 c1 c1 F.lam w0 d1 d1 u t)
    (Applications.diagonalSlope c1 F.lam w0 d1 d1 u) hG hD
  refine ⟨c,hc,?_⟩
  intro T C tstar hclass htarget
  have htG : (fun t => T (P t).probabilityMeasure) =ᶠ[nhds 0]
      fun t => Applications.diagonalIntegrand c0 c1 c1 F.lam w0 d1 d1 u t + tstar := by
    filter_upwards [htarget, hrepr] with t ht hr
    exact ht.trans (congrArg (fun x => x + tstar) hr)
  exact huniform T C tstar hclass htG

end RoughRegime.AffineResponseLower
