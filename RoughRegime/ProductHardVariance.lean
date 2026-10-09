module

public import RoughRegime.ProductMoments
public import RoughRegime.CanonicalPoissonData
public import RoughRegime.SourceModel


@[expose] public section
/-! Actual Rademacher hard observations keep their response square equal to
one. Local mean bounds therefore give the variance restriction needed for R². -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
namespace RoughRegime.Applications.Products

theorem boundedDiagonalBaseline_sq_ae :
    ∀ᵐ (z : BoundedResponse) ∂(boundedDiagonalBaseline : Measure BoundedResponse),(z:ℝ)^2=1 := by
  change ∀ᵐ (z : BoundedResponse) ∂(diagonalBaseline : Measure Bool).map signPoint,(z:ℝ)^2=1
  apply (ae_map_iff (measurable_of_countable signPoint).aemeasurable
    (measurableSet_eq_fun (measurable_subtype_coe.pow_const 2) measurable_const)).mpr
  exact Filter.Eventually.of_forall (fun b => by cases b <;> norm_num [signPoint,sign])

theorem quadratic_baselineB_zero (A : Model.Parameters) (hM : 1≤A.M0) :
    Model.baselineB A (quadraticObservables A hM) boundedDiagonalBaseline=0 := by
  have hmean : (∫ z : BoundedResponse,(z:ℝ) ∂(boundedDiagonalBaseline : Measure BoundedResponse))=0 := by
    rw [boundedDiagonalBaseline_integral _ measurable_subtype_coe]
    norm_num [signPoint,sign]
  change (∫ z : BoundedResponse,(z:ℝ) ∂(boundedDiagonalBaseline : Measure BoundedResponse)) / _=0
  rw [hmean,zero_div]

theorem quadratic_local_responseMean_abs_le (A : Model.Parameters) (hM : 1≤A.M0)
    (r : ℝ) (P : ProbabilityMeasure (Model.Observation A BoundedResponse))
    (hP : P ∈ Model.localClass A (quadraticObservables A hM) boundedDiagonalBaseline r) :
    |responseMean A P|≤r := by
  obtain ⟨WM,hclose⟩ := hP
  let W := fromModel A (quadraticObservables A hM) rfl P WM
  have hb : ∀ᵐ x ∂Model.cubeVolume A.d,|WM.b x|≤r := by
    filter_upwards [hclose] with x hx
    simpa only [quadratic_baselineB_zero A hM,sub_zero] using hx.2.2
  have hbp : ∀ᵐ o ∂(P : Measure (Model.Observation A BoundedResponse)),|WM.b o.1|≤r := by
    apply ae_of_ae_map (f := Prod.fst) (p := fun x => |WM.b x|≤r) measurable_fst.aemeasurable
    rw [WM.marginal]
    exact hb.filter_mono (withDensity_absolutelyContinuous _ _).ae_le
  have ht : responseMean A P=∫ o, WM.b o.1 ∂(P : Measure (Model.Observation A BoundedResponse)) := by
    calc
      _ = ∫ o, (P : Measure (Model.Observation A BoundedResponse))[
          ((Subtype.val : BoundedResponse→ℝ) ∘ Prod.snd) |
          Model.covariateInformation A BoundedResponse] o ∂(P : Measure _) :=
        (integral_condExp measurable_fst.comap_le).symm
      _ = _ := integral_congr_ae W.momentV
  rw [ht]
  have hh := norm_integral_le_of_norm_le_const
    (μ := (P : Measure (Model.Observation A BoundedResponse)))
    (f := fun o : Model.Observation A BoundedResponse => WM.b o.1) (C := r)
    (by simpa only [Real.norm_eq_abs] using hbp)
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using hh

theorem diagonal_affine_secondMoment_one {X : Type*} [MeasurableSpace X]
    (η : Measure X) [IsProbabilityMeasure η]
    (S : SpatialAffine.Scores (boundedDiagonalBaseline : Measure BoundedResponse))
    (F : SpatialAffine.Field η) (hsmall : F.epsilon*S.C≤1/4) :
    (∫ o : X×BoundedResponse,(o.2:ℝ)^2 ∂(SpatialAffine.law S F hsmall).measure)=1 := by
  have hp : ∀ᵐ (o : X×BoundedResponse) ∂η.prod
      (boundedDiagonalBaseline : Measure BoundedResponse),(o.2:ℝ)^2=1 :=
    ((Measure.quasiMeasurePreserving_snd (μ := η)
      (ν := (boundedDiagonalBaseline : Measure BoundedResponse))).tendsto_ae).eventually
      boundedDiagonalBaseline_sq_ae
  have hl : ∀ᵐ (o : X×BoundedResponse) ∂(SpatialAffine.law S F hsmall).measure,(o.2:ℝ)^2=1 := by
    change ∀ᵐ (o : X×BoundedResponse) ∂(η.prod
      (boundedDiagonalBaseline : Measure BoundedResponse)).withDensity _,(o.2:ℝ)^2=1
    exact hp.filter_mono (withDensity_absolutelyContinuous _ _).ae_le
  rw [integral_congr_ae hl,integral_const,probReal_univ,one_smul]

theorem canonical_responseSecondMoment_one (A0 : Model.Parameters) {D N : ℕ}
    {ι : Type*} [Fintype ι] (G : LatticePriors.CanonicalFrame D N ι)
    (S : SpatialAffine.Scores (boundedDiagonalBaseline : Measure BoundedResponse))
    (hsmall : (G.Au+G.Av)/G.rminus*S.C≤1/4)
    (z : LatticePriors.GridPair D N → LatticePriors.PairState ι) :
    responseSecondMoment (A0.withDimension D)
      (G.observationProbability boundedDiagonalBaseline S hsmall z)=1 :=
  diagonal_affine_secondMoment_one _ S (G.field z) hsmall

theorem canonical_local_responseVariance_lower (A0 : Model.Parameters) {D N : ℕ}
    {ι : Type*} [Fintype ι] (G : LatticePriors.CanonicalFrame D N ι)
    (S : SpatialAffine.Scores (boundedDiagonalBaseline : Measure BoundedResponse))
    (hsmall : (G.Au+G.Av)/G.rminus*S.C≤1/4)
    (z : LatticePriors.GridPair D N → LatticePriors.PairState ι)
    (hM : 1≤(A0.withDimension D).M0) (r vmin : ℝ) (hr : 0≤r) (hvr : r^2≤1-vmin)
    (hlocal : G.observationProbability boundedDiagonalBaseline S hsmall z ∈
      Model.localClass (A0.withDimension D) (quadraticObservables _ hM) boundedDiagonalBaseline r) :
    vmin≤responseVariance (A0.withDimension D)
      (G.observationProbability boundedDiagonalBaseline S hsmall z) := by
  let A := A0.withDimension D
  let P : ProbabilityMeasure (Model.Observation A BoundedResponse) :=
    G.observationProbability boundedDiagonalBaseline S hsmall z
  have hsecond : responseSecondMoment A P=1 := canonical_responseSecondMoment_one A0 G S hsmall z
  change vmin≤responseVariance A P
  rw [responseVariance_identity A P,hsecond]
  have hm := quadratic_local_responseMean_abs_le A hM r P hlocal
  have hsq := (sq_le_sq₀ (abs_nonneg (responseMean A P)) hr).mpr hm
  rw [sq_abs] at hsq
  linarith

end RoughRegime.Applications.Products
