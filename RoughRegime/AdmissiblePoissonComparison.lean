module

public import RoughRegime.AdmissibleLikelihoodMean
public import RoughRegime.AdmissibleComparisonUniform
public import RoughRegime.AffineResponseLower


@[expose] public section
/-! Standalone original Lemma 11: physical coefficients and actual marked
Poisson prior mixtures, under the original pointwise response smallness.
The fixed count bound follows from B≥n and permits rates above one. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace RoughRegime.PoissonMeasure.AdmissiblePhasePair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {H X Z : Type*} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Z]
    {μ : Measure X} [IsProbabilityMeasure μ] {π : Measure Z} [IsProbabilityMeasure π]
    {lo hi barp C0 : ℝ}

 def physicalGamma (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (nu : Measure H) [IsProbabilityMeasure nu] (Au Av : ℝ) (M j : ℕ)
     (xs : Fin (j+2)→X) : ℝ :=
   (∫q,labeledTensor (A.field.feature Au Av) (j+2) (leadingLabels j) q xs
     ∂(phasePrior nu M 1 (by norm_num)).measure)-
   (∫q,labeledTensor (A.field.feature Au Av) (j+2) (leadingLabels j) q xs
     ∂(phasePrior nu M (-1) (by norm_num)).measure)

 omit [IsProbabilityMeasure μ] in
 theorem physicalGamma_eq (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (nu : Measure H) [IsProbabilityMeasure nu] (hlo : 0<lo) (hhi : 0 ≤ hi)
     (hbarp : 0 ≤ barp) (hC0 : 0 ≤ C0) (Au Av : ℝ)
     (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (M j : ℕ) (xs : Fin (j+2)→X) :
     A.physicalGamma nu Au Av M j xs=
       labeledMixture (phaseBase nu) (phaseDifference M) (A.field.feature Au Av)
         (j+2) (leadingLabels j) xs := by
   have hb := A.field_bounded hlo hhi hbarp hC0
   have hC := rawBound_nonneg (lo:=lo) hhi hbarp hC0
   have hm : Measurable (fun q:PhaseParameter H=>
       labeledTensor (A.field.feature Au Av) (j+2) (leadingLabels j) q xs) :=
     (labeledTensor_measurable _ (A.field.feature_measurable A.measurable Au Av) (j+2) (leadingLabels j)).comp (measurable_id.prodMk measurable_const)
   let V := (3*rawBound lo hi barp C0)^(j+2)*Au^labelCount (j+2) (leadingLabels j) 1*
     Av^labelCount (j+2) (leadingLabels j) 2
   have hbound (q:PhaseParameter H) : |labeledTensor (A.field.feature Au Av) (j+2) (leadingLabels j) q xs| ≤ V :=
     A.field.tensor_bound Au Av _ hAu hAv hC hb.c hb.a hb.b hb.hu hb.hv _ _ _ _
   have hI (s:ℝ)(hs:|s| ≤ 1) : Integrable (fun q:PhaseParameter H=>
       phaseDensity M s q*labeledTensor (A.field.feature Au Av) (j+2) (leadingLabels j) q xs) (phaseBase nu) := by
     apply bounded_integrable _ _ ((phaseDensity_measurable M s).mul hm) (2*V)
     intro q
     change |phaseDensity M s q*labeledTensor (A.field.feature Au Av) (j+2) (leadingLabels j) q xs| ≤ 2*V
     rw [abs_mul]
     exact mul_le_mul ((phaseDensity_bound M s hs q).2) (hbound q) (abs_nonneg _) (by norm_num)
   unfold physicalGamma
   rw [AffineResponseLower.densityLaw_integral_eq,AffineResponseLower.densityLaw_integral_eq]
   change (∫q,phaseDensity M 1 q*labeledTensor (A.field.feature Au Av) (j+2) (leadingLabels j) q xs ∂phaseBase nu)-
     (∫q,phaseDensity M (-1) q*labeledTensor (A.field.feature Au Av) (j+2) (leadingLabels j) q xs ∂phaseBase nu)=_
   rw [←integral_sub (hI 1 (by norm_num)) (hI (-1) (by norm_num))]
   apply integral_congr_ae
   filter_upwards with q
   dsimp only [phasePrior,labeledMixture,phaseDifference]
   ring

 def sourceRawBound (lo hi C0 : ℝ) : ℝ := rawBound lo hi hi C0
 def sourceNormBound (lo hi C0 : ℝ) : ℝ := sourceRawBound lo hi C0/lo
 def sourceComparisonConstant (lo hi v0 C0 scoreBound : ℝ) : ℝ :=
   physicalComparisonConstant
     (comparisonConstant (sourceNormBound lo hi C0) (max 1 scoreBound) (lo/(2*hi)) (4*v0*hi))
     (1/lo^2) (2*hi)

 omit [IsProbabilityMeasure μ] in
 theorem field_bounded_source (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0 ≤ barp) (hbarphi : barp ≤ hi) (hC0 : 0 ≤ C0) :
     A.field.Bounded (sourceRawBound lo hi C0) := by
   have hb := A.field_bounded hlo hhi hbarp hC0
   have he : rawBound lo hi barp C0 ≤ sourceRawBound lo hi C0 := by
     simp only [sourceRawBound,rawBound]
     linarith
   exact ⟨fun q x=>(hb.c q x).trans he,fun q x=>(hb.a q x).trans he,
     fun q x=>(hb.b q x).trans he,fun q x=>(hb.hu q x).trans he,fun q x=>(hb.hv q x).trans he⟩

 omit [IsProbabilityMeasure μ] in
 theorem physicalGamma_zero (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (nu : Measure H) [IsProbabilityMeasure nu] (hlo : 0<lo) (hhi : 0 ≤ hi)
     (hbarp : 0 ≤ barp) (hC0 : 0 ≤ C0) (Au Av : ℝ)
     (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
     (M j : ℕ) (hj : j<M) (xs : Fin (j+2)→X) : A.physicalGamma nu Au Av M j xs=0 := by
   rw [A.physicalGamma_eq nu hlo hhi hbarp hC0 Au Av hAu hAv]
   exact A.field.labeled_low_degree A.measurable nu Au Av _ hAu hAu1 hAv hAv1
     (rawBound_nonneg hhi hbarp hC0) (A.field_bounded hlo hhi hbarp hC0) M _ _
     (by simpa only [leadingLabels_count_density] using hj) xs


 theorem source_normalization_bounds (hlo : 0<lo) (hhi : 0<hi)
     (hbarp : lo ≤ barp) (_hbarphi : barp ≤ hi) (hC0 : 0 ≤ C0) :
     0 ≤ sourceRawBound lo hi C0 ∧ 0 ≤ sourceNormBound lo hi C0 ∧
       |1/barp| * sourceRawBound lo hi C0 ≤ sourceNormBound lo hi C0 ∧
       (1/barp)^2 ≤ 1/lo^2 := by
   have hp : 0<barp := hlo.trans_le hbarp
   have hr := rawBound_nonneg (lo:=lo) hhi.le hhi.le hC0
   have hi : 1/barp ≤ 1/lo := one_div_le_one_div_of_le hlo hbarp
   refine ⟨hr,div_nonneg hr hlo.le,?_,?_⟩
   · rw [abs_of_pos (one_div_pos.mpr hp)]
     simpa only [sourceNormBound,sourceRawBound,div_eq_mul_inv,one_mul,mul_one,mul_comm] using
       mul_le_mul_of_nonneg_right hi hr
   · calc
       (1/barp)^2 ≤ (1/lo)^2 := pow_le_pow_left₀ (by positivity) hi _
       _ = 1/lo^2 := by rw [div_pow,one_pow]

 omit [IsProbabilityMeasure μ] in
 theorem normalized_field_bounded_source (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (hlo : 0<lo) (hhi : 0<hi) (hbarp : lo ≤ barp) (hbarphi : barp ≤ hi) (hC0 : 0 ≤ C0) :
     (A.field.scale (1/barp)).Bounded (sourceNormBound lo hi C0) := by
   have hb := A.field.scale_bounded (1/barp) _
     (A.field_bounded_source hlo hhi.le (hlo.trans_le hbarp).le hbarphi hC0)
   have he := (source_normalization_bounds hlo hhi hbarp hbarphi hC0).2.2.1
   exact ⟨fun q x=>(hb.c q x).trans he,fun q x=>(hb.a q x).trans he,
     fun q x=>(hb.b q x).trans he,fun q x=>(hb.hu q x).trans he,fun q x=>(hb.hv q x).trans he⟩

 theorem likelihood_lower_source (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (S : SpatialAffine.Scores π) (Au Av : ℝ) (hlo : 0<lo) (hhi : 0<hi)
     (hbarp : lo ≤ barp) (hbarphi : barp ≤ hi)
     (hpoint : ∀(q:H×ℝ)(x:X)(z:Z),|A.unsignedProfileU Au q x*S.su z|+
       |A.unsignedProfileV Av q x*S.sv z|≤1/2) (q : PhaseParameter H) (o : X×Z) :
     lo/(2*hi) ≤ A.likelihood S Au Av q o := by
   apply le_trans _ (A.likelihood_lower_pointwise S Au Av hlo (hlo.trans_le hbarp) hpoint q o)
   have hp : 0<barp := hlo.trans_le hbarp
   exact (div_le_div_iff₀ (by positivity : 0<2*hi) (by positivity : 0<2*barp)).mpr (by nlinarith)

 def sourcePoissonMixture (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (nu : Measure H) [IsProbabilityMeasure nu] (S : SpatialAffine.Scores π)
     (hlo : 0<lo) (hhi : 0<hi) (hbarp : lo ≤ barp) (hbarphi : barp ≤ hi) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
     (hpoint : ∀(q:H×ℝ)(x:X)(z:Z),|A.unsignedProfileU Au q x*S.su z|+
       |A.unsignedProfileV Av q x*S.sv z|≤1/2) (M : ℕ) (rate : ℝ≥0) (positive : Bool) :
     GeneralTesting.DensityLaw (referenceProcess (μ.prod π) rate) :=
   (A.field.scale (1/barp)).poissonLaw nu μ π (A.field.scale_isMeasurable A.measurable _)
     Au Av (sourceNormBound lo hi C0) (max 1 S.C) hAu hAu1 hAv hAv1
     (source_normalization_bounds hlo hhi hbarp hbarphi hC0).2.1
     (zero_le_one.trans (le_max_left _ _))
     (A.normalized_field_bounded_source hlo hhi hbarp hbarphi hC0)
     (phaseScores S) (phaseScores_measurable S) (phaseScores_bound S)
     (A.markedFactor_integral_zero_without_smallness S hlo hhi.le (hlo.trans_le hbarp) hC0 Au Av)
     (lo/(2*hi)) (by positivity) (A.likelihood_lower_source S Au Av hlo hhi hbarp hbarphi hpoint)
     M rate positive

/-- Original Lemma 11, allowing the full fixed count range forced by B≥n.
The priors are actual normalized marked-Poisson mixtures, and the response
assumption is the paper's pointwise one-half bound. -/
 theorem source_poisson_comparison {p : ℕ} [NeZero p]
     (A : Fin p→AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (nu : Fin p→Measure H) [∀i,IsProbabilityMeasure (nu i)] (S : SpatialAffine.Scores π)
     (hlo : 0<lo) (hhi : 0<hi) (hbarp : lo ≤ barp) (hbarphi : barp ≤ hi) (hC0 : 0 ≤ C0)
     (v0 : ℝ) (_hv0 : 0 ≤ v0) (Au Av : ℝ)
     (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
     (hpoint : ∀i(q:H×ℝ)(x:X)(z:Z),|(A i).unsignedProfileU Au q x*S.su z|+
       |(A i).unsignedProfileV Av q x*S.sv z|≤1/2)
     (M : ℕ) (rate : ℝ≥0) (Lambda : ℝ) (hLambda : 0 ≤ Lambda)
     (hRate : (rate:ℝ) ≤ 4*v0*hi) (hRateScale : (rate:ℝ) ≤ 2*hi*Lambda) :
     let C := sourceComparisonConstant lo hi v0 C0 S.C
     1 ≤ C ∧ GeneralTesting.hellingerSquared
       (LowerMeasure.productDensityLaw (fun i=>(A i).sourcePoissonMixture (nu i) S hlo hhi hbarp hbarphi hC0
         Au Av hAu hAu1 hAv hAv1 (hpoint i) M rate true))
       (LowerMeasure.productDensityLaw (fun i=>(A i).sourcePoissonMixture (nu i) S hlo hhi hbarp hbarphi hC0
         Au Av hAu hAu1 hAv hAv1 (hpoint i) M rate false)) ≤
       C*(2*p)*Lambda^2*(∑'j,if M ≤ j then (C*Lambda)^j/j.factorial*
         AffinePhaseField.physicalGammaMaximum nu μ (fun i=>(A i).field) Au Av M j else 0)+
       C*(2*p)*Lambda^4*Au^2*Av^2*(Au^2+Av^2)^2*((C*Lambda)^M/M.factorial) := by
   have hn := source_normalization_bounds hlo hhi hbarp hbarphi hC0
   have he := AffinePhaseField.physical_pair_comparison nu μ π
     (fun i=>(A i).field) (fun i=>(A i).measurable) Au Av (sourceRawBound lo hi C0)
     (sourceNormBound lo hi C0) (max 1 S.C) (1/barp) (1/lo^2) (2*hi) Lambda
     hAu hAu1 hAv hAv1 hn.1 hn.2.1 (zero_le_one.trans (le_max_left _ _))
     (by positivity) hn.2.2.2 (by positivity) hLambda
     (fun i=>(A i).field_bounded_source hlo hhi.le (hlo.trans_le hbarp).le hbarphi hC0) hn.2.2.1
     (phaseScores S) (phaseScores_measurable S) (phaseScores_bound S)
     (fun i=>(A i).markedFactor_integral_zero_without_smallness S hlo hhi.le (hlo.trans_le hbarp) hC0 Au Av)
     (lo/(2*hi)) (by positivity)
     (fun i=>(A i).likelihood_lower_source S Au Av hlo hhi hbarp hbarphi (hpoint i))
     M rate (4*v0*hi) hRate hRateScale
   dsimp only at he
   change 1 ≤ sourceComparisonConstant lo hi v0 C0 S.C ∧ _ at he
   refine ⟨he.1,he.2.trans ?_⟩
   have hc : 0 ≤ sourceComparisonConstant lo hi v0 C0 S.C := zero_le_one.trans he.1
   have hp : (p:ℝ) ≤ 2*p := by nlinarith [Nat.cast_nonneg (α:=ℝ) p]
   dsimp only [sourceComparisonConstant] at hc ⊢
   apply add_le_add
   · gcongr
     exact tsum_nonneg (fun j=>by
       have hg := finiteMaximum_nonneg (fun i=>(A i).field.gammaNorm (nu i) ((2:ENNReal)•μ) Au Av M j)
         (fun i=>(A i).field.gammaNorm_nonneg (nu i) _ Au Av M j)
       split_ifs <;> positivity)
   · gcongr


 def physicalGammaNorm (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (nu : Measure H) [IsProbabilityMeasure nu] (Au Av : ℝ) (M j : ℕ) : ℝ :=
   ∫xs,(A.physicalGamma nu Au Av M j xs)^2 ∂Measure.pi (fun _ : Fin (j+2)=>(2:ENNReal)•μ)

 omit [IsProbabilityMeasure μ] in
 theorem physicalGammaNorm_eq (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (nu : Measure H) [IsProbabilityMeasure nu] (hlo : 0<lo) (hhi : 0 ≤ hi)
     (hbarp : 0 ≤ barp) (hC0 : 0 ≤ C0) (Au Av : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (M j : ℕ) :
     A.physicalGammaNorm nu Au Av M j=A.field.gammaNorm nu ((2:ENNReal)•μ) Au Av M j := by
   unfold physicalGammaNorm AffinePhaseField.gammaNorm labeledNormSquared
   simp_rw [A.physicalGamma_eq nu hlo hhi hbarp hC0 Au Av hAu hAv]

 def sampleLambda (v0 : ℝ) (n p : ℕ) : ℝ := 2*v0*n/(2*p)

 theorem sampleLambda_bounds (v0 : ℝ) (hv0 : 0 ≤ v0) (n p : ℕ) [NeZero p] (hn : n ≤ 2*p) :
     0 ≤ sampleLambda v0 n p ∧ sampleLambda v0 n p ≤ 2*v0 := by
   have hp : (0:ℝ)<2*p := by exact_mod_cast Nat.mul_pos (by norm_num) (NeZero.pos p)
   have hnR : (n:ℝ) ≤ 2*p := by exact_mod_cast hn
   refine ⟨by unfold sampleLambda; positivity,?_⟩
   unfold sampleLambda
   apply (div_le_iff₀ hp).mpr
   exact mul_le_mul_of_nonneg_left hnR (by positivity)

 def samplePairRate (v0 : ℝ) (hv0 : 0 ≤ v0) (n p : ℕ)
     (barp : ℝ) (hbarp : 0 ≤ barp) : ℝ≥0 :=
   ⟨2*barp*sampleLambda v0 n p,by unfold sampleLambda; positivity⟩

 theorem samplePairRate_bounds (v0 : ℝ) (hv0 : 0 ≤ v0) (n p : ℕ) [NeZero p]
     (barp : ℝ) (hbarp : 0 ≤ barp) (hbarphi : barp ≤ hi) (hhi : 0 ≤ hi) (hn : n ≤ 2*p) :
     ((samplePairRate v0 hv0 n p barp hbarp:ℝ≥0):ℝ) ≤ 4*v0*hi ∧
       ((samplePairRate v0 hv0 n p barp hbarp:ℝ≥0):ℝ) ≤ 2*hi*sampleLambda v0 n p := by
   have hb := sampleLambda_bounds v0 hv0 n p hn
   change 2*barp*sampleLambda v0 n p ≤ _ ∧ 2*barp*sampleLambda v0 n p ≤ _
   constructor
   · calc
       _ ≤ 2*hi*(2*v0) := mul_le_mul (by nlinarith) hb.2 hb.1 (by positivity)
       _ = _ := by ring
   · exact mul_le_mul_of_nonneg_right (by nlinarith) hb.1

/-- The standalone source statement at B=2p≥n has a comparison constant
chosen before n,B,M and amplitudes. Its Gamma norm is the literal prior
expectation difference integrated on the unnormalized physical two-block
space. Every low-degree Gamma vanishes. -/
 theorem original_lemma11 {p : ℕ} [NeZero p]
     (A : Fin p→AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (nu : Fin p→Measure H) [∀i,IsProbabilityMeasure (nu i)] (S : SpatialAffine.Scores π)
     (hlo : 0<lo) (hhi : 0<hi) (hbarp : lo ≤ barp) (hbarphi : barp ≤ hi) (hC0 : 0 ≤ C0)
     (v0 : ℝ) (hv0 : 0 ≤ v0) (n : ℕ) (hn : n ≤ 2*p) (Au Av : ℝ)
     (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
     (hpoint : ∀i(q:H×ℝ)(x:X)(z:Z),|(A i).unsignedProfileU Au q x*S.su z|+
       |(A i).unsignedProfileV Av q x*S.sv z|≤1/2) (M : ℕ) :
     let C := sourceComparisonConstant lo hi v0 C0 S.C
     let Lambda := sampleLambda v0 n p
     let rate := samplePairRate v0 hv0 n p barp (hlo.trans_le hbarp).le
     1 ≤ C ∧
       (∀i j,j<M→∀xs,(A i).physicalGamma (nu i) Au Av M j xs=0) ∧
       GeneralTesting.hellingerSquared
         (LowerMeasure.productDensityLaw (fun i=>(A i).sourcePoissonMixture (nu i) S hlo hhi hbarp hbarphi hC0
           Au Av hAu hAu1 hAv hAv1 (hpoint i) M rate true))
         (LowerMeasure.productDensityLaw (fun i=>(A i).sourcePoissonMixture (nu i) S hlo hhi hbarp hbarphi hC0
           Au Av hAu hAu1 hAv hAv1 (hpoint i) M rate false)) ≤
         C*(2*p)*Lambda^2*(∑'j,if M ≤ j then (C*Lambda)^j/j.factorial*
           finiteMaximum (fun i=>(A i).physicalGammaNorm (nu i) Au Av M j) else 0)+
         C*(2*p)*Lambda^4*Au^2*Av^2*(Au^2+Av^2)^2*((C*Lambda)^M/M.factorial) := by
   have hLambda := sampleLambda_bounds v0 hv0 n p hn
   have hRate := samplePairRate_bounds (hi:=hi) v0 hv0 n p barp (hlo.trans_le hbarp).le hbarphi hhi.le hn
   have hc := source_poisson_comparison A nu S hlo hhi hbarp hbarphi hC0 v0 hv0 Au Av
     hAu hAu1 hAv hAv1 hpoint M _ _ hLambda.1 hRate.1 hRate.2
   dsimp only
   refine ⟨hc.1,fun i j hj xs=>(A i).physicalGamma_zero (nu i) hlo hhi.le
     (hlo.trans_le hbarp).le hC0 Au Av hAu hAu1 hAv hAv1 M j hj xs,?_⟩
   have hnorm : ∀i j,(A i).physicalGammaNorm (nu i) Au Av M j=
       (A i).field.gammaNorm (nu i) ((2:ENNReal)•μ) Au Av M j :=
     fun i j=>(A i).physicalGammaNorm_eq (nu i) hlo hhi.le (hlo.trans_le hbarp).le hC0 Au Av hAu hAv M j
   simp_rw [hnorm]
   simpa only [AffinePhaseField.physicalGammaMaximum] using hc.2

end RoughRegime.PoissonMeasure.AdmissiblePhasePair
