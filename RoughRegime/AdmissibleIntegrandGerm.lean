module

public import RoughRegime.AdmissibleReductionTesting
public import RoughRegime.IntegrandGerm


@[expose] public section
/-! Proposition 12 needs only a C4 germ. Values of an arbitrary integrand
outside the genuine source neighborhood never enter the statistical laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
namespace RoughRegime.PoissonMeasure.AdmissiblePhaseExperiment
variable {H X Z Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Z] [MeasurableSpace Y] {p : ℕ} [NeZero p]
    {μ : Measure X} [IsProbabilityMeasure μ] {π : ProbabilityMeasure Z}
    (E : AdmissiblePhaseExperiment (H:=H) (Y:=Y) p μ π)

 omit [NeZero p] [IsProbabilityMeasure μ] in
 theorem targetFunctional_congr_box (F G : ℝ×ℝ→ℝ) (r : ℝ) (hr : 0 ≤ r)
     (hEq : ∀u v,|u| ≤ r→|v| ≤ r→F (u,v)=G (u,v))
     (hu : E.C0*E.Au ≤ r) (hv : E.C0*E.Av ≤ r) (q : Fin p→PhaseParameter H) :
     E.targetFunctional F q=E.targetFunctional G q := by
   unfold targetFunctional
   have h0 : F 0=G 0 := hEq 0 0 (by simpa using hr) (by simpa using hr)
   rw [h0]
   congr 2
   apply Finset.sum_congr rfl
   intro i _
   unfold AdmissiblePhasePair.localTarget
   apply integral_congr_ae
   filter_upwards with x
   unfold AdmissiblePhasePair.responseIntegrand
   rw [h0]
   congr 2
   apply hEq
   · have hsign (s:Bool)(a:ℝ) : |Lower.sign s*a|=|a| := by cases s <;> simp [Lower.sign]
     rw [hsign]
     exact ((E.pairs i).unsignedProfileU_bound E.lo_pos E.Au E.amplitudeU_nonneg (q i).1 x).trans hu
   · have hsign (s:Bool)(a:ℝ) : |Lower.sign s*a|=|a| := by cases s <;> simp [Lower.sign]
     rw [hsign]
     exact ((E.pairs i).unsignedProfileV_bound E.lo_pos E.Av E.amplitudeV_nonneg (q i).1 x).trans hv

end RoughRegime.PoissonMeasure.AdmissiblePhaseExperiment

namespace RoughRegime.PoissonMeasure.AdmissibleReductionTesting
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open AdmissiblePhasePair
 theorem local_admissible_testing_lower (Phi : ℝ×ℝ→ℝ)
     (hPhi4 : ContDiffAt ℝ 4 Phi 0) :
     ∃ epsilon>0,∃ C ≥ 0,∃ B ≥ 0,∀ {H X Z Y : Type*} [MeasurableSpace H]
       [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
       {p : ℕ} [NeZero p] (μ : Measure X) [IsProbabilityMeasure μ] (π : ProbabilityMeasure Z)
       (E : AdmissiblePhaseExperiment (H:=H) (Y:=Y) p μ π)
       (nu : Fin p→Measure H) [∀ i,IsProbabilityMeasure (nu i)]
       (M : ℕ) (CG CE R Lambda : ℝ) (rate : ℝ≥0)
       (_hAu1 : E.Au ≤ 1) (_hAv1 : E.Av ≤ 1)
       (_hu : E.C0*E.Au ≤ epsilon) (_hv : E.C0*E.Av ≤ epsilon)
       (_hLambda : 0 ≤ Lambda) (_hCG : 0 ≤ CG) (_hR : 0<R) (_hratepos : 0<rate)
       (_hrate : ((rate*E.pairMass/(p:ℝ≥0):ℝ≥0):ℝ) ≤ 1)
       (_hscale : ((rate*E.pairMass/(p:ℝ≥0):ℝ≥0):ℝ) ≤ 2*E.barp*Lambda)
       (_hGamma : ∀i j,M ≤ j→(E.pairs i).field.gammaNorm (nu i) ((2:ENNReal)•μ) E.Au E.Av M j ≤
         CG^(j+1)*E.Au^2*E.Av^2*Real.exp (CE*M)*LatticePriors.gammaSpatialFactor R M j)
       (_hHard : (p:ℝ)*LatticePriors.canonicalPoissonMajorant
         (comparisonStar E.lo E.hi E.barp E.C0 E.scores.C) CG CE R Lambda E.Au E.Av M ≤ 1/128)
       (c2 gap delta : ℝ) (_hc2 : 0<c2) (_hgap : 0<gap) (_hdelta : 0<delta)
       (_hBilinear : c2*gap ≤ |(∫q,E.targetFunctional (fun x=>x.1*x.2) q ∂AdmissiblePhaseExperiment.parameterPrior nu M true)-
         (∫q,E.targetFunctional (fun x=>x.1*x.2) q ∂AdmissiblePhaseExperiment.parameterPrior nu M false)|)
       (_hTaylor : 4*delta ≤ |OddTaylor.mixedDerivative Phi 0| *c2*gap-
         E.v0*C*E.hi*E.C0^4*E.Au*E.Av*(E.Au^2+E.Av^2))
       (_hVar : 8*E.v0^2*(E.hi*B)^2/(2*p:ℕ) ≤ (4*delta)^2/1024)
       (T : ProbabilityMeasure Y→ℝ) (Cls : Set (ProbabilityMeasure Y))
       (_hT : ∀q,T (E.observationProbability q)=E.targetFunctional Phi q)
       (_hCls : ∀q,E.observationProbability q∈Cls)
       (n : ℕ) (_hcount : ProbabilityTheory.poissonMeasure rate {m | m<n} ≤ (1/32:ℝ≥0∞)),
       (3/8:ℝ≥0∞) ≤ Model.minimaxTail n T Cls delta ∧
         ENNReal.ofReal (delta/2) ≤ Model.minimaxRMSE n T Cls := by
   obtain ⟨r,hr,G,hG,hG4,hbox,hMixed⟩ := OddTaylor.exists_continuous_representative Phi hPhi4
   obtain ⟨epsilon,he,C,hC,B,hB,hFinite⟩ := admissible_testing_lower G hG.measurable hG4
   refine ⟨min epsilon r,lt_min he hr,C,hC,B,hB,?_⟩
   intro H X Z Y _ _ _ _ p _ μ _ π E nu _ M CG CE R Lambda rate hAu1 hAv1 hu hv
     hLambda hCG hR hratepos hrate hscale hGamma hHard c2 gap delta hc2 hgap hdelta hBilinear hTaylor hVar T Cls hT hCls n hcount
   have hue := hu.trans (min_le_left _ _)
   have hve := hv.trans (min_le_left _ _)
   have hur := hu.trans (min_le_right _ _)
   have hvr := hv.trans (min_le_right _ _)
   have hTaylorG : 4*delta ≤ |OddTaylor.mixedDerivative G 0| *c2*gap-
       E.v0*C*E.hi*E.C0^4*E.Au*E.Av*(E.Au^2+E.Av^2) := by
     rw [hMixed]
     exact hTaylor
   have hTg (q : Fin p→PhaseParameter H) : T (E.observationProbability q)=E.targetFunctional G q := by
     rw [hT]
     exact (E.targetFunctional_congr_box G Phi r hr.le hbox hur hvr q).symm
   exact hFinite μ π E nu M CG CE R Lambda rate hAu1 hAv1 hue hve hLambda hCG hR hratepos
     hrate hscale hGamma hHard c2 gap delta hc2 hgap hdelta hBilinear hTaylorG hVar T Cls hTg hCls n hcount

end RoughRegime.PoissonMeasure.AdmissibleReductionTesting
