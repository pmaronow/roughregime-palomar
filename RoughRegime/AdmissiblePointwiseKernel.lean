module

public import RoughRegime.AdmissiblePoissonComparison


@[expose] public section
/-! The original pointwise one-half response condition gives the actual
normalized spatial mark law, common Markov Poisson kernel, and exact native
prior marginal. No stronger global amplitude-smallness condition is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace RoughRegime.PoissonMeasure.AdmissiblePhasePair
set_option backward.isDefEq.respectTransparency false
variable {H X Z : Type*} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Z]
    {μ : Measure X} [IsProbabilityMeasure μ] {π : Measure Z} [IsProbabilityMeasure π]
    {lo hi barp C0 : ℝ}

 def pointwiseMarkLaw (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (S : SpatialAffine.Scores π) (hlo : 0 < lo) (hhi : 0 < hi)
     (hbarp : lo ≤ barp) (hbarphi : barp ≤ hi) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
     (hpoint : ∀ (q : H×ℝ) (x : X) (z : Z),
       |A.unsignedProfileU Au q x*S.su z|+|A.unsignedProfileV Av q x*S.sv z| ≤ 1/2)
     (q : PhaseParameter H) : GeneralTesting.DensityLaw (μ.prod π) :=
   pointLaw (μ.prod π) (A.likelihood S Au Av) (A.likelihood_measurable S Au Av)
     (1+9*normalizedBound lo hi barp C0*(max 1 S.C))
     (A.likelihood_abs_bound S hlo hhi.le (hlo.trans_le hbarp) hC0 Au Av hAu hAu1 hAv hAv1)
     (fun q y => (by positivity : (0:ℝ) ≤ lo/(2*hi)).trans
       (A.likelihood_lower_source S Au Av hlo hhi hbarp hbarphi hpoint q y))
     (A.likelihood_integral_without_smallness S hlo hhi.le (hlo.trans_le hbarp) hC0 Au Av) q

 theorem pointwiseMarkLaw_density (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (S : SpatialAffine.Scores π) (hlo : 0 < lo) (hhi : 0 < hi)
     (hbarp : lo ≤ barp) (hbarphi : barp ≤ hi) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
     (hpoint : ∀ (q : H×ℝ) (x : X) (z : Z),
       |A.unsignedProfileU Au q x*S.su z|+|A.unsignedProfileV Av q x*S.sv z| ≤ 1/2)
     (q : PhaseParameter H) (y : X×Z) :
     (A.pointwiseMarkLaw S hlo hhi hbarp hbarphi hC0 Au Av hAu hAu1 hAv hAv1 hpoint q).density y=
       A.likelihood S Au Av q y := rfl

 theorem poissonKernel_markov_pointwise (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (S : SpatialAffine.Scores π) (hlo : 0 < lo) (hhi : 0 < hi)
     (hbarp : lo ≤ barp) (hbarphi : barp ≤ hi) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
     (hpoint : ∀ (q : H×ℝ) (x : X) (z : Z),
       |A.unsignedProfileU Au q x*S.su z|+|A.unsignedProfileV Av q x*S.sv z| ≤ 1/2)
     (rate : ℝ≥0) : IsMarkovKernel (A.poissonKernel S Au Av rate) :=
   observationKernel_isMarkov (μ.prod π) (A.likelihood S Au Av) (A.likelihood_measurable S Au Av)
     (1+9*normalizedBound lo hi barp C0*(max 1 S.C))
     (A.likelihood_abs_bound S hlo hhi.le (hlo.trans_le hbarp) hC0 Au Av hAu hAu1 hAv hAv1)
     (fun q y => (by positivity : (0:ℝ) ≤ lo/(2*hi)).trans
       (A.likelihood_lower_source S Au Av hlo hhi hbarp hbarphi hpoint q y))
     (A.likelihood_integral_without_smallness S hlo hhi.le (hlo.trans_le hbarp) hC0 Au Av) rate

 theorem poissonKernel_marginal_pointwise (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (nu : Measure H) [IsProbabilityMeasure nu] (S : SpatialAffine.Scores π)
     (hlo : 0 < lo) (hhi : 0 < hi) (hbarp : lo ≤ barp) (hbarphi : barp ≤ hi) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
     (hpoint : ∀ (q : H×ℝ) (x : X) (z : Z),
       |A.unsignedProfileU Au q x*S.su z|+|A.unsignedProfileV Av q x*S.sv z| ≤ 1/2)
     (M : ℕ) (rate : ℝ≥0) (positive : Bool) :
     ((phasePrior nu M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure
       ⊗ₘ A.poissonKernel S Au Av rate).snd=
       (A.sourcePoissonMixture nu S hlo hhi hbarp hbarphi hC0
         Au Av hAu hAu1 hAv hAv1 hpoint M rate positive).measure := by
   exact observationKernel_marginal (μ.prod π) (phaseBase nu)
     (phasePrior nu M (if positive then 1 else -1) (by cases positive <;> norm_num))
     (A.likelihood S Au Av) (A.likelihood_measurable S Au Av) 2
     (1+9*normalizedBound lo hi barp C0*(max 1 S.C)) (by norm_num)
     (by have := normalizedBound_nonneg (lo:=lo) hhi.le (hlo.trans_le hbarp) hC0
         have := zero_le_one.trans (le_max_left 1 S.C)
         positivity)
     (fun q => (phaseDensity_bound M _ (by cases positive <;> norm_num) q).2)
     (A.likelihood_abs_bound S hlo hhi.le (hlo.trans_le hbarp) hC0 Au Av hAu hAu1 hAv hAv1)
     (fun q y => (by positivity : (0:ℝ) ≤ lo/(2*hi)).trans
       (A.likelihood_lower_source S Au Av hlo hhi hbarp hbarphi hpoint q y))
     (A.likelihood_integral_without_smallness S hlo hhi.le (hlo.trans_le hbarp) hC0 Au Av) rate

 theorem poissonKernel_apply_pointwise (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (S : SpatialAffine.Scores π) (hlo : 0 < lo) (hhi : 0 < hi)
     (hbarp : lo ≤ barp) (hbarphi : barp ≤ hi) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
     (hpoint : ∀ (q : H×ℝ) (x : X) (z : Z),
       |A.unsignedProfileU Au q x*S.su z|+|A.unsignedProfileV Av q x*S.sv z| ≤ 1/2)
     (rate : ℝ≥0) (q : PhaseParameter H) :
     A.poissonKernel S Au Av rate q=Measure.sum (fun n =>
       ENNReal.ofReal (Lower.poissonMass rate n) •
         ((LowerMeasure.iidDensityLaw
           (A.pointwiseMarkLaw S hlo hhi hbarp hbarphi hC0 Au Av hAu hAu1 hAv hAv1 hpoint q) n).measure).map
           (@Sigma.mk ℕ (fun k => Fin k→X×Z) n)) := by
   exact observationKernel_apply (μ.prod π) (A.likelihood S Au Av)
     (A.likelihood_measurable S Au Av) (1+9*normalizedBound lo hi barp C0*(max 1 S.C))
     (A.likelihood_abs_bound S hlo hhi.le (hlo.trans_le hbarp) hC0 Au Av hAu hAu1 hAv hAv1)
     (fun q y => (by positivity : (0:ℝ) ≤ lo/(2*hi)).trans
       (A.likelihood_lower_source S Au Av hlo hhi hbarp hbarphi hpoint q y))
     (A.likelihood_integral_without_smallness S hlo hhi.le (hlo.trans_le hbarp) hC0 Au Av) rate q

end RoughRegime.PoissonMeasure.AdmissiblePhasePair
