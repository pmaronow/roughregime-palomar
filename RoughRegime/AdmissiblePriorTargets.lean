module

public import RoughRegime.AdmissiblePhasePair
public import RoughRegime.IndependentPriorVariance


@[expose] public section
/-! Actual nonlinear target means and concentration under arbitrary admissible
phase priors. All spatial integrals and independent products are genuine. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace RoughRegime.PoissonMeasure.AdmissiblePhasePair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {lo hi barp C0 : ℝ}

 def responseIntegrand (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (Phi : ℝ×ℝ→ℝ) (Au Av : ℝ) (z : PhaseParameter H×X) : ℝ :=
   A.field.designDensity barp z.1.1 z.2*
     (Phi (Lower.sign z.1.2.1*A.unsignedProfileU Au z.1.1 z.2,
       Lower.sign z.1.2.2*A.unsignedProfileV Av z.1.1 z.2)-Phi 0)

 def localTarget (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (Phi : ℝ×ℝ→ℝ) (Au Av : ℝ) (q : PhaseParameter H) : ℝ :=
   ∫ x,A.responseIntegrand Phi Au Av (q,x) ∂μ

 omit [IsProbabilityMeasure μ] in
 theorem responseIntegrand_measurable (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (Phi : ℝ×ℝ→ℝ) (hPhi : Measurable Phi) (Au Av : ℝ) :
     Measurable (A.responseIntegrand Phi Au Av) := by
   have hj : Measurable (fun z : PhaseParameter H×X=>(z.1.1,z.2)) := measurable_fst.fst.prodMk measurable_snd
   have hp := A.designDensity_measurable.comp hj
   have hu := (A.unsignedProfileU_measurable Au).comp hj
   have hv := (A.unsignedProfileV_measurable Av).comp hj
   have hs : Measurable Lower.sign := measurable_of_countable _
   unfold responseIntegrand
   exact hp.mul ((hPhi.comp (((hs.comp measurable_fst.snd.fst).mul hu).prodMk
     ((hs.comp measurable_fst.snd.snd).mul hv))).sub measurable_const)

 theorem localTarget_measurable (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (Phi : ℝ×ℝ→ℝ) (hPhi : Measurable Phi) (Au Av : ℝ) : Measurable (A.localTarget Phi Au Av) :=
   (A.responseIntegrand_measurable Phi hPhi Au Av).stronglyMeasurable.integral_prod_right'.measurable

 theorem localTarget_bound (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (hlo : 0<lo) (Phi : ℝ×ℝ→ℝ) (Au Av B : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av)
     (hbound : ∀ u v,|u| ≤ C0*Au→|v| ≤ C0*Av→|Phi (u,v)-Phi 0| ≤ B)
     (q : PhaseParameter H) : |A.localTarget Phi Au Av q| ≤ hi*B := by
   have hb : ∀ x,‖A.responseIntegrand Phi Au Av (q,x)‖ ≤ hi*B := by
     intro x
     rw [Real.norm_eq_abs]
     unfold responseIntegrand
     rw [abs_mul,abs_of_nonneg (hlo.trans_le (A.densityBounds q.1 x).1).le]
     have hsign (s : Bool) (u : ℝ) : |Lower.sign s*u|=|u| := by cases s <;> simp [Lower.sign]
     apply mul_le_mul (A.densityBounds q.1 x).2 _ (abs_nonneg _) ((hlo.trans_le (A.densityBounds q.1 x).1).trans_le (A.densityBounds q.1 x).2).le
     exact hbound _ _ (by rw [hsign]; exact A.unsignedProfileU_bound hlo Au hAu q.1 x)
       (by rw [hsign]; exact A.unsignedProfileV_bound hlo Av hAv q.1 x)
   have hh := norm_integral_le_of_norm_le_const (μ:=μ)
     (f:=fun x=>A.responseIntegrand Phi Au Av (q,x)) (C:=hi*B) (Filter.Eventually.of_forall hb)
   simpa only [localTarget,Real.norm_eq_abs,probReal_univ,mul_one] using hh

 omit [IsProbabilityMeasure μ] in
 theorem localTarget_phase_integral (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (nu : Measure H) [IsProbabilityMeasure nu] (M : ℕ) (positive : Bool)
     (Phi : ℝ×ℝ→ℝ) (Au Av : ℝ) :
     (∫ q,A.localTarget Phi Au Av q ∂(phasePrior nu M (if positive then 1 else -1)
       (by cases positive <;> norm_num)).measure)=
       ∫ q,spatialSignedTarget μ (fun x=>Phi x-Phi 0)
         (Function.uncurry (A.field.designDensity barp))
         (Function.uncurry (A.unsignedProfileU Au)) (Function.uncurry (A.unsignedProfileV Av)) q
           ∂nu.prod (RoughRegime.LatticeFourier.angleSignLaw M positive) := by
   let e : PhaseParameter H ≃ᵐ H×(ℝ×(Bool×Bool)) := MeasurableEquiv.prodAssoc
   have hmp : MeasurePreserving e
       (phasePrior nu M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure
       (nu.prod (RoughRegime.LatticeFourier.angleSignLaw M positive)) :=
     ⟨e.measurable,RoughRegime.LatticePriors.phasePrior_assoc nu M positive⟩
   exact hmp.integral_comp' (fun q=>spatialSignedTarget μ (fun x=>Phi x-Phi 0)
     (Function.uncurry (A.field.designDensity barp))
     (Function.uncurry (A.unsignedProfileU Au)) (Function.uncurry (A.unsignedProfileV Av)) q)

/-- A genuine C4 integrand supplies one neighborhood and a uniform local
nonlinear mean remainder for every admissible pair and every phase prior. -/
 theorem local_target_taylor (Phi : ℝ×ℝ→ℝ) (hPhi : Measurable Phi) (hPhi4 : ContDiffAt ℝ 4 Phi 0) :
     ∃ epsilon>0,∃ C ≥ 0,∀ {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
       (μ : Measure X) [IsProbabilityMeasure μ] {lo hi barp C0 : ℝ}
       (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
       (hlo : 0<lo) (hhi : 0 ≤ hi) (hC0 : 0 ≤ C0) (nu : Measure H) [IsProbabilityMeasure nu]
       (M : ℕ) (Au Av : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av),
     C0*Au ≤ epsilon→C0*Av ≤ epsilon→
     |((∫ q,A.localTarget Phi Au Av q ∂(phasePrior nu M 1 (by norm_num)).measure)-
        (∫ q,A.localTarget Phi Au Av q ∂(phasePrior nu M (-1) (by norm_num)).measure))-
       OddTaylor.mixedDerivative Phi 0*((∫ q,A.localTarget (fun x=>x.1*x.2) Au Av q
          ∂(phasePrior nu M 1 (by norm_num)).measure)-
        (∫ q,A.localTarget (fun x=>x.1*x.2) Au Av q ∂(phasePrior nu M (-1) (by norm_num)).measure))| ≤ 
       C*hi*C0^4*Au*Av*(Au^2+Av^2) := by
   obtain ⟨epsilon,he,C,hC,hTaylor⟩ := spatial_prior_target_taylor (fun x=>Phi x-Phi 0)
     (hPhi.sub measurable_const) (hPhi4.sub contDiffAt_const)
   refine ⟨epsilon,he,C,hC,?_⟩
   intro H X _ _ μ _ lo hi barp C0 A hlo hhi hC0 nu _ M Au Av hAu hAv hAue hAve
   have hp := A.localTarget_phase_integral nu M true Phi Au Av
   have hn := A.localTarget_phase_integral nu M false Phi Au Av
   have hup := A.localTarget_phase_integral nu M true (fun x=>x.1*x.2) Au Av
   have hun := A.localTarget_phase_integral nu M false (fun x=>x.1*x.2) Au Av
   simp only [Bool.false_eq_true,ite_false,ite_true] at hp hn hup hun
   rw [hp,hn,hup,hun]

   have h := hTaylor nu μ M (Function.uncurry (A.field.designDensity barp))
     (Function.uncurry (A.unsignedProfileU Au)) (Function.uncurry (A.unsignedProfileV Av))
     A.designDensity_measurable (A.unsignedProfileU_measurable Au) (A.unsignedProfileV_measurable Av)
     hi (C0*Au) (C0*Av) hhi (mul_nonneg hC0 hAu) (mul_nonneg hC0 hAv) hAue hAve
     (fun z=>by change |A.field.designDensity barp z.1 z.2| ≤ hi; rw [abs_of_nonneg (hlo.trans_le (A.densityBounds z.1 z.2).1).le];exact (A.densityBounds z.1 z.2).2)
     (fun z=>A.unsignedProfileU_bound hlo Au hAu z.1 z.2)
     (fun z=>A.unsignedProfileV_bound hlo Av hAv z.1 z.2)
   rw [mixedDerivative_sub_const] at h
   have heq : C*hi*(C0*Au)*(C0*Av)*((C0*Au)^2+(C0*Av)^2)=C*hi*C0^4*Au*Av*(Au^2+Av^2) := by ring
   rw [heq] at h
   simpa only [Prod.fst_zero,Prod.snd_zero,mul_zero,sub_zero] using h

end RoughRegime.PoissonMeasure.AdmissiblePhasePair
