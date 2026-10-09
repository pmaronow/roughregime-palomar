module

public import RoughRegime.AdmissiblePriorTargets


@[expose] public section
/-! Genuine target mean and variance calculations for arbitrary independent
admissible pairs, with no identical-distribution assumption. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace RoughRegime.PoissonMeasure.AdmissibleTargets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {ι H X : Type*} [Fintype ι] [MeasurableSpace H] [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {lo hi barp C0 : ℝ}

 def independentPrior (nu : ι→Measure H) [∀ i,IsProbabilityMeasure (nu i)] (M : ℕ) (positive : Bool) :
     Measure (ι→PhaseParameter H) :=
   Measure.pi fun i=>(phasePrior (nu i) M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure

 instance independentPrior_probability (nu : ι→Measure H) [∀ i,IsProbabilityMeasure (nu i)]
     (M : ℕ) (positive : Bool) : IsProbabilityMeasure (independentPrior nu M positive) := by
   unfold independentPrior
   infer_instance

 def independentTarget (A : ι→AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (Phi : ℝ×ℝ→ℝ) (scale Au Av : ℝ) (q : ι→PhaseParameter H) : ℝ :=
   Phi 0+scale*∑ i,(A i).localTarget Phi Au Av (q i)

 theorem independentTarget_measurable (A : ι→AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (Phi : ℝ×ℝ→ℝ) (hPhi : Measurable Phi) (scale Au Av : ℝ) :
     Measurable (independentTarget A Phi scale Au Av) := by
   apply measurable_const.add
   apply measurable_const.mul
   exact Finset.measurable_sum Finset.univ fun i _=>
     ((A i).localTarget_measurable Phi hPhi Au Av).comp (measurable_pi_apply i)

 theorem independentTarget_memLp (A : ι→AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (Phi : ℝ×ℝ→ℝ) (hPhi : Measurable Phi) (scale Au Av B : ℝ)
     (hlo : 0<lo) (hAu : 0≤Au) (hAv : 0≤Av)
     (hbound : ∀ u v,|u|≤C0*Au→|v|≤C0*Av→|Phi (u,v)-Phi 0|≤B)
     (nu : ι→Measure H) [∀ i,IsProbabilityMeasure (nu i)] (M : ℕ) (positive : Bool) :
     MemLp (independentTarget A Phi scale Au Av) 2 (independentPrior nu M positive) := by
   apply MemLp.of_bound (independentTarget_measurable A Phi hPhi scale Au Av).aestronglyMeasurable
     (|Phi 0|+|scale| *Fintype.card ι*(hi*B))
   filter_upwards with q
   rw [Real.norm_eq_abs,independentTarget]
   have hs : |∑ i,(A i).localTarget Phi Au Av (q i)|≤Fintype.card ι*(hi*B) := by
     calc
       _ ≤ ∑ i,|(A i).localTarget Phi Au Av (q i)| := Finset.abs_sum_le_sum_abs _ _
       _ ≤ ∑ _i:ι,hi*B := Finset.sum_le_sum fun i _=>(A i).localTarget_bound hlo Phi Au Av B hAu hAv hbound (q i)
       _ = _ := by simp
   calc
     _ ≤ |Phi 0|+|scale*(∑ i,(A i).localTarget Phi Au Av (q i))| := abs_add_le _ _
     _ = |Phi 0|+|scale| *|∑ i,(A i).localTarget Phi Au Av (q i)| := by rw [abs_mul]
     _ ≤ _ := by
       simpa only [mul_assoc] using add_le_add (le_refl |Phi 0|) (mul_le_mul_of_nonneg_left hs (abs_nonneg scale))

 omit [IsProbabilityMeasure μ] in
 theorem independentTarget_integral (A : ι→AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (Phi : ℝ×ℝ→ℝ) (scale Au Av : ℝ)
     (nu : ι→Measure H) [∀ i,IsProbabilityMeasure (nu i)] (M : ℕ) (positive : Bool)
     (hI : ∀ i,Integrable ((A i).localTarget Phi Au Av)
       (phasePrior (nu i) M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure) :
     (∫ q,independentTarget A Phi scale Au Av q ∂independentPrior nu M positive)=
       Phi 0+scale*∑ i,∫ q,(A i).localTarget Phi Au Av q
         ∂(phasePrior (nu i) M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure := by
   have hcomp (i:ι) : Integrable (fun q:ι→PhaseParameter H=>(A i).localTarget Phi Au Av (q i))
       (independentPrior nu M positive) :=
     (measurePreserving_eval (fun j=>(phasePrior (nu j) M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure) i).integrable_comp_of_integrable (hI i)
   unfold independentTarget
   rw [integral_add (integrable_const (Phi 0))
     ((integrable_finsetSum Finset.univ (fun i _=>hcomp i)).const_mul scale),integral_const_mul,
     integral_finsetSum Finset.univ (fun i _=>hcomp i)]
   simp only [integral_const,probReal_univ,one_smul]
   congr 2
   apply Finset.sum_congr rfl
   intro i _
   exact integral_comp_eval (hI i).aestronglyMeasurable

 theorem independentTarget_variance (A : ι→AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (Phi : ℝ×ℝ→ℝ) (hPhi : Measurable Phi) (scale Au Av B : ℝ)
     (hlo : 0<lo) (hhi : 0≤hi) (hB : 0≤B) (hAu : 0≤Au) (hAv : 0≤Av)
     (hbound : ∀ u v,|u|≤C0*Au→|v|≤C0*Av→|Phi (u,v)-Phi 0|≤B)
     (nu : ι→Measure H) [∀ i,IsProbabilityMeasure (nu i)] (M : ℕ) (positive : Bool) :
     variance (independentTarget A Phi scale Au Av) (independentPrior nu M positive) ≤
       scale^2*Fintype.card ι*(2*hi*B)^2 := by
   let F := fun i:ι=>fun label:Bool=>fun q:PhaseParameter H=>if label then (A i).localTarget Phi Au Av q else 0
   have hF (i:ι)(label:Bool) : Measurable (F i label) := by
     cases label
     · exact measurable_const
     · exact (A i).localTarget_measurable Phi hPhi Au Av
   have hb (i:ι)(label:Bool)(q:PhaseParameter H) : |F i label q-0|≤hi*B := by
     cases label
     · simp [F]; positivity
     · simpa only [F,ite_true,sub_zero] using (A i).localTarget_bound hlo Phi Au Av B hAu hAv hbound q
   have hv := LowerMeasure.independent_pair_variance
     (fun i=>(phasePrior (nu i) M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure)
     F hF (fun _=>0) (hi*B) (mul_nonneg hhi hB) hb scale
   have hm : Measurable (fun q:ι→PhaseParameter H=>scale*∑ i,(A i).localTarget Phi Au Av (q i)) := by
     apply measurable_const.mul
     exact Finset.measurable_sum Finset.univ fun i _=>
       ((A i).localTarget_measurable Phi hPhi Au Av).comp (measurable_pi_apply i)
   unfold independentTarget
   rw [variance_const_add hm.aestronglyMeasurable]
   simpa only [F,Bool.false_eq_true,ite_false,ite_true,zero_add,independentPrior,mul_assoc] using hv

end RoughRegime.PoissonMeasure.AdmissibleTargets

namespace RoughRegime.PoissonMeasure.AdmissiblePhasePair
variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
    {μ : Measure X} [IsProbabilityMeasure μ] {lo hi barp C0 : ℝ}

 theorem localTarget_integrable (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (Phi : ℝ×ℝ→ℝ) (hPhi : Measurable Phi) (Au Av B : ℝ)
     (hlo : 0<lo) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av)
     (hbound : ∀ u v,|u| ≤ C0*Au→|v| ≤ C0*Av→|Phi (u,v)-Phi 0| ≤ B)
     (nu : Measure H) [IsProbabilityMeasure nu] (M : ℕ) (positive : Bool) :
     Integrable (A.localTarget Phi Au Av)
       (phasePrior nu M (if positive then 1 else -1) (by cases positive <;> norm_num)).measure :=
   bounded_integrable _ _ (A.localTarget_measurable Phi hPhi Au Av) (hi*B)
     (A.localTarget_bound hlo Phi Au Av B hAu hAv hbound)
end RoughRegime.PoissonMeasure.AdmissiblePhasePair

namespace RoughRegime.PoissonMeasure.AdmissibleTargets
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open OddTaylor

/-- Uniform nonlinear prior control, including actual second moments and
variance, valid across changing finite pair counts and changing latent spaces. -/
 theorem uniform_target_controls (Phi : ℝ×ℝ→ℝ) (hPhi : Measurable Phi)
     (hPhi4 : ContDiffAt ℝ 4 Phi 0) :
     ∃ epsilon>0,∃ C ≥ 0,∃ B ≥ 0,∀ {ι H X : Type*} [Fintype ι]
       [MeasurableSpace H] [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
       {lo hi barp C0 : ℝ} (A : ι→AdmissiblePhasePair (H:=H) μ lo hi barp C0)
       (_hlo : 0<lo) (_hhi : 0 ≤ hi) (_hC0 : 0 ≤ C0)
       (nu : ι→Measure H) [∀ i,IsProbabilityMeasure (nu i)]
       (M : ℕ) (scale Au Av : ℝ) (_hAu : 0 ≤ Au) (_hAv : 0 ≤ Av),
       C0*Au ≤ epsilon→C0*Av ≤ epsilon→
       (∀ positive,MemLp (independentTarget A Phi scale Au Av) 2 (independentPrior nu M positive)) ∧
       (∀ positive,variance (independentTarget A Phi scale Au Av) (independentPrior nu M positive) ≤
         scale^2*Fintype.card ι*(2*hi*B)^2) ∧
       |((∫ q,independentTarget A Phi scale Au Av q ∂independentPrior nu M true)-
           (∫ q,independentTarget A Phi scale Au Av q ∂independentPrior nu M false))-
         mixedDerivative Phi 0*((∫ q,independentTarget A (fun x=>x.1*x.2) scale Au Av q
              ∂independentPrior nu M true)-
           (∫ q,independentTarget A (fun x=>x.1*x.2) scale Au Av q ∂independentPrior nu M false))| ≤
         |scale| *Fintype.card ι*C*hi*C0^4*Au*Av*(Au^2+Av^2) := by
   obtain ⟨e1,he1,C,hC,hT⟩ := AdmissiblePhasePair.local_target_taylor Phi hPhi hPhi4
   obtain ⟨e2,he2,_,_,B,hB,hlocal⟩ := local_oddOdd_taylor_and_bound Phi hPhi4
   refine ⟨min e1 e2,lt_min he1 he2,C,hC,2*B,by positivity,?_⟩
   intro ι H X _ _ _ μ _ lo hi barp C0 A hlo hhi hC0 nu _ M scale Au Av hAu hAv hue hve
   have hbound : ∀ u v,|u| ≤ C0*Au→|v| ≤ C0*Av→|Phi (u,v)-Phi 0| ≤ 2*B := by
     intro u v hu hv
     have hu' := hu.trans (hue.trans (min_le_right _ _))
     have hv' := hv.trans (hve.trans (min_le_right _ _))
     have hf := (hlocal u v hu' hv').2
     have hf0 := (hlocal 0 0 (by simpa using he2.le) (by simpa using he2.le)).2
     exact (abs_sub _ _).trans (by simpa only [Prod.mk_zero_zero,two_mul] using add_le_add hf hf0)
   have hmult : Measurable (fun x : ℝ×ℝ=>x.1*x.2) := measurable_fst.mul measurable_snd
   have hmb : ∀u v,|u| ≤ C0*Au→|v| ≤ C0*Av→|u*v-(0:ℝ)| ≤ C0^2*Au*Av := by
     intro u v hu hv
     rw [sub_zero,abs_mul]
     convert mul_le_mul hu hv (abs_nonneg _) (mul_nonneg hC0 hAu) using 1; ring
   have hI (i:ι)(positive:Bool) := (A i).localTarget_integrable Phi hPhi Au Av (2*B)
     hlo hAu hAv hbound (nu i) M positive
   have hIm (i:ι)(positive:Bool) := (A i).localTarget_integrable (fun x=>x.1*x.2) hmult Au Av
     (C0^2*Au*Av) hlo hAu hAv (by simpa only [Prod.fst_zero,Prod.snd_zero,mul_zero] using hmb) (nu i) M positive
   refine ⟨fun positive=>independentTarget_memLp A Phi hPhi scale Au Av (2*B) hlo hAu hAv hbound nu M positive,
     fun positive=>independentTarget_variance A Phi hPhi scale Au Av (2*B) hlo hhi (by positivity) hAu hAv hbound nu M positive,?_⟩
   rw [independentTarget_integral A Phi scale Au Av nu M true (fun i=>hI i true),
     independentTarget_integral A Phi scale Au Av nu M false (fun i=>hI i false),
     independentTarget_integral A (fun x=>x.1*x.2) scale Au Av nu M true (fun i=>hIm i true),
     independentTarget_integral A (fun x=>x.1*x.2) scale Au Av nu M false (fun i=>hIm i false)]
   simp only [ite_true,Bool.false_eq_true,ite_false,Prod.fst_zero,Prod.snd_zero,mul_zero]
   let error : ι→ℝ := fun i=>
     ((∫ q,(A i).localTarget Phi Au Av q ∂(phasePrior (nu i) M 1 (by norm_num)).measure)-
       (∫ q,(A i).localTarget Phi Au Av q ∂(phasePrior (nu i) M (-1) (by norm_num)).measure))-
     mixedDerivative Phi 0*((∫ q,(A i).localTarget (fun x=>x.1*x.2) Au Av q
         ∂(phasePrior (nu i) M 1 (by norm_num)).measure)-
       (∫ q,(A i).localTarget (fun x=>x.1*x.2) Au Av q ∂(phasePrior (nu i) M (-1) (by norm_num)).measure))
   have he (i:ι) : |error i| ≤ C*hi*C0^4*Au*Av*(Au^2+Av^2) :=
     hT μ (A i) hlo hhi hC0 (nu i) M Au Av hAu hAv
       (hue.trans (min_le_left _ _)) (hve.trans (min_le_left _ _))
   have hs := (Finset.abs_sum_le_sum_abs (s:=Finset.univ) error).trans
     (Finset.sum_le_sum (fun i _=>he i))
   simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
   calc
     _ = |scale*(∑ i,error i)| := by
       congr 1
       dsimp only [error]
       simp only [mul_sub,Finset.sum_sub_distrib,←Finset.mul_sum]
       ring
     _ = |scale| *|∑ i,error i| := abs_mul _ _
     _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs (abs_nonneg scale)

end RoughRegime.PoissonMeasure.AdmissibleTargets
