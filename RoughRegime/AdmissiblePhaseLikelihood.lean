module

public import RoughRegime.AdmissiblePhasePair
public import RoughRegime.PoissonKernelMixtures


@[expose] public section
/-! Genuine normalized likelihood and common kernels for arbitrary A2--A5
phase pairs. All point-density side conditions follow from their actual
spatial affine response laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace RoughRegime.PoissonMeasure.AdmissiblePhasePair
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {H X Z : Type*} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Z]
    {μ : Measure X} [IsProbabilityMeasure μ] {π : Measure Z} [IsProbabilityMeasure π]
    {lo hi barp C0 : ℝ}

 omit [IsProbabilityMeasure μ] in
 theorem spatialField_p_measurable (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) :
     Measurable (fun z : PhaseParameter H×X=>(A.spatialField hlo hhi hbarp hC0 Au Av hAu hAv z.1).p z.2) :=
   (A.designDensity_measurable.comp (measurable_fst.fst.prodMk measurable_snd)).div_const barp

 omit [IsProbabilityMeasure μ] in
 theorem spatialField_u_measurable (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) :
     Measurable (fun z : PhaseParameter H×X=>(A.spatialField hlo hhi hbarp hC0 Au Av hAu hAv z.1).u z.2) := by
   have hs : Measurable Lower.sign := measurable_of_countable _
   exact (hs.comp measurable_fst.snd.fst).mul
     ((A.unsignedProfileU_measurable Au).comp (measurable_fst.fst.prodMk measurable_snd))

 omit [IsProbabilityMeasure μ] in
 theorem spatialField_v_measurable (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) :
     Measurable (fun z : PhaseParameter H×X=>(A.spatialField hlo hhi hbarp hC0 Au Av hAu hAv z.1).v z.2) := by
   have hs : Measurable Lower.sign := measurable_of_countable _
   exact (hs.comp measurable_fst.snd.snd).mul
     ((A.unsignedProfileV_measurable Av).comp (measurable_fst.fst.prodMk measurable_snd))

 def markLaw (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0) (S : SpatialAffine.Scores π)
     (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hsmall : C0*(Au+Av)*S.C ≤ 1/4)
     (q : PhaseParameter H) : GeneralTesting.DensityLaw (μ.prod π) :=
   SpatialAffine.law S (A.spatialField hlo hhi hbarp hC0 Au Av hAu hAv q) hsmall

 def markKernel (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0) (S : SpatialAffine.Scores π)
     (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hsmall : C0*(Au+Av)*S.C ≤ 1/4) :
     Kernel (PhaseParameter H) (X×Z) :=
   SpatialAffine.observationKernel S (A.spatialField hlo hhi hbarp hC0 Au Av hAu hAv) (fun _=>hsmall)
     (A.spatialField_p_measurable hlo hhi hbarp hC0 Au Av hAu hAv)
     (A.spatialField_u_measurable hlo hhi hbarp hC0 Au Av hAu hAv)
     (A.spatialField_v_measurable hlo hhi hbarp hC0 Au Av hAu hAv)

 instance markKernel_markov (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0) (S : SpatialAffine.Scores π)
     (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hsmall : C0*(Au+Av)*S.C ≤ 1/4) :
     IsMarkovKernel (A.markKernel S hlo hhi hbarp hC0 Au Av hAu hAv hsmall) := by
   unfold markKernel
   infer_instance

 theorem markLaw_density_eq (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0) (S : SpatialAffine.Scores π)
     (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hsmall : C0*(Au+Av)*S.C ≤ 1/4)
     (q : PhaseParameter H) (o : X×Z) :
     (A.markLaw S hlo hhi hbarp hC0 Au Av hAu hAv hsmall q).density o=
       1+(A.field.scale (1/barp)).markedFactor Au Av (phaseScores S) q o :=
   A.spatialLaw_density_eq S hlo hhi hbarp hC0 Au Av hAu hAv hsmall q o

 theorem markedFactor_integral_zero (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (S : SpatialAffine.Scores π) (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hsmall : C0*(Au+Av)*S.C ≤ 1/4)
     (q : PhaseParameter H) :
     (∫ o,(A.field.scale (1/barp)).markedFactor Au Av (phaseScores S) q o ∂μ.prod π)=0 := by
   let L := A.markLaw S hlo hhi hbarp hC0 Au Av hAu hAv hsmall q
   have he : (A.field.scale (1/barp)).markedFactor Au Av (phaseScores S) q=(fun o=>L.density o-1) := by
     funext o
     have hh := A.markLaw_density_eq S hlo hhi hbarp hC0 Au Av hAu hAv hsmall q o
     dsimp [L]
     linarith
   rw [he,integral_sub L.integrable (integrable_const 1),L.integral_one]
   simp

 theorem likelihood_lower (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (S : SpatialAffine.Scores π) (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hsmall : C0*(Au+Av)*S.C ≤ 1/4)
     (q : PhaseParameter H) (o : X×Z) :
     lo/(2*barp)  ≤  1+(A.field.scale (1/barp)).markedFactor Au Av (phaseScores S) q o := by
   rw [←A.markLaw_density_eq S hlo hhi hbarp hC0 Au Av hAu hAv hsmall q o]
   let F := A.spatialField hlo hhi hbarp hC0 Au Av hAu hAv q
   change lo/(2*barp) ≤ F.p o.1*SpatialAffine.responseFactor S F o.1 o.2
   have hp : lo/barp ≤ F.p o.1 := div_le_div_of_nonneg_right (A.densityBounds q.1 o.1).1 hbarp.le
   have hresp := (SpatialAffine.responseFactor_bounds S F hsmall o.1 o.2).1
   calc
     _ = (lo/barp)*(1/2) := by ring
     _  ≤  _ := mul_le_mul hp hresp (by norm_num) (F.densityBounds o.1).1

end RoughRegime.PoissonMeasure.AdmissiblePhasePair
