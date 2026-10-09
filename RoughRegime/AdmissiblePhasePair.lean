module

public import RoughRegime.SpatialAffineLaw
public import RoughRegime.PoissonPhysicalComparison
public import RoughRegime.SourcePriorReindex
public import RoughRegime.SpatialPriorMean


@[expose] public section
/-! Arbitrary admissible affine phase pairs. The fields are the literal A4
coefficients, their true density has the A2 bounds and constant pair mass,
and their unsigned scores have the A3 bounds. No lattice construction is used. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]

 def AffinePhaseField.designDensity (F : AffinePhaseField H X) (barp : ℝ)
     (q : H×ℝ) (x : X) : ℝ := barp+F.c q.1 x+F.a q.1 x*Real.cos q.2+F.b q.1 x*Real.sin q.2

structure AdmissiblePhasePair (μ : Measure X) (lo hi barp C0 : ℝ) where
  field : AffinePhaseField H X
  measurable : field.IsMeasurable
  densityBounds : ∀ q x,lo ≤ field.designDensity barp q x ∧ field.designDensity barp q x ≤ hi
  constantMass : ∀ q,(∫ x,field.designDensity barp q x ∂μ)=barp
  unsignedU : ∀ q x,|field.hu q.1 x| ≤ C0*field.designDensity barp q x
  unsignedV : ∀ q x,|field.hv q.1 x| ≤ C0*field.designDensity barp q x

namespace AdmissiblePhasePair
variable {μ : Measure X} {lo hi barp C0 : ℝ}

 def rawBound (_lo hi barp C0 : ℝ) : ℝ := 1+2*hi+barp+C0*hi

 theorem rawBound_nonneg (hhi : 0 ≤ hi) (hbarp : 0 ≤ barp) (hC0 : 0 ≤ C0) :
     0 ≤ rawBound lo hi barp C0 := by unfold rawBound; positivity

 theorem field_bounded (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0 ≤ barp) (hC0 : 0 ≤ C0) :
     A.field.Bounded (rawBound lo hi barp C0) := by
   refine ⟨?_,?_,?_,?_,?_⟩
   · intro h x
     have hp := A.densityBounds (h,0) x
     have hn := A.densityBounds (h,Real.pi) x
     simp only [AffinePhaseField.designDensity,Real.cos_zero,Real.sin_zero,Real.cos_pi,Real.sin_pi,
       mul_one,mul_zero,add_zero,mul_neg_one] at hp hn
     rw [abs_le]
     unfold rawBound
     have hc : 0 ≤ C0*hi := mul_nonneg hC0 hhi
     constructor <;> linarith
   · intro h x
     have hp := A.densityBounds (h,0) x
     have hn := A.densityBounds (h,Real.pi) x
     simp only [AffinePhaseField.designDensity,Real.cos_zero,Real.sin_zero,Real.cos_pi,Real.sin_pi,
       mul_one,mul_zero,add_zero,mul_neg_one] at hp hn
     rw [abs_le]
     unfold rawBound
     have hc : 0 ≤ C0*hi := mul_nonneg hC0 hhi
     constructor <;> linarith
   · intro h x
     have hp := A.densityBounds (h,Real.pi/2) x
     have hn := A.densityBounds (h,-(Real.pi/2)) x
     simp only [AffinePhaseField.designDensity,Real.cos_pi_div_two,Real.sin_pi_div_two,
       Real.cos_neg,Real.sin_neg,mul_one,mul_zero,add_zero,mul_neg_one] at hp hn
     rw [abs_le]
     unfold rawBound
     have hc : 0 ≤ C0*hi := mul_nonneg hC0 hhi
     constructor <;> linarith
   · intro h x
     exact (A.unsignedU (h,0) x).trans ((mul_le_mul_of_nonneg_left (A.densityBounds (h,0) x).2 hC0).trans (by
       unfold rawBound; linarith))
   · intro h x
     exact (A.unsignedV (h,0) x).trans ((mul_le_mul_of_nonneg_left (A.densityBounds (h,0) x).2 hC0).trans (by
       unfold rawBound; linarith))

 theorem designDensity_measurable (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0) :
     Measurable (Function.uncurry (A.field.designDensity barp)) := by
   have hj : Measurable (fun z : (H×ℝ)×X=>(z.1.1,z.2)) := measurable_fst.fst.prodMk measurable_snd
   have hc := A.measurable.c.comp hj
   have ha := A.measurable.a.comp hj
   have hb := A.measurable.b.comp hj
   unfold Function.uncurry AffinePhaseField.designDensity at *
   fun_prop

 def unsignedProfileU (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0) (Au : ℝ)
     (q : H×ℝ) (x : X) : ℝ := Au*A.field.hu q.1 x/A.field.designDensity barp q x
 def unsignedProfileV (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0) (Av : ℝ)
     (q : H×ℝ) (x : X) : ℝ := Av*A.field.hv q.1 x/A.field.designDensity barp q x

 theorem unsignedProfileU_measurable (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0) (Au : ℝ) :
     Measurable (Function.uncurry (A.unsignedProfileU Au)) :=
   ((A.measurable.hu.comp (measurable_fst.fst.prodMk measurable_snd)).const_mul Au).div
     A.designDensity_measurable
 theorem unsignedProfileV_measurable (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0) (Av : ℝ) :
     Measurable (Function.uncurry (A.unsignedProfileV Av)) :=
   ((A.measurable.hv.comp (measurable_fst.fst.prodMk measurable_snd)).const_mul Av).div
     A.designDensity_measurable

 theorem unsignedProfileU_bound (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (hlo : 0<lo) (Au : ℝ) (hAu : 0 ≤ Au) (q : H×ℝ) (x : X) :
     |A.unsignedProfileU Au q x| ≤ C0*Au := by
   have hp : 0<A.field.designDensity barp q x := hlo.trans_le (A.densityBounds q x).1
   unfold unsignedProfileU
   rw [abs_div,abs_mul,abs_of_nonneg hAu,abs_of_pos hp]
   apply (div_le_iff₀ hp).mpr
   convert mul_le_mul_of_nonneg_left (A.unsignedU q x) hAu using 1; ring
 theorem unsignedProfileV_bound (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (hlo : 0<lo) (Av : ℝ) (hAv : 0 ≤ Av) (q : H×ℝ) (x : X) :
     |A.unsignedProfileV Av q x| ≤ C0*Av := by
   have hp : 0<A.field.designDensity barp q x := hlo.trans_le (A.densityBounds q x).1
   unfold unsignedProfileV
   rw [abs_div,abs_mul,abs_of_nonneg hAv,abs_of_pos hp]
   apply (div_le_iff₀ hp).mpr
   convert mul_le_mul_of_nonneg_left (A.unsignedV q x) hAv using 1; ring

 variable [IsProbabilityMeasure μ]
 def spatialField (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
     (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (q : PhaseParameter H) : SpatialAffine.Field μ where
   p x := A.field.designDensity barp q.1 x/barp
   u x := Lower.sign q.2.1*A.unsignedProfileU Au q.1 x
   v x := Lower.sign q.2.2*A.unsignedProfileV Av q.1 x
   measurableP := (A.designDensity_measurable.comp (measurable_const.prodMk measurable_id)).div_const barp
   measurableU := (A.unsignedProfileU_measurable Au).comp (measurable_const.prodMk measurable_id) |>.const_mul _
   measurableV := (A.unsignedProfileV_measurable Av).comp (measurable_const.prodMk measurable_id) |>.const_mul _
   P := hi/barp
   nonnegativeP := div_nonneg hhi hbarp.le
   densityBounds x := ⟨div_nonneg (hlo.trans_le (A.densityBounds q.1 x).1).le hbarp.le,
     div_le_div_of_nonneg_right (A.densityBounds q.1 x).2 hbarp.le⟩
   integralP := by rw [integral_div,A.constantMass,div_self hbarp.ne']
   epsilon := C0*(Au+Av)
   nonnegativeEpsilon := mul_nonneg hC0 (add_nonneg hAu hAv)
   boundU x := by
     have hs : |Lower.sign q.2.1|=1 := by cases q.2.1 <;> simp [Lower.sign]
     rw [abs_mul,hs,one_mul]
     exact (A.unsignedProfileU_bound hlo Au hAu q.1 x).trans
       (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hAv) hC0)
   boundV x := by
     have hs : |Lower.sign q.2.2|=1 := by cases q.2.2 <;> simp [Lower.sign]
     rw [abs_mul,hs,one_mul]
     exact (A.unsignedProfileV_bound hlo Av hAv q.1 x).trans
       (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hAu) hC0)

 def phaseScores {Z : Type*} [MeasurableSpace Z] {π : Measure Z} (S : SpatialAffine.Scores π)
     (l : Fin 3) (z : Z) : ℝ := if l=0 then 1 else if l=1 then S.su z else S.sv z

 theorem phaseScores_measurable {Z : Type*} [MeasurableSpace Z] {π : Measure Z}
     (S : SpatialAffine.Scores π) (l : Fin 3) : Measurable (phaseScores S l) := by
   fin_cases l
   · change Measurable (fun _ : Z=>(1:ℝ)); exact measurable_const
   · change Measurable S.su; exact S.measurableU
   · change Measurable S.sv; exact S.measurableV

 theorem phaseScores_bound {Z : Type*} [MeasurableSpace Z] {π : Measure Z}
     (S : SpatialAffine.Scores π) (l : Fin 3) (z : Z) : |phaseScores S l z| ≤ max 1 S.C := by
   fin_cases l
   · change |(1:ℝ)| ≤ max 1 S.C
     rw [abs_one]
     exact le_max_left _ _
   · simpa [phaseScores] using (S.boundU z).trans (le_max_right _ _)
   · simpa [phaseScores] using (S.boundV z).trans (le_max_right _ _)

 theorem spatialLaw_density_eq {Z : Type*} [MeasurableSpace Z] {π : Measure Z} [IsProbabilityMeasure π]
     (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0) (S : SpatialAffine.Scores π)
     (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
     (Au Av : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hsmall : C0*(Au+Av)*S.C ≤ 1/4)
     (q : PhaseParameter H) (o : X×Z) :
     (SpatialAffine.law S (A.spatialField hlo hhi hbarp hC0 Au Av hAu hAv q) hsmall).density o=
       1+(A.field.scale (1/barp)).markedFactor Au Av (phaseScores S) q o := by
   have hp : A.field.designDensity barp q.1 o.1≠0 :=
     (hlo.trans_le (A.densityBounds q.1 o.1).1).ne'
   simp only [SpatialAffine.law,SpatialAffine.responseFactor,spatialField,unsignedProfileU,unsignedProfileV,
     AffinePhaseField.markedFactor,AffinePhaseField.scale,AffinePhaseField.feature,AffinePhaseField.unsigned,
     phaseScores,Fin.sum_univ_three]
   simp only [Fin.isValue,ite_true,ite_false,show (1:Fin 3)≠0 by decide,
     show (2:Fin 3)≠0 by decide,show (2:Fin 3)≠1 by decide,
     show (0:Fin 3)≠1 by decide,show (0:Fin 3)≠2 by decide,show (1:Fin 3)≠2 by decide]
   unfold AffinePhaseField.designDensity at hp ⊢
   field_simp [hbarp.ne',hp]
   ring

end AdmissiblePhasePair
end RoughRegime.PoissonMeasure
