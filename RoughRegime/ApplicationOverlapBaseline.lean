module

public import RoughRegime.ApplicationOverlapClass
public import RoughRegime.SignPrior
public import RoughRegime.SpatialModel


@[expose] public section
/-! The actual four-atom correlated response baseline and bounded affine
scores from the overlap-effect proof, on the full [0,1] response space. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RoughRegime.Applications.Overlap
set_option backward.isDefEq.respectTransparency false

def binaryPoint (b : Bool×Bool) : Response := (b.1,MAR.bitOutcome b.2)
def baseline (c : ℝ) (hc : |c|≤1/4) : ProbabilityMeasure Response :=
  ProbabilityMeasure.map ⟨(LatticeFourier.signLaw c (hc.trans (by norm_num))).toMeasure,inferInstance⟩ binaryPoint
def signA (z : Response) : ℝ := RoughRegime.Lower.sign z.1
def signY (z : Response) : ℝ := 2*outcome z-1
def scoreU (c : ℝ) (z : Response) : ℝ := 2*signA z/(1+c*signA z*signY z)
def scoreV (c : ℝ) (z : Response) : ℝ := 2*signY z/(1+c*signA z*signY z)

theorem signA_measurable : Measurable signA := (measurable_of_countable RoughRegime.Lower.sign).comp measurable_fst
theorem signY_measurable : Measurable signY := (outcome_measurable.const_mul 2).sub_const 1
theorem scoreU_measurable (c : ℝ) : Measurable (scoreU c) := by
  unfold scoreU
  exact (signA_measurable.const_mul 2).div
    (measurable_const.add ((signA_measurable.const_mul c).mul signY_measurable))
theorem scoreV_measurable (c : ℝ) : Measurable (scoreV c) := by
  unfold scoreV
  exact (signY_measurable.const_mul 2).div
    (measurable_const.add ((signA_measurable.const_mul c).mul signY_measurable))
theorem signA_abs (z : Response) : |signA z|=1 := by
  cases hz : z.1 <;> norm_num [signA,RoughRegime.Lower.sign,hz]
theorem signY_bound (z : Response) : |signY z|≤1 := by
  rw [abs_le]
  have h := outcome_range z
  unfold signY
  constructor <;> linarith [h.1,h.2]
theorem score_denominator_lower (c : ℝ) (hc : |c|≤1/4) (z : Response) :
    3/4≤1+c*signA z*signY z := by
  have he : |c*signA z*signY z|≤1/4 := by
    rw [abs_mul,abs_mul,signA_abs,mul_one]
    exact (mul_le_mul hc (signY_bound z) (abs_nonneg _) (by norm_num)).trans_eq (mul_one _)
  linarith [neg_le_abs (c*signA z*signY z)]
theorem scoreU_bound (c : ℝ) (hc : |c|≤1/4) (z : Response) : |scoreU c z|≤4 := by
  have hd := score_denominator_lower c hc z
  unfold scoreU
  rw [abs_div,abs_mul,signA_abs,abs_of_pos (by norm_num : (0:ℝ)<2),mul_one,
    abs_of_pos (by linarith : 0<1+c*signA z*signY z)]
  apply (div_le_iff₀ (by linarith : 0<1+c*signA z*signY z)).mpr
  linarith
theorem scoreV_bound (c : ℝ) (hc : |c|≤1/4) (z : Response) : |scoreV c z|≤4 := by
  have hd := score_denominator_lower c hc z
  unfold scoreV
  rw [abs_div,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),
    abs_of_pos (by linarith : 0<1+c*signA z*signY z)]
  apply (div_le_iff₀ (by linarith : 0<1+c*signA z*signY z)).mpr
  nlinarith [signY_bound z]

theorem baseline_integral (c : ℝ) (hc : |c|≤1/4) (f : Response→ℝ) (hf : Measurable f) :
    (∫ z,f z ∂(baseline c hc:Measure Response))=
      ((1+c)*f (binaryPoint (false,false))+(1-c)*f (binaryPoint (false,true))+
        (1-c)*f (binaryPoint (true,false))+(1+c)*f (binaryPoint (true,true)))/4 := by
  change (∫ z,f z ∂(LatticeFourier.signLaw c (hc.trans (by norm_num))).toMeasure.map binaryPoint)=_
  rw [integral_map (measurable_of_countable binaryPoint).aemeasurable hf.aestronglyMeasurable,PMF.integral_eq_sum]
  simp only [LatticeFourier.signLaw_apply,ENNReal.toReal_ofReal (RoughRegime.Lower.signWeight_nonneg
    (hc.trans (by norm_num)) _ _),smul_eq_mul,Fintype.sum_prod_type]
  simp [RoughRegime.Lower.signWeight,RoughRegime.Lower.sign]
  ring

theorem baseline_moments (c : ℝ) (hc : |c|≤1/4) :
    (∫ z,treatment z ∂(baseline c hc:Measure Response))=1/2 ∧
    (∫ z,outcome z ∂(baseline c hc:Measure Response))=1/2 ∧
    (∫ z,treatment z*outcome z ∂(baseline c hc:Measure Response))=(1+c)/4 := by
  rw [baseline_integral c hc _ treatment_measurable,
    baseline_integral c hc _ outcome_measurable,
    baseline_integral c hc (fun z=>treatment z*outcome z) (treatment_measurable.mul outcome_measurable)]
  norm_num [binaryPoint,treatment,MAR.armIndicator,MAR.bitOutcome,outcome]

theorem baseline_score_moments (c : ℝ) (hc : |c|≤1/4) :
    (∫ z,scoreU c z ∂(baseline c hc:Measure Response))=0 ∧
    (∫ z,scoreV c z ∂(baseline c hc:Measure Response))=0 ∧
    (∫ z,treatment z*scoreU c z ∂(baseline c hc:Measure Response))=1 ∧
    (∫ z,treatment z*scoreV c z ∂(baseline c hc:Measure Response))=0 ∧
    (∫ z,outcome z*scoreU c z ∂(baseline c hc:Measure Response))=0 ∧
    (∫ z,outcome z*scoreV c z ∂(baseline c hc:Measure Response))=1 ∧
    (∫ z,(treatment z*outcome z)*scoreU c z ∂(baseline c hc:Measure Response))=1/2 ∧
    (∫ z,(treatment z*outcome z)*scoreV c z ∂(baseline c hc:Measure Response))=1/2 := by
  rw [baseline_integral c hc _ (scoreU_measurable c),baseline_integral c hc _ (scoreV_measurable c),
    baseline_integral c hc (fun z=>treatment z*scoreU c z) (treatment_measurable.mul (scoreU_measurable c)),
    baseline_integral c hc (fun z=>treatment z*scoreV c z) (treatment_measurable.mul (scoreV_measurable c)),
    baseline_integral c hc (fun z=>outcome z*scoreU c z) (outcome_measurable.mul (scoreU_measurable c)),
    baseline_integral c hc (fun z=>outcome z*scoreV c z) (outcome_measurable.mul (scoreV_measurable c)),
    baseline_integral c hc (fun z=>(treatment z*outcome z)*scoreU c z) ((treatment_measurable.mul outcome_measurable).mul (scoreU_measurable c)),
    baseline_integral c hc (fun z=>(treatment z*outcome z)*scoreV c z) ((treatment_measurable.mul outcome_measurable).mul (scoreV_measurable c))]
  have hp : 1+c≠0 := by have hh:=abs_le.mp hc;linarith
  have hm : 1-c≠0 := by have hh:=abs_le.mp hc;linarith
  have hm' : 1+-c≠0 := by have hh:=abs_le.mp hc;linarith
  norm_num [scoreU,scoreV,signA,signY,binaryPoint,treatment,MAR.armIndicator,MAR.bitOutcome,outcome,RoughRegime.Lower.sign]
  and_intros <;> field_simp [hp,hm,hm'] <;> ring

def scores (c : ℝ) (hc : |c|≤1/4) : SpatialAffine.Scores (baseline c hc:Measure Response) where
  su:=scoreU c
  sv:=scoreV c
  measurableU:=scoreU_measurable c
  measurableV:=scoreV_measurable c
  C:=4
  nonnegativeC:=by norm_num
  boundU:=scoreU_bound c hc
  boundV:=scoreV_bound c hc
  meanU:=(baseline_score_moments c hc).1
  meanV:=(baseline_score_moments c hc).2.1

def diagonalScores : SpatialAffine.Scores (baseline (1/4) (by norm_num):Measure Response) where
  su:=scoreU (1/4)
  sv:=scoreU (1/4)
  measurableU:=scoreU_measurable _
  measurableV:=scoreU_measurable _
  C:=4
  nonnegativeC:=by norm_num
  boundU:=scoreU_bound _ (by norm_num)
  boundV:=scoreU_bound _ (by norm_num)
  meanU:=(baseline_score_moments (1/4) (by norm_num)).1
  meanV:=(baseline_score_moments (1/4) (by norm_num)).1

theorem baseline_finite_support (c : ℝ) (hc : |c|≤1/4) :
    ∃ s : Finset Response,(baseline c hc:Measure Response) (s:Set Response)=1 := by
  classical
  refine ⟨Finset.univ.image binaryPoint,?_⟩
  change (LatticeFourier.signLaw c (hc.trans (by norm_num))).toMeasure.map binaryPoint
    (↑(Finset.univ.image binaryPoint))=1
  rw [Measure.map_apply (measurable_of_countable binaryPoint) (Finset.measurableSet _)]
  have he : binaryPoint ⁻¹' (↑(Finset.univ.image binaryPoint):Set Response)=univ := by ext b;simp
  rw [he,measure_univ]

theorem independent_baseline_nondegenerate (A : Model.Parameters)
    (O : Model.Observables Response A) (hD : O.D=fun _=>1) (hU : O.U=treatment) (hV : O.V=outcome)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hH : 1/2<A.H) :
    Model.Nondegenerate A O (baseline 0 (by norm_num)) := by
  have hw : Model.baselineW A O (baseline 0 (by norm_num))=1 := by
    unfold Model.baselineW
    rw [hD]
    simp
  have ha : Model.baselineA A O (baseline 0 (by norm_num))=1/2 := by
    rw [Model.baselineA,hU,(baseline_moments 0 (by norm_num)).1,hw]
    norm_num
  have hb : Model.baselineB A O (baseline 0 (by norm_num))=1/2 := by
    rw [Model.baselineB,hV,(baseline_moments 0 (by norm_num)).2.1,hw]
    norm_num
  refine ⟨baseline_finite_support 0 (by norm_num),by simpa only [hw] using hlo,
    by simpa only [hw] using hhi,by simpa only [ha,abs_of_pos (by norm_num : (0:ℝ)<1/2)] using hH,
    by simpa only [hb,abs_of_pos (by norm_num : (0:ℝ)<1/2)] using hH,?_⟩
  dsimp only
  rw [ha,hb,hD,hU,hV]
  simp only [mul_one]
  rw [baseline_integral 0 (by norm_num) _ ((treatment_measurable.sub_const (1/2)).pow_const 2),
    baseline_integral 0 (by norm_num) (fun z=>(treatment z-1/2)*(outcome z-1/2))
      ((treatment_measurable.sub_const (1/2)).mul (outcome_measurable.sub_const (1/2))),
    baseline_integral 0 (by norm_num) _ ((outcome_measurable.sub_const (1/2)).pow_const 2)]
  left
  norm_num [binaryPoint,treatment,outcome,MAR.armIndicator,MAR.bitOutcome]

theorem diagonal_baseline_nondegenerate (A : Model.Parameters)
    (O : Model.Observables Response A) (hD : O.D=fun _=>1) (hU : O.U=treatment) (hV : O.V=treatment)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hH : 1/2<A.H) (hab : A.α=A.β) :
    Model.Nondegenerate A O (baseline (1/4) (by norm_num)) := by
  have hw : Model.baselineW A O (baseline (1/4) (by norm_num))=1 := by
    unfold Model.baselineW
    rw [hD]
    simp
  have ha : Model.baselineA A O (baseline (1/4) (by norm_num))=1/2 := by
    rw [Model.baselineA,hU,(baseline_moments (1/4) (by norm_num)).1,hw]
    norm_num
  have hb : Model.baselineB A O (baseline (1/4) (by norm_num))=1/2 := by
    rw [Model.baselineB,hV,(baseline_moments (1/4) (by norm_num)).1,hw]
    norm_num
  refine ⟨baseline_finite_support (1/4) (by norm_num),by simpa only [hw] using hlo,
    by simpa only [hw] using hhi,by simpa only [ha,abs_of_pos (by norm_num : (0:ℝ)<1/2)] using hH,
    by simpa only [hb,abs_of_pos (by norm_num : (0:ℝ)<1/2)] using hH,?_⟩
  dsimp only
  right
  refine ⟨by rw [hU,hV],hab,?_⟩
  rw [ha,hD,hU]
  simp only [mul_one]
  rw [baseline_integral (1/4) (by norm_num) _ ((treatment_measurable.sub_const (1/2)).pow_const 2)]
  norm_num [binaryPoint,treatment,outcome,MAR.armIndicator,MAR.bitOutcome]

end RoughRegime.Applications.Overlap
