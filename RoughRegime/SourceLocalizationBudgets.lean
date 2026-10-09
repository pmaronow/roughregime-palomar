module

public import RoughRegime.SpatialLocalClass


@[expose] public section
/-! One genuinely positive scalar threshold implies every source
localization inequality, including the shrinking density collar. -/
noncomputable section
open MeasureTheory
namespace RoughRegime.SpatialAffine

 theorem exists_source_localization_threshold (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
     (O : Model.Observables Z A) (π : ProbabilityMeasure Z) (S : Scores (π : Measure Z))
     (rminus rplus κ : ℝ) (hrminus : 0 < rminus) (hrplus : 0 ≤ rplus) (hκ : 0 < κ)
     (hbase : A.δ < Model.baselineW A O π) :
     ∃ c : ℝ, 0 < c ∧ ∀ delta r amp : ℝ, 0 ≤ delta → 0 ≤ r → 0 ≤ amp →
       amp ≤ c*min delta (min r 1) →
       amp ≤ κ ∧ (amp/rminus)*S.C ≤ 1/4 ∧
       2*(amp/rminus)*A.M0*S.C ≤ Model.baselineW A O π-A.δ ∧
       (2*(amp/rminus)*A.M0*S.C)*rplus ≤ Model.baselineW A O π*delta ∧
       2*(amp/rminus)*A.M0*S.C ≤ r ∧
       (amp/rminus)*(|residualMomentU A O π S true|+|residualMomentU A O π S false|)/(Model.baselineW A O π/2) ≤ r ∧
       (amp/rminus)*(|residualMomentV A O π S true|+|residualMomentV A O π S false|)/(Model.baselineW A O π/2) ≤ r := by
   let w0 := Model.baselineW A O π
   have hw : 0 < w0 := A.hδ.trans hbase
   let W := 2*A.M0*S.C
   let RU := (|residualMomentU A O π S true|+|residualMomentU A O π S false|)/(w0/2)
   let RV := (|residualMomentV A O π S true|+|residualMomentV A O π S false|)/(w0/2)
   have hW : 0 ≤ W := by dsimp [W]; exact mul_nonneg (mul_nonneg (by norm_num) A.hM0.le) S.nonnegativeC
   have hRU : 0 ≤ RU := by dsimp [RU]; positivity
   have hRV : 0 ≤ RV := by dsimp [RV]; positivity
   have hC0 := S.nonnegativeC
   let C := 1+S.C+W+W*rplus+RU+RV
   have hC : 0 < C := by dsimp [C]; nlinarith [mul_nonneg hW hrplus]
   have hCS : S.C ≤ C := by dsimp [C]; nlinarith [mul_nonneg hW hrplus]
   have hCW : W ≤ C := by dsimp [C]; nlinarith [mul_nonneg hW hrplus]
   have hCP : W*rplus ≤ C := by dsimp [C]; nlinarith [mul_nonneg hW hrplus]
   have hCU : RU ≤ C := by dsimp [C]; nlinarith [mul_nonneg hW hrplus]
   have hCV : RV ≤ C := by dsimp [C]; nlinarith [mul_nonneg hW hrplus]
   let b := min (1/4:ℝ) (min (w0-A.δ) w0)
   have hb : 0 < b := lt_min (by norm_num) (lt_min (sub_pos.mpr hbase) hw)
   have hb4 : b ≤ 1/4 := min_le_left _ _
   have hbG : b ≤ w0-A.δ := (min_le_right _ _).trans (min_le_left _ _)
   have hbw : b ≤ w0 := (min_le_right _ _).trans (min_le_right _ _)
   let c := min κ (rminus*b/C)
   have hc : 0 < c := lt_min hκ (div_pos (mul_pos hrminus hb) hC)
   refine ⟨c,hc,?_⟩
   intro delta r amp hd hr ha hbound
   let t := min delta (min r 1)
   have ht : 0 ≤ t := le_min hd (le_min hr (by norm_num))
   have htδ : t ≤ delta := min_le_left _ _
   have htr : t ≤ r := (min_le_right _ _).trans (min_le_left _ _)
   have ht1 : t ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
   have hck : c ≤ κ := min_le_left _ _
   have hcc : c ≤ rminus*b/C := min_le_right _ _
   have hampt : amp ≤ c*t := hbound
   have hsmall : amp ≤ c := hampt.trans (by nlinarith)
   have he0 : 0 ≤ amp/rminus := div_nonneg ha hrminus.le
   have heC : (amp/rminus)*C ≤ b*t := by
     have he := hampt.trans (mul_le_mul_of_nonneg_right hcc ht)
     have hmul : amp*C ≤ rminus*b*t := by
       calc
         amp*C ≤ (rminus*b/C*t)*C := mul_le_mul_of_nonneg_right he hC.le
         _ = rminus*b*t := by field_simp
     rw [div_mul_eq_mul_div]
     apply (div_le_iff₀ hrminus).mpr
     nlinarith only [hmul]
   have heCδ : (amp/rminus)*C ≤ b*delta := heC.trans (mul_le_mul_of_nonneg_left htδ hb.le)
   have heCr : (amp/rminus)*C ≤ b*r := heC.trans (mul_le_mul_of_nonneg_left htr hb.le)
   have heC1 : (amp/rminus)*C ≤ b := heC.trans (by nlinarith)
   have heS := (mul_le_mul_of_nonneg_left hCS he0).trans heC1
   have heW := (mul_le_mul_of_nonneg_left hCW he0).trans heC1
   have heP := (mul_le_mul_of_nonneg_left hCP he0).trans heCδ
   have heWr := (mul_le_mul_of_nonneg_left hCW he0).trans heCr
   have heU := (mul_le_mul_of_nonneg_left hCU he0).trans heCr
   have heV := (mul_le_mul_of_nonneg_left hCV he0).trans heCr
   refine ⟨hsmall.trans hck,heS.trans hb4,?_,?_,?_,?_,?_⟩
   · convert heW.trans hbG using 1 <;> ring
   · have hbδ := mul_le_mul_of_nonneg_right hbw hd
     convert heP.trans hbδ using 1 <;> ring
   · have hbr : b*r ≤ r := by
       simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb4.trans (by norm_num : (1/4:ℝ) ≤ 1)) hr
     convert heWr.trans hbr using 1 <;> ring
   · have hbr : b*r ≤ r := by
       simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb4.trans (by norm_num : (1/4:ℝ) ≤ 1)) hr
     convert heU.trans hbr using 1 <;> ring
   · have hbr : b*r ≤ r := by
       simpa only [one_mul] using mul_le_mul_of_nonneg_right (hb4.trans (by norm_num : (1/4:ℝ) ≤ 1)) hr
     convert heV.trans hbr using 1 <;> ring

end RoughRegime.SpatialAffine
