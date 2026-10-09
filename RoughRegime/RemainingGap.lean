module

public import RoughRegime.BracketRateConsequences


@[expose] public section
/-! The literal logarithmic factor left between the true rough-regime lower
and upper scales, and the weaker common-scale consequence of the main lower. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology ENNReal
namespace RoughRegime.Rates

 def remainingGapFactor (n nu : ℝ) : ℝ := (Real.log n)^(nu/2-3/4)

 theorem subcritical_bracket_gap_factor (n theta tau nu : ℝ) (hn : 1<n) :
     (subcriticalScale n theta tau*(Real.log n)^(nu/2+1/4))/
       (subcriticalScale n theta tau*Real.log n)=remainingGapFactor n nu := by
   have hs := (scale_pos n theta tau hn).ne'
   have hl := (Real.log_pos hn).ne'
   rw [mul_div_mul_left _ _ hs]
   unfold remainingGapFactor
   have he : nu/2-3/4=(nu/2+1/4)-1 := by ring
   rw [he,Real.rpow_sub (Real.log_pos hn),Real.rpow_one]

 theorem remainingGapFactor_two (n : ℝ) : remainingGapFactor n 2=(Real.log n)^(1/4:ℝ) := by
   unfold remainingGapFactor
   congr 1
   norm_num

 theorem remainingGapFactor_tendsto (nu : ℝ) (hnu : 2 ≤ nu) :
     Tendsto (fun n:ℕ=>remainingGapFactor n nu) atTop atTop := by
   have hexp : 0<nu/2-3/4 := by linarith
   exact (tendsto_rpow_atTop hexp).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

end RoughRegime.Rates

namespace RoughRegime.Model

 theorem Bracket.remaining_gap_factor {Y : Type*} [MeasurableSpace Y]
     {T : ProbabilityMeasure Y→ℝ} {Cls : Set (ProbabilityMeasure Y)}
     {A : BracketParameters} {nu : ℝ} (_hb : Bracket T Cls A nu)
     (hrough : A.theta<1/2) (n : ℕ) (hn : 1<n) :
     upperBracketScale A nu n/lowerBracketScale A n=
       Rates.remainingGapFactor n nu := by
   simp only [upperBracketScale,lowerBracketScale,ite_eq_left hrough]
   exact Rates.subcritical_bracket_gap_factor n _ _ _ (by exact_mod_cast hn)

 theorem main_common_scale_lower (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (F : Observables Z A) (pi : ProbabilityMeasure Z) (r : ℝ)
     (hnd : Nondegenerate A F pi) (hr : 0<r)
     (Cls : Set (ProbabilityMeasure (Observation A Z))) (hCls : localClass A F pi r⊆Cls)
     (hrough : A.theta<1/2) :
     ∃c:ℝ,0<c ∧ ∀ᶠ n:ℕ in atTop,
       ENNReal.ofReal (c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)) ≤
         minimaxRMSE n (target A F) Cls ∧
       (1/4:ℝ≥0∞) ≤ minimaxTail n (target A F) Cls
         (2*c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)) := by
   obtain ⟨c,hc,n0,_,hlower⟩ := mainLowerClaim A F pi r hnd hr
   refine ⟨c,hc,?_⟩
   have hlog : ∀ᶠ n:ℕ in atTop,1 ≤ Real.log n :=
     (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
   filter_upwards [eventually_ge_atTop n0,hlog,eventually_gt_atTop (1:ℕ)] with n hn hln hn1
   have hs := Rates.scale_pos n A.theta (Rates.tau A.gminus A.gplus) (by exact_mod_cast hn1)
   have hscale : c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus) ≤
       c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)*Real.log n :=
     le_mul_of_one_le_right (mul_pos hc hs).le hln
   obtain ⟨hL,hT⟩ := (hlower (localClass A F pi r) (Set.Subset.refl _) (localClass_subset A F pi r) n hn).2 ⟨A.theta_pos,hrough⟩
   exact ⟨(ENNReal.ofReal_le_ofReal hscale).trans (hL.trans (minimaxRMSE_mono_class n _ hCls)),
     (hT.trans (minimaxTail_mono_class n _ _ hCls)).trans (minimaxTail_antitone_threshold n _ _ (by linarith [hscale]))⟩

end RoughRegime.Model
