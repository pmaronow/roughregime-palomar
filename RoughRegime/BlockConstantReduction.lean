module

public import RoughRegime.AdmissibleReduction


@[expose] public section
/-! The J=0 numerical specialization: R=m=1 is genuinely admissible and
Proposition 12 gives the common scale without the lattice logarithmic gain. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace RoughRegime.ReductionScales

 def AbstractScaleParameters.blockConstantChoice (A : AbstractScaleParameters) : NaturalScaleChoice A where
   R := fun _=>1
   m := fun _=>1
   hRpos := Eventually.of_forall (fun _=>le_rfl)
   hmpos := Eventually.of_forall (fun _=>le_rfl)
   hR := by
     apply Asymptotics.IsBigO.of_bound 0
     simp
   hmM := by
     have he := (frequency_tendsto A.theta A.tau A.theta_pos A.hhalf A.tau_pos).comp
       tendsto_natCast_atTop_atTop
     filter_upwards [he.eventually_ge_atTop (1/A.cstar)] with n hn
     have h := mul_le_mul_of_nonneg_left hn A.hcstar.le
     simpa only [mul_one_div_cancel A.hcstar.ne',Function.comp_apply] using h
   hma := Eventually.of_forall (fun _=>by simp)
   hmb := Eventually.of_forall (fun _=>by simp)

@[simp] theorem AbstractScaleParameters.blockConstantChoice_R (A : AbstractScaleParameters) (n : ℕ) :
    A.blockConstantChoice.R n=1 := rfl
@[simp] theorem AbstractScaleParameters.blockConstantChoice_m (A : AbstractScaleParameters) (n : ℕ) :
    A.blockConstantChoice.m n=1 := rfl

 theorem AbstractScaleParameters.blockConstant_amplitudes (A : AbstractScaleParameters) (n : ℕ) :
     A.blockConstantChoice.Au n=A.epsilonU*(A.blockConstantChoice.B n:ℝ)^(-A.a) ∧
       A.blockConstantChoice.Av n=A.epsilonV*(A.blockConstantChoice.B n:ℝ)^(-A.b) := by
   rw [NaturalScaleChoice.Au_eq,NaturalScaleChoice.Av_eq]
   simp [amplitude]

end RoughRegime.ReductionScales

namespace RoughRegime.PoissonMeasure.AdmissibleReduction
open ReductionScales
universe uH uX uZ uY
variable {X:Type uX}{Z:Type uZ}{Y:Type uY}
    [MeasurableSpace X][MeasurableSpace Z][MeasurableSpace Y]
    (mu : Measure X)[IsProbabilityMeasure mu](pi : ProbabilityMeasure Z)

/-- With the original two prior estimates at R=m=1, the actual construction
has a fixed-sample common-scale tail and RMSE lower bound. -/
 theorem Parameters.block_constant_reduction (P : Parameters)
     (scores : SpatialAffine.Scores (pi:Measure Z)) (hScores : scores.C=P.scoreBound)
     (Phi : ℝ×ℝ→ℝ) (hPhi4 : ContDiffAt ℝ 4 Phi 0)
     (hMixed : deriv (fun u=>deriv (fun v=>Phi (u,v)) 0) 0≠0)
     (hPriors : GridExistenceHypothesis.{uH,uX,uZ,uY} (Y:=Y) mu pi P.numeric
       P.numeric.blockConstantChoice P.C0 P.c2) :
     ∃c1:ℝ,0<c1 ∧
       (∀q:ℝ,Tendsto (fun n:ℕ=>(P.numeric.blockConstantChoice.B n:ℝ)/((n:ℝ)*(Real.log n)^q)) atTop atTop) ∧
       ∀ᶠ n:ℕ in atTop,n ≤ P.numeric.blockConstantChoice.B n ∧
         ∃G:GridPrior.{uH,uX,uZ,uY} (Y:=Y) mu pi P.numeric P.numeric.blockConstantChoice P.C0 P.c2 n
             (P.numeric.blockConstantChoice.B n),
         ∃hAu:0 ≤ P.numeric.blockConstantChoice.Au n,∃hAv:0 ≤ P.numeric.blockConstantChoice.Av n,
         ∃hsmall:P.C0*(P.numeric.blockConstantChoice.Au n+P.numeric.blockConstantChoice.Av n)*scores.C ≤ 1/4,
         ∀(T:ProbabilityMeasure Y→ℝ)(Cls : Set (ProbabilityMeasure Y)),
           (∀q,T ((G.experiment scores (zero_le_one.trans P.hC0) hAu hAv hsmall).observationProbability q)=
             (G.experiment scores (zero_le_one.trans P.hC0) hAu hAv hsmall).targetFunctional Phi q)→
           (∀q,(G.experiment scores (zero_le_one.trans P.hC0) hAu hAv hsmall).observationProbability q∈Cls)→
           (3/8:ℝ≥0∞) ≤ Model.minimaxTail n T Cls
             (c1*RoughRegime.Rates.subcriticalScale n P.numeric.theta P.numeric.tau) ∧
           ENNReal.ofReal (c1/2*RoughRegime.Rates.subcriticalScale n P.numeric.theta P.numeric.tau) ≤
             Model.minimaxRMSE n T Cls := by
   obtain ⟨c1,hc1,hlogs,hfinal⟩ := P.paper_reduction_to_two_estimates mu pi P.numeric.blockConstantChoice
     scores hScores Phi hPhi4 hMixed hPriors
   refine ⟨c1,hc1,hlogs,?_⟩
   filter_upwards [hfinal] with n hn
   obtain ⟨hn,_,_,_,G,hAu,hAv,hsmall,ht⟩ := hn
   refine ⟨hn,G,hAu,hAv,hsmall,?_⟩
   intro T Cls hT hCls
   simpa only [AbstractScaleParameters.blockConstantChoice_m,one_pow,mul_one] using ht T Cls hT hCls

end RoughRegime.PoissonMeasure.AdmissibleReduction
