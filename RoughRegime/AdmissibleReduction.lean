module

public import RoughRegime.AdmissibleGridPrior
public import RoughRegime.AdmissibleReductionSequence
public import RoughRegime.AdmissibleScaleParameters
public import RoughRegime.OddTaylorDerivative


@[expose] public section
/-! Proposition 12 with its original universal admissible-prior existence
hypothesis. The block count is selected by the proved numerical reduction;
small response probabilities, actual concentration, statistical distances and
randomized fixed-sample risk are all conclusions of the construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology
namespace RoughRegime.PoissonMeasure.AdmissibleReduction
open ReductionScales AdmissiblePhasePair
universe uH uX uZ uY
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {X : Type uX} {Z : Type uZ} {Y : Type uY}
    [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (π : ProbabilityMeasure Z)

/-- The coefficient and bilinear-separation estimates exist at every
sufficiently large sample size and every admissible even-side grid. -/
def GridExistenceHypothesis (A : AbstractScaleParameters) (S : NaturalScaleChoice A)
    (C0 c2 : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,∀B:ℕ,n ≤ B→(∃k:ℕ,Even k ∧ B=k^A.d)→
    Nonempty (GridPrior.{uH,uX,uZ,uY} (Y:=Y) μ π A S C0 c2 n B)

/-- The selected actual priors, amplitude bounds, block growth and randomized
fixed-sample lower risk in Proposition 12. -/
def GridReductionConclusion (A : AbstractScaleParameters) (S : NaturalScaleChoice A)
    (C0 c2 : ℝ) (hC0 : 1 ≤ C0) (scores : SpatialAffine.Scores (π:Measure Z))
    (Phi : ℝ×ℝ→ℝ) : Prop :=
    ∃ c1 : ℝ,0<c1 ∧
      (∀ q : ℝ,Tendsto (fun n : ℕ=>(S.B n:ℝ)/((n:ℝ)*(Real.log n)^q)) atTop atTop) ∧
      ∀ᶠ n : ℕ in atTop,n ≤ S.B n ∧
        (∃ k : ℕ,0<k ∧ Even k ∧ S.B n=k^A.d) ∧
        S.Au n ≤ A.epsilonU*(S.B n:ℝ)^(-A.a) ∧
        S.Av n ≤ A.epsilonV*(S.B n:ℝ)^(-A.b) ∧
        ∃G : GridPrior.{uH,uX,uZ,uY} (Y:=Y) μ π A S C0 c2 n (S.B n),
        ∃hAu : 0 ≤ S.Au n,∃hAv : 0 ≤ S.Av n,
        ∃hsmall : C0*(S.Au n+S.Av n)*scores.C ≤ 1/4,
        ∀(T : ProbabilityMeasure Y→ℝ)(Cls : Set (ProbabilityMeasure Y)),
          (∀q,T ((G.experiment scores (zero_le_one.trans hC0) hAu hAv hsmall).observationProbability q)=
            (G.experiment scores (zero_le_one.trans hC0) hAu hAv hsmall).targetFunctional Phi q)→
          (∀q,(G.experiment scores (zero_le_one.trans hC0) hAu hAv hsmall).observationProbability q∈Cls)→
          (3/8:ℝ≥0∞) ≤ Model.minimaxTail n T Cls
            (c1*(S.m n)^2*RoughRegime.Rates.subcriticalScale n A.theta A.tau) ∧
          ENNReal.ofReal (c1/2*(S.m n)^2*RoughRegime.Rates.subcriticalScale n A.theta A.tau) ≤
            Model.minimaxRMSE n T Cls

 theorem reduction_from_grid_estimates (A : AbstractScaleParameters) (S : NaturalScaleChoice A)
    (C0 c2 : ℝ) (hC0 : 1 ≤ C0) (hc2 : 0<c2)
    (scores : SpatialAffine.Scores (π:Measure Z))
    (hconstant : ∀barp∈Icc A.lo A.hi,comparisonStar A.lo A.hi barp C0 scores.C ≤ A.Cstar)
    (Phi : ℝ×ℝ→ℝ) (hPhi4 : ContDiffAt ℝ 4 Phi 0)
    (hMixed : OddTaylor.mixedDerivative Phi 0≠0)
    (hPriors : GridExistenceHypothesis.{uH,uX,uZ,uY} (Y:=Y) μ π A S C0 c2) :
    ∃ c1 : ℝ,0<c1 ∧
      (∀ q : ℝ,Tendsto (fun n : ℕ=>(S.B n:ℝ)/((n:ℝ)*(Real.log n)^q)) atTop atTop) ∧
      ∀ᶠ n : ℕ in atTop,n ≤ S.B n ∧
        (∃ k : ℕ,0<k ∧ Even k ∧ S.B n=k^A.d) ∧
        S.Au n ≤ A.epsilonU*(S.B n:ℝ)^(-A.a) ∧
        S.Av n ≤ A.epsilonV*(S.B n:ℝ)^(-A.b) ∧
        ∃G : GridPrior.{uH,uX,uZ,uY} (Y:=Y) μ π A S C0 c2 n (S.B n),
        ∃hAu : 0 ≤ S.Au n,∃hAv : 0 ≤ S.Av n,
        ∃hsmall : C0*(S.Au n+S.Av n)*scores.C ≤ 1/4,
        ∀(T : ProbabilityMeasure Y→ℝ)(Cls : Set (ProbabilityMeasure Y)),
          (∀q,T ((G.experiment scores (zero_le_one.trans hC0) hAu hAv hsmall).observationProbability q)=
            (G.experiment scores (zero_le_one.trans hC0) hAu hAv hsmall).targetFunctional Phi q)→
          (∀q,(G.experiment scores (zero_le_one.trans hC0) hAu hAv hsmall).observationProbability q∈Cls)→
          (3/8:ℝ≥0∞) ≤ Model.minimaxTail n T Cls
            (c1*(S.m n)^2*RoughRegime.Rates.subcriticalScale n A.theta A.tau) ∧
          ENNReal.ofReal (c1/2*(S.m n)^2*RoughRegime.Rates.subcriticalScale n A.theta A.tau) ≤
            Model.minimaxRMSE n T Cls := by
  obtain ⟨c1,hc1,hLogs,hTests⟩ := natural_admissible_reduction A S C0 scores.C c2
    hC0 hc2 hconstant Phi hPhi4 hMixed
  have hsmallE := S.amplitude_small_budget (C0*scores.C) (1/4) (by norm_num)
  refine ⟨c1,hc1,hLogs,?_⟩
  filter_upwards [hTests,hPriors,S.amplitude_bounds,hsmallE] with n ht hp ha hs
  obtain ⟨k,hkpos,hkeven,hkB⟩ := ht.2.1
  obtain ⟨G⟩ := hp (S.B n) ht.1 ⟨k,hkeven,hkB⟩
  have hAu : 0 ≤ S.Au n := ha.1.le
  have hAv : 0 ≤ S.Av n := ha.2.1.le
  have hsmall : C0*(S.Au n+S.Av n)*scores.C ≤ 1/4 := by
    convert hs using 1; ring
  let E := G.experiment scores (zero_le_one.trans hC0) hAu hAv hsmall
  have hId : PhysicalScaleIdentification A S n C0 scores.C E := by
    refine ⟨G.blocks_eq.symm,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  refine ⟨ht.1,⟨k,hkpos,hkeven,hkB⟩,ha.2.2.1,ha.2.2.2.1,G,hAu,hAv,hsmall,?_⟩
  intro T Cls hT hCls
  exact ht.2.2 μ π E hId (fun i=>(G.prior i:Measure G.H))
    (G.experiment_coefficient scores (zero_le_one.trans hC0) hAu hAv hsmall)
    (G.experiment_bilinear scores (zero_le_one.trans hC0) hAu hAv hsmall) T Cls hT hCls

namespace Parameters

/-- The original reduction uses only the fixed source constants, arbitrary
admissible R,m sequences, a local C4 integrand with nonzero ordinary mixed
partial derivative, and the two prior estimates on every sufficiently large
even-side grid. The comparison constant and c0 are chosen internally. -/
 theorem paper_reduction_to_two_estimates (P : Parameters) (S : NaturalScaleChoice P.numeric)
     (scores : SpatialAffine.Scores (π:Measure Z)) (hScores : scores.C=P.scoreBound)
     (Phi : ℝ×ℝ→ℝ) (hPhi4 : ContDiffAt ℝ 4 Phi 0)
     (hScalarMixed : deriv (fun u=>deriv (fun v=>Phi (u,v)) 0) 0≠0)
     (hPriors : GridExistenceHypothesis.{uH,uX,uZ,uY} (Y:=Y) μ π P.numeric S P.C0 P.c2) :
     GridReductionConclusion.{uH,uX,uZ,uY} (Y:=Y) μ π P.numeric S P.C0 P.c2 P.hC0 scores Phi := by
   have hMixed : OddTaylor.mixedDerivative Phi 0≠0 := by
     rw [OddTaylor.mixedDerivative_eq_reverse_scalar_deriv Phi (hPhi4.of_le (by norm_num))]
     exact hScalarMixed
   exact reduction_from_grid_estimates μ π P.numeric S P.C0 P.c2 P.hC0 P.hc2 scores
     (by intro barp hp; rw [hScores]; exact P.numeric_comparison_bound barp hp)
     Phi hPhi4 hMixed hPriors

end Parameters

end RoughRegime.PoissonMeasure.AdmissibleReduction
