module

public import RoughRegime.AdmissibleReductionSequence


@[expose] public section
/-! Fixed constants for the original abstract reduction. The physical
comparison constant and logarithmic offset are constructed from the fixed
primitive parameters before all sample sizes and all admissible priors. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal BigOperators Topology
namespace RoughRegime.PoissonMeasure.AdmissibleReduction
open ReductionScales AdmissiblePhasePair AdmissiblePhaseExperiment
set_option backward.isDefEq.respectTransparency false

structure Parameters where
  d : ℕ
  hd : 0<d
  a : ℝ
  b : ℝ
  ha : 0<a
  hb : 0<b
  hhalf : a+b<1/2
  lo : ℝ
  hi : ℝ
  hlo : 0<lo
  hlt : lo<hi
  v0 : ℝ
  hv : 0<v0
  epsilonU : ℝ
  epsilonV : ℝ
  hεu : 0<epsilonU
  hεu1 : epsilonU ≤ 1
  hεv : 0<epsilonV
  hεv1 : epsilonV ≤ 1
  C0 : ℝ
  hC0 : 1 ≤ C0
  CΓ : ℝ
  hCΓ : 1 ≤ CΓ
  CE : ℝ
  hCE : 0 ≤ CE
  cstar : ℝ
  hcstar : 0<cstar
  c2 : ℝ
  hc2 : 0<c2
  scoreBound : ℝ

namespace Parameters
 def comparisonConstant (P : Parameters) : ℝ:=
   Classical.choose (exists_uniform_comparisonStar P.lo P.hi P.C0 P.scoreBound P.hlo)
 theorem comparisonConstant_ge_one (P : Parameters) : 1 ≤ P.comparisonConstant:=
   (Classical.choose_spec (exists_uniform_comparisonStar P.lo P.hi P.C0 P.scoreBound P.hlo)).1
 theorem comparisonConstant_bound (P : Parameters) :
    ∀barp∈Icc P.lo P.hi,comparisonStar P.lo P.hi barp P.C0 P.scoreBound ≤ P.comparisonConstant:=
   (Classical.choose_spec (exists_uniform_comparisonStar P.lo P.hi P.C0 P.scoreBound P.hlo)).2

 def numeric (P : Parameters) : AbstractScaleParameters where
   d:=P.d
   hd:=P.hd
   a:=P.a
   b:=P.b
   lo:=P.lo
   hi:=P.hi
   v0:=P.v0
   epsilonU:=P.epsilonU
   epsilonV:=P.epsilonV
   Cstar:=P.comparisonConstant
   CΓ:=P.CΓ
   CE:=P.CE
   cstar:=P.cstar
   c0:=2+Real.log (2*P.v0*P.comparisonConstant*P.CΓ)+P.CE
   ha:=P.ha
   hb:=P.hb
   hhalf:=P.hhalf
   hlo:=P.hlo
   hlt:=P.hlt
   hv:=P.hv
   hεu:=P.hεu
   hεu1:=P.hεu1
   hεv:=P.hεv
   hεv1:=P.hεv1
   hCstar:=P.comparisonConstant_ge_one
   hCΓ:=P.hCΓ
   hCE:=P.hCE
   hcstar:=P.hcstar
   hmargin:=by linarith

 theorem numeric_comparison_bound (P : Parameters) :
    ∀barp∈Icc P.numeric.lo P.numeric.hi,
      comparisonStar P.numeric.lo P.numeric.hi barp P.C0 P.scoreBound ≤ P.numeric.Cstar:=
   P.comparisonConstant_bound

 def choice_of_original_sequences (P : Parameters) (R m : ℕ→ℝ)
    (hRpos : ∀ᶠ n in atTop,1 ≤ R n) (hmpos : ∀ᶠ n in atTop,1 ≤ m n)
    (hR : (fun n:ℕ=>Real.log (R n)) =O[atTop]
      (fun n=>Real.log (frequency n (P.a+P.b) (RoughRegime.Rates.tau P.lo P.hi))))
    (hmM : ∀ᶠ n in atTop,m n ≤ P.cstar*frequency n (P.a+P.b) (RoughRegime.Rates.tau P.lo P.hi))
    (hma : ∀ᶠ n in atTop,m n ≤ (R n)^P.a) (hmb : ∀ᶠ n in atTop,m n ≤ (R n)^P.b) :
    NaturalScaleChoice P.numeric where
   R:=R
   m:=m
   hRpos:=hRpos
   hmpos:=hmpos
   hR:=hR
   hmM:=hmM
   hma:=hma
   hmb:=hmb

end Parameters

 def NaturalReductionConclusion (A : AbstractScaleParameters) (S : NaturalScaleChoice A)
    (C0 scoreBound c2 : ℝ) (Phi : ℝ×ℝ→ℝ) : Prop :=
    ∃ c1 : ℝ,0<c1 ∧
      (∀ q : ℝ,Tendsto (fun n : ℕ=>(S.B n:ℝ)/((n:ℝ)*(Real.log n)^q)) atTop atTop) ∧
      ∀ᶠ n : ℕ in atTop,n ≤ S.B n ∧
        (∃ k : ℕ,0<k ∧ Even k ∧ S.B n=k^A.d) ∧
        ∀ {H X Z Y : Type*} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace Y]
          {p : ℕ} [NeZero p] (μ : Measure X) [IsProbabilityMeasure μ] (π : ProbabilityMeasure Z)
          (E : AdmissiblePhaseExperiment (H:=H) (Y:=Y) p μ π)
          (_hId : PhysicalScaleIdentification A S n C0 scoreBound E)
          (nu : Fin p→Measure H) [∀ i,IsProbabilityMeasure (nu i)]
          (_hGamma : ∀i j,frequency n A.theta A.tau ≤ j→
            (E.pairs i).field.gammaNorm (nu i) ((2:ENNReal)•μ) E.Au E.Av (frequency n A.theta A.tau) j ≤
              A.CΓ^(j+1)*E.Au^2*E.Av^2*Real.exp (A.CE*frequency n A.theta A.tau)*
                LatticePriors.gammaSpatialFactor (S.R n) (frequency n A.theta A.tau) j)
          (_hBilinear : c2*S.gap n ≤
            |(∫ q,E.targetFunctional (fun x=>x.1*x.2) q ∂parameterPrior nu (frequency n A.theta A.tau) true)-
             (∫ q,E.targetFunctional (fun x=>x.1*x.2) q ∂parameterPrior nu (frequency n A.theta A.tau) false)|)
          (T : ProbabilityMeasure Y→ℝ) (Cls : Set (ProbabilityMeasure Y))
          (_hT : ∀q,T (E.observationProbability q)=E.targetFunctional Phi q)
          (_hCls : ∀q,E.observationProbability q∈Cls),
          (3/8:ℝ≥0∞) ≤ Model.minimaxTail n T Cls
            (c1*(S.m n)^2*RoughRegime.Rates.subcriticalScale n A.theta A.tau) ∧
          ENNReal.ofReal (c1/2*(S.m n)^2*RoughRegime.Rates.subcriticalScale n A.theta A.tau) ≤
            Model.minimaxRMSE n T Cls

namespace Parameters

/-- The full natural-sequence testing reduction with its own fixed numerical
constants, for the original local-C4 integrand assumption. -/
 theorem reduction_to_two_estimates (P : Parameters) (S : NaturalScaleChoice P.numeric)
    (Phi : ℝ×ℝ→ℝ) (hPhi4 : ContDiffAt ℝ 4 Phi 0) (hMixed : OddTaylor.mixedDerivative Phi 0≠0) :
    NaturalReductionConclusion P.numeric S P.C0 P.scoreBound P.c2 Phi :=
   natural_admissible_reduction P.numeric S P.C0 P.scoreBound P.c2 P.hC0 P.hc2
     P.numeric_comparison_bound Phi hPhi4 hMixed

end Parameters
end RoughRegime.PoissonMeasure.AdmissibleReduction
