module

public import RoughRegime.SourceBlockConstantPoisson
public import RoughRegime.SourceBlockConstantStatistics
public import RoughRegime.CanonicalTesting


@[expose] public section
/-! Independent J=0 lower bound in the actual Model experiment. This proof
uses literal block-constant source priors, their comparison, concentration
and common placement; it has no mainLowerClaim dependency. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
namespace RoughRegime.LatticePriors.SourceModelFamily
open RoughRegime.ReductionScales RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {pi : ProbabilityMeasure Z}

/-- Literal J=0,m=R=1 priors give the common rough scale in every class
containing the original local class. Constants precede all sample sizes. -/
 theorem source_block_constant_lower (F : SourceModelFamily A0 D O pi) (hF : F.Localized)
     (hrough : (A0.withDimension D).theta<1/2) (r : ℝ) (hr : 0<r)
     (Cls : Set (ProbabilityMeasure (Model.Observation (A0.withDimension D) Z)))
     (hCls : Model.localClass (A0.withDimension D) O pi r⊆Cls) :
     ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
       ENNReal.ofReal (c*RoughRegime.Rates.subcriticalScale n (A0.withDimension D).theta
         (RoughRegime.Rates.tau A0.gminus A0.gplus))≤
         Model.minimaxRMSE n (Model.target (A0.withDimension D) O) Cls ∧
       (3/8:ℝ≥0∞) ≤ Model.minimaxTail n (Model.target (A0.withDimension D) O) Cls
         (2*c*RoughRegime.Rates.subcriticalScale n (A0.withDimension D).theta
           (RoughRegime.Rates.tau A0.gminus A0.gplus)) := by
   obtain ⟨C,CG,CE,Cstar,H,hstar,hPoi⟩ := F.blockConstant_poisson_comparison hF hrough
   let P := F.blockConstantParameters hrough Cstar CG CE hstar
     H.gamma_constant_ge_one H.entropy_constant_nonneg
   obtain ⟨cg,hcg,hstats⟩ := F.blockConstant_target_statistics hrough Cstar CG CE hstar
     H.gamma_constant_ge_one H.entropy_constant_nonneg
   let c := cg/8
   have hc : 0<c := div_pos hcg (by norm_num)
   have hevent : ∀ᶠn:ℕ in atTop,
       ENNReal.ofReal (c*RoughRegime.Rates.subcriticalScale n P.theta P.tau)≤
         Model.minimaxRMSE n (Model.target (A0.withDimension D) O) Cls ∧
       (3/8:ℝ≥0∞) ≤ Model.minimaxTail n (Model.target (A0.withDimension D) O) Cls
         (2*c*RoughRegime.Rates.subcriticalScale n P.theta P.tau) := by
     filter_upwards [hPoi,hstats,F.eventually_blockConstant_hard_laws hF P.theta P.tau P.c0 r
       P.theta_pos P.hhalf P.tau_pos hr,poisson_count_eventually_small,eventually_gt_atTop 1]
       with n hPn hSn hCn hcount hn
     obtain ⟨V,hH⟩ := hPn
     let G := F.blockConstantFrame P.theta P.tau P.c0 n V.validity
     let nu := F.latticeSetup.coefficientPrior 0 (frequency n P.theta P.tau) V.positive_frequency
       (by simpa [sourceFineScale] using V.band_budget)
     have hsmall : (G.Au+G.Av)/G.rminus*F.scores.C ≤ 1/4 := V.small
     obtain ⟨hLp,hvar,hmean⟩ := hSn V.validity V.positive_frequency V.band_budget hsmall
     obtain ⟨Vclass,hsmallclass,hclass⟩ := hCn
     have hclassG : ∀z,G.observationProbability pi F.scores hsmall z∈Cls := by
       intro z
       exact hCls ((hclass z).1)
     have hnr : 1<(n:ℝ) := by exact_mod_cast hn
     have hs := RoughRegime.Rates.scale_pos n P.theta P.tau hnr
     have hgap : 0<F.actualMeanGap G hsmall nu := (mul_pos hcg hs).trans_le hmean
     have hHel : GeneralTesting.hellingerSquared
         (G.canonicalPairedMixture nu pi F.scores hsmall (G.pairPoissonRate (sourceObservationRate n)) true)
         (G.canonicalPairedMixture nu pi F.scores hsmall (G.pairPoissonRate (sourceObservationRate n)) false)≤1/128 := hH
     let delta := 2*c*RoughRegime.Rates.subcriticalScale n P.theta P.tau
     have hd : 0≤delta := by dsimp [delta]; positivity
     have hdgap : delta≤F.actualMeanGap G hsmall nu/4 := by dsimp [delta,c]; linarith
     have hrRate : 0<sourceObservationRate n := by change 0<2*(n:ℝ); positivity
     have ht := F.canonical_testing_lower G nu hsmall (sourceObservationRate n) hrRate n Cls
       hclassG hHel hLp hgap hvar hcount delta hd hdgap
     refine ⟨?_,ht.1⟩
     apply le_trans _ ht.2
     apply le_of_eq
     congr 1
     dsimp [delta]
     ring
   refine ⟨c,hc,?_⟩
   have htheta : P.theta=(A0.withDimension D).theta :=
     F.blockConstantParameters_theta hrough Cstar CG CE hstar
       H.gamma_constant_ge_one H.entropy_constant_nonneg
   have htau : P.tau=RoughRegime.Rates.tau A0.gminus A0.gplus := F.normalized_tau
   simpa only [htheta,htau] using hevent

end RoughRegime.LatticePriors.SourceModelFamily

namespace RoughRegime.Model
open RoughRegime.LatticePriors RoughRegime.LatticePriors.SourceModelFamily

 theorem dimension_block_constant_minimax_lower (A0 : Parameters) (D : ℕ)
     {Z : Type*} [MeasurableSpace Z] (O : Observables Z (A0.withDimension D))
     (pi : ProbabilityMeasure Z) (r : ℝ)
     (hnd : Nondegenerate (A0.withDimension D) O pi) (hr : 0<r)
     (hrough : (A0.withDimension D).theta<1/2) :
     ∃c:ℝ,0<c ∧ ∃n0:ℕ,3≤n0 ∧ ∀n:ℕ,n0≤n→
       ∀Cls : Set (ProbabilityMeasure (Observation (A0.withDimension D) Z)),
         localClass (A0.withDimension D) O pi r⊆Cls→
       ENNReal.ofReal (c*Rates.subcriticalScale n (A0.withDimension D).theta
         (Rates.tau A0.gminus A0.gplus))≤ minimaxRMSE n (target (A0.withDimension D) O) Cls ∧
       (3/8:ℝ≥0∞)≤ minimaxTail n (target (A0.withDimension D) O) Cls
         (2*c*Rates.subcriticalScale n (A0.withDimension D).theta (Rates.tau A0.gminus A0.gplus)) := by
   obtain ⟨F,hF⟩ := nondegenerate_source_model_family A0 D O pi hnd
   obtain ⟨c,hc,he⟩ := F.source_block_constant_lower hF hrough r hr
     (localClass (A0.withDimension D) O pi r) (Set.Subset.refl _)
   obtain ⟨n0,hn0⟩ := eventually_atTop.mp he
   refine ⟨c,hc,max n0 3,le_max_right _ _,?_⟩
   intro n hn Cls hCls
   have hh := hn0 n ((le_max_left _ _).trans hn)
   exact ⟨hh.1.trans (minimaxRMSE_mono_class n _ hCls),
     hh.2.trans (minimaxTail_mono_class n _ _ hCls)⟩

/-- The weaker common-scale rate follows independently from the literal
J=0 priors in every original model dimension and either score branch. -/
 theorem block_constant_minimax_lower (A : Parameters) {Z : Type*} [MeasurableSpace Z]
     (O : Observables Z A) (pi : ProbabilityMeasure Z) (r : ℝ)
     (hnd : Nondegenerate A O pi) (hr : 0<r) (hrough : A.theta<1/2) :
     ∃c:ℝ,0<c ∧ ∃n0:ℕ,3≤n0 ∧ ∀n:ℕ,n0≤n→
       ∀Cls : Set (ProbabilityMeasure (Observation A Z)),localClass A O pi r⊆Cls→
       ENNReal.ofReal (c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus))≤
         minimaxRMSE n (target A O) Cls ∧
       (3/8:ℝ≥0∞)≤ minimaxTail n (target A O) Cls
         (2*c*Rates.subcriticalScale n A.theta (Rates.tau A.gminus A.gplus)) := by
   cases A with
   | mk d alpha beta H delta gminus gplus M0 hd ha hb hH hdelta hgminus hgplus hM0 =>
     cases d with
     | zero => omega
     | succ D =>
       exact dimension_block_constant_minimax_lower
         (Parameters.mk (D+1) alpha beta H delta gminus gplus M0 hd ha hb hH hdelta hgminus hgplus hM0)
         D O pi r hnd hr hrough

end RoughRegime.Model
