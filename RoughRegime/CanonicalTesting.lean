module

public import RoughRegime.CanonicalPairedMixtures
public import RoughRegime.SourceSelectedStatistics
public import RoughRegime.PoissonMinimaxReduction


@[expose] public section
/-! Actual canonical prior testing transfers through the literal physical
placement kernel into the true fixed-size model experiment. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace RoughRegime.LatticePriors.SourceModelFamily
open RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}

 theorem canonical_testing_lower (F : SourceModelFamily A0 D O π)
     {N : ℕ} {ι : Type*} [Fintype ι] (G : CanonicalFrame D N ι)
     (nu : Measure (ι→ℤ)) [IsProbabilityMeasure nu]
     (hsmall : (G.Au+G.Av)/G.rminus*F.scores.C ≤ 1/4)
     (rate : ℝ≥0) (hrate : 0<rate) (n : ℕ)
     (C : Set (ProbabilityMeasure (Model.Observation (A0.withDimension D) Z)))
     (hclass : ∀ z,G.observationProbability π F.scores hsmall z∈C)
     (hH : GeneralTesting.hellingerSquared
       (G.canonicalPairedMixture nu π F.scores hsmall (G.pairPoissonRate rate) true)
       (G.canonicalPairedMixture nu π F.scores hsmall (G.pairPoissonRate rate) false) ≤ 1/128)
     (hLp : ∀ positive:Bool,MemLp (F.actualTarget G hsmall) 2 (globalBlockPrior nu G.M positive))
     (hgap : 0<F.actualMeanGap G hsmall nu)
     (hvar : ∀ positive:Bool,variance (F.actualTarget G hsmall) (globalBlockPrior nu G.M positive) ≤
       (F.actualMeanGap G hsmall nu)^2/1024)
     (hcount : ProbabilityTheory.poissonMeasure rate {m | m < n} ≤ (1/32 : ℝ≥0∞))
     (δ : ℝ) (hδ : 0 ≤ δ) (hδgap : δ ≤ F.actualMeanGap G hsmall nu/4) :
     (3/8 : ℝ≥0∞) ≤ Model.minimaxTail n (Model.target (A0.withDimension D) O) C δ ∧
       ENNReal.ofReal (δ/2) ≤ Model.minimaxRMSE n (Model.target (A0.withDimension D) O) C := by
   let L := G.canonicalPairedMixture nu π F.scores hsmall (G.pairPoissonRate rate) true
   let R := G.canonicalPairedMixture nu π F.scores hsmall (G.pairPoissonRate rate) false
   let PL := globalBlockPrior (D:=D) (N:=N) nu G.M true
   let PR := globalBlockPrior (D:=D) (N:=N) nu G.M false
   let K := G.physicalPairProductKernel π F.scores hsmall (G.pairPoissonRate rate)
   let J := G.pairObservationKernel π F.scores hsmall rate
   let P := G.observationProbability π F.scores hsmall
   let T := Model.target (A0.withDimension D) O
   have hPL : (PL ⊗ₘ K).map Prod.snd=L.measure :=
     G.physicalPairProductKernel_marginal nu π F.scores hsmall (G.pairPoissonRate rate) true
   have hPR : (PR ⊗ₘ K).map Prod.snd=R.measure :=
     G.physicalPairProductKernel_marginal nu π F.scores hsmall (G.pairPoissonRate rate) false
   have htarget : (fun z=>T (P z))=F.actualTarget G hsmall := rfl
   have hgap' : 0 < |(∫ z,T (P z) ∂PR)-(∫ z,T (P z) ∂PL)| := by
     rw [htarget,abs_sub_comm]
     exact hgap
   have hvarL : variance (fun z=>T (P z)) PL ≤ |(∫ z,T (P z) ∂PR)-(∫ z,T (P z) ∂PL)|^2/1024 := by
     rw [htarget,abs_sub_comm]
     exact hvar true
   have hvarR : variance (fun z=>T (P z)) PR ≤ |(∫ z,T (P z) ∂PR)-(∫ z,T (P z) ∂PL)|^2/1024 := by
     rw [htarget,abs_sub_comm]
     exact hvar false
   have hδgap' : δ ≤ |(∫ z,T (P z) ∂PR)-(∫ z,T (P z) ∂PL)|/4 := by
     rw [htarget,abs_sub_comm]
     exact hδgap
   exact GeneralTesting.fuzzy_placement_fixed_minimax L R PL PR K hPL hPR J P T rate
     (fun z=>(G.physicalPairProductKernel_placement π F.scores hsmall rate hrate z).symm)
     C hclass (F.actualTarget_measurable G hsmall) (hLp true) (hLp false)
     hH hgap' hvarL hvarR n hcount δ hδ hδgap'

end RoughRegime.LatticePriors.SourceModelFamily
