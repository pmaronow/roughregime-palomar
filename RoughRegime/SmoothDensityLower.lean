module

public import RoughRegime.SmoothDensityParametric
public import RoughRegime.ModelSourceHardness
public import RoughRegime.BracketRateConsequences


@[expose] public section
/-! The original main lower bounds persist on actual C-infinity design laws
without any uniform bound on their derivatives. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology
namespace RoughRegime.LatticePriors.CanonicalFrame

theorem observationProbability_mem_smoothDensityClass {D N : ℕ} {ι : Type*} [Fintype ι]
    (G : CanonicalFrame D N ι) {Z : Type*} [MeasurableSpace Z]
    (π : ProbabilityMeasure Z) (S : SpatialAffine.Scores (π : Measure Z))
    (hsmall : (G.Au+G.Av)/G.rminus*S.C≤1/4)
    (z : GridPair D N→PairState ι) :
    G.observationProbability π S hsmall z∈Model.smoothDensityClass (D+1) Z := by
  refine ⟨G.p z,(G.realization z).density_smooth,?_⟩
  exact G.observationProbability_marginal π S hsmall z

end RoughRegime.LatticePriors.CanonicalFrame
namespace RoughRegime.Model
open RoughRegime.LatticePriors RoughRegime.LatticePriors.SourceModelFamily
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 theorem smooth_localClass_rough_hardness_dimension (A0 : Parameters) (D : ℕ)
    {Z : Type*} [MeasurableSpace Z] (O : Observables Z (A0.withDimension D))
    (π : ProbabilityMeasure Z) (hnd : Nondegenerate (A0.withDimension D) O π)
    (r : ℝ) (hr : 0<r) (hrough : (A0.withDimension D).theta<1/2) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
      (3/8:ℝ≥0∞)≤ minimaxTail n (target (A0.withDimension D) O)
        (localClass (A0.withDimension D) O π r ∩ smoothDensityClass (D+1) Z)
        (2*c*lowerBracketScale (A0.withDimension D).bracketParameters n) := by
  obtain ⟨F,hF⟩ := nondegenerate_source_model_family A0 D O π hnd
  have hθ := (A0.withDimension D).theta_pos
  have hτ := Rates.tau_pos _ _ F.interval.1 (F.interval.2.1.trans F.interval.2.2)
  have hclass : ∀c0:ℝ,F.SelectedClassClaim (A0.withDimension D).theta
      (Rates.tau F.rminus F.rplus) c0
        (localClass (A0.withDimension D) O π r ∩ smoothDensityClass (D+1) Z) := by
    intro c0
    filter_upwards [F.selectedClassClaim_local hF _ _ c0 r hθ hrough hτ hr] with n hn
    obtain ⟨V,hsmall,hm⟩ := hn
    exact ⟨V,hsmall,fun z => ⟨hm z,
      (F.selectedFrame _ _ c0 n V).observationProbability_mem_smoothDensityClass π F.scores hsmall z⟩⟩
  obtain ⟨c,hc,n0,_,hb⟩ := F.source_family_rough_lower hF hrough _ hclass
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop n0] with n hn
  have hs : lowerBracketScale (A0.withDimension D).bracketParameters n=
      Rates.subcriticalScale n (A0.withDimension D).theta (Rates.tau A0.gminus A0.gplus)*Real.log n := by
    unfold lowerBracketScale
    change (if (A0.withDimension D).theta<1/2 then _ else _)=_
    rw [ite_eq_left hrough]
    rfl
  rw [hs]
  convert (hb n hn).2 using 1
  congr 1
  ring

 theorem smooth_localClass_rough_hardness (A : Parameters)
    {Z : Type*} [MeasurableSpace Z] (O : Observables Z A)
    (π : ProbabilityMeasure Z) (hnd : Nondegenerate A O π)
    (r : ℝ) (hr : 0<r) (hrough : A.theta<1/2) :
    ∃c:ℝ,0<c ∧ ∀ᶠn:ℕ in atTop,
      (3/8:ℝ≥0∞)≤ minimaxTail n (target A O)
        (localClass A O π r ∩ smoothDensityClass A.d Z)
        (2*c*lowerBracketScale A.bracketParameters n) := by
  cases A with
  | mk d α β H δ gminus gplus M0 hd hα hβ hH hδ hgminus hgplus hM0 => cases d with
    | zero => omega
    | succ D =>
      exact smooth_localClass_rough_hardness_dimension
        (Parameters.mk (D+1) α β H δ gminus gplus M0 hd hα hβ hH hδ hgminus hgplus hM0)
        D O π hnd r hr hrough

 theorem smooth_localClass_lowerBracket (A : Parameters)
    {Z : Type*} [MeasurableSpace Z] (O : Observables Z A)
    (π : ProbabilityMeasure Z) (hnd : Nondegenerate A O π) (r : ℝ) (hr : 0<r) :
    LowerBracket (target A O) (localClass A O π r ∩ smoothDensityClass A.d Z) A.bracketParameters := by
  by_cases hrough : A.theta<1/2
  · obtain ⟨c,hc,he⟩ := smooth_localClass_rough_hardness A O π hnd r hr hrough
    have hnonneg : ∀ n : ℕ,0≤2*c*lowerBracketScale A.bracketParameters n := by
      intro n
      unfold lowerBracketScale
      change 0≤2*c*(if A.theta<1/2 then _ else _)
      rw [ite_eq_left hrough]
      by_cases hn : n=0
      · subst n; simp [Rates.subcriticalScale]
      · have hnR : 1≤(n:ℝ) := by exact_mod_cast (show 1≤n by omega)
        have hln := Real.log_nonneg hnR
        unfold Rates.subcriticalScale
        positivity
    have hh := hardness_to_risk (target A O)
      (fun _=>localClass A O π r ∩ smoothDensityClass A.d Z)
      (localClass A O π r ∩ smoothDensityClass A.d Z)
      (fun n=>2*c*lowerBracketScale A.bracketParameters n) hnonneg
      (Eventually.of_forall (fun _=>subset_rfl))
      (le_liminf_of_le (by isBoundedDefault) he)
    have hp : ∀ᶠn:ℕ in atTop,
        ENNReal.ofReal (c*lowerBracketScale A.bracketParameters n)≤
          minimaxRMSE n (target A O) (localClass A O π r ∩ smoothDensityClass A.d Z) ∧
        (1/4:ℝ≥0∞)≤ minimaxTail n (target A O)
          (localClass A O π r ∩ smoothDensityClass A.d Z) (2*c*lowerBracketScale A.bracketParameters n) := by
      filter_upwards [hh] with n hn
      refine ⟨?_,hn.1⟩
      convert hn.2 using 1
      congr 1
      ring
    obtain ⟨n0,hn0⟩ := eventually_atTop.mp hp
    refine ⟨c,hc,max 3 n0,le_max_left _ _,?_⟩
    intro n hn
    have hh := hn0 n ((le_max_right _ _).trans hn)
    exact ⟨hh.1,fun _=>hh.2⟩
  · obtain ⟨c,hc,he⟩ := smooth_localClass_parametric_rootn A O π hnd r hr
    obtain ⟨n0,hn0⟩ := eventually_atTop.mp he
    refine ⟨c,hc,max 3 n0,le_max_left _ _,?_⟩
    intro n hn
    refine ⟨?_,fun hh=>False.elim (hrough hh)⟩
    simpa only [lowerBracketScale,Parameters.bracketParameters,ite_eq_right hrough]
      using hn0 n ((le_max_right _ _).trans hn)

 theorem smooth_localClass_bracket (A : Parameters)
    {Z : Type*} [MeasurableSpace Z] (O : Observables Z A)
    (π : ProbabilityMeasure Z) (hnd : Nondegenerate A O π) (r : ℝ) (hr : 0<r) :
    Bracket (target A O) (localClass A O π r ∩ smoothDensityClass A.d Z)
      A.bracketParameters (A.nu:ℝ) :=
  ⟨smooth_localClass_lowerBracket A O π hnd r hr,
    upperBracket_mono_class _ _ _ (fun _ h=>localClass_subset A O π r h.1) (model_upperBracket A O)⟩

end RoughRegime.Model
