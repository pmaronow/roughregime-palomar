module

public import RoughRegime.SourceRoughSequence
public import RoughRegime.AffineRisk
public import RoughRegime.PoissonMinimaxReduction


@[expose] public section
/-! A single statistically chosen genuine pair of prior sequences works for
any subsequently supplied class containing its support. The fixed offset and
risk constant are chosen before that class; additive target offsets preserve
both actual randomized minimax risks. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology
namespace RoughRegime.LatticePriors.SourceModelFamily
open RoughRegime.ReductionScales RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}
/-- The set of the literal selected hard observation laws. Validity and
smallness witnesses are proofs and do not change the underlying laws. -/
def selectedHardClass (F : SourceModelFamily A0 D O π) (θ τ c0 : ℝ) (n : ℕ) :
    Set (ProbabilityMeasure (Model.Observation (A0.withDimension D) Z)) :=
  {P | ∃ V : F.SelectedValidity θ τ c0 n,
    let G := F.selectedFrame θ τ c0 n V
    ∃ hsmall : (G.Au+G.Av)/G.rminus*F.scores.C ≤ 1/4,
    ∃ z, P=G.observationProbability π F.scores hsmall z}

/-- The target-offset requirement concerns only hard laws, even when the
containing class also includes other laws with unrelated target values. -/
def SelectedTargetOffsetClaim (F : SourceModelFamily A0 D O π) (θ τ c0 : ℝ)
    (T : ProbabilityMeasure (Model.Observation (A0.withDimension D) Z)→ℝ)
    (tstar : ℝ) : Prop :=
  ∀ᶠ n in atTop, ∀ P∈F.selectedHardClass θ τ c0 n,
    T P=Model.target (A0.withDimension D) O P+tstar

 theorem exists_fixed_offset_rough_lower (F : SourceModelFamily A0 D O π) (hF : F.Localized)
     (hrough : (A0.withDimension D).theta<1/2)
 :
     ∃ c0 c : ℝ, 0 < c ∧
       ∀ Cn : ℕ→Set (ProbabilityMeasure (Model.Observation (A0.withDimension D) Z)),
       F.SelectedClassSequenceClaim (A0.withDimension D).theta
         (RoughRegime.Rates.tau F.rminus F.rplus) c0 Cn →
       ∀ᶠ n : ℕ in atTop,
         ENNReal.ofReal (c*RoughRegime.Rates.subcriticalScale n (A0.withDimension D).theta
           (RoughRegime.Rates.tau A0.gminus A0.gplus)*Real.log n) ≤
           Model.minimaxRMSE n (Model.target (A0.withDimension D) O) (Cn n) ∧
         (3/8 : ℝ≥0∞) ≤ Model.minimaxTail n (Model.target (A0.withDimension D) O) (Cn n)
           (2*c*RoughRegime.Rates.subcriticalScale n (A0.withDimension D).theta
             (RoughRegime.Rates.tau A0.gminus A0.gplus)*Real.log n) := by
   classical
   let θ := (A0.withDimension D).theta
   let τ := RoughRegime.Rates.tau F.rminus F.rplus
   have hθ : 0<θ := by
     change 0<(A0.α+A0.β)/(D+1:ℕ)
     exact div_pos (add_pos A0.hα A0.hβ) (Nat.cast_pos.mpr (Nat.succ_pos _))
   have hab : A0.α/(D+1:ℕ)+A0.β/(D+1:ℕ)=θ := by
     change A0.α/(D+1:ℕ)+A0.β/(D+1:ℕ)=(A0.α+A0.β)/(D+1:ℕ)
     rw [add_div]
   have hτ : 0<τ := RoughRegime.Rates.tau_pos _ _ F.interval.1 (F.interval.2.1.trans F.interval.2.2)
   obtain ⟨c0,_,hH⟩ := F.exists_selected_poisson_small hF θ τ hθ hrough hτ hab
   obtain ⟨epsilon,he,Cerr,hCerr,B,hB,_,_,hcontrol⟩ :=
     F.eventually_actual_prior_control hF θ τ c0 1 hθ hrough hτ (by norm_num)
   obtain ⟨cg,hcg,hloggap⟩ := F.eventually_selected_mean_gap_log_lower θ c0 hθ hrough hab
   obtain ⟨cs,hcs,hscalegap⟩ := selectedSourceGapScale_eventually_log_lower A0 (D+1)
     (Nat.succ_pos _) θ c0 F.epsilonU F.epsilonV F.rminus F.rplus hθ hrough
     F.epsilonU_pos F.epsilonV_pos F.interval.1 (F.interval.2.1.trans F.interval.2.2) hab
   let c := cg/8
   have hc : 0<c := div_pos hcg (by norm_num)
   have hb := F.eventually_selected_scaled_variance_bound θ c0 (4*(F.rplus*B)^2) hθ hrough hab
   have hmean := F.eventually_selected_mean_gap θ c0 hθ hrough hab
   refine ⟨c0,c,hc,?_⟩
   intro Cn hclass
   have hevent : ∀ᶠ n : ℕ in atTop,
       ENNReal.ofReal (c*RoughRegime.Rates.subcriticalScale n θ τ*Real.log n) ≤
         Model.minimaxRMSE n (Model.target (A0.withDimension D) O) (Cn n) ∧
       (3/8 : ℝ≥0∞) ≤ Model.minimaxTail n (Model.target (A0.withDimension D) O) (Cn n)
         (2*c*RoughRegime.Rates.subcriticalScale n θ τ*Real.log n) := by
     filter_upwards [hH,hcontrol,hloggap,hb,hmean,hclass,
       tendsto_natCast_atTop_atTop.eventually hscalegap,poisson_count_eventually_small,
       eventually_ge_atTop 3] with n hHn hcontroln hlogn hbn hmeann hclassn hscalen hcountn hn
     let V := Classical.choice hHn.1
     let G := F.selectedFrame θ τ c0 n V.validity
     let nu := F.latticeSetup.coefficientPrior (selectedSourceLevel A0 (D+1) θ τ n)
       (frequency n θ τ) V.positive_frequency V.band_budget
     have hsmall : (G.Au+G.Av)/G.rminus*F.scores.C≤1/4 := V.small
     obtain ⟨Vcontrol,hsmallcontrol,_,_,_,hcontrols⟩ := hcontroln
     have hcp := hcontrols nu
     have hLp : ∀ positive:Bool,MemLp (F.actualTarget G hsmall) 2 (globalBlockPrior nu G.M positive) := hcp.1
     have hvarbase : ∀ positive:Bool,variance (F.actualTarget G hsmall) (globalBlockPrior nu G.M positive) ≤
         4*(F.rplus*B)^2/(selectedBlockCount θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℝ) := hcp.2.1
     obtain ⟨Vclass,hsmallclass,hclasslaws⟩ := hclassn
     have hclassactual : ∀ z,G.observationProbability π F.scores hsmall z∈Cn n := hclasslaws
     have hnr : 1<(n:ℝ) := by exact_mod_cast (by omega : 1<n)
     have hlogpos : 0<Real.log n := Real.log_pos hnr
     have hscalepos := RoughRegime.Rates.scale_pos n θ τ hnr
     have hgaplower : cg*Real.log n*RoughRegime.Rates.subcriticalScale n θ τ≤F.actualMeanGap G hsmall nu :=
       hlogn V.validity V.positive_frequency V.band_budget hsmall
     have hgap : 0<F.actualMeanGap G hsmall nu :=
       (mul_pos (mul_pos hcg hlogpos) hscalepos).trans_le hgaplower
     let base := F.gapCoefficient*selectedSourceGapScale A0 (D+1) θ τ c0
       F.epsilonU F.epsilonV F.rminus F.rplus n
     have hbase : 0≤base := (mul_pos F.gapCoefficient_pos
       ((mul_pos (mul_pos hcs hlogpos) hscalepos).trans_le hscalen)).le
     have hvar := F.prior_variance_control_of_bounds G hsmall nu
       (4*(F.rplus*B)^2/(selectedBlockCount θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n:ℝ))
       base hbase hvarbase hbn (hmeann V.validity V.positive_frequency V.band_budget hsmall)
     have hHel : GeneralTesting.hellingerSquared
         (G.canonicalPairedMixture nu π F.scores hsmall (G.pairPoissonRate (sourceObservationRate n)) true)
         (G.canonicalPairedMixture nu π F.scores hsmall (G.pairPoissonRate (sourceObservationRate n)) false) ≤1/128 := by
       change GeneralTesting.hellingerSquared (F.selectedPairedMixture θ τ c0 n V true)
         (F.selectedPairedMixture θ τ c0 n V false) ≤ 1/128
       rw [←F.selectedPairedHellinger_eq θ τ c0 n V]
       exact hHn.2
     have hr : 0<sourceObservationRate n := by
       change 0<2*(n:ℝ)
       positivity
     let delta := 2*c*RoughRegime.Rates.subcriticalScale n θ τ*Real.log n
     have hdelta : 0≤delta := by dsimp [delta]; positivity
     have hdeltaGap : delta≤F.actualMeanGap G hsmall nu/4 := by
       dsimp [delta,c]
       nlinarith
     have htest := F.canonical_testing_lower G nu hsmall (sourceObservationRate n) hr n (Cn n)
       hclassactual hHel hLp hgap hvar hcountn delta hdelta hdeltaGap
     refine ⟨?_,htest.1⟩
     apply le_trans _ htest.2
     apply le_of_eq
     congr 1
     dsimp [delta]
     ring
   simpa only [τ,F.normalized_tau,θ] using hevent

/-- The literal Proposition15(a) loss and additive-offset version. The prior
sequence and positive constant are selected before all containing classes and
all target offsets. -/
 theorem exists_fixed_offset_shift_rough_lower
     (F : SourceModelFamily A0 D O π) (hF : F.Localized)
     (hrough : (A0.withDimension D).theta < 1/2) :
     ∃ c0 c : ℝ, 0 < c ∧
       ∀ (Cn : ℕ→Set (ProbabilityMeasure (Model.Observation (A0.withDimension D) Z)))
         (T : ProbabilityMeasure (Model.Observation (A0.withDimension D) Z)→ℝ) (tstar : ℝ),
       F.SelectedClassSequenceClaim (A0.withDimension D).theta
         (RoughRegime.Rates.tau F.rminus F.rplus) c0 Cn →
       F.SelectedTargetOffsetClaim (A0.withDimension D).theta
         (RoughRegime.Rates.tau F.rminus F.rplus) c0 T tstar →
       ∀ᶠ n : ℕ in atTop,
         ENNReal.ofReal (Real.sqrt (3/8)*c*RoughRegime.Rates.subcriticalScale n
           (A0.withDimension D).theta (RoughRegime.Rates.tau A0.gminus A0.gplus)*Real.log n) ≤
           Model.minimaxRMSE n T (Cn n) ∧
         (3/8 : ℝ≥0∞) ≤ Model.minimaxTail n T (Cn n)
           (c*RoughRegime.Rates.subcriticalScale n (A0.withDimension D).theta
             (RoughRegime.Rates.tau A0.gminus A0.gplus)*Real.log n) := by
   obtain ⟨c0,c,hc,hbound⟩ := F.exists_fixed_offset_rough_lower hF hrough
   refine ⟨c0,c,hc,?_⟩
   intro Cn T tstar hclass htarget
   let Hn := F.selectedHardClass (A0.withDimension D).theta
     (RoughRegime.Rates.tau F.rminus F.rplus) c0
   have hHard : F.SelectedClassSequenceClaim (A0.withDimension D).theta
       (RoughRegime.Rates.tau F.rminus F.rplus) c0 Hn := by
     filter_upwards [hclass] with n hn
     obtain ⟨V,hsmall,hCl⟩ := hn
     exact ⟨V,hsmall,fun z=>⟨V,hsmall,z,rfl⟩⟩
   have hsub : ∀ᶠ n in atTop,Hn n⊆Cn n := by
     filter_upwards [hclass] with n hn
     obtain ⟨V,hsmall,hCl⟩ := hn
     rintro P ⟨VP,hsmallP,z,rfl⟩
     exact hCl z
   have hsqrt : Real.sqrt (3/8) ≤ 1 := by
     rw [Real.sqrt_le_one]
     norm_num
   filter_upwards [hbound Hn hHard,hsub,htarget,eventually_ge_atTop 3]
     with n hn hsubn htargetn hn3
   have hnr : 1 < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
   have hscale : 0 ≤ c*RoughRegime.Rates.subcriticalScale n
       (A0.withDimension D).theta (RoughRegime.Rates.tau A0.gminus A0.gplus)*Real.log n := by
     exact (mul_pos (mul_pos hc (RoughRegime.Rates.scale_pos n _ _ hnr)) (Real.log_pos hnr)).le
   have heq := Model.sign_affine_risks_eq n (Model.target (A0.withDimension D) O) T
     (Hn n) 1 tstar (c*RoughRegime.Rates.subcriticalScale n
       (A0.withDimension D).theta (RoughRegime.Rates.tau A0.gminus A0.gplus)*Real.log n)
       (by norm_num) (fun P hP => by simpa only [one_mul] using htargetn P hP)
   constructor
   · apply le_trans _ (Model.minimaxRMSE_mono_class n T hsubn)
     rw [heq.2]
     apply le_trans (ENNReal.ofReal_le_ofReal ?_) hn.1
     have hh := mul_le_mul_of_nonneg_right hsqrt hscale
     convert hh using 1 <;> ring
   · apply le_trans _ (Model.minimaxTail_mono_class n T _ hsubn)
     rw [heq.1]
     exact hn.2.trans (Model.minimaxTail_antitone_threshold n _ _ (by nlinarith [hscale]))

end RoughRegime.LatticePriors.SourceModelFamily
