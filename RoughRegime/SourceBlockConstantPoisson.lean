module

public import RoughRegime.SourceBlockConstantModel
public import RoughRegime.SourceBlockConstantParameters
public import RoughRegime.SourceSelectedPoisson


@[expose] public section
/-! Genuine marked-Poisson comparison for the literal J=0 construction.
The comparison constants are chosen before all grids and sample sizes. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology
namespace RoughRegime.LatticePriors.SourceModelFamily
open RoughRegime.ReductionScales RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}

structure BlockConstantPoissonValidity (F : SourceModelFamily A0 D O π)
    (θ τ c0 : ℝ) (n : ℕ) : Prop where
  validity : F.BlockConstantValidity θ τ c0 n
  positive_frequency : 0 < frequency n θ τ
  band_budget : 1 ≤ sourceBandConstant (D+1) A0.α A0.β * frequency n θ τ
  small : ((F.blockConstantFrame θ τ c0 n validity).Au+
    (F.blockConstantFrame θ τ c0 n validity).Av)/F.rminus*F.scores.C ≤ 1/4

def blockConstantPairedMixture (F : SourceModelFamily A0 D O π) (θ τ c0 : ℝ) (n : ℕ)
    (V : F.BlockConstantPoissonValidity θ τ c0 n) (positive : Bool) :=
  let G := F.blockConstantFrame θ τ c0 n V.validity
  G.canonicalPairedMixture
    (F.latticeSetup.coefficientPrior 0 (frequency n θ τ) V.positive_frequency
      (by simpa [sourceFineScale] using V.band_budget)) π F.scores V.small
    (G.pairPoissonRate (sourceObservationRate n)) positive

def blockConstantLambda (F : SourceModelFamily A0 D O π) (θ τ c0 : ℝ) (n : ℕ) : ℝ :=
  2*F.volume*(n:ℝ)/(selectedBlockCount θ τ c0 (fun _ => 1) (D+1) n:ℝ)

def blockConstantMajorant (F : SourceModelFamily A0 D O π)
    (θ τ c0 Cstar CG CE : ℝ) (n : ℕ) : ℝ :=
  (selectedBlockCount θ τ c0 (fun _ => 1) (D+1) n:ℝ)*
    canonicalPoissonMajorant Cstar CG CE 1 (F.blockConstantLambda θ τ c0 n)
      (amplitude F.epsilonU (selectedBlockCount θ τ c0 (fun _ => 1) (D+1) n:ℝ)
        1 (A0.α/(D+1:ℕ)) 1)
      (amplitude F.epsilonV (selectedBlockCount θ τ c0 (fun _ => 1) (D+1) n:ℝ)
        1 (A0.β/(D+1:ℕ)) 1) (frequency n θ τ)

theorem blockConstantPoissonValidity_eventually (F : SourceModelFamily A0 D O π)
    (hF : F.Localized) (θ τ c0 : ℝ) (hθ : 0 < θ) (hhalf : θ < 1/2) (hτ : 0 < τ) :
    ∀ᶠ n : ℕ in atTop, Nonempty (F.BlockConstantPoissonValidity θ τ c0 n) := by
  have hc := (sourceBandConstant_bounds (D+1) (Nat.succ_pos _) A0.α A0.β A0.hα A0.hβ).1
  have hf := ((frequency_tendsto θ τ hθ hhalf hτ).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop
    (max 1 (1/sourceBandConstant (D+1) A0.α A0.β))
  filter_upwards [F.eventually_blockConstant_hard_laws hF θ τ c0 1 hθ hhalf hτ (by norm_num),hf]
    with n hn hm
  obtain ⟨V,hsmall,_⟩ := hn
  simp only [Function.comp_apply] at hm
  have hm1 := (le_max_left (1:ℝ) _).trans hm
  have hmp : 0 < frequency n θ τ := by exact_mod_cast (zero_lt_one.trans_le hm1)
  have hmb := mul_le_mul_of_nonneg_left ((le_max_right (1:ℝ) _).trans hm) hc.le
  have hmb' : 1 ≤ sourceBandConstant (D+1) A0.α A0.β * frequency n θ τ := by
    simpa only [mul_one_div_cancel hc.ne'] using hmb
  exact ⟨⟨V,hmp,hmb',hsmall⟩⟩

def BlockConstantPairBound (F : SourceModelFamily A0 D O π) (Cstar CG CE : ℝ) : Prop :=
  ∀ (θ τ c0 : ℝ) (n : ℕ) (V : F.BlockConstantPoissonValidity θ τ c0 n),
    ((F.blockConstantFrame θ τ c0 n V.validity).pairPoissonRate (sourceObservationRate n):ℝ) ≤ 1 →
    GeneralTesting.hellingerSquared (F.blockConstantPairedMixture θ τ c0 n V true)
      (F.blockConstantPairedMixture θ τ c0 n V false) ≤ F.blockConstantMajorant θ τ c0 Cstar CG CE n

theorem blockConstantFrame_pair_rate_le (F : SourceModelFamily A0 D O π)
    (θ τ c0 : ℝ) (n : ℕ) (V : F.BlockConstantPoissonValidity θ τ c0 n) :
    0 ≤ F.blockConstantLambda θ τ c0 n ∧
    ((F.blockConstantFrame θ τ c0 n V.validity).pairPoissonRate (sourceObservationRate n):ℝ) ≤
      2*F.rplus*F.blockConstantLambda θ τ c0 n := by
  have hΛ : 0 ≤ F.blockConstantLambda θ τ c0 n := by
    unfold blockConstantLambda
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) F.volume_pos.le) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)
  refine ⟨hΛ,?_⟩
  change 2*(n:ℝ)*(F.blockConstantFrame θ τ c0 n V.validity).pairMass ≤ _
  rw [F.blockConstantFrame_pair_mean θ τ c0 n V.validity]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (F.blockConstantFrame θ τ c0 n V.validity).pairBarDensity_bounds.2
      (by norm_num)) hΛ

theorem uniform_blockConstant_pair_bound (F : SourceModelFamily A0 D O π) :
    ∃ C CG CE Cstar : ℝ, SourceLatticeConclusions F.latticeSetup C CG CE ∧
      1 ≤ Cstar ∧ F.BlockConstantPairBound Cstar CG CE := by
  obtain ⟨C,CG,CE,H⟩ := source_lattice_priors F.latticeSetup
  obtain ⟨Cstar,hstar,hcomp⟩ := F.latticeSetup.uniform_canonical_pair_comparison C CG CE H π F.scores
  refine ⟨C,CG,CE,Cstar,H,hstar,?_⟩
  intro θ τ c0 n V hrate
  let G := F.blockConstantFrame θ τ c0 n V.validity
  let ν := F.latticeSetup.coefficientPrior 0 (frequency n θ τ) V.positive_frequency
    (by simpa [sourceFineScale] using V.band_budget)
  have hr := F.blockConstantFrame_pair_rate_le θ τ c0 n V
  have hp := hcomp (F.blockConstantGrid θ τ c0 n) 0 (frequency n θ τ)
    V.validity.positive_grid F.epsilonU F.epsilonV (sourceDensityMargin n)
    F.epsilonU_pos.le F.epsilonV_pos.le V.validity.positive_margin V.validity.margin_le
    V.positive_frequency (by simpa [sourceFineScale] using V.band_budget)
    F.epsilonU_le F.epsilonV_le
  rw [←F.blockConstantFrame_eq_latticeSetup θ τ c0 n V.validity] at hp
  have hp' : GeneralTesting.hellingerSquared
      (G.canonicalPairMixture ν π F.scores V.small (G.pairPoissonRate (sourceObservationRate n)) true)
      (G.canonicalPairMixture ν π F.scores V.small (G.pairPoissonRate (sourceObservationRate n)) false) ≤
      canonicalPoissonMajorant Cstar CG CE 1 (F.blockConstantLambda θ τ c0 n) G.Au G.Av (frequency n θ τ) := by
    simpa only [Nat.mul_zero,pow_zero] using
      hp V.small (G.pairPoissonRate (sourceObservationRate n)) (F.blockConstantLambda θ τ c0 n)
        hr.1 hrate hr.2
  have ht := G.canonicalPairedMixture_hellinger_le ν π F.scores V.small
    (G.pairPoissonRate (sourceObservationRate n))
  have hcard : (Fintype.card (GridPair D (F.blockConstantGrid θ τ c0 n)):ℝ) ≤
      (selectedBlockCount θ τ c0 (fun _ => 1) (D+1) n:ℝ) := by
    rw [←selectedGrid_blockCount_eq,gridPair_card]
    unfold blockConstantGrid sourceGridCount
    push_cast
    rw [pow_succ]
    nlinarith [pow_nonneg (by positivity : 0 ≤ (2:ℝ)*
      selectedGridPairs θ τ c0 (fun _ => 1) (D+1) n) D]
  have hmajor : 0 ≤ canonicalPoissonMajorant Cstar CG CE 1 (F.blockConstantLambda θ τ c0 n)
      G.Au G.Av (frequency n θ τ) := by
    have hstar0 := zero_le_one.trans hstar
    have hcg0 := zero_le_one.trans H.gamma_constant_ge_one
    have hΛ := hr.1
    unfold canonicalPoissonMajorant
    positivity
  have hprod := (ht.trans (mul_le_mul_of_nonneg_left hp' (Nat.cast_nonneg _))).trans
    (mul_le_mul_of_nonneg_right hcard hmajor)
  change GeneralTesting.hellingerSquared (F.blockConstantPairedMixture θ τ c0 n V true)
    (F.blockConstantPairedMixture θ τ c0 n V false) ≤ _ at hprod
  simpa only [G,blockConstantMajorant,F.blockConstantFrame_Au θ τ c0 n V.validity,
    F.blockConstantFrame_Av θ τ c0 n V.validity] using hprod

theorem naturalLambda_tendsto_zero {P : AbstractScaleParameters} (S : NaturalScaleChoice P) :
    Tendsto S.Lambda atTop (𝓝 0) := by
  have hb := S.block_superlog 0
  simp only [Real.rpow_zero,mul_one] at hb
  have hi := (tendsto_inv_atTop_zero.comp hb).const_mul (2*P.v0)
  simp only [mul_zero] at hi
  apply hi.congr
  intro n
  rw [S.Lambda_eq]
  simp only [Function.comp_apply, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

 theorem blockConstantMajorant_eq_natural (F : SourceModelFamily A0 D O π)
    (hrough : (A0.withDimension D).theta < 1/2)
    (Cstar CG CE : ℝ) (hstar : 1 ≤ Cstar) (hCG : 1 ≤ CG) (hCE : 0 ≤ CE)
    (n : ℕ) (hn : 0 < n)
    (hM : 0 < frequency n (F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE).theta
      (F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE).tau) :
    let P := F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE
    F.blockConstantMajorant P.theta P.tau P.c0 Cstar CG CE n = P.blockConstantChoice.poissonMajorant n := by
  let P := F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE
  let S := P.blockConstantChoice
  have hB : S.B n = selectedBlockCount P.theta P.tau P.c0 (fun _ => 1) (D+1) n := rfl
  have hΛ : S.Lambda n = F.blockConstantLambda P.theta P.tau P.c0 n := by
    rw [S.Lambda_eq,hB]
    rfl
  have hAu : S.Au n = amplitude F.epsilonU
      (selectedBlockCount P.theta P.tau P.c0 (fun _ => 1) (D+1) n:ℝ) 1 (A0.α/(D+1:ℕ)) 1 := by
    rw [S.Au_eq,hB]
    rfl
  have hAv : S.Av n = amplitude F.epsilonV
      (selectedBlockCount P.theta P.tau P.c0 (fun _ => 1) (D+1) n:ℝ) 1 (A0.β/(D+1:ℕ)) 1 := by
    rw [S.Av_eq,hB]
    rfl
  change F.blockConstantMajorant P.theta P.tau P.c0 Cstar CG CE n = S.poissonMajorant n
  unfold blockConstantMajorant
  rw [←hAu,←hAv,←hΛ,←hB,
    block_mul_canonicalPoissonMajorant _ _ _ _ _ _ _ _ _ (by norm_num) (zero_lt_one.trans_le hCG) hM]
  have hraw := S.rawI_eq_physical n hn (by simp [S])
  have hpeq := S.poissonMajorant_eq n
  rw [hpeq,hraw]
  rfl

 theorem blockConstantMajorant_tendsto_zero (F : SourceModelFamily A0 D O π)
    (hrough : (A0.withDimension D).theta < 1/2)
    (Cstar CG CE : ℝ) (hstar : 1 ≤ Cstar) (hCG : 1 ≤ CG) (hCE : 0 ≤ CE) :
    let P := F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE
    Tendsto (F.blockConstantMajorant P.theta P.tau P.c0 Cstar CG CE) atTop (𝓝 0) := by
  let P := F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE
  have hm := ((frequency_tendsto P.theta P.tau P.theta_pos P.hhalf P.tau_pos).comp
    tendsto_natCast_atTop_atTop).eventually_gt_atTop 0
  apply P.blockConstantChoice.poissonMajorant_tendsto_zero.congr'
  filter_upwards [hm,eventually_gt_atTop 0] with n hm hn
  simp only [Function.comp_apply] at hm
  exact (F.blockConstantMajorant_eq_natural hrough Cstar CG CE hstar hCG hCE n hn (by exact_mod_cast hm)).symm

theorem blockConstantLambda_tendsto_zero (F : SourceModelFamily A0 D O π)
    (hrough : (A0.withDimension D).theta < 1/2)
    (Cstar CG CE : ℝ) (hstar : 1 ≤ Cstar) (hCG : 1 ≤ CG) (hCE : 0 ≤ CE) :
    let P := F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE
    Tendsto (F.blockConstantLambda P.theta P.tau P.c0) atTop (𝓝 0) := by
  let P := F.blockConstantParameters hrough Cstar CG CE hstar hCG hCE
  apply (naturalLambda_tendsto_zero P.blockConstantChoice).congr
  intro n
  rw [NaturalScaleChoice.Lambda_eq]
  rfl

/-- The actual J=0 paired experiment has small Hellinger square under the
original independent coefficient priors, with fixed comparison constants. -/
theorem blockConstant_poisson_comparison (F : SourceModelFamily A0 D O π)
    (hF : F.Localized) (hrough : (A0.withDimension D).theta < 1/2) :
    ∃ C CG CE Cstar : ℝ, ∃ H : SourceLatticeConclusions F.latticeSetup C CG CE,
      ∃ hstar : 1 ≤ Cstar,
      let P := F.blockConstantParameters hrough Cstar CG CE hstar
        H.gamma_constant_ge_one H.entropy_constant_nonneg
      ∀ᶠ n : ℕ in atTop, ∃ V : F.BlockConstantPoissonValidity P.theta P.tau P.c0 n,
        GeneralTesting.hellingerSquared (F.blockConstantPairedMixture P.theta P.tau P.c0 n V true)
          (F.blockConstantPairedMixture P.theta P.tau P.c0 n V false) ≤ 1/128 := by
  classical
  obtain ⟨C,CG,CE,Cstar,H,hstar,HB⟩ := F.uniform_blockConstant_pair_bound
  refine ⟨C,CG,CE,Cstar,H,hstar,?_⟩
  let P := F.blockConstantParameters hrough Cstar CG CE hstar
    H.gamma_constant_ge_one H.entropy_constant_nonneg
  have hLambda := F.blockConstantLambda_tendsto_zero hrough Cstar CG CE hstar
    H.gamma_constant_ge_one H.entropy_constant_nonneg
  have hr := hLambda.const_mul (2*F.rplus)
  simp only [mul_zero] at hr
  have hm := F.blockConstantMajorant_tendsto_zero hrough Cstar CG CE hstar
    H.gamma_constant_ge_one H.entropy_constant_nonneg
  filter_upwards [F.blockConstantPoissonValidity_eventually hF P.theta P.tau P.c0
    P.theta_pos P.hhalf P.tau_pos,hr.eventually_lt_const (by norm_num : (0:ℝ) < 1),
    hm.eventually_lt_const (by norm_num : (0:ℝ) < 1/128)] with n hn hr hm
  let V := Classical.choice hn
  refine ⟨V,?_⟩
  exact (HB P.theta P.tau P.c0 n V ((F.blockConstantFrame_pair_rate_le P.theta P.tau P.c0 n V).2.trans hr.le)).trans hm.le

end RoughRegime.LatticePriors.SourceModelFamily
