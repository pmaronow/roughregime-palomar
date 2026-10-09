module

public import RoughRegime.SourceStandaloneExtras


@[expose] public section
/-! The original selected source has true smooth-germ Holder constants
independent of the requested epsilon and all scale choices, plus genuine
little-o sup localization relative to the actual density margin. -/
noncomputable section
open MeasureTheory Filter Set
open scoped ContDiff Topology
namespace RoughRegime.LatticePriors.SourceModelFamily
open RoughRegime.Localization RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false
variable {A0 : Model.Parameters} {D : ℕ} {Z : Type*} [MeasurableSpace Z]
    {O : Model.Observables Z (A0.withDimension D)} {π : ProbabilityMeasure Z}

theorem germ_holder_frame_budget (F : SourceModelFamily A0 D O π)
    (G : SmoothGerm) (mode : GermMode) (haxis : mode.axisCondition G) :
    ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧
      ∀ (N J M : ℕ) (hN : 0 < N) (m epsilonU epsilonV delta : ℝ),
      ∀ (hm : 0 < m) (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
        (hmargin : delta ≤ F.margin),
      (2:ℝ)^((J:ℝ)*sourceAlpha0 A0.α A0.β) ≤ m →
      m ≤ (2:ℝ)^((J:ℝ)*min A0.α A0.β) →
      let B := sourceCanonicalFrame D N J (sourceGateOrder A0.α A0.β) M hN
        (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) A0.α A0.β)
        (sourceAlpha0 A0.α A0.β) m epsilonU epsilonV A0.α A0.β F.volume F.rminus F.rplus delta
        (sourceGammaStar_bounds (D+1) (Nat.succ_pos _)).1
        (sourceGammaStar_bounds (D+1) (Nat.succ_pos _)).2.1 hm heU heV F.volume_pos
        (F.volume_half.trans (by norm_num)) F.interval.1 (F.interval.2.1.trans F.interval.2.2)
        hd hmargin F.denominator_pos
      B.Au+B.Av ≤ eta → ∀ z,
        ContDiff ℝ ∞ (fun x => G.K ((B.field z).u x,(B.field z).v x)-G.baseline) ∧
        ∀ t : ℝ, 0 < t → t ≤ mode.exponent A0.α A0.β →
          Model.holderNorm (fun x => G.K ((B.field z).u x,(B.field z).v x)-G.baseline) t ≤
            ENNReal.ofReal (C*(epsilonU+epsilonV)) := by
  exact source_germ_holder D (sourceGateOrder A0.α A0.β) (sourceJetBudget A0.α A0.β)
    (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) A0.α A0.β) (sourceAlpha0 A0.α A0.β)
    A0.α A0.β F.volume F.rminus F.rplus
    (sourceGammaStar_bounds (D+1) (Nat.succ_pos _)).1
    (sourceGammaStar_bounds (D+1) (Nat.succ_pos _)).2.1
    (zero_lt_one.trans_le (sourceLambdaStar_ge_one _ _ _))
    (sourceAlpha0_pos _ _ A0.hα A0.hβ).le (sourceAlpha0_lt_one _ _)
    (sourceJetBudget_pos _ _) (sourceJetBudget_le_twice_order _ _)
    (lt_min (sourceAlpha0_lt_alpha _ _ A0.hα) (sourceAlpha0_lt_beta _ _ A0.hβ))
    (source_alpha_derivative_budget _ _ A0.hα) (source_beta_derivative_budget _ _ A0.hβ)
    F.volume_pos (F.volume_half.trans (by norm_num)) F.interval.1
    (F.interval.2.1.trans F.interval.2.2) F.denominator_pos G mode haxis

theorem selected_germ_holder_budget (F : SourceModelFamily A0 D O π)
    (G : SmoothGerm) (mode : GermMode) (haxis : mode.axisCondition G) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ τ c0 epsilon : ℝ), 0 < θ → θ < 1/2 → 0 < τ →
      F.epsilonU+F.epsilonV ≤ epsilon →
      ∀ᶠ n in atTop, ∀ V : F.SelectedValidity θ τ c0 n, ∀ z,
        let B := F.selectedFrame θ τ c0 n V
        ContDiff ℝ ∞ (fun x => G.K ((B.field z).u x,(B.field z).v x)-G.baseline) ∧
        ∀ t : ℝ, 0 < t → t ≤ mode.exponent A0.α A0.β →
          Model.holderNorm (fun x => G.K ((B.field z).u x,(B.field z).v x)-G.baseline) t ≤
            ENNReal.ofReal (C*epsilon) := by
  obtain ⟨eta,C,heta,hC,hbound⟩ := F.germ_holder_frame_budget G mode haxis
  refine ⟨C,hC,?_⟩
  intro θ τ c0 epsilon hθ hhalf hτ hweight
  have he := (selectedAmplitudeEnvelope_tendsto A0 (D+1) (Nat.succ_pos _)).eventually_lt_const heta
  filter_upwards [F.selectedFrame_amplitude_le_envelope θ τ c0 hθ hhalf hτ,he] with n hn hne
  intro V z
  have hsmall : (F.selectedFrame θ τ c0 n V).Au+(F.selectedFrame θ τ c0 n V).Av ≤ eta :=
    (hn V).trans hne.le
  have hh := hbound _ _ _ V.positive_grid _ _ _ _ V.positive_multiplier
    F.epsilonU_pos.le F.epsilonV_pos.le V.positive_margin V.margin_le
    (selectedSource_level_budgets A0 (D+1) θ τ n).1 le_rfl hsmall z
  refine ⟨hh.1,?_⟩
  intro t ht htg
  exact (hh.2 t ht htg).trans
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hweight hC.le))

/-- Every local smooth nuisance has a true sup envelope little-o of the
literal density margin, uniformly over all prior realizations and scale choices. -/
theorem selected_germ_sup_littleO (F : SourceModelFamily A0 D O π)
    (G : SmoothGerm) :
    ∃ C : ℝ, 0 < C ∧
      (fun n => C*selectedAmplitudeEnvelope A0 (D+1) n) =o[atTop] sourceDensityMargin ∧
      ∀ (θ τ c0 : ℝ), 0 < θ → θ < 1/2 → 0 < τ →
      ∀ᶠ n in atTop, ∀ V : F.SelectedValidity θ τ c0 n, ∀ z x,
        |G.K (((F.selectedFrame θ τ c0 n V).field z).u x,
          ((F.selectedFrame θ τ c0 n V).field z).v x)-G.baseline| ≤
          C*selectedAmplitudeEnvelope A0 (D+1) n := by
  obtain ⟨eta,C,heta,hC,hcontrol⟩ := canonical_germ_sup_control G F.rminus F.interval.1
  refine ⟨C,hC,?_,?_⟩
  · apply (Asymptotics.isLittleO_iff_tendsto' ?_).mpr
    · simpa only [mul_zero,mul_div_assoc] using
        (selectedAmplitudeEnvelope_div_margin_tendsto A0 (D+1) (Nat.succ_pos _)).const_mul C
    · filter_upwards [eventually_ge_atTop 2] with n hn
      intro hzero
      exact False.elim ((sourceDensityMargin_pos n (by omega)).ne' hzero)
  · intro θ τ c0 hθ hhalf hτ
    have he := (selectedAmplitudeEnvelope_tendsto A0 (D+1) (Nat.succ_pos _)).eventually_lt_const heta
    filter_upwards [F.selectedFrame_amplitude_le_envelope θ τ c0 hθ hhalf hτ,he] with n hn hne
    intro V z x
    let B := F.selectedFrame θ τ c0 n V
    have hsmall : B.Au+B.Av ≤ eta := (hn V).trans hne.le
    have hs := (hcontrol D _ _ B rfl hsmall z).1 x
    exact hs.trans (mul_le_mul_of_nonneg_left (hn V) hC.le)

end RoughRegime.LatticePriors.SourceModelFamily
