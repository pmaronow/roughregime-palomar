module

public import RoughRegime.ApplicationsPilot
public import RoughRegime.ApplicationsRisk


@[expose] public section
/-! The Lipschitz risk reductions with actual independent samples and random seeds. -/
noncomputable section
open scoped BigOperators ENNReal Topology
open MeasureTheory Filter
namespace RoughRegime.Applications

/-- The actual projected empirical vector mean has the required L² error. -/
lemma projectedMomentMean_error_eLpNorm {Ω S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (seedLaw : Measure S) [IsProbabilityMeasure seedLaw] {k n : ℕ} (hn : n ≠ 0)
    (h : Fin k → Ω → ℝ) (hmh : ∀ j, Measurable (h j)) (hh : ∀ j, MemLp (h j) 2 μ)
    (lo hi : Fin k → ℝ) (hlohi : ∀ j, lo j ≤ hi j)
    (hm : ∀ j, (∫ x, h j x ∂μ) ∈ Set.Icc (lo j) (hi j))
    (B : ℝ) (hB : 0 ≤ B)
    (hvariance : (∫ x, ‖responseVector h x - momentMean μ h‖ ^ 2 ∂μ) ≤ B ^ 2) :
    eLpNorm (fun x : (Fin n → Ω) × S =>
      ‖projectedMomentMean h lo hi hlohi x.1 - momentMean μ h‖) 2
      ((Measure.pi (fun _ : Fin n => μ)).prod seedLaw) ≤ ENNReal.ofReal (B / Real.sqrt n) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : Measurable (fun x : (Fin n → Ω) × S =>
      ‖projectedMomentMean h lo hi hlohi x.1 - momentMean μ h‖) :=
    (((projectedMomentMean_measurable h hmh lo hi hlohi).comp measurable_fst).sub measurable_const).norm
  have hint := (projectedMomentMean_error_integrable μ h hmh lo hi hlohi (momentMean μ h) (n := n)).comp_fst seedLaw
  apply eLpNorm_two_le_of_mse _ _ he hint B n hB hnreal
  rw [integral_prod _ hint]
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
  exact (projectedMomentMean_mse μ hn h hh hmh lo hi hlohi hm).trans
    (div_le_div_of_nonneg_right hvariance hnreal.le)

/-- Lemma 19(a), and the approximate reverse-risk inequality of Lemma 19(b),
with the projected empirical vector mean built from the same actual iid sample.
The sample's extra probability space permits arbitrary independent estimator randomness. -/
theorem lipschitz_iid_minimax_rmse {Ω Θ S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] (seedLaw : Measure S) [IsProbabilityMeasure seedLaw]
    {k m n : ℕ} (hn : n ≠ 0) (laws : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (laws θ)]
    (T0 : Θ → ℝ) (Ti : Fin m → Θ → ℝ) (C : Set Θ)
    (h : Fin k → Ω → ℝ) (hmh : ∀ j, Measurable (h j))
    (hh : ∀ θ j, MemLp (h j) 2 (laws θ))
    (mlo mhi : Fin k → ℝ) (hmlohi : ∀ j, mlo j ≤ mhi j)
    (hm : ∀ θ j, (∫ x, h j x ∂laws θ) ∈ Set.Icc (mlo j) (mhi j))
    (lo hi : Fin m → ℝ) (hlohi : ∀ i, lo i ≤ hi i)
    (Φ : ((i : Fin m) → Set.Icc (lo i) (hi i)) → momentRectangle mlo mhi → ℝ)
    (L e B : ℝ) (hL : 0 ≤ L) (he : 0 ≤ e) (hB : 0 ≤ B)
    (hLip : ∀ a b q r, |Φ a q - Φ b r| ≤
      L * ((∑ i, |(a i : ℝ) - b i|) + dist q r))
    (hmem : ∀ θ ∈ C, ∀ i, Ti i θ ∈ Set.Icc (lo i) (hi i))
    (hrelation : ∀ θ ∈ C,
      |T0 θ - Φ (fun i => Set.projIcc (lo i) (hi i) (hlohi i) (Ti i θ))
        ⟨momentMean (laws θ) h, hm θ⟩| ≤ e)
    (hvariance : ∀ θ ∈ C,
      (∫ x, ‖responseVector h x - momentMean (laws θ) h‖ ^ 2 ∂laws θ) ≤ B ^ 2) :
    minimaxRMSE (fun θ => (Measure.pi (fun _ : Fin n => laws θ)).prod seedLaw) T0 C ≤
      ENNReal.ofReal L * (∑ i, minimaxRMSE
        (fun θ => (Measure.pi (fun _ : Fin n => laws θ)).prod seedLaw) (Ti i) C) +
      ENNReal.ofReal L * ENNReal.ofReal (B / Real.sqrt n) + ENNReal.ofReal e := by
  let μhat : ((Fin n → Ω) × S) → momentRectangle mlo mhi := fun x =>
    ⟨projectedMomentMean h mlo mhi hmlohi x.1,
      fun j => (Set.projIcc (mlo j) (mhi j) (hmlohi j) (empiricalMean (h j) x.1)).property⟩
  have hμhat : Measurable μhat :=
    ((projectedMomentMean_measurable h hmh mlo mhi hmlohi).comp measurable_fst).subtype_mk
  let μtrue : Θ → momentRectangle mlo mhi := fun θ => ⟨momentMean (laws θ) h, hm θ⟩
  apply lipschitz_combination_minimax
    (fun θ => (Measure.pi (fun _ : Fin n => laws θ)).prod seedLaw)
    T0 Ti C lo hi hlohi Φ (lipschitz_combination_measurable lo hi Φ L hL hLip) μhat hμhat μtrue L e
    (ENNReal.ofReal (B / Real.sqrt n)) hL he hLip hmem hrelation
  intro θ hθ
  dsimp only [μhat, μtrue]
  simp only [Subtype.dist_eq, dist_eq_norm]
  exact projectedMomentMean_error_eLpNorm (laws θ) seedLaw hn h hmh (hh θ)
    mlo mhi hmlohi (hm θ) B hB (hvariance θ hθ)

/-- The Chebyshev error vanishes under the paper's condition `n t_n² → ∞`. -/
lemma transfer_error_tendsto_zero (L B : ℝ) (tn : ℕ → ℝ)
    (hnt : Tendsto (fun n : ℕ => (n : ℝ) * (tn n) ^ 2) atTop atTop) :
    Tendsto (fun n : ℕ => ENNReal.ofReal (16 * L ^ 2 * B ^ 2 / ((n : ℝ) * (tn n) ^ 2)))
      atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => 16 * L ^ 2 * B ^ 2 / ((n : ℝ) * (tn n) ^ 2)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hnt
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp h

/-- The hardness consequence of Lemma 19(b), on genuine iid experiments with
independent estimator randomness. The zero-moment case is represented by `B = 0`. -/
theorem hardness_reverse_transfer_iid {Ω Θ S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] (seedLaw : Measure S) [IsProbabilityMeasure seedLaw]
    {k : ℕ} (laws : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (laws θ)]
    (T0 T1 : Θ → ℝ) (Cn : ℕ → Set Θ)
    (h : Fin k → Ω → ℝ) (hmh : ∀ j, Measurable (h j))
    (hh : ∀ θ j, MemLp (h j) 2 (laws θ))
    (mlo mhi : Fin k → ℝ) (hmlohi : ∀ j, mlo j ≤ mhi j)
    (hm : ∀ θ j, (∫ x, h j x ∂laws θ) ∈ Set.Icc (mlo j) (mhi j))
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (Φ : Set.Icc lo hi → momentRectangle mlo mhi → ℝ)
    (L B : ℝ) (hL : 0 < L)
    (hLip : ∀ a b q r, |Φ a q - Φ b r| ≤ L * (|(a : ℝ) - b| + dist q r))
    (tn en : ℕ → ℝ) (ht : ∀ᶠ n in atTop, 0 < tn n)
    (hconditions : ∀ᶠ n in atTop, en n ≤ tn n / 2 ∧
      (∀ θ ∈ Cn n, T0 θ ∈ Set.Icc lo hi) ∧
      (∀ θ ∈ Cn n, |T1 θ - Φ (Set.projIcc lo hi hlohi (T0 θ))
        ⟨momentMean (laws θ) h, hm θ⟩| ≤ en n) ∧
      (∀ θ ∈ Cn n,
        (∫ x, ‖responseVector h x - momentMean (laws θ) h‖ ^ 2 ∂laws θ) ≤ B ^ 2))
    (hdecay : B = 0 ∨ Tendsto (fun n : ℕ => (n : ℝ) * (tn n) ^ 2) atTop atTop)
    (H : ℝ≥0∞)
    (hhard : H ≤ Filter.liminf (fun n =>
      minimaxTail (fun θ => (Measure.pi (fun _ : Fin n => laws θ)).prod seedLaw)
        T1 (Cn n) (tn n)) atTop) :
    H ≤ Filter.liminf (fun n =>
      minimaxTail (fun θ => (Measure.pi (fun _ : Fin n => laws θ)).prod seedLaw)
        T0 (Cn n) (tn n / (4 * L))) atTop := by
  let η : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (16 * L ^ 2 * B ^ 2 / ((n : ℝ) * (tn n) ^ 2))
  apply hardness_transfer_vanishing_error _ _ η H hhard
  · filter_upwards [ht, hconditions, eventually_gt_atTop 0] with n htn hc hn
    exact reverse_transfer_iid_randomized seedLaw (Nat.ne_of_gt hn) laws T0 T1 (Cn n)
      h hmh hh mlo mhi hmlohi hm lo hi hlohi Φ
      (lipschitz_reverse_measurable lo hi Φ L hL.le hLip)
      L (tn n) (en n) B hL htn hc.1 hLip hc.2.1 hc.2.2.1 hc.2.2.2
  · rcases hdecay with hzero | hnt
    · simp only [η, hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_div,
        ENNReal.ofReal_zero]
      exact tendsto_const_nhds
    · exact transfer_error_tendsto_zero L B tn hnt

end RoughRegime.Applications
