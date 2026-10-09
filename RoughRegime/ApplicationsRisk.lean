module

public import RoughRegime.Applications


@[expose] public section
/-! Minkowski and optimization steps for Lemma 19(a) and (b). -/
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
namespace RoughRegime.Applications

/-- The paper's coordinatewise Lipschitz hypothesis already ensures measurability. -/
lemma lipschitz_combination_measurable {M : Type*} [PseudoMetricSpace M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] {m : ℕ}
    (lo hi : Fin m → ℝ)
    (Φ : ((i : Fin m) → Set.Icc (lo i) (hi i)) → M → ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ a b q r, |Φ a q - Φ b r| ≤
      L * ((∑ i, |(a i : ℝ) - b i|) + dist q r)) :
    Measurable (Function.uncurry Φ) := by
  let K : NNReal := ⟨L * (m + 1), by positivity⟩
  have hl : LipschitzWith K (Function.uncurry Φ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have hs : (∑ i, |(x.1 i : ℝ) - y.1 i|) ≤ (m : ℝ) * dist x y := by
      calc
        _ ≤ ∑ _i : Fin m, dist x y := by
          apply Finset.sum_le_sum
          intro i _
          have hc := dist_le_pi_dist x.1 y.1 i
          rw [Subtype.dist_eq, Real.dist_eq] at hc
          exact hc.trans (by simp only [Prod.dist_eq]; exact le_max_left _ _)
        _ = (m : ℝ) * dist x y := by simp
    have hd : dist x.2 y.2 ≤ dist x y := by
      simp only [Prod.dist_eq]
      exact le_max_right _ _
    exact (hLip x.1 y.1 x.2 y.2).trans
      ((mul_le_mul_of_nonneg_left (add_le_add hs hd) hL).trans_eq (by
        change _ = (L * (m + 1)) * dist x y
        ring))
  exact hl.continuous.measurable

lemma lipschitz_reverse_measurable {M : Type*} [PseudoMetricSpace M]
    [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    (lo hi : ℝ) (Φ : Set.Icc lo hi → M → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ a b q r, |Φ a q - Φ b r| ≤ L * (|(a : ℝ) - b| + dist q r)) :
    Measurable (Function.uncurry Φ) := by
  let K : NNReal := ⟨2 * L, by positivity⟩
  have hl : LipschitzWith K (Function.uncurry Φ) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Real.dist_eq]
    have hx : |(x.1 : ℝ) - y.1| ≤ dist x y := by
      change dist x.1 y.1 ≤ dist x y
      simp only [Prod.dist_eq]
      exact le_max_left _ _
    have hy : dist x.2 y.2 ≤ dist x y := by
      simp only [Prod.dist_eq]
      exact le_max_right _ _
    exact (hLip x.1 y.1 x.2 y.2).trans
      ((mul_le_mul_of_nonneg_left (add_le_add hx hy) hL).trans_eq (by
        change _ = (2 * L) * dist x y
        ring))
  exact hl.continuous.measurable

lemma eLpNorm_abs {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ) (hf : Measurable f) :
    eLpNorm (fun x => |f x|) 2 μ = eLpNorm f 2 μ := by
  simpa only [Real.norm_eq_abs] using eLpNorm_norm f hf.aestronglyMeasurable

/-- The actual L² Minkowski step, allowing dependent estimators. -/
theorem combined_error_eLpNorm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ}
    (f : Fin m → Ω → ℝ) (hf : ∀ i, Measurable (f i))
    (g b : Ω → ℝ) (hg : Measurable g) (L e : ℝ) (hL : 0 ≤ L) (he : 0 ≤ e)
    (hbound : ∀ x, |g x| ≤ L * ((∑ i, |f i x|) + b x) + e) :
    eLpNorm g 2 μ ≤ ENNReal.ofReal L *
      ((∑ i, eLpNorm (f i) 2 μ) + eLpNorm b 2 μ) + ENNReal.ofReal e := by
  have hm := eLpNorm_mono_ae_real (p := 2) hg.aestronglyMeasurable
    (ae_of_all μ (fun x => by simpa only [Real.norm_eq_abs] using hbound x))
  apply hm.trans
  have hconst : eLpNorm (fun _ : Ω => e) 2 μ = ENNReal.ofReal e := by
    rw [eLpNorm_const' e (by norm_num) (by norm_num)]
    simp [measure_univ, Real.enorm_eq_ofReal_abs, abs_of_nonneg he]
  have hscale : eLpNorm (fun x => L * ((∑ i, |f i x|) + b x)) 2 μ =
      ENNReal.ofReal L * eLpNorm (fun x => (∑ i, |f i x|) + b x) 2 μ := by
    change eLpNorm (L • (fun x => (∑ i, |f i x|) + b x)) 2 μ = _
    rw [eLpNorm_const_smul]
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hL]
  have hsum : eLpNorm (fun x => ∑ i, |f i x|) 2 μ ≤ ∑ i, eLpNorm (f i) 2 μ := by
    have hs := eLpNorm_sum_le (p := 2) (μ := μ)
      (f := fun i : Fin m => fun x => |f i x|) (s := Finset.univ) (by norm_num)
    have heq : (∑ i : Fin m, fun x => |f i x|) = (fun x => ∑ i, |f i x|) := by ext x; simp
    rw [heq] at hs
    simpa only [eLpNorm_abs μ _ (hf _)] using hs
  calc
    _ ≤ eLpNorm (fun x => L * ((∑ i, |f i x|) + b x)) 2 μ +
        eLpNorm (fun _ : Ω => e) 2 μ := eLpNorm_add_le (by norm_num)
    _ = ENNReal.ofReal L * eLpNorm (fun x => (∑ i, |f i x|) + b x) 2 μ + ENNReal.ofReal e := by
      rw [hscale, hconst]
    _ ≤ ENNReal.ofReal L * (eLpNorm (fun x => ∑ i, |f i x|) 2 μ + eLpNorm b 2 μ) +
        ENNReal.ofReal e := by
      gcongr
      exact eLpNorm_add_le (by norm_num)
    _ ≤ _ := by gcongr

/-- Optimization does not require independent estimators: each coordinate may
be selected independently as a function, then evaluated on the same data. -/
theorem combination_minimax {Ω Θ : Type*} [MeasurableSpace Ω] {m : ℕ}
    (laws : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (laws θ)]
    (T0 : Θ → ℝ) (Ti : Fin m → Θ → ℝ) (C : Set Θ)
    (combine : (Fin m → Estimator Ω) → Estimator Ω)
    (momentError : Θ → Ω → ℝ) (L e : ℝ) (β : ℝ≥0∞)
    (hL : 0 ≤ L) (he : 0 ≤ e)
    (hbound : ∀ f θ, θ ∈ C → ∀ x,
      |(combine f).val x - T0 θ| ≤
        L * ((∑ i, |(f i).val x - Ti i θ|) + momentError θ x) + e)
    (hβ : ∀ θ ∈ C, eLpNorm (momentError θ) 2 (laws θ) ≤ β) :
    minimaxRMSE laws T0 C ≤ ENNReal.ofReal L * (∑ i, minimaxRMSE laws (Ti i) C) +
      ENNReal.ofReal L * β + ENNReal.ofReal e := by
  classical
  let R : Fin m → Estimator Ω → ℝ≥0∞ := fun i f =>
    ⨆ θ ∈ C, eLpNorm (fun x => f.val x - Ti i θ) 2 (laws θ)
  have hi : minimaxRMSE laws T0 C ≤
      ⨅ f : Fin m → Estimator Ω, ENNReal.ofReal L * (∑ i, R i (f i)) +
        ENNReal.ofReal L * β + ENNReal.ofReal e := by
    apply le_iInf
    intro f
    rw [minimaxRMSE_eq_eLpNorm]
    apply (iInf_le _ (combine f)).trans
    apply iSup_le
    intro θ
    apply iSup_le
    intro hθ
    have hn := combined_error_eLpNorm (laws θ)
      (fun i x => (f i).val x - Ti i θ) (fun i => (f i).property.sub measurable_const)
      (fun x => (combine f).val x - T0 θ) (momentError θ)
      ((combine f).property.sub measurable_const) L e hL he (hbound f θ hθ)
    apply hn.trans
    rw [mul_add]
    gcongr
    · exact le_iSup_of_le θ (le_iSup_of_le hθ le_rfl)
    · exact hβ θ hθ
  have hopt : (⨅ f : Fin m → Estimator Ω, ENNReal.ofReal L * (∑ i, R i (f i)) +
      ENNReal.ofReal L * β + ENNReal.ofReal e) =
      ENNReal.ofReal L * (∑ i, minimaxRMSE laws (Ti i) C) +
      ENNReal.ofReal L * β + ENNReal.ofReal e := by
    rw [← ENNReal.iInf_add, ← ENNReal.iInf_add, ← ENNReal.mul_iInf]
    · congr 2
      have hdir : ∀ (s : Finset (Fin m)) (f g : Fin m → Estimator Ω),
          ∃ u : Fin m → Estimator Ω, ∀ i ∈ s, R i (u i) ≤ R i (f i) ∧ R i (u i) ≤ R i (g i) := by
        intro s f g
        refine ⟨fun i => if R i (f i) ≤ R i (g i) then f i else g i, ?_⟩
        intro i _
        dsimp only
        split_ifs with h
        · exact ⟨le_rfl, h⟩
        · exact ⟨(le_of_not_ge h), le_rfl⟩
      rw [ENNReal.iInf_sum hdir]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [minimaxRMSE_eq_eLpNorm]
      change (⨅ f : Fin m → Estimator Ω, R i (f i)) = ⨅ f : Estimator Ω, R i f
      apply le_antisymm
      · apply le_iInf
        intro f
        exact iInf_le _ (fun _ => f)
      · apply le_iInf
        intro f
        exact iInf_le _ (f i)
    · intro h
      exact (ENNReal.ofReal_ne_top h).elim
  exact hi.trans_eq hopt

/-- The full measurable Lipschitz-composition reduction, including compact-interval
projection, with any moment estimator of uniformly bounded L² error. -/
theorem lipschitz_combination_minimax {Ω Θ M : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    {m : ℕ} (laws : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (laws θ)]
    (T0 : Θ → ℝ) (Ti : Fin m → Θ → ℝ) (C : Set Θ)
    (lo hi : Fin m → ℝ) (hlohi : ∀ i, lo i ≤ hi i)
    (Φ : ((i : Fin m) → Set.Icc (lo i) (hi i)) → M → ℝ)
    (hΦ : Measurable (Function.uncurry Φ))
    (μhat : Ω → M) (hμhat : Measurable μhat) (μtrue : Θ → M)
    (L e : ℝ) (β : ℝ≥0∞) (hL : 0 ≤ L) (he : 0 ≤ e)
    (hLip : ∀ a b q r, |Φ a q - Φ b r| ≤
      L * ((∑ i, |(a i : ℝ) - b i|) + dist q r))
    (_hmem : ∀ θ ∈ C, ∀ i, Ti i θ ∈ Set.Icc (lo i) (hi i))
    (hrelation : ∀ θ ∈ C,
      |T0 θ - Φ (fun i => Set.projIcc (lo i) (hi i) (hlohi i) (Ti i θ)) (μtrue θ)| ≤ e)
    (hβ : ∀ θ ∈ C, eLpNorm (fun x => dist (μhat x) (μtrue θ)) 2 (laws θ) ≤ β) :
    minimaxRMSE laws T0 C ≤ ENNReal.ofReal L * (∑ i, minimaxRMSE laws (Ti i) C) +
      ENNReal.ofReal L * β + ENNReal.ofReal e := by
  let combine : (Fin m → Estimator Ω) → Estimator Ω := fun f =>
    ⟨fun x => Φ (fun i => Set.projIcc (lo i) (hi i) (hlohi i) ((f i).val x)) (μhat x), by
      have htup : Measurable (fun x => fun i =>
          Set.projIcc (lo i) (hi i) (hlohi i) ((f i).val x)) := by
        apply Measurable.of_eval
        intro i
        have hc : Measurable (Set.projIcc (lo i) (hi i) (hlohi i)) := continuous_projIcc.measurable
        exact hc.comp (f i).property
      exact hΦ.comp (htup.prodMk hμhat)⟩
  apply combination_minimax laws T0 Ti C combine (fun θ x => dist (μhat x) (μtrue θ))
    L e β hL he _ hβ
  intro f θ hθ x
  have htri := abs_sub_le ((combine f).val x)
    (Φ (fun i => Set.projIcc (lo i) (hi i) (hlohi i) (Ti i θ)) (μtrue θ)) (T0 θ)
  have hrel := hrelation θ hθ
  rw [abs_sub_comm (T0 θ)] at hrel
  have hl := hLip
    (fun i => Set.projIcc (lo i) (hi i) (hlohi i) ((f i).val x))
    (fun i => Set.projIcc (lo i) (hi i) (hlohi i) (Ti i θ)) (μhat x) (μtrue θ)
  have hc : (∑ i, |(Set.projIcc (lo i) (hi i) (hlohi i) ((f i).val x) : ℝ) -
      (Set.projIcc (lo i) (hi i) (hlohi i) (Ti i θ) : ℝ)|) ≤
      ∑ i, |(f i).val x - Ti i θ| := by
    apply Finset.sum_le_sum
    intro i _
    have hp := Set.abs_projIcc_sub_projIcc (hlohi i) (c := (f i).val x) (d := Ti i θ)
    exact hp
  exact htri.trans (add_le_add (hl.trans
    (mul_le_mul_of_nonneg_left (add_le_add hc le_rfl) hL)) hrel)

/-- Lemma 19(b)'s reverse RMSE relation, before specializing the moment estimator. -/
theorem lipschitz_reverse_minimax {Ω Θ M : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    (laws : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (laws θ)]
    (T0 T1 : Θ → ℝ) (C : Set Θ)
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (Φ : Set.Icc lo hi → M → ℝ) (hΦ : Measurable (Function.uncurry Φ))
    (μhat : Ω → M) (hμhat : Measurable μhat) (μtrue : Θ → M)
    (L e : ℝ) (β : ℝ≥0∞) (hL : 0 ≤ L) (he : 0 ≤ e)
    (hLip : ∀ a b q r, |Φ a q - Φ b r| ≤ L * (|(a : ℝ) - b| + dist q r))
    (hmem : ∀ θ ∈ C, T0 θ ∈ Set.Icc lo hi)
    (hrelation : ∀ θ ∈ C, |T1 θ - Φ (Set.projIcc lo hi hlohi (T0 θ)) (μtrue θ)| ≤ e)
    (hβ : ∀ θ ∈ C, eLpNorm (fun x => dist (μhat x) (μtrue θ)) 2 (laws θ) ≤ β) :
    minimaxRMSE laws T1 C ≤ ENNReal.ofReal L * minimaxRMSE laws T0 C +
      ENNReal.ofReal L * β + ENNReal.ofReal e := by
  have hΦ' : Measurable (Function.uncurry
      (fun (a : Fin 1 → Set.Icc lo hi) q => Φ (a 0) q)) :=
    by
      have htup : Measurable (fun z : (Fin 1 → Set.Icc lo hi) × M => (z.1 0, z.2)) :=
        ((measurable_pi_apply 0).comp measurable_fst).prodMk measurable_snd
      exact hΦ.comp htup
  have hl : ∀ (a b : Fin 1 → Set.Icc lo hi) q r,
      |Φ (a 0) q - Φ (b 0) r| ≤ L * ((∑ i : Fin 1, |(a i : ℝ) - b i|) + dist q r) := by
    intro a b q r
    simpa using hLip (a 0) (b 0) q r
  have hr := lipschitz_combination_minimax laws T1 (fun _ : Fin 1 => T0) C
    (fun _ => lo) (fun _ => hi) (fun _ => hlohi) (fun a q => Φ (a 0) q) hΦ'
    μhat hμhat μtrue L e β hL he hl (fun θ hθ _ => hmem θ hθ) hrelation hβ
  simpa using hr

/-- Taking square roots of a genuine second-moment bound. -/
lemma eLpNorm_two_le_of_mse {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (b : Ω → ℝ) (hb : Measurable b)
    (hbint : Integrable (fun x => (b x) ^ 2) μ)
    (B n : ℝ) (hB : 0 ≤ B) (hn : 0 < n)
    (hsecond : (∫ x, (b x) ^ 2 ∂μ) ≤ B ^ 2 / n) :
    eLpNorm b 2 μ ≤ ENNReal.ofReal (B / Real.sqrt n) := by
  rw [eLpNorm_two_eq_squaredIntegral μ b hb,
    ← ofReal_integral_eq_lintegral_ofReal hbint (ae_of_all μ (fun x => sq_nonneg (b x)))]
  have hsq : ENNReal.ofReal (B ^ 2 / n) = (ENNReal.ofReal (B / Real.sqrt n)) ^ (2 : ℝ) := by
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (by positivity : 0 ≤ B / Real.sqrt n) 2]
    congr 1
    have hs : (Real.sqrt n) ^ 2 = n := Real.sq_sqrt hn.le
    have hsne : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn).ne'
    field_simp
    nlinarith
  have hm := ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hsecond) (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [hsq, ← ENNReal.rpow_mul] at hm
  norm_num only [mul_one_div_cancel, ENNReal.rpow_one] at hm
  exact hm

end RoughRegime.Applications
