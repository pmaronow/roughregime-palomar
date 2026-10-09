module

public import RoughRegime.Applications


@[expose] public section
/-! Actual vector empirical means and rectangle projection used in Lemma 19. -/
noncomputable section
open scoped BigOperators ENNReal Topology
open MeasureTheory
namespace RoughRegime.Applications

/-- A vector of finitely many bounded observable coordinates. -/
def responseVector {Ω : Type*} {k : ℕ} (h : Fin k → Ω → ℝ) (x : Ω) :
    EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun j => h j x)

/-- Coordinatewise expectation, with the Euclidean metric. -/
def momentMean {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) (h : Fin k → Ω → ℝ) : EuclideanSpace ℝ (Fin k) :=
  WithLp.toLp 2 (fun j => ∫ x, h j x ∂μ)

/-- Coordinatewise expectation agrees with the actual Bochner expectation. -/
lemma momentMean_eq_integral {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (h : Fin k → Ω → ℝ)
    (hh : ∀ j, MemLp (h j) 2 μ) :
    momentMean μ h = ∫ x, responseVector h x ∂μ := by
  ext j
  rw [eval_integral_piLp (f := responseVector h) (fun i => (hh i).integrable (by norm_num)) j]
  rfl

/-- Coordinatewise clipping of the empirical mean onto a compact rectangle. -/
def projectedMomentMean {Ω : Type*} {k n : ℕ} (h : Fin k → Ω → ℝ)
    (lo hi : Fin k → ℝ) (hlohi : ∀ j, lo j ≤ hi j) (x : Fin n → Ω) :
    EuclideanSpace ℝ (Fin k) := WithLp.toLp 2
      (fun j => (Set.projIcc (lo j) (hi j) (hlohi j) (empiricalMean (h j) x) : ℝ))

lemma projectedMean_memLp {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {n : ℕ} (h : Ω → ℝ) (hmh : Measurable h)
    (lo hi : ℝ) (hlohi : lo ≤ hi) :
    MemLp (fun x : Fin n → Ω =>
      (Set.projIcc lo hi hlohi (empiricalMean h x) : ℝ)) 2
      (Measure.pi (fun _ : Fin n => μ)) := by
  have he : Measurable (empiricalMean (n := n) h) := by unfold empiricalMean; fun_prop
  have hc : Measurable (fun t : ℝ => (Set.projIcc lo hi hlohi t : ℝ)) :=
    (continuous_subtype_val.comp continuous_projIcc).measurable
  exact memLp_of_bounded (ae_of_all _ (fun x => (Set.projIcc lo hi hlohi (empiricalMean h x)).property))
    (hc.comp he).aestronglyMeasurable 2

lemma projectedMomentMean_measurable {Ω : Type*} [MeasurableSpace Ω] {k n : ℕ}
    (h : Fin k → Ω → ℝ) (hmh : ∀ j, Measurable (h j))
    (lo hi : Fin k → ℝ) (hlohi : ∀ j, lo j ≤ hi j) :
    Measurable (projectedMomentMean (n := n) h lo hi hlohi) := by
  unfold projectedMomentMean
  apply (WithLp.measurable_toLp 2 _).comp
  apply Measurable.of_eval
  intro j
  have he : Measurable (empiricalMean (n := n) (h j)) := by unfold empiricalMean; fun_prop
  have hc : Measurable (fun t : ℝ => (Set.projIcc (lo j) (hi j) (hlohi j) t : ℝ)) :=
    (continuous_subtype_val.comp continuous_projIcc).measurable
  exact hc.comp he

/-- Full vector pilot MSE bound: covariance between coordinates is harmless because
Euclidean squared error is the sum of the coordinate squared errors. -/
theorem projectedMomentMean_mse {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {k n : ℕ} (hn : n ≠ 0)
    (h : Fin k → Ω → ℝ) (hh : ∀ j, MemLp (h j) 2 μ) (hmh : ∀ j, Measurable (h j))
    (lo hi : Fin k → ℝ) (hlohi : ∀ j, lo j ≤ hi j)
    (hm : ∀ j, (∫ x, h j x ∂μ) ∈ Set.Icc (lo j) (hi j)) :
    (∫ x, ‖projectedMomentMean h lo hi hlohi x - momentMean μ h‖ ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) ≤
    (∫ x, ‖responseVector h x - momentMean μ h‖ ^ 2 ∂μ) / n := by
  have hL : (fun x : Fin n → Ω => ‖projectedMomentMean h lo hi hlohi x - momentMean μ h‖ ^ 2) =
      (fun x => ∑ j : Fin k,
        ((Set.projIcc (lo j) (hi j) (hlohi j) (empiricalMean (h j) x) : ℝ) - ∫ y, h j y ∂μ) ^ 2) := by
    funext x
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  have hR : (fun x : Ω => ‖responseVector h x - momentMean μ h‖ ^ 2) =
      (fun x => ∑ j : Fin k, (h j x - ∫ y, h j y ∂μ) ^ 2) := by
    funext x
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [hL, hR]
  have hiL := integral_finsetSum Finset.univ (fun (j : Fin k) _ =>
    ((projectedMean_memLp μ (n := n) (h j) (hmh j) (lo j) (hi j) (hlohi j)).sub
      (memLp_const (∫ y, h j y ∂μ))).integrable_sq)
  change (∫ x, ∑ j : Fin k,
    ((Set.projIcc (lo j) (hi j) (hlohi j) (empiricalMean (h j) x) : ℝ) - ∫ y, h j y ∂μ) ^ 2
      ∂Measure.pi (fun _ : Fin n => μ)) = _ at hiL
  have hiR := integral_finsetSum Finset.univ (fun (j : Fin k) _ =>
    ((hh j).sub (memLp_const (∫ y, h j y ∂μ))).integrable_sq)
  change (∫ x, ∑ j : Fin k, (h j x - ∫ y, h j y ∂μ) ^ 2 ∂μ) = _ at hiR
  rw [hiL, hiR, Finset.sum_div]
  apply Finset.sum_le_sum
  intro j _
  exact projected_empiricalMean_mse μ hn (h j) (hh j) (lo j) (hi j) (hlohi j) (hm j) (hmh j)

end RoughRegime.Applications

namespace RoughRegime.Applications

/-- The compact rectangle equipped with its Euclidean subspace metric. -/
def momentRectangle {k : ℕ} (lo hi : Fin k → ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {z | ∀ j, z j ∈ Set.Icc (lo j) (hi j)}

lemma projectedMomentMean_error_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {k n : ℕ}
    (h : Fin k → Ω → ℝ) (hmh : ∀ j, Measurable (h j))
    (lo hi : Fin k → ℝ) (hlohi : ∀ j, lo j ≤ hi j) (z : EuclideanSpace ℝ (Fin k)) :
    Integrable (fun x : Fin n → Ω => ‖projectedMomentMean h lo hi hlohi x - z‖ ^ 2)
      (Measure.pi (fun _ : Fin n => μ)) := by
  have heq : (fun x : Fin n → Ω => ‖projectedMomentMean h lo hi hlohi x - z‖ ^ 2) =
      fun x => ∑ j : Fin k,
        ((Set.projIcc (lo j) (hi j) (hlohi j) (empiricalMean (h j) x) : ℝ) - z j) ^ 2 := by
    funext x
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  rw [heq]
  exact integrable_finsetSum Finset.univ (fun j _ =>
    ((projectedMean_memLp μ (n := n) (h j) (hmh j) (lo j) (hi j) (hlohi j)).sub
      (memLp_const (z j))).integrable_sq)

/-- Lemma 19(b)'s minimax probability inequality on the actual independent sample,
using the actual projected empirical vector mean instead of an assumed pilot. -/
theorem reverse_transfer_iid {Ω Θ : Type*} [MeasurableSpace Ω]
    {k n : ℕ} (hn : n ≠ 0) (laws : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (laws θ)]
    (T0 T1 : Θ → ℝ) (C : Set Θ)
    (h : Fin k → Ω → ℝ) (hmh : ∀ j, Measurable (h j))
    (hh : ∀ θ j, MemLp (h j) 2 (laws θ))
    (mlo mhi : Fin k → ℝ) (hmlohi : ∀ j, mlo j ≤ mhi j)
    (hm : ∀ θ j, (∫ x, h j x ∂laws θ) ∈ Set.Icc (mlo j) (mhi j))
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (Φ : Set.Icc lo hi → momentRectangle mlo mhi → ℝ)
    (hΦ : Measurable (Function.uncurry Φ))
    (L t e B : ℝ) (hL : 0 < L) (ht : 0 < t) (he : e ≤ t / 2)
    (hLip : ∀ a b q r, |Φ a q - Φ b r| ≤ L * (|(a : ℝ) - b| + dist q r))
    (hmem : ∀ θ ∈ C, T0 θ ∈ Set.Icc lo hi)
    (hrelation : ∀ θ ∈ C, |T1 θ - Φ (Set.projIcc lo hi hlohi (T0 θ))
      ⟨momentMean (laws θ) h, hm θ⟩| ≤ e)
    (hvariance : ∀ θ ∈ C,
      (∫ x, ‖responseVector h x - momentMean (laws θ) h‖ ^ 2 ∂laws θ) ≤ B ^ 2) :
    minimaxTail (fun θ => Measure.pi (fun _ : Fin n => laws θ)) T1 C t ≤
      minimaxTail (fun θ => Measure.pi (fun _ : Fin n => laws θ)) T0 C (t / (4 * L)) +
      ENNReal.ofReal (16 * L ^ 2 * B ^ 2 / ((n : ℝ) * t ^ 2)) := by
  let μhat : (Fin n → Ω) → momentRectangle mlo mhi := fun x =>
    ⟨projectedMomentMean h mlo mhi hmlohi x,
      fun j => (Set.projIcc (mlo j) (mhi j) (hmlohi j) (empiricalMean (h j) x)).property⟩
  have hμhat : Measurable μhat :=
    (projectedMomentMean_measurable h hmh mlo mhi hmlohi).subtype_mk
  let μtrue : Θ → momentRectangle mlo mhi := fun θ => ⟨momentMean (laws θ) h, hm θ⟩
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  apply reverse_transfer_minimax
    (fun θ => Measure.pi (fun _ : Fin n => laws θ)) T0 T1 C lo hi hlohi Φ hΦ
    μhat hμhat μtrue L t e B n hL ht hnreal he hLip hmem hrelation
  · intro θ _
    change Integrable (fun x => ‖projectedMomentMean h mlo mhi hmlohi x - momentMean (laws θ) h‖ ^ 2)
      (Measure.pi (fun _ : Fin n => laws θ))
    exact projectedMomentMean_error_integrable (laws θ) h hmh mlo mhi hmlohi _
  · intro θ hθ
    change (∫ x, ‖projectedMomentMean h mlo mhi hmlohi x - momentMean (laws θ) h‖ ^ 2
      ∂Measure.pi (fun _ : Fin n => laws θ)) ≤ B ^ 2 / n
    exact (projectedMomentMean_mse (laws θ) hn h (hh θ) hmh mlo mhi hmlohi (hm θ)).trans
      (div_le_div_of_nonneg_right (hvariance θ hθ) hnreal.le)


/-- The same probability transfer with arbitrary independent estimator randomness. -/
theorem reverse_transfer_iid_randomized {Ω Θ S : Type*} [MeasurableSpace Ω]
    [MeasurableSpace S] (seedLaw : Measure S) [IsProbabilityMeasure seedLaw]
    {k n : ℕ} (hn : n ≠ 0) (laws : Θ → Measure Ω) [∀ θ, IsProbabilityMeasure (laws θ)]
    (T0 T1 : Θ → ℝ) (C : Set Θ)
    (h : Fin k → Ω → ℝ) (hmh : ∀ j, Measurable (h j))
    (hh : ∀ θ j, MemLp (h j) 2 (laws θ))
    (mlo mhi : Fin k → ℝ) (hmlohi : ∀ j, mlo j ≤ mhi j)
    (hm : ∀ θ j, (∫ x, h j x ∂laws θ) ∈ Set.Icc (mlo j) (mhi j))
    (lo hi : ℝ) (hlohi : lo ≤ hi)
    (Φ : Set.Icc lo hi → momentRectangle mlo mhi → ℝ)
    (hΦ : Measurable (Function.uncurry Φ))
    (L t e B : ℝ) (hL : 0 < L) (ht : 0 < t) (he : e ≤ t / 2)
    (hLip : ∀ a b q r, |Φ a q - Φ b r| ≤ L * (|(a : ℝ) - b| + dist q r))
    (hmem : ∀ θ ∈ C, T0 θ ∈ Set.Icc lo hi)
    (hrelation : ∀ θ ∈ C, |T1 θ - Φ (Set.projIcc lo hi hlohi (T0 θ))
      ⟨momentMean (laws θ) h, hm θ⟩| ≤ e)
    (hvariance : ∀ θ ∈ C,
      (∫ x, ‖responseVector h x - momentMean (laws θ) h‖ ^ 2 ∂laws θ) ≤ B ^ 2) :
    minimaxTail (fun θ => (Measure.pi (fun _ : Fin n => laws θ)).prod seedLaw) T1 C t ≤
      minimaxTail (fun θ => (Measure.pi (fun _ : Fin n => laws θ)).prod seedLaw) T0 C (t / (4 * L)) +
      ENNReal.ofReal (16 * L ^ 2 * B ^ 2 / ((n : ℝ) * t ^ 2)) := by
  let μhat : ((Fin n → Ω) × S) → momentRectangle mlo mhi := fun x =>
    ⟨projectedMomentMean h mlo mhi hmlohi x.1,
      fun j => (Set.projIcc (mlo j) (mhi j) (hmlohi j) (empiricalMean (h j) x.1)).property⟩
  have hμhat : Measurable μhat :=
    ((projectedMomentMean_measurable h hmh mlo mhi hmlohi).comp measurable_fst).subtype_mk
  let μtrue : Θ → momentRectangle mlo mhi := fun θ => ⟨momentMean (laws θ) h, hm θ⟩
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  apply reverse_transfer_minimax
    (fun θ => (Measure.pi (fun _ : Fin n => laws θ)).prod seedLaw) T0 T1 C lo hi hlohi Φ hΦ
    μhat hμhat μtrue L t e B n hL ht hnreal he hLip hmem hrelation
  · intro θ _
    dsimp only [μhat, μtrue]
    simp only [Subtype.dist_eq, dist_eq_norm]
    exact (projectedMomentMean_error_integrable (laws θ) h hmh mlo mhi hmlohi _).comp_fst seedLaw
  · intro θ hθ
    dsimp only [μhat, μtrue]
    simp only [Subtype.dist_eq, dist_eq_norm]
    rw [integral_prod _ ((projectedMomentMean_error_integrable
      (laws θ) h hmh mlo mhi hmlohi _).comp_fst seedLaw)]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul]
    exact (projectedMomentMean_mse (laws θ) hn h (hh θ) hmh mlo mhi hmlohi (hm θ)).trans
      (div_le_div_of_nonneg_right (hvariance θ hθ) hnreal.le)

end RoughRegime.Applications

namespace RoughRegime.Applications
open Filter

/-- A vanishing additive probability error preserves the hardness liminf. -/
theorem hardness_transfer_vanishing_error (p0 p1 η : ℕ → ℝ≥0∞) (H : ℝ≥0∞)
    (hH : H ≤ Filter.liminf p1 atTop)
    (hineq : ∀ᶠ n in atTop, p1 n ≤ p0 n + η n)
    (hη : Tendsto η atTop (nhds 0)) : H ≤ Filter.liminf p0 atTop := by
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  have hε' : (0 : ℝ≥0∞) < ε := ENNReal.coe_pos.mpr hε
  have hsmall : ∀ᶠ n in atTop, η n < ε := hη.eventually (Iio_mem_nhds hε')
  have hb : ∀ᶠ n in atTop, p1 n ≤ p0 n + ε := by
    filter_upwards [hineq, hsmall] with n hn hs
    exact hn.trans (add_le_add le_rfl hs.le)
  have hm := Filter.liminf_le_liminf hb
  rw [liminf_add_const atTop p0 ε (by isBoundedDefault) (by isBoundedDefault)] at hm
  exact hH.trans hm

end RoughRegime.Applications
