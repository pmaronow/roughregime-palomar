module

public import RoughRegime.DesignGram
public import RoughRegime.DesignMoments


@[expose] public section
/-! Genuine weighted L² cell representatives and their Gram/projection geometry. -/
noncomputable section
namespace RoughRegime.Model
open MeasureTheory Matrix
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

variable {X n a : Type*} [MeasurableSpace X] [Fintype n] [DecidableEq n]
  [Fintype a] [DecidableEq a]

 def weightedDesignMeasure (μ : Measure X) (g : X → ℝ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (g x))

 theorem weightedDesignMeasure_mass_le (μ : Measure X) [IsProbabilityMeasure μ]
    (g : X → ℝ) (hi : ℝ) (hg : ∀ᵐ x ∂μ, g x ≤ hi) :
    weightedDesignMeasure μ g Set.univ ≤ ENNReal.ofReal hi := by
  rw [weightedDesignMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hh := lintegral_mono_ae (hg.mono (fun x hx => ENNReal.ofReal_le_ofReal hx))
  simpa using hh

 theorem weightedDesignMeasure_finite (μ : Measure X) [IsProbabilityMeasure μ]
    (g : X → ℝ) (hi : ℝ) (hg : ∀ᵐ x ∂μ, g x ≤ hi) :
    IsFiniteMeasure (weightedDesignMeasure μ g) :=
  ⟨(weightedDesignMeasure_mass_le μ g hi hg).trans_lt ENNReal.ofReal_lt_top⟩

 theorem weightedDesignMeasure_ac (μ : Measure X) (g : X → ℝ) :
    weightedDesignMeasure μ g ≪ μ := withDensity_absolutelyContinuous μ _

 theorem weightedDesignMeasure_integral (μ : Measure X) (g : X → ℝ) (hg : Measurable g)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x) (f : X → ℝ) :
    (∫ x, f x ∂weightedDesignMeasure μ g) = ∫ x, g x * f x ∂μ := by
  change (∫ x, f x ∂μ.withDensity (fun x => ENNReal.ofReal (g x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun x => ENNReal.ofReal (g x)) from ENNReal.measurable_ofReal.comp hg)
    (Filter.Eventually.of_forall (fun x => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  filter_upwards [hg0] with x hx
  simp [ENNReal.toReal_ofReal hx]

 def designLp (ν : Measure X) [IsFiniteMeasure ν] (f : X → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ x, |f x| ≤ B) : Lp ℝ 2 ν :=
  (MemLp.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs] using hb x))).toLp f

 theorem designLp_ae (ν : Measure X) [IsFiniteMeasure ν] (f : X → ℝ) (hf : Measurable f)
    (B : ℝ) (hb : ∀ x, |f x| ≤ B) : designLp ν f hf B hb =ᵐ[ν] f := MemLp.coeFn_toLp _

 theorem designLp_inner (ν : Measure X) [IsFiniteMeasure ν]
    (f t : X → ℝ) (hf : Measurable f) (ht : Measurable t)
    (B C : ℝ) (hb : ∀ x, |f x| ≤ B) (hc : ∀ x, |t x| ≤ C) :
    inner ℝ (designLp ν f hf B hb) (designLp ν t ht C hc) = ∫ x, f x * t x ∂ν := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [designLp_ae ν f hf B hb, designLp_ae ν t ht C hc] with x hfx htx
  simp [hfx, htx, mul_comm]

 theorem weighted_designLp_gram (μ : Measure X) [IsProbabilityMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (hi : ℝ) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hghi : ∀ᵐ x ∂μ, g x ≤ hi)
    (z : n → X → ℝ) (hz : ∀ i, Measurable (z i)) (B : ℝ) (hb : ∀ i x, |z i x| ≤ B) :
    letI := weightedDesignMeasure_finite μ g hi hghi
    Matrix.gram ℝ (fun i => designLp (weightedDesignMeasure μ g) (z i) (hz i) B (hb i)) = designGram μ g z := by
  letI := weightedDesignMeasure_finite μ g hi hghi
  ext i j
  rw [Matrix.gram_apply, designLp_inner, weightedDesignMeasure_integral μ g hg hg0]
  simp only [designGram, mul_assoc]

 theorem weighted_designLp_moments (μ : Measure X) [IsProbabilityMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (hi : ℝ) (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hghi : ∀ᵐ x ∂μ, g x ≤ hi)
    (z : n → X → ℝ) (hz : ∀ i, Measurable (z i)) (B : ℝ) (hb : ∀ i x, |z i x| ≤ B)
    (f : X → ℝ) (hf : Measurable f) (C : ℝ) (hc : ∀ x, |f x| ≤ C) :
    letI := weightedDesignMeasure_finite μ g hi hghi
    RoughRegime.HilbertGram.moments (fun i => designLp (weightedDesignMeasure μ g) (z i) (hz i) B (hb i))
      (designLp (weightedDesignMeasure μ g) f hf C hc) =
      fun i => ∫ x, g x * (z i x * f x) ∂μ := by
  letI := weightedDesignMeasure_finite μ g hi hghi
  funext i
  rw [RoughRegime.HilbertGram.moments, designLp_inner, weightedDesignMeasure_integral μ g hg hg0]

 theorem weighted_designLp_linearIndependent (μ : Measure X) [IsProbabilityMeasure μ]
    (g : X → ℝ) (hg : Measurable g) (lo hi : ℝ) (hlo : 0 < lo)
    (hgb : ∀ᵐ x ∂μ, lo ≤ g x ∧ g x ≤ hi)
    (z : n → X → ℝ) (hz : ∀ i, Measurable (z i)) (B : ℝ) (hB : 0 ≤ B) (hb : ∀ i x, |z i x| ≤ B)
    (horth : ∀ i j, (∫ x, z i x * z j x ∂μ) = if i = j then 1 else 0) :
    letI := weightedDesignMeasure_finite μ g hi (hgb.mono (fun _ hx => hx.2))
    LinearIndependent ℝ (fun i => designLp (weightedDesignMeasure μ g) (z i) (hz i) B (hb i)) := by
  letI := weightedDesignMeasure_finite μ g hi (hgb.mono (fun _ hx => hx.2))
  apply Matrix.linearIndependent_of_posDef_gram
  rw [weighted_designLp_gram μ g hg hi (hgb.mono (fun _ hx => hlo.le.trans hx.1))
    (hgb.mono (fun _ hx => hx.2)) z hz B hb]
  exact designGram_posDef μ g hg lo hi hlo hgb z hz B hB hb horth

/-- Every genuinely essentially bounded cell function belongs to weighted L². -/
 theorem weighted_memLp_of_ae_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (g : X → ℝ) (hi : ℝ) (hghi : ∀ᵐ x ∂μ, g x ≤ hi)
    (f : X → ℝ) (hf : AEStronglyMeasurable f μ) (B : ℝ)
    (hb : ∀ᵐ x ∂μ, |f x| ≤ B) :
    letI := weightedDesignMeasure_finite μ g hi hghi
    MemLp f 2 (weightedDesignMeasure μ g) := by
  letI := weightedDesignMeasure_finite μ g hi hghi
  apply MemLp.of_bound (hf.mono_ac (weightedDesignMeasure_ac μ g)) B
  exact (weightedDesignMeasure_ac μ g).ae_le (hb.mono (fun x hx => by
    simpa only [Real.norm_eq_abs] using hx))

/-- The weighted L² norm retains the square-root upper-density constant. -/
 theorem weightedLp_norm_le_of_ae_bound (μ : Measure X) [IsProbabilityMeasure μ]
    (g : X → ℝ) (hi : ℝ) (hhi : 0 ≤ hi) (hghi : ∀ᵐ x ∂μ, g x ≤ hi)
    (E : ℝ) (hE : 0 ≤ E) :
    letI := weightedDesignMeasure_finite μ g hi hghi
    ∀ (f : Lp ℝ 2 (weightedDesignMeasure μ g)),
      (∀ᵐ x ∂weightedDesignMeasure μ g, |f x| ≤ E) → ‖f‖ ≤ Real.sqrt hi * E := by
  letI := weightedDesignMeasure_finite μ g hi hghi
  intro f hf
  have hn := Lp.norm_le_of_ae_bound (f := f) hE (hf.mono (fun x hx => by
    simpa only [Real.norm_eq_abs] using hx))
  have hm : (measureUnivNNReal (weightedDesignMeasure μ g) : ℝ) ≤ hi := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (weightedDesignMeasure_mass_le μ g hi hghi)
    simpa only [ENNReal.toReal_ofReal hhi, measureUnivNNReal, ENNReal.coe_toNNReal_eq_toReal] using h
  have hroot : (measureUnivNNReal (weightedDesignMeasure μ g) : ℝ) ^ (2 : ℝ)⁻¹ ≤ Real.sqrt hi := by
    rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hm
  exact hn.trans (mul_le_mul_of_nonneg_right (by simpa using hroot) hE)

/-- An actual pointwise cell approximation yields its weighted L² approximation,
with no assumed weighted residual estimate. -/
 theorem weightedLp_approximation (μ : Measure X) [IsProbabilityMeasure μ]
    (g : X → ℝ) (hi : ℝ) (hhi : 0 ≤ hi) (hghi : ∀ᵐ x ∂μ, g x ≤ hi)
    (f t : X → ℝ) (E : ℝ) (hE : 0 ≤ E) (he : ∀ᵐ x ∂μ, |f x - t x| ≤ E) :
    letI := weightedDesignMeasure_finite μ g hi hghi
    ∀ (hf : MemLp f 2 (weightedDesignMeasure μ g)) (ht : MemLp t 2 (weightedDesignMeasure μ g)),
      ‖hf.toLp f - ht.toLp t‖ ≤ Real.sqrt hi * E := by
  letI := weightedDesignMeasure_finite μ g hi hghi
  intro hf ht
  apply weightedLp_norm_le_of_ae_bound μ g hi hhi hghi E hE
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (ht.toLp t), hf.coeFn_toLp, ht.coeFn_toLp,
    (weightedDesignMeasure_ac μ g).ae_le he] with x hs hfx htx hx
  simpa only [hs, Pi.sub_apply, hfx, htx] using hx

/-- The coefficient expansion has its literal almost-everywhere representative. -/
 theorem parentBasis_representative (μ : Measure X) (z : n → Lp ℝ 2 μ)
    (zr : n → X → ℝ) (hz : ∀ i, z i =ᵐ[μ] zr i) (L : Matrix n a ℝ) (j : a) :
    RoughRegime.HilbertGram.parentBasis z L j =ᵐ[μ] fun x => ∑ i, L i j * zr i x := by
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun i => L i j • z i)
  have ht : ∀ᵐ x ∂μ, ∀ i, (L i j • z i) x = L i j * zr i x := by
    rw [Filter.eventually_all]
    intro i
    filter_upwards [Lp.coeFn_smul (L i j) (z i), hz i] with x hx hzx
    simpa only [hx, Pi.smul_apply, smul_eq_mul, hzx]
  exact hs.trans (ht.mono (fun x hx => Finset.sum_congr rfl (fun i _ => hx i)))

/-- A true parent expansion in unweighted L² transfers to the weighted L² space
through absolute continuity. The inclusion matrix remains fixed. -/
 theorem transfer_parentBasis (μ ν : Measure X) (hac : ν ≪ μ)
    (zμ : n → Lp ℝ 2 μ) (pμ : a → Lp ℝ 2 μ)
    (zν : n → Lp ℝ 2 ν) (pν : a → Lp ℝ 2 ν)
    (zr : n → X → ℝ) (pr : a → X → ℝ)
    (hzμ : ∀ i, zμ i =ᵐ[μ] zr i) (hpμ : ∀ j, pμ j =ᵐ[μ] pr j)
    (hzν : ∀ i, zν i =ᵐ[ν] zr i) (hpν : ∀ j, pν j =ᵐ[ν] pr j)
    (L : Matrix n a ℝ) (he : RoughRegime.HilbertGram.parentBasis zμ L = pμ) :
    RoughRegime.HilbertGram.parentBasis zν L = pν := by
  funext j
  apply Lp.ext
  have hraw : (fun x => ∑ i, L i j * zr i x) =ᵐ[μ] pr j := by
    have h := parentBasis_representative μ zμ zr hzμ L j
    rw [he] at h
    exact h.symm.trans (hpμ j)
  exact (parentBasis_representative ν zν zr hzν L j).trans
    ((hac.ae_eq hraw).trans (hpν j).symm)

/-- True membership of a polynomial in the parent space transfers with the
representatives; it is not a new membership assumption in the weighted space. -/
 theorem transfer_parentSpan (μ ν : Measure X) (hac : ν ≪ μ)
    (pμ : a → Lp ℝ 2 μ) (pν : a → Lp ℝ 2 ν) (pr : a → X → ℝ)
    (hpμ : ∀ j, pμ j =ᵐ[μ] pr j) (hpν : ∀ j, pν j =ᵐ[ν] pr j)
    (fμ : Lp ℝ 2 μ) (fν : Lp ℝ 2 ν) (f : X → ℝ)
    (hfμ : fμ =ᵐ[μ] f) (hfν : fν =ᵐ[ν] f)
    (hm : fμ ∈ RoughRegime.HilbertGram.basisSpan pμ) :
    fν ∈ RoughRegime.HilbertGram.basisSpan pν := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hm
  apply (Submodule.mem_span_range_iff_exists_fun ℝ).mpr
  refine ⟨c, ?_⟩
  apply Lp.ext
  have hμ := parentBasis_representative μ pμ pr hpμ (fun i (_ : Unit) => c i) ()
  change (∑ i, c i • pμ i) =ᵐ[μ] (fun x => ∑ i, c i * pr i x) at hμ
  rw [hc] at hμ
  have hν := parentBasis_representative ν pν pr hpν (fun i (_ : Unit) => c i) ()
  change (∑ i, c i • pν i) =ᵐ[ν] (fun x => ∑ i, c i * pr i x) at hν
  exact hν.trans ((hac.ae_eq (hμ.symm.trans hfμ)).trans hfν.symm)

/-- Genuine orthonormal L² basis representatives have the required Lebesgue
orthogonality integrals. -/
 theorem orthogonality_integrals_of_orthonormal (μ : Measure X) (z : n → Lp ℝ 2 μ)
    (zr : n → X → ℝ) (hz : ∀ i, z i =ᵐ[μ] zr i) (ho : Orthonormal ℝ z) :
    ∀ i j, (∫ x, zr i x * zr j x ∂μ) = if i = j then 1 else 0 := by
  intro i j
  have he := orthonormal_iff_ite.mp ho i j
  rw [L2.inner_def] at he
  have hr : (∫ x, inner ℝ (z i x) (z j x) ∂μ) = ∫ x, zr i x * zr j x ∂μ := by
    apply integral_congr_ae
    filter_upwards [hz i, hz j] with x hi hj
    simp [hi, hj, mul_comm]
  exact hr.symm.trans he

end RoughRegime.Model
