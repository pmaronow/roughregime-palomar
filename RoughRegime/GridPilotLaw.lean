module

public import RoughRegime.SmoothGridPilot
public import RoughRegime.Model


@[expose] public section
/-! Actual random-design laws for the smooth fixed-grid pilot. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ContDiff Topology ENNReal
namespace RoughRegime.Applications

theorem gridCell_volume (d k : ℕ) (hk : 0 < k) (j : Fin d → Fin k) :
    volume (gridCell d k j) = ENNReal.ofReal ((1 / (k : ℝ)) ^ d) := by
  have hbox : gridCell d k j = WithLp.ofLp ⁻¹'
      Icc (fun i : Fin d => (j i : ℝ) / k)
        (fun i : Fin d => ((j i : ℝ) + 1) / k) := by
    ext x
    simp only [gridCell, mem_ofPred_eq, mem_preimage, mem_Icc, Pi.le_def]
    exact forall_and
  rw [hbox, (PiLp.volume_preserving_ofLp (Fin d)).measure_preimage
    measurableSet_Icc.nullMeasurableSet, Real.volume_Icc_pi]
  have hdiff : ∀ i : Fin d, ((j i : ℝ) + 1) / k - (j i : ℝ) / k = 1 / k := by
    intro i
    ring
  simp only [hdiff, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by positivity)]

theorem gridCell_cubeVolume (d k : ℕ) (hk : 0 < k) (j : Fin d → Fin k) :
    Model.cubeVolume d (gridCell d k j) = ENNReal.ofReal ((1 / (k : ℝ)) ^ d) := by
  rw [Model.cubeVolume, Measure.restrict_apply (gridCell_measurable d k j)]
  have hs : gridCell d k j ⊆ Model.cube d := fun y hy => gridCell_subset_cube d k hk j y hy
  rw [inter_eq_left.mpr hs]
  exact gridCell_volume d k hk j

/-- A lower design density gives the source's actual positive cell probability. -/
theorem gridCell_probability_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d k : ℕ) (hk : 0 < k)
    (X : Ω → Model.Covariate d) (hX : Measurable X) (p : Model.Covariate d → ℝ)
    (hmarginal : μ.map X = (Model.cubeVolume d).withDensity (fun x => ENNReal.ofReal (p x)))
    (pmin : ℝ) (hpmin : 0 < pmin) (hp : ∀ᵐ x ∂Model.cubeVolume d, pmin ≤ p x)
    (j : Fin d → Fin k) :
    pmin * (1 / (k : ℝ)) ^ d ≤ μ.real (X ⁻¹' gridCell d k j) := by
  have hle : (Model.cubeVolume d).withDensity (fun _ => ENNReal.ofReal pmin) ≤
      (Model.cubeVolume d).withDensity (fun x => ENNReal.ofReal (p x)) :=
    withDensity_mono (hp.mono (fun x hx => ENNReal.ofReal_le_ofReal hx))
  have hc := hle (gridCell d k j)
  rw [withDensity_const, Measure.smul_apply, gridCell_cubeVolume d k hk j,
    ← hmarginal, Measure.map_apply hX (gridCell_measurable d k j)] at hc
  have hr := ENNReal.toReal_mono (measure_ne_top μ _) hc
  simpa only [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hpmin.le,
    ENNReal.toReal_ofReal (show 0 ≤ (1 / (k : ℝ)) ^ d by positivity), measureReal_def] using hr

/-- The grid resolution can be chosen uniformly from a positive Hölder exponent. -/
theorem exists_fine_grid (d : ℕ) (C γ ζ : ℝ) (hγ : 0 < γ) (hζ : 0 < ζ) :
    ∃ k : ℕ, 0 < k ∧ C * (2 * Real.sqrt d / (k : ℝ)) ^ γ ≤ ζ / 4 := by
  have hi : Tendsto (fun k : ℕ => (k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun k : ℕ => 2 * Real.sqrt d / (k : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul (2 * Real.sqrt d)
  have hp := (Real.continuousAt_rpow_const 0 γ (Or.inr hγ.le)).tendsto.comp hd
  have hc : Tendsto (fun k : ℕ => C * (2 * Real.sqrt d / (k : ℝ)) ^ γ) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow hγ.ne', mul_zero, Function.comp_def] using hp.const_mul C
  have he := hc.eventually (eventually_lt_nhds (by linarith : (0 : ℝ) < ζ / 4))
  obtain ⟨k, hk, hf⟩ := ((eventually_ge_atTop 1).and he).exists
  exact ⟨k, hk, hf.le⟩

/-- The resolution and the exponential constant depend only on the fixed
regularity, density and accuracy parameters. -/
theorem fixed_accuracy_grid_constants (d : ℕ) (C γ ζ pmin : ℝ)
    (hγ : 0 < γ) (hζ : 0 < ζ) (hpmin : 0 < pmin) :
    ∃ (k : ℕ) (c : ℝ), 0 < k ∧ 0 < c ∧
      C * (2 * Real.sqrt d / (k : ℝ)) ^ γ ≤ ζ / 4 ∧
      ∀ n : ℕ, (3 * k ^ d : ℝ) * Real.exp
        (-(n : ℝ) * (pmin * (1 / (k : ℝ)) ^ d) ^ 2 * ζ ^ 2 / 32) ≤
        c⁻¹ * Real.exp (-c * n) := by
  obtain ⟨k, hk, hfine⟩ := exists_fine_grid d C γ ζ hγ hζ
  let a : ℝ := (pmin * (1 / (k : ℝ)) ^ d) ^ 2 * ζ ^ 2 / 32
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨c, hc, hb⟩ := exponential_bound_shared_constant (3 * k ^ d) a (by positivity) ha
  refine ⟨k, c, hk, hc, hfine, fun n => ?_⟩
  have harg : -(n : ℝ) * (pmin * (1 / (k : ℝ)) ^ d) ^ 2 * ζ ^ 2 / 32 = -a * n := by
    dsimp [a]
    ring
  rw [harg]
  exact hb n

def smoothGridPilot {Ω : Type*} (d k : ℕ) {n : ℕ}
    (X : Ω → Model.Covariate d) (R : Ω → ℝ) (ε : ℝ) (hε : ε ≤ 1 - ε)
    (x : Model.Covariate d) (data : Fin n → Ω) : ℝ :=
  fixedGridPilot (fun j : Fin d → Fin k => X ⁻¹' gridCell d k j) R
    (tensorGridWeight d k) ε hε x data

theorem smoothGridPilot_jointly_measurable {Ω : Type*} [MeasurableSpace Ω]
    (d k : ℕ) {n : ℕ} (X : Ω → Model.Covariate d) (hX : Measurable X)
    (R : Ω → ℝ) (hR : Measurable R) (ε : ℝ) (hε : ε ≤ 1 - ε) :
    Measurable (Function.uncurry (smoothGridPilot (n := n) d k X R ε hε)) :=
  fixedGridPilot_jointly_measurable _ (fun j => (gridCell_measurable d k j).preimage hX)
    R hR _ (fun j => (tensorGridWeight_smooth d k j).continuous.measurable) ε hε

theorem smoothGridPilot_smooth {Ω : Type*} (d k : ℕ) {n : ℕ}
    (X : Ω → Model.Covariate d) (R : Ω → ℝ) (ε : ℝ) (hε : ε ≤ 1 - ε)
    (data : Fin n → Ω) : ContDiff ℝ ∞ (fun x => smoothGridPilot d k X R ε hε x data) :=
  fixedGridPilot_smooth _ R _ (tensorGridWeight_smooth d k) ε hε data

theorem smoothGridPilot_range {Ω : Type*} (d k : ℕ) (hk : 0 < k) {n : ℕ}
    (X : Ω → Model.Covariate d) (R : Ω → ℝ) (ε : ℝ) (hε : ε ≤ 1 - ε)
    (x : Model.Covariate d) (data : Fin n → Ω) :
    smoothGridPilot d k X R ε hε x data ∈ Icc ε (1 - ε) :=
  fixedGridPilot_range _ R _ ε hε x data (fun j => tensorGridWeight_nonneg d k j x)
    (tensorGridWeight_sum d k hk x)

/-- Exponential concentration of the explicitly constructed smooth pilot under
the actual marginal density and conditional response mean. -/
theorem smoothGridPilot_exponential_tail {Ω : Type*} [m0 : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d k : ℕ) (hk : 0 < k)
    (X : Ω → Model.Covariate d) (hX : Measurable X)
    (R : Ω → ℝ) (hmR : Measurable R) (hR : ∀ o, R o ∈ Icc (0 : ℝ) 1)
    (p w : Model.Covariate d → ℝ)
    (hmarginal : μ.map X = (Model.cubeVolume d).withDensity (fun x => ENNReal.ofReal (p x)))
    (pmin : ℝ) (hpmin : 0 < pmin) (hp : ∀ᵐ x ∂Model.cubeVolume d, pmin ≤ p x)
    (hw : μ[R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun o => w (X o))
    (ε : ℝ) (hε : ε ≤ 1 - ε) (hwrange : ∀ x ∈ Model.cube d, w x ∈ Icc ε (1 - ε))
    (C γ : ℝ) (hC : 0 ≤ C) (hγ : 0 < γ)
    (hmod : ∀ x ∈ Model.cube d, ∀ y ∈ Model.cube d,
      |w x - w y| ≤ C * ‖x - y‖ ^ γ)
    (ζ : ℝ) (hζ : 0 < ζ) (hζone : ζ ≤ 1)
    (hfine : C * (2 * Real.sqrt d / (k : ℝ)) ^ γ ≤ ζ / 4)
    {n : ℕ} (hn : n ≠ 0) :
    (Measure.pi (fun _ : Fin n => μ)).real
      {data | ∃ x ∈ Model.cube d, ζ < |smoothGridPilot d k X R ε hε x data - w x|} ≤
      (3 * k ^ d : ℝ) * Real.exp
        (-(n : ℝ) * (pmin * (1 / (k : ℝ)) ^ d) ^ 2 * ζ ^ 2 / 32) := by
  let Q : (Fin d → Fin k) → Set Ω := fun j => X ⁻¹' gridCell d k j
  have hm : MeasurableSpace.comap X inferInstance ≤ m0 := measurable_iff_comap_le.mp hX
  have hXm : @Measurable Ω (Model.Covariate d)
      (MeasurableSpace.comap X inferInstance) inferInstance X :=
    measurable_iff_comap_le.mpr le_rfl
  have hQ : ∀ j, MeasurableSet (Q j) := fun j => (gridCell_measurable d k j).preimage hX
  have hQm : ∀ j, @MeasurableSet Ω (MeasurableSpace.comap X inferInstance) (Q j) := fun j =>
    (gridCell_measurable d k j).preimage hXm
  have hprob : 0 < pmin * (1 / (k : ℝ)) ^ d := by positivity
  have hπ : ∀ j, pmin * (1 / (k : ℝ)) ^ d ≤ μ.real (Q j) :=
    fun j => gridCell_probability_lower μ d k hk X hX p hmarginal pmin hpmin hp j
  have hRi : Integrable R μ := Integrable.of_mem_Icc 0 1 hmR.aemeasurable (ae_of_all μ hR)
  have hmeans : ∀ j, cellMean μ (Q j) R ∈ Icc ε (1 - ε) := by
    intro j
    apply conditional_cellMean_mem_Icc μ (MeasurableSpace.comap X inferInstance) hm
      (Q j) (hQm j) (hprob.trans_le (hπ j))
      R (fun o => w (X o)) hRi hw ε (1 - ε)
    intro o ho
    exact hwrange (X o) (gridCell_subset_cube d k hk j (X o) ho)
  have hbias : ∀ x ∈ Model.cube d, ∀ j, tensorGridWeight d k j x ≠ 0 →
      |cellMean μ (Q j) R - w x| ≤ ζ / 4 := by
    intro x hx j hj
    apply conditional_cellMean_bias μ (MeasurableSpace.comap X inferInstance) hm
      (Q j) (hQm j) (hprob.trans_le (hπ j))
      R (fun o => w (X o)) hRi hw (w x) (ζ / 4)
    intro o ho
    have hy := gridCell_subset_cube d k hk j (X o) ho
    have hdist := tensorGridWeight_cell_distance d k hk j x (X o) hx ho hj
    have hreg := hmod x hx (X o) hy
    rw [abs_sub_comm] at hreg
    exact hreg.trans ((mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (norm_nonneg _) hdist hγ.le) hC).trans hfine)
  have hb := fixedGridPilot_uniform_exponential_tail μ hn Q hQ _ hprob hπ R hmR hR
    (tensorGridWeight d k) (Model.cube d) w ε hε hmeans
    (fun x _ j => tensorGridWeight_nonneg d k j x)
    (fun x _ => tensorGridWeight_sum d k hk x) ζ hζ hζone hbias
  simpa only [smoothGridPilot, Q, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hb

end RoughRegime.Applications
