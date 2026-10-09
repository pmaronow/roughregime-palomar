module

public import RoughRegime.GridPilotLaw
public import RoughRegime.HolderModulus
public import RoughRegime.HolderRegularity


@[expose] public section
/-! The fixed-accuracy smooth pilot, including its actual uniform Hölder norm. -/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped BigOperators ContDiff ENNReal
namespace RoughRegime.Applications

/-- A strict exceedance of a continuous spatial family is measurable in the data. -/
theorem measurableSet_exists_lt_of_continuous {S Y : Type*} [TopologicalSpace S]
    [SeparableSpace S] [MeasurableSpace Y] (f : S → Y → ℝ)
    (hm : ∀ x, Measurable (f x)) (hc : ∀ y, Continuous (fun x => f x y)) (a : ℝ) :
    MeasurableSet {y | ∃ x, a < f x y} := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense S
  have : Countable D := hDc.to_subtype
  have heq : {y | ∃ x, a < f x y} = ⋃ x : D, {y | a < f x y} := by
    ext y
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨z, hzD, hz⟩ := hDd.exists_mem_open
        (isOpen_lt continuous_const (hc y)) ⟨x, hx⟩
      exact ⟨⟨z, hzD⟩, hz⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, hx⟩
  rw [heq]
  exact MeasurableSet.iUnion (fun x => measurableSet_lt measurable_const (hm x))

theorem smoothGridPilot_error_event_measurable {Ω : Type*} [MeasurableSpace Ω]
    (d k : ℕ) {n : ℕ} (X : Ω → Model.Covariate d) (hX : Measurable X)
    (R : Ω → ℝ) (hmR : Measurable R) (ε : ℝ) (hε : ε ≤ 1 - ε)
    (w : Model.Covariate d → ℝ) (hw : ContinuousOn w (Model.cube d)) (ζ : ℝ) :
    MeasurableSet {data : Fin n → Ω | ∃ x ∈ Model.cube d,
      ζ < |smoothGridPilot d k X R ε hε x data - w x|} := by
  let f : Model.cube d → (Fin n → Ω) → ℝ :=
    fun x data => |smoothGridPilot d k X R ε hε x data - w x|
  have hfm : ∀ x, Measurable (f x) := by
    intro x
    exact ((smoothGridPilot_jointly_measurable d k X hX R hmR ε hε).comp
      measurable_prodMk_left |>.sub measurable_const).abs
  have hfc : ∀ data, Continuous (fun x => f x data) := by
    intro data
    exact ((smoothGridPilot_smooth d k X R ε hε data).continuous.comp continuous_subtype_val
      |>.sub (continuousOn_iff_continuous_domRestrict.mp hw)).abs
  simpa only [f, Subtype.exists, exists_prop] using
    measurableSet_exists_lt_of_continuous f hfm hfc ζ

theorem finite_smooth_combination_holder_bound {J : Type*} [Fintype J] (d : ℕ)
    (φ : J → Model.Covariate d → ℝ) (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (α : ℝ) (hα : 0 < α) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ a : J → ℝ, (∀ j, |a j| ≤ 1) →
      (fun x => ∑ j, a j * φ j x) ∈ Model.holderBall α H := by
  have hbs : ∀ q : Fin (Model.holderOrder α + 2), ∃ B : ℝ, 0 ≤ B ∧
      ∀ a : J → ℝ, (∀ j, |a j| ≤ 1) → ∀ x ∈ Model.cube d,
        ‖iteratedFDeriv ℝ q.val (fun y => ∑ j, a j * φ j y) x‖ ≤ B := by
    intro q
    exact finite_smooth_combination_derivative_bound (Model.cube d) (Model.isCompact_cube d)
      φ hφ q
  choose b hb hbound using hbs
  let B : ℝ := ∑ q, b q
  have hB : 0 ≤ B := Finset.sum_nonneg (fun q _ => hb q)
  refine ⟨3 * B, by positivity, fun a ha => ?_⟩
  apply Model.holderNorm_le_of_iteratedFDeriv_bound _ α hα
    (ContDiff.sum (fun j _ => contDiff_const.mul (hφ j))) B hB
  intro q hq x hx
  let fq : Fin (Model.holderOrder α + 2) := ⟨q, by omega⟩
  exact (hbound fq a ha x hx).trans
    (Finset.single_le_sum (fun q _ => hb q) (Finset.mem_univ fq))

theorem smoothGridPilot_uniform_holder_bound {Ω : Type*} (d k : ℕ)
    (X : Ω → Model.Covariate d) (R : Ω → ℝ) (ε : ℝ)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 - ε) (α : ℝ) (hα : 0 < α) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ n : ℕ, ∀ data : Fin n → Ω,
      (fun x => smoothGridPilot d k X R ε hε x data) ∈ Model.holderBall α H := by
  obtain ⟨H, hH, hb⟩ := finite_smooth_combination_holder_bound d
    (tensorGridWeight d k) (tensorGridWeight_smooth d k) α hα
  refine ⟨H, hH, fun n data => ?_⟩
  have ha : ∀ j : Fin d → Fin k,
      |(Set.projIcc ε (1 - ε) hε (cellAverage (X ⁻¹' gridCell d k j) R data) : ℝ)| ≤ 1 := by
    intro j
    have hh := (Set.projIcc ε (1 - ε) hε (cellAverage (X ⁻¹' gridCell d k j) R data)).property
    rw [abs_of_nonneg (hε0.trans hh.1)]
    linarith [hh.2]
  simpa only [smoothGridPilot, fixedGridPilot, mul_comm] using
    hb (fun j => (Set.projIcc ε (1 - ε) hε
      (cellAverage (X ⁻¹' gridCell d k j) R data) : ℝ)) ha

/-- Lemma 20. The same explicitly constructed pilot works for every actual
random-design law with the stated density, conditional-mean and Hölder bounds. -/
theorem fixed_accuracy_smooth_pilot {Ω : Type*} [MeasurableSpace Ω]
    (d : ℕ) (α H0 ε pmin ζ : ℝ) (hα : 0 < α) (hH0 : 0 ≤ H0)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1 - ε) (hpmin : 0 < pmin)
    (hζ : 0 < ζ) (hζone : ζ ≤ 1)
    (X : Ω → Model.Covariate d) (hX : Measurable X)
    (R : Ω → ℝ) (hmR : Measurable R) (hR : ∀ o, R o ∈ Icc (0 : ℝ) 1) :
    ∃ (k : ℕ) (H1 c : ℝ), 0 < k ∧ 0 ≤ H1 ∧ 0 < c ∧
      (∀ n : ℕ,
        Measurable (Function.uncurry (smoothGridPilot (n := n) d k X R ε hε)) ∧
        ∀ data : Fin n → Ω,
          ContDiff ℝ ∞ (fun x => smoothGridPilot d k X R ε hε x data) ∧
          (∀ x, smoothGridPilot d k X R ε hε x data ∈ Icc ε (1 - ε)) ∧
          (fun x => smoothGridPilot d k X R ε hε x data) ∈ Model.holderBall α H1) ∧
      ∀ (μ : Measure Ω), IsProbabilityMeasure μ →
        ∀ p w : Model.Covariate d → ℝ,
          μ.map X = (Model.cubeVolume d).withDensity (fun x => ENNReal.ofReal (p x)) →
          (∀ᵐ x ∂Model.cubeVolume d, pmin ≤ p x) →
          (μ[R | MeasurableSpace.comap X inferInstance] =ᵐ[μ] fun o => w (X o)) →
          w ∈ Model.holderBall α H0 →
          (∀ x ∈ Model.cube d, w x ∈ Icc ε (1 - ε)) →
          ∀ n : ℕ, n ≠ 0 →
            (Measure.pi (fun _ : Fin n => μ)).real
              {data | ∃ x ∈ Model.cube d,
                ζ < |smoothGridPilot d k X R ε hε x data - w x|} ≤
              c⁻¹ * Real.exp (-c * n) := by
  let C : ℝ := ((d : ℝ) + 1) * H0
  let γ : ℝ := min α 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hγ : 0 < γ := lt_min hα (by norm_num)
  obtain ⟨k, c, hk, hc, hfine, hexp⟩ :=
    fixed_accuracy_grid_constants d C γ ζ pmin hγ hζ hpmin
  obtain ⟨H1, hH1, hnorm⟩ := smoothGridPilot_uniform_holder_bound d k X R ε hε0 hε α hα
  refine ⟨k, H1, c, hk, hH1, hc, ?_, ?_⟩
  · intro n
    refine ⟨smoothGridPilot_jointly_measurable d k X hX R hmR ε hε, fun data => ?_⟩
    exact ⟨smoothGridPilot_smooth d k X R ε hε data,
      fun x => smoothGridPilot_range d k hk X R ε hε x data, hnorm n data⟩
  · intro μ hμ p w hmarginal hp hw hholder hwrange n hn
    have := hμ
    apply (smoothGridPilot_exponential_tail μ d k hk X hX R hmR hR p w hmarginal
      pmin hpmin hp hw ε hε hwrange C γ hC hγ ?_ ζ hζ hζone hfine hn).trans (hexp n)
    intro x hx y hy
    exact Model.holderBall_spatial_modulus w α H0 hH0 hholder x y hx hy

end RoughRegime.Applications
