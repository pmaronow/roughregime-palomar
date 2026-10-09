module

public import RoughRegime.SpatialPriorMean
public import RoughRegime.IndependentPriorVariance


@[expose] public section
/-! Transfer of the genuine local nonlinear-prior Taylor remainder to the
actual independent-pair global target. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace RoughRegime.LatticePriors
set_option backward.isDefEq.respectTransparency false
variable {D N : ℕ} {ι : Type*} [Fintype ι]

/-- Finite independent-pair averaging retains the spatial Taylor remainder.
The conclusion concerns the actual integrals under the genuine product priors. -/
theorem independentPairTarget_taylor_error (ell : ℝ) (hell : 0 ≤ ell)
    (μ : Measure (ι → ℤ)) [IsProbabilityMeasure μ] (M : ℕ)
    (F G : Bool → ((ι → ℤ) × (ℝ × (Bool × Bool))) → ℝ)
    (hF : ∀ positive label, Integrable (F label) (blockPrior μ M positive))
    (hG : ∀ positive label, Integrable (G label) (blockPrior μ M positive))
    (d error : ℝ)
    (hb : ∀ label,
      |((∫ q, F label q ∂blockPrior μ M true)-(∫ q, F label q ∂blockPrior μ M false))-
        d*((∫ q, G label q ∂blockPrior μ M true)-(∫ q, G label q ∂blockPrior μ M false))| ≤ error) :
    |((∫ q, independentPairTarget (D := D) (N := N) ell F q ∂globalBlockPrior μ M true)-
       (∫ q, independentPairTarget (D := D) (N := N) ell F q ∂globalBlockPrior μ M false))-
      d*((∫ q, independentPairTarget (D := D) (N := N) ell G q ∂globalBlockPrior μ M true)-
         (∫ q, independentPairTarget (D := D) (N := N) ell G q ∂globalBlockPrior μ M false))| ≤
      (ell*(2*N : ℕ))^(D+1)*error := by
  let EF := fun label => (∫ q, F label q ∂blockPrior μ M true)-(∫ q, F label q ∂blockPrior μ M false)
  let EG := fun label => (∫ q, G label q ∂blockPrior μ M true)-(∫ q, G label q ∂blockPrior μ M false)
  have hFm : ((∫ q, independentPairTarget (D := D) (N := N) ell F q ∂globalBlockPrior μ M true)-
      (∫ q, independentPairTarget (D := D) (N := N) ell F q ∂globalBlockPrior μ M false)) =
      ell^(D+1)*∑ b : GridBlock D N, EF b.2 := by
    rw [independentPairTarget_integral ell μ M true F (hF true),
      independentPairTarget_integral ell μ M false F (hF false),←mul_sub,←Finset.sum_sub_distrib]
  have hGm : ((∫ q, independentPairTarget (D := D) (N := N) ell G q ∂globalBlockPrior μ M true)-
      (∫ q, independentPairTarget (D := D) (N := N) ell G q ∂globalBlockPrior μ M false)) =
      ell^(D+1)*∑ b : GridBlock D N, EG b.2 := by
    rw [independentPairTarget_integral ell μ M true G (hG true),
      independentPairTarget_integral ell μ M false G (hG false),←mul_sub,←Finset.sum_sub_distrib]
  rw [hFm,hGm]
  have he : ell^(D+1)*(∑ b : GridBlock D N, EF b.2)-
      d*(ell^(D+1)*∑ b : GridBlock D N, EG b.2) =
      ell^(D+1)*∑ b : GridBlock D N, (EF b.2-d*EG b.2) := by
    rw [Finset.sum_sub_distrib (f := fun b : GridBlock D N => EF b.2)
      (g := fun b : GridBlock D N => d*EG b.2)]
    rw [← Finset.mul_sum (s := Finset.univ) (f := fun b : GridBlock D N => EG b.2) (a := d)]
    ring
  rw [he,abs_mul,abs_of_nonneg (pow_nonneg hell _)]
  have hh : |∑ b : GridBlock D N, (EF b.2-d*EG b.2)| ≤
      Fintype.card (GridBlock D N)*error := by
    calc
      _ ≤ ∑ b : GridBlock D N, |EF b.2-d*EG b.2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : GridBlock D N, error := Finset.sum_le_sum fun b _ => hb b.2
      _ = _ := by simp
  have hm := mul_le_mul_of_nonneg_left hh (pow_nonneg hell (D+1))
  convert hm using 1
  simp only [gridBlock_card,Nat.cast_pow,Nat.cast_mul,Nat.cast_ofNat,mul_pow]
  ring

/-- A nonzero true mixed coefficient preserves the actual product-prior
separation once the derived Taylor remainder is small. -/
theorem independentPairTarget_taylor_separation (ell : ℝ) (hell : 0 ≤ ell)
    (μ : Measure (ι → ℤ)) [IsProbabilityMeasure μ] (M : ℕ)
    (F G : Bool → ((ι → ℤ) × (ℝ × (Bool × Bool))) → ℝ)
    (hF : ∀ positive label, Integrable (F label) (blockPrior μ M positive))
    (hG : ∀ positive label, Integrable (G label) (blockPrior μ M positive))
    (d error c : ℝ)
    (hb : ∀ label,
      |((∫ q, F label q ∂blockPrior μ M true)-(∫ q, F label q ∂blockPrior μ M false))-
        d*((∫ q, G label q ∂blockPrior μ M true)-(∫ q, G label q ∂blockPrior μ M false))| ≤ error)
    (hc : ∀ label, c ≤ (∫ q, G label q ∂blockPrior μ M true)-
      (∫ q, G label q ∂blockPrior μ M false)) :
    (ell*(2*N : ℕ))^(D+1)*(|d| * c-error) ≤
      |(∫ q, independentPairTarget (D := D) (N := N) ell F q ∂globalBlockPrior μ M true)-
       (∫ q, independentPairTarget (D := D) (N := N) ell F q ∂globalBlockPrior μ M false)| := by
  have he := independentPairTarget_taylor_error (D := D) (N := N) ell hell μ M F G hF hG d error hb
  have hs := independentPairTarget_separation (D := D) (N := N) ell hell μ M G hG c hc
  let f := (∫ q, independentPairTarget (D := D) (N := N) ell F q ∂globalBlockPrior μ M true)-
    (∫ q, independentPairTarget (D := D) (N := N) ell F q ∂globalBlockPrior μ M false)
  let g := (∫ q, independentPairTarget (D := D) (N := N) ell G q ∂globalBlockPrior μ M true)-
    (∫ q, independentPairTarget (D := D) (N := N) ell G q ∂globalBlockPrior μ M false)
  change |f-d*g| ≤ _ at he
  change _ ≤ g at hs
  change _ ≤ |f|
  have hsg : (ell*(2*N : ℕ))^(D+1)*c ≤ |g| := hs.trans (le_abs_self g)
  have hp := mul_le_mul_of_nonneg_left hsg (abs_nonneg d)
  have ht : |d*g| ≤ |f-d*g|+|f| := by
    have h := abs_add_le (d*g-f) f
    rw [sub_add_cancel,abs_sub_comm] at h
    exact h
  rw [abs_mul] at ht
  nlinarith

omit [Fintype ι] in
/-- Measurability of the literal finite-pair target follows from the measurable
local block functions. -/
theorem independentPairTarget_measurable (ell : ℝ)
    (F : Bool → ((ι → ℤ) × (ℝ × (Bool × Bool))) → ℝ)
    (hF : ∀ label, Measurable (F label)) :
    Measurable (independentPairTarget (D := D) (N := N) ell F) := by
  unfold independentPairTarget
  apply measurable_const.mul
  apply Finset.measurable_sum
  intro b _
  exact (hF b.2).comp (measurable_pi_apply b.1)

/-- Bounded block targets have true finite second moments under the genuine
continuous/countable independent-pair priors. -/
theorem independentPairTarget_memLp (ell : ℝ)
    (μ : Measure (ι → ℤ)) [IsProbabilityMeasure μ] (M : ℕ) (positive : Bool)
    (F : Bool → ((ι → ℤ) × (ℝ × (Bool × Bool))) → ℝ)
    (hF : ∀ label, Measurable (F label)) (B : ℝ)
    (hb : ∀ label q, |F label q| ≤ B) :
    MemLp (independentPairTarget (D := D) (N := N) ell F) 2 (globalBlockPrior μ M positive) := by
  apply MemLp.of_bound (independentPairTarget_measurable ell F hF).aestronglyMeasurable
    (|ell^(D+1)| * Fintype.card (GridBlock D N)*B)
  filter_upwards with q
  rw [Real.norm_eq_abs,independentPairTarget,abs_mul]
  have hs : |∑ b : GridBlock D N, F b.2 (q b.1)| ≤ Fintype.card (GridBlock D N)*B := by
    calc
      _ ≤ ∑ b : GridBlock D N, |F b.2 (q b.1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : GridBlock D N, B := Finset.sum_le_sum fun b _ => hb _ _
      _ = _ := by simp
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hs (abs_nonneg _)

/-- Adding the genuine baseline target leaves the independent-pair variance
bound unchanged. This applies to centered local response functions. -/
theorem baseline_add_independentPairTarget_variance_bound (ell baseline : ℝ)
    (μ : Measure (ι → ℤ)) [IsProbabilityMeasure μ] (M : ℕ) (positive : Bool)
    (F : Bool → ((ι → ℤ) × (ℝ × (Bool × Bool))) → ℝ)
    (hF : ∀ label, Measurable (F label)) (B : ℝ) (hB : 0≤B)
    (hb : ∀ label q, |F label q|≤B) :
    variance (fun q => baseline+independentPairTarget (D := D) (N := N) ell F q)
      (globalBlockPrior μ M positive) ≤
      8*(ell^(D+1))^2*Fintype.card (GridPair D N)*B^2 := by
  rw [variance_const_add (independentPairTarget_measurable ell F hF).aestronglyMeasurable baseline]
  have hh := independentPairTarget_variance_bound (D := D) (N := N) μ M positive F hF
    0 B 1 0 ell hB (by norm_num) (by norm_num) (by simpa using hb)
  simpa only [one_pow,zero_pow (by decide : 2≠0),add_zero,mul_one] using hh

end RoughRegime.LatticePriors
