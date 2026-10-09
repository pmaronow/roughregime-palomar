module

public import RoughRegime.PoissonPhase
public import RoughRegime.PoissonPermutation


@[expose] public section
/-! Actual affine phase fields, with the sign-power factorization and source
amplitude bound for every finite observation labeling. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

variable {H X : Type*}

structure AffinePhaseField (H X : Type*) where
  c : H → X → ℝ
  a : H → X → ℝ
  b : H → X → ℝ
  hu : H → X → ℝ
  hv : H → X → ℝ

 def AffinePhaseField.unsigned (F : AffinePhaseField H X) (Au Av : ℝ)
    (l : Fin 3) (p : H × ℝ) (x : X) : ℝ :=
  if l = 0 then F.c p.1 x + F.a p.1 x * Real.cos p.2 + F.b p.1 x * Real.sin p.2
  else if l = 1 then Au * F.hu p.1 x else Av * F.hv p.1 x

 def AffinePhaseField.feature (F : AffinePhaseField H X) (Au Av : ℝ)
    (l : Fin 3) (q : PhaseParameter H) (x : X) : ℝ :=
  (if l = 1 then Lower.sign q.2.1 else 1) *
  (if l = 2 then Lower.sign q.2.2 else 1) * F.unsigned Au Av l q.1 x

 theorem prod_label_sign (k : ℕ) (labels : Fin k → Fin 3) (l : Fin 3) (s : ℝ) :
    (∏ i, if labels i = l then s else 1) = s ^ labelCount k labels l := by
  rw [Finset.prod_ite]
  simp [labelCount]

 theorem AffinePhaseField.tensor_factor (F : AffinePhaseField H X) (Au Av : ℝ)
    (k : ℕ) (labels : Fin k → Fin 3) (q : PhaseParameter H) (xs : Fin k → X) :
    labeledTensor (F.feature Au Av) k labels q xs =
      Lower.sign q.2.1 ^ labelCount k labels 1 *
      Lower.sign q.2.2 ^ labelCount k labels 2 * labeledTensor (F.unsigned Au Av) k labels q.1 xs := by
  unfold labeledTensor AffinePhaseField.feature
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    prod_label_sign, prod_label_sign]

 theorem AffinePhaseField.unsigned_bound (F : AffinePhaseField H X) (Au Av C : ℝ)
    (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hC : 0 ≤ C)
    (hc : ∀ h x, |F.c h x| ≤ C) (ha : ∀ h x, |F.a h x| ≤ C)
    (hb : ∀ h x, |F.b h x| ≤ C) (hu : ∀ h x, |F.hu h x| ≤ C)
    (hv : ∀ h x, |F.hv h x| ≤ C) (l : Fin 3) (p : H × ℝ) (x : X) :
    |F.unsigned Au Av l p x| ≤
      (3 * C) * (if l = 1 then Au else 1) * (if l = 2 then Av else 1) := by
  fin_cases l
  · simpa [AffinePhaseField.unsigned] using
      affine_factor_bound _ _ _ _ C hC (hc p.1 x) (ha p.1 x) (hb p.1 x)
  · norm_num [AffinePhaseField.unsigned, abs_mul, abs_of_nonneg hAu]
    have hi := mul_le_mul_of_nonneg_left (hu p.1 x) hAu
    nlinarith
  · norm_num [AffinePhaseField.unsigned, abs_mul, abs_of_nonneg hAv]
    have hi := mul_le_mul_of_nonneg_left (hv p.1 x) hAv
    nlinarith

 theorem AffinePhaseField.tensor_bound (F : AffinePhaseField H X) (Au Av C : ℝ)
    (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hC : 0 ≤ C)
    (hc : ∀ h x, |F.c h x| ≤ C) (ha : ∀ h x, |F.a h x| ≤ C)
    (hb : ∀ h x, |F.b h x| ≤ C) (hu : ∀ h x, |F.hu h x| ≤ C)
    (hv : ∀ h x, |F.hv h x| ≤ C)
    (k : ℕ) (labels : Fin k → Fin 3) (q : PhaseParameter H) (xs : Fin k → X) :
    |labeledTensor (F.feature Au Av) k labels q xs| ≤
      (3 * C) ^ k * Au ^ labelCount k labels 1 * Av ^ labelCount k labels 2 := by
  rw [F.tensor_factor, abs_mul, abs_mul, sign_power_abs, sign_power_abs, one_mul, one_mul]
  unfold labeledTensor
  rw [Finset.abs_prod]
  have hp := Finset.prod_le_prod₀ (s := Finset.univ)
    (f := fun i => |F.unsigned Au Av (labels i) q.1 (xs i)|)
    (g := fun i => (3 * C) * (if labels i = 1 then Au else 1) * (if labels i = 2 then Av else 1))
    (fun _ _ => abs_nonneg _)
    (fun i _ => F.unsigned_bound Au Av C hAu hAv hC hc ha hb hu hv (labels i) q.1 (xs i))
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    prod_label_sign] at hp
  simpa only [mul_pow] using hp


variable [MeasurableSpace H] [MeasurableSpace X]

structure AffinePhaseField.IsMeasurable (F : AffinePhaseField H X) : Prop where
  c : Measurable (Function.uncurry F.c)
  a : Measurable (Function.uncurry F.a)
  b : Measurable (Function.uncurry F.b)
  hu : Measurable (Function.uncurry F.hu)
  hv : Measurable (Function.uncurry F.hv)

structure AffinePhaseField.Bounded (F : AffinePhaseField H X) (C : ℝ) : Prop where
  c : ∀ h x, |F.c h x| ≤ C
  a : ∀ h x, |F.a h x| ≤ C
  b : ∀ h x, |F.b h x| ≤ C
  hu : ∀ h x, |F.hu h x| ≤ C
  hv : ∀ h x, |F.hv h x| ≤ C

 theorem AffinePhaseField.unsigned_measurable (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (Au Av : ℝ) (l : Fin 3) :
    Measurable (Function.uncurry (F.unsigned Au Av l)) := by
  have hm' : Measurable (fun q : (H × ℝ) × X => (q.1.1, q.2)) := measurable_fst.fst.prodMk measurable_snd
  have hc := hm.c.comp hm'
  have ha := hm.a.comp hm'
  have hb := hm.b.comp hm'
  have hu := hm.hu.comp hm'
  have hv := hm.hv.comp hm'
  unfold Function.uncurry AffinePhaseField.unsigned at *
  by_cases h0 : l = 0
  · simp only [h0, ite_true]
    fun_prop
  by_cases h1 : l = 1
  · simp only [h1, ite_true]
    exact hu.const_mul Au
  · simp only [h0, h1, ite_false]
    exact hv.const_mul Av

 theorem AffinePhaseField.feature_measurable (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (Au Av : ℝ) (l : Fin 3) :
    Measurable (Function.uncurry (F.feature Au Av l)) := by
  have hs : Measurable Lower.sign := Measurable.of_discrete
  have hu : Measurable (fun q : PhaseParameter H × X => F.unsigned Au Av l q.1.1 q.2) :=
    (F.unsigned_measurable hm Au Av l).comp (measurable_fst.fst.prodMk measurable_snd)
  have hs1 : Measurable (fun q : PhaseParameter H × X => if l = 1 then Lower.sign q.1.2.1 else 1) := by
    by_cases h : l = 1
    · simp only [h, ite_true]; fun_prop
    · simp only [h, ite_false]; exact measurable_const
  have hs2 : Measurable (fun q : PhaseParameter H × X => if l = 2 then Lower.sign q.1.2.2 else 1) := by
    by_cases h : l = 2
    · simp only [h, ite_true]; fun_prop
    · simp only [h, ite_false]; exact measurable_const
  exact (hs1.mul hs2).mul hu

omit [MeasurableSpace H] [MeasurableSpace X] in
 theorem AffinePhaseField.unsigned_uniform_bound (F : AffinePhaseField H X) (Au Av C : ℝ)
    (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hC : 0 ≤ C) (hb : F.Bounded C) (l : Fin 3) (p : H × ℝ) (x : X) :
    |F.unsigned Au Av l p x| ≤ 3 * C := by
  have h := F.unsigned_bound Au Av C hAu hAv hC hb.c hb.a hb.b hb.hu hb.hv l p x
  have hu' : (if l = 1 then Au else 1) ≤ 1 := by split_ifs <;> linarith
  have hv' : (if l = 2 then Av else 1) ≤ 1 := by split_ifs <;> linarith
  have hi := mul_le_mul hu' hv' (by split_ifs <;> positivity) zero_le_one
  have he := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 3 * C)
  have he' : (3 * C) * (if l = 1 then Au else 1) * (if l = 2 then Av else 1) ≤ 3 * C := by
    simpa only [one_mul, mul_one, mul_assoc] using he
  exact h.trans he'

omit [MeasurableSpace H] [MeasurableSpace X] in
 theorem AffinePhaseField.feature_uniform_bound (F : AffinePhaseField H X) (Au Av C : ℝ)
    (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hC : 0 ≤ C) (hb : F.Bounded C) (l : Fin 3) (q : PhaseParameter H) (x : X) :
    |F.feature Au Av l q x| ≤ 3 * C := by
  have h := F.unsigned_uniform_bound Au Av C hAu hAu1 hAv hAv1 hC hb l q.1 x
  have hs (s : Bool) : |Lower.sign s| = 1 := by cases s <;> simp [Lower.sign]
  unfold AffinePhaseField.feature
  rw [abs_mul, abs_mul]
  split_ifs <;> simpa only [hs, abs_one, one_mul, mul_one] using h

 theorem AffinePhaseField.labeled_parity (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (ν : Measure H) [IsProbabilityMeasure ν]
    (Au Av C : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hC : 0 ≤ C) (hb : F.Bounded C) (M k : ℕ) (labels : Fin k → Fin 3) (xs : Fin k → X) :
    labeledMixture (phaseBase ν) (fun q => phaseDensity M 1 q - phaseDensity M (-1) q)
      (F.feature Au Av) k labels xs =
      if Odd (labelCount k labels 1) ∧ Odd (labelCount k labels 2) then
        2 * ∫ p, Real.cos ((M : ℝ) * p.2) * labeledTensor (F.unsigned Au Av) k labels p xs
          ∂ν.prod LatticePriors.angleUniform else 0 := by
  let f := fun p : H × ℝ => labeledTensor (F.unsigned Au Av) k labels p xs
  have hf : Measurable f := (labeledTensor_measurable _ (F.unsigned_measurable hm Au Av) k labels).comp
    (measurable_id.prodMk measurable_const)
  have hfb : ∀ p, |f p| ≤ (3 * C) ^ k := fun p =>
    labeledTensor_bound _ (3 * C)
      (fun l p x => F.unsigned_uniform_bound Au Av C hAu hAu1 hAv hAv1 hC hb l p x) k labels p xs
  have hd := phasePrior_signed_difference ν M (labelCount k labels 1) (labelCount k labels 2)
    f hf ((3 * C) ^ k) (by positivity) hfb
  rw [densityLaw_integral, densityLaw_integral] at hd
  have hip := phaseDensity_signed_integrable ν M (labelCount k labels 1) (labelCount k labels 2)
    1 (by norm_num) f hf ((3 * C) ^ k) (by positivity) hfb
  have him := phaseDensity_signed_integrable ν M (labelCount k labels 1) (labelCount k labels 2)
    (-1) (by norm_num) f hf ((3 * C) ^ k) (by positivity) hfb
  change (∫ q, phaseDensity M 1 q * _ ∂phaseBase ν) -
    (∫ q, phaseDensity M (-1) q * _ ∂phaseBase ν) = _ at hd
  rw [← integral_sub hip him] at hd
  unfold labeledMixture
  rw [← hd]
  congr 1
  funext q
  rw [F.tensor_factor]
  dsimp only [f]
  ring

end RoughRegime.PoissonMeasure
