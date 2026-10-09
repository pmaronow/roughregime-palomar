module

public import RoughRegime.PhaseField
public import RoughRegime.PoissonSpectral


@[expose] public section
/-! The actual labeled coefficient vanishes unless both sign counts are odd
and at least M observations carry a density label. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]

 theorem AffinePhaseField.labeled_low_degree (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (ν : Measure H) [IsProbabilityMeasure ν]
    (Au Av C : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hC : 0 ≤ C) (hb : F.Bounded C) (M k : ℕ) (labels : Fin k → Fin 3)
    (hj : labelCount k labels 0 < M) (xs : Fin k → X) :
    labeledMixture (phaseBase ν) (fun q => phaseDensity M 1 q - phaseDensity M (-1) q)
      (F.feature Au Av) k labels xs = 0 := by
  classical
  rw [F.labeled_parity hm ν Au Av C hAu hAu1 hAv hAv1 hC hb M k labels xs]
  let T := {i : Fin k // labels i = 0}
  let w := fun h : H => ∏ i ∈ Finset.univ.filter (fun i : Fin k => labels i ≠ 0),
    if labels i = 1 then Au * F.hu h (xs i) else Av * F.hv h (xs i)
  have hw : Measurable w := by
    apply Finset.measurable_prod
    intro i _
    by_cases h1 : labels i = 1
    · simp only [h1, ite_true]
      exact (hm.hu.comp (measurable_id.prodMk measurable_const)).const_mul Au
    · simp only [h1, ite_false]
      exact (hm.hv.comp (measurable_id.prodMk measurable_const)).const_mul Av
  let A := (3 * C) ^ (Finset.univ.filter (fun i : Fin k => labels i ≠ 0)).card
  have hA : 0 ≤ A := by positivity
  have hwbound : ∀ h, |w h| ≤ A := by
    intro h
    unfold w
    rw [Finset.abs_prod]
    have hi := Finset.prod_le_prod₀ (s := Finset.univ.filter (fun i : Fin k => labels i ≠ 0))
      (f := fun i => |if labels i = 1 then Au * F.hu h (xs i) else Av * F.hv h (xs i)|)
      (g := fun _ => 3 * C) (fun _ _ => abs_nonneg _) (fun i hi => by
        have hi0 : labels i ≠ 0 := (Finset.mem_filter.mp hi).2
        simpa only [AffinePhaseField.unsigned, hi0, ite_false] using
          F.unsigned_uniform_bound Au Av C hAu hAu1 hAv hAv1 hC hb (labels i) (h, 0) (xs i))
    simpa [A] using hi
  have hcard : Fintype.card T < M := by
    simpa [T, Fintype.card_subtype, labelCount] using hj
  have hc (i : T) : Measurable (fun h => F.c h (xs i.val)) :=
    hm.c.comp (measurable_id.prodMk measurable_const)
  have ha (i : T) : Measurable (fun h => F.a h (xs i.val)) :=
    hm.a.comp (measurable_id.prodMk measurable_const)
  have hb' (i : T) : Measurable (fun h => F.b h (xs i.val)) :=
    hm.b.comp (measurable_id.prodMk measurable_const)
  have hz := latent_affine_angular_zero_fintype ν M hcard w
    (fun i : T => fun h => F.c h (xs i.val))
    (fun i : T => fun h => F.a h (xs i.val))
    (fun i : T => fun h => F.b h (xs i.val)) hw hc ha hb' A C hA hC hwbound
    (fun i h => hb.c h (xs i.val)) (fun i h => hb.a h (xs i.val)) (fun i h => hb.b h (xs i.val))
  have he (p : H × ℝ) : labeledTensor (F.unsigned Au Av) k labels p xs =
      w p.1 * ∏ i : T, (F.c p.1 (xs i.val) + F.a p.1 (xs i.val) * Real.cos p.2 +
        F.b p.1 (xs i.val) * Real.sin p.2) := by
    unfold labeledTensor AffinePhaseField.unsigned
    rw [Finset.prod_ite]
    have hs : (∏ i : T, (F.c p.1 (xs i.val) + F.a p.1 (xs i.val) * Real.cos p.2 +
        F.b p.1 (xs i.val) * Real.sin p.2)) =
        ∏ i ∈ Finset.univ.filter (fun i : Fin k => labels i = 0),
          (F.c p.1 (xs i) + F.a p.1 (xs i) * Real.cos p.2 + F.b p.1 (xs i) * Real.sin p.2) := by
      simpa [T] using Finset.prod_subtype_eq_prod_filter (s := Finset.univ)
        (p := fun i : Fin k => labels i = 0)
        (fun i => F.c p.1 (xs i) + F.a p.1 (xs i) * Real.cos p.2 + F.b p.1 (xs i) * Real.sin p.2)
    rw [hs]
    change _ * w p.1 = _
    ring
  have he' : (fun p : H × ℝ => Real.cos ((M : ℝ) * p.2) *
      labeledTensor (F.unsigned Au Av) k labels p xs) =
      fun p => w p.1 * Real.cos ((M : ℝ) * p.2) *
        ∏ i : T, (F.c p.1 (xs i.val) + F.a p.1 (xs i.val) * Real.cos p.2 +
          F.b p.1 (xs i.val) * Real.sin p.2) := by
    funext p
    rw [he]
    ring
  rw [he', hz]
  simp

 theorem AffinePhaseField.labeled_even_count (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (ν : Measure H) [IsProbabilityMeasure ν]
    (Au Av C : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1) (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1)
    (hC : 0 ≤ C) (hb : F.Bounded C) (M k : ℕ) (labels : Fin k → Fin 3)
    (hp : ¬ (Odd (labelCount k labels 1) ∧ Odd (labelCount k labels 2)))
    (xs : Fin k → X) :
    labeledMixture (phaseBase ν) (fun q => phaseDensity M 1 q - phaseDensity M (-1) q)
      (F.feature Au Av) k labels xs = 0 := by
  rw [F.labeled_parity hm ν Au Av C hAu hAu1 hAv hAv1 hC hb M k labels xs, ite_eq_right hp]

end RoughRegime.PoissonMeasure
