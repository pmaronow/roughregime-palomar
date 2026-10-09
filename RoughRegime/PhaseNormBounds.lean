module

public import RoughRegime.PhaseCancellation


@[expose] public section
/-! Actual labeled-coefficient norm bounds, retaining the two first-order
perturbations and controlling all higher odd powers uniformly. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

 theorem labelCount_sum (k : ℕ) (labels : Fin k → Fin 3) :
    labelCount k labels 0 + labelCount k labels 1 + labelCount k labels 2 = k := by
  have h := Finset.card_eq_sum_card_fiberwise (f := labels)
    (s := Finset.univ) (t := Finset.univ) (by simp)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  have hs : (∑ l : Fin 3, labelCount k labels l) =
      labelCount k labels 0 + labelCount k labels 1 + labelCount k labels 2 := by
    simp [Fin.sum_univ_succ, Nat.add_assoc, labelCount]
  change k = ∑ l : Fin 3, labelCount k labels l at h
  omega

 theorem higher_odd_amplitude (Au Av : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1)
    (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) (ku kv : ℕ) (hu : Odd ku) (hv : Odd kv)
    (hfirst : ¬ (ku = 1 ∧ kv = 1)) :
    Au ^ (2 * ku) * Av ^ (2 * kv) ≤ Au ^ 2 * Av ^ 2 * (Au ^ 2 + Av ^ 2) ^ 2 := by
  obtain ⟨u, hu⟩ := hu
  obtain ⟨v, hv⟩ := hv
  have hu1 : 1 ≤ ku := by omega
  have hv1 : 1 ≤ kv := by omega
  have hcase : 3 ≤ ku ∨ 3 ≤ kv := by omega
  have hAu2 : 0 ≤ Au ^ 2 := sq_nonneg _
  have hAv2 : 0 ≤ Av ^ 2 := sq_nonneg _
  rcases hcase with h3 | h3
  · have hp := pow_le_pow_of_le_one hAu hAu1 (show 6 ≤ 2 * ku by omega)
    have hq := pow_le_pow_of_le_one hAv hAv1 (show 2 ≤ 2 * kv by omega)
    have hh := mul_le_mul hp hq (pow_nonneg hAv _) (pow_nonneg hAu 6)
    have hs : Au ^ 4 ≤ (Au ^ 2 + Av ^ 2) ^ 2 := by nlinarith
    have ht := mul_le_mul_of_nonneg_left hs (mul_nonneg hAu2 hAv2)
    calc
      _ ≤ Au ^ 6 * Av ^ 2 := hh
      _ ≤ _ := by nlinarith [ht]
  · have hp := pow_le_pow_of_le_one hAu hAu1 (show 2 ≤ 2 * ku by omega)
    have hq := pow_le_pow_of_le_one hAv hAv1 (show 6 ≤ 2 * kv by omega)
    have hh := mul_le_mul hp hq (pow_nonneg hAv _) (pow_nonneg hAu 2)
    have hs : Av ^ 4 ≤ (Au ^ 2 + Av ^ 2) ^ 2 := by nlinarith
    have ht := mul_le_mul_of_nonneg_left hs (mul_nonneg hAu2 hAv2)
    calc
      _ ≤ Au ^ 2 * Av ^ 6 := hh
      _ ≤ _ := by nlinarith [ht]

variable {H X : Type*} [MeasurableSpace H] [MeasurableSpace X]
variable (ν : Measure H) (μ : Measure X) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ]

 def phaseDifference (M : ℕ) (q : PhaseParameter H) : ℝ := phaseDensity M 1 q - phaseDensity M (-1) q

omit [MeasurableSpace H] in
 theorem phaseDifference_bound (M : ℕ) (q : PhaseParameter H) : |phaseDifference M q| ≤ 2 := by
  have he : phaseDifference M q = 2 * Lower.sign q.2.1 * Lower.sign q.2.2 *
      Real.cos ((M : ℝ) * q.1.2) := by unfold phaseDifference phaseDensity; ring
  rw [he, abs_mul, abs_mul, abs_mul]
  have hs (s : Bool) : |Lower.sign s| = 1 := by cases s <;> simp [Lower.sign]
  simp only [hs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), mul_one]
  exact mul_le_of_le_one_right (by norm_num) (Real.abs_cos_le_one _)

 theorem AffinePhaseField.labeledNorm_bound (F : AffinePhaseField H X)
    (Au Av C : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hC : 0 ≤ C)
    (hb : F.Bounded C) (M k : ℕ) (labels : Fin k → Fin 3) :
    labeledNormSquared (phaseBase ν) μ (phaseDifference M) (F.feature Au Av) k labels ≤
      4 * (9 * C ^ 2) ^ k * Au ^ (2 * labelCount k labels 1) * Av ^ (2 * labelCount k labels 2) := by
  let B := 2 * (3 * C) ^ k * Au ^ labelCount k labels 1 * Av ^ labelCount k labels 2
  have hB : 0 ≤ B := by positivity
  have hp (xs : Fin k → X) : |labeledMixture (phaseBase ν) (phaseDifference M)
      (F.feature Au Av) k labels xs| ≤ B := by
    have hi := norm_integral_le_of_norm_le_const (μ := phaseBase ν)
      (f := fun q => phaseDifference M q * labeledTensor (F.feature Au Av) k labels q xs)
      (C := B) (Filter.Eventually.of_forall fun q => by
        rw [Real.norm_eq_abs, abs_mul]
        have ht := F.tensor_bound Au Av C hAu hAv hC hb.c hb.a hb.b hb.hu hb.hv k labels q xs
        have he := mul_le_mul (phaseDifference_bound M q) ht (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
        simpa [B, mul_assoc] using he)
    simpa [labeledMixture, Real.norm_eq_abs] using hi
  have hsq (xs : Fin k → X) : |labeledMixture (phaseBase ν) (phaseDifference M)
      (F.feature Au Av) k labels xs ^ 2| ≤ B ^ 2 := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hp xs) 2
  have hi := norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : Fin k => μ))
    (f := fun xs => labeledMixture (phaseBase ν) (phaseDifference M) (F.feature Au Av) k labels xs ^ 2)
    (C := B ^ 2) (Filter.Eventually.of_forall hsq)
  have hnonneg : 0 ≤ labeledNormSquared (phaseBase ν) μ (phaseDifference M) (F.feature Au Av) k labels :=
    integral_nonneg fun _ => sq_nonneg _
  have hi' : |labeledNormSquared (phaseBase ν) μ (phaseDifference M) (F.feature Au Av) k labels| ≤ B ^ 2 := by
    simpa [labeledNormSquared, Real.norm_eq_abs] using hi
  clear hi
  rw [abs_of_nonneg hnonneg] at hi'
  have he : B ^ 2 = 4 * (9 * C ^ 2) ^ k * Au ^ (2 * labelCount k labels 1) * Av ^ (2 * labelCount k labels 2) := by
    dsimp [B]
    simp only [mul_pow, ← pow_mul]
    ring_nf
    rw [show (3 : ℝ) ^ (k * 2) = 9 ^ k by rw [Nat.mul_comm k 2, pow_mul]; norm_num]
  rwa [he] at hi'

 def AffinePhaseField.gammaNorm (F : AffinePhaseField H X) (Au Av : ℝ) (M j : ℕ) : ℝ :=
   labeledNormSquared (phaseBase ν) μ (phaseDifference M) (F.feature Au Av) (j + 2) (leadingLabels j)

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] in
 theorem AffinePhaseField.gammaNorm_nonneg (F : AffinePhaseField H X) (Au Av : ℝ) (M j : ℕ) :
    0 ≤ F.gammaNorm ν μ Au Av M j := integral_nonneg fun _ => sq_nonneg _

omit [IsProbabilityMeasure μ] in
 theorem AffinePhaseField.labeledNorm_low_degree (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (Au Av C : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1)
    (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) (hC : 0 ≤ C) (hb : F.Bounded C)
    (M k : ℕ) (labels : Fin k → Fin 3) (hj : labelCount k labels 0 < M) :
    labeledNormSquared (phaseBase ν) μ (phaseDifference M) (F.feature Au Av) k labels = 0 := by
  unfold labeledNormSquared
  change (∫ xs, labeledMixture (phaseBase ν) (fun q => phaseDensity M 1 q - phaseDensity M (-1) q)
    (F.feature Au Av) k labels xs ^ 2 ∂Measure.pi (fun _ : Fin k => μ)) = 0
  simp_rw [F.labeled_low_degree hm ν Au Av C hAu hAu1 hAv hAv1 hC hb M k labels hj]
  simp

omit [IsProbabilityMeasure μ] in
 theorem AffinePhaseField.labeledNorm_bad_parity (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (Au Av C : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1)
    (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) (hC : 0 ≤ C) (hb : F.Bounded C)
    (M k : ℕ) (labels : Fin k → Fin 3)
    (hp : ¬ (Odd (labelCount k labels 1) ∧ Odd (labelCount k labels 2))) :
    labeledNormSquared (phaseBase ν) μ (phaseDifference M) (F.feature Au Av) k labels = 0 := by
  unfold labeledNormSquared
  change (∫ xs, labeledMixture (phaseBase ν) (fun q => phaseDensity M 1 q - phaseDensity M (-1) q)
    (F.feature Au Av) k labels xs ^ 2 ∂Measure.pi (fun _ : Fin k => μ)) = 0
  simp_rw [F.labeled_even_count hm ν Au Av C hAu hAu1 hAv hAv1 hC hb M k labels hp]
  simp


 def AffinePhaseField.leadingContribution (F : AffinePhaseField H X) (Au Av : ℝ) (M k : ℕ) : ℝ :=
    if M + 2 ≤ k then F.gammaNorm ν μ Au Av M (k - 2) else 0

 def remainderContribution (Au Av C : ℝ) (M k : ℕ) : ℝ :=
    if M + 4 ≤ k then 4 * (9 * C ^ 2) ^ k * Au ^ 2 * Av ^ 2 * (Au ^ 2 + Av ^ 2) ^ 2 else 0

omit [IsProbabilityMeasure ν] [IsProbabilityMeasure μ] in
 theorem AffinePhaseField.leadingContribution_nonneg (F : AffinePhaseField H X)
    (Au Av : ℝ) (M k : ℕ) : 0 ≤ F.leadingContribution ν μ Au Av M k := by
  unfold AffinePhaseField.leadingContribution
  split_ifs
  · exact F.gammaNorm_nonneg ν μ Au Av M _
  · positivity

 theorem remainderContribution_nonneg (Au Av C : ℝ) (M k : ℕ) : 0 ≤ remainderContribution Au Av C M k := by
  unfold remainderContribution
  split_ifs <;> positivity

 theorem AffinePhaseField.labeledNorm_contribution (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (Au Av C : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1)
    (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) (hC : 0 ≤ C) (hb : F.Bounded C)
    (M k : ℕ) (labels : Fin k → Fin 3) :
    labeledNormSquared (phaseBase ν) μ (phaseDifference M) (F.feature Au Av) k labels ≤
      F.leadingContribution ν μ Au Av M k + remainderContribution Au Av C M k := by
  have hzero : 0 ≤ F.leadingContribution ν μ Au Av M k + remainderContribution Au Av C M k :=
    add_nonneg (F.leadingContribution_nonneg ν μ Au Av M k) (remainderContribution_nonneg _ _ _ _ _)
  by_cases hp : Odd (labelCount k labels 1) ∧ Odd (labelCount k labels 2)
  swap
  · rw [F.labeledNorm_bad_parity ν μ hm Au Av C hAu hAu1 hAv hAv1 hC hb M k labels hp]
    exact hzero
  by_cases hj : labelCount k labels 0 < M
  · rw [F.labeledNorm_low_degree ν μ hm Au Av C hAu hAu1 hAv hAv1 hC hb M k labels hj]
    exact hzero
  have hj' : M ≤ labelCount k labels 0 := by omega
  have hs := labelCount_sum k labels
  obtain ⟨u, hu⟩ := hp.1
  obtain ⟨v, hv⟩ := hp.2
  by_cases hlead : labelCount k labels 1 = 1 ∧ labelCount k labels 2 = 1
  · have hk2 : 2 ≤ k := by omega
    have hkM : M + 2 ≤ k := by omega
    have hnorm : labeledNormSquared (phaseBase ν) μ (phaseDifference M) (F.feature Au Av) k labels =
        F.gammaNorm ν μ Au Av M (k - 2) := by
      obtain ⟨j, hk⟩ := Nat.exists_eq_add_of_le hk2
      have hk' : k = j + 2 := by omega
      clear hk
      subst k
      have hjsub : j + 2 - 2 = j := by omega
      rw [hjsub]
      exact leading_labeledNormSquared_eq (phaseBase ν) μ
        (phaseDifference M) (F.feature Au Av) j labels hlead.1 hlead.2
    rw [hnorm, AffinePhaseField.leadingContribution, ite_eq_left hkM]
    exact le_add_of_nonneg_right (remainderContribution_nonneg _ _ _ _ _)
  · have hq : 4 ≤ labelCount k labels 1 + labelCount k labels 2 := by omega
    have hkM : M + 4 ≤ k := by omega
    have ham := higher_odd_amplitude Au Av hAu hAu1 hAv hAv1
      (labelCount k labels 1) (labelCount k labels 2) hp.1 hp.2 hlead
    have hi := F.labeledNorm_bound ν μ Au Av C hAu hAv hC hb M k labels
    have hh := mul_le_mul_of_nonneg_left ham (by positivity : 0 ≤ 4 * (9 * C ^ 2) ^ k)
    have hupper : labeledNormSquared (phaseBase ν) μ (phaseDifference M) (F.feature Au Av) k labels ≤
        remainderContribution Au Av C M k := by
      unfold remainderContribution
      rw [ite_eq_left hkM]
      exact hi.trans (by simpa only [mul_assoc] using hh)
    exact hupper.trans (le_add_of_nonneg_left (F.leadingContribution_nonneg ν μ Au Av M k))

 theorem AffinePhaseField.labelingSum_contribution (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (Au Av C : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1)
    (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) (hC : 0 ≤ C) (hb : F.Bounded C) (M k : ℕ) :
    (∑ labels : Fin k → Fin 3, labeledNormSquared (phaseBase ν) μ (phaseDifference M)
      (F.feature Au Av) k labels) ≤
      (3 : ℝ) ^ k * (F.leadingContribution ν μ Au Av M k + remainderContribution Au Av C M k) := by
  have hi := Finset.sum_le_sum (fun (labels : Fin k → Fin 3) (_ : labels ∈ Finset.univ) =>
    F.labeledNorm_contribution ν μ hm Au Av C hAu hAu1 hAv hAv1 hC hb M k labels)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] using hi


 theorem leadingLabels_count_u (j : ℕ) : labelCount (j + 2) (leadingLabels j) 1 = 1 := by
  unfold labelCount
  have he : (Finset.univ.filter (fun i : Fin (j + 2) => leadingLabels j i = 1)) = {0} := by
    ext i
    by_cases hi0 : i = 0
    · subst i; simp [leadingLabels]
    · by_cases hi1 : i = 1
      · subst i; simp [leadingLabels]
      · simp [leadingLabels, hi0, hi1]
  rw [he]
  simp

 theorem leadingLabels_count_v (j : ℕ) : labelCount (j + 2) (leadingLabels j) 2 = 1 := by
  unfold labelCount
  have he : (Finset.univ.filter (fun i : Fin (j + 2) => leadingLabels j i = 2)) = {1} := by
    ext i
    by_cases hi0 : i = 0
    · subst i; simp [leadingLabels]
    · simp [leadingLabels, hi0]
  rw [he]
  simp

 theorem leadingLabels_count_density (j : ℕ) : labelCount (j + 2) (leadingLabels j) 0 = j := by
  have hs := labelCount_sum (j + 2) (leadingLabels j)
  rw [leadingLabels_count_u, leadingLabels_count_v] at hs
  omega

omit [IsProbabilityMeasure μ] in
 theorem AffinePhaseField.gammaNorm_zero (F : AffinePhaseField H X)
    (hm : F.IsMeasurable) (Au Av C : ℝ) (hAu : 0 ≤ Au) (hAu1 : Au ≤ 1)
    (hAv : 0 ≤ Av) (hAv1 : Av ≤ 1) (hC : 0 ≤ C) (hb : F.Bounded C)
    (M j : ℕ) (hj : j < M) : F.gammaNorm ν μ Au Av M j = 0 := by
  unfold AffinePhaseField.gammaNorm
  exact F.labeledNorm_low_degree ν μ hm Au Av C hAu hAu1 hAv hAv1 hC hb M (j + 2)
    (leadingLabels j) (by simpa only [leadingLabels_count_density] using hj)

 theorem AffinePhaseField.gammaNorm_bound (F : AffinePhaseField H X)
    (Au Av C : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hC : 0 ≤ C)
    (hb : F.Bounded C) (M j : ℕ) :
    F.gammaNorm ν μ Au Av M j ≤ 4 * (9 * C ^ 2) ^ (j + 2) * Au ^ 2 * Av ^ 2 := by
  have hi := F.labeledNorm_bound ν μ Au Av C hAu hAv hC hb M (j + 2) (leadingLabels j)
  simpa [AffinePhaseField.gammaNorm, leadingLabels_count_u, leadingLabels_count_v] using hi

 theorem AffinePhaseField.gammaSeries_summable (F : AffinePhaseField H X)
    (Au Av C : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hC : 0 ≤ C)
    (hb : F.Bounded C) (M : ℕ) (z : ℝ) (hz : 0 ≤ z) :
    Summable (fun j => z ^ j / j.factorial * F.gammaNorm ν μ Au Av M j) := by
  let A := 9 * C ^ 2
  have hA : 0 ≤ A := by positivity
  have hi (j : ℕ) : z ^ j / j.factorial * F.gammaNorm ν μ Au Av M j ≤
      (4 * A ^ 2 * Au ^ 2 * Av ^ 2) * ((z * A) ^ j / j.factorial) := by
    have hg := mul_le_mul_of_nonneg_left (F.gammaNorm_bound ν μ Au Av C hAu hAv hC hb M j)
      (by positivity : 0 ≤ z ^ j / j.factorial)
    calc
      _ ≤ z ^ j / j.factorial * (4 * A ^ (j + 2) * Au ^ 2 * Av ^ 2) := hg
      _ = _ := by rw [pow_add, mul_pow]; ring
  apply Summable.of_nonneg_of_le (fun j => mul_nonneg (by positivity) (F.gammaNorm_nonneg ν μ Au Av M j)) hi
  exact (Real.summable_pow_div_factorial (z * A)).mul_left (4 * A ^ 2 * Au ^ 2 * Av ^ 2)

end RoughRegime.PoissonMeasure
