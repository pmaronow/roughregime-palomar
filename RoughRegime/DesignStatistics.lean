module

public import RoughRegime.DesignBessel


@[expose] public section
/-! Literal observable packing of the upper-triangular cell design moments. -/
noncomputable section
namespace RoughRegime.Model
open MeasureTheory
open scoped BigOperators ENNReal
set_option backward.isDefEq.respectTransparency false

abbrev DesignUpperPair (n : ℕ) := {ij : Fin n × Fin n // ij.1 ≤ ij.2}
abbrev DesignMomentIndex (n : ℕ) := DesignUpperPair n ⊕ (Fin n ⊕ Fin n)

def designRawCoordinate (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) {n : ℕ} (z : Fin n → Covariate A.d → ℝ)
    (o : Observation A Z) : DesignMomentIndex n → ℝ
  | .inl ij => F.D o.2 * z ij.1.1 o.1 * z ij.1.2 o.1
  | .inr (.inl i) => F.U o.2 * z i o.1
  | .inr (.inr i) => F.V o.2 * z i o.1

def designStatistic (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) {n : ℕ} (z : Fin n → Covariate A.d → ℝ)
    (C : Set (Covariate A.d)) (K : ℝ) (o : Observation A Z) :
    EuclideanSpace ℝ (DesignMomentIndex n) :=
  WithLp.toLp 2 (fun i => K * C.indicator (fun x => designRawCoordinate A F z (x, o.2) i) o.1)

def designPopulation (A : Parameters) (μ : Measure (Covariate A.d)) (g a b : Covariate A.d → ℝ)
    {n : ℕ} (z : Fin n → Covariate A.d → ℝ) : EuclideanSpace ℝ (DesignMomentIndex n) :=
  WithLp.toLp 2 (fun i => match i with
    | .inl ij => designGram μ g z ij.1.1 ij.1.2
    | .inr (.inl q) => designMoment μ g z a q
    | .inr (.inr q) => designMoment μ g z b q)

 theorem finiteEuclidean_norm_le_uniform {ι : Type*} [Fintype ι]
    (v : EuclideanSpace ℝ ι) (B : ℝ) (hB : 0 ≤ B) (hv : ∀ i, |v i| ≤ B) :
    ‖v‖ ≤ Real.sqrt (Fintype.card ι) * B := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hB)).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc
    ∑ i, ‖v i‖ ^ 2 ≤ ∑ _ : ι, B ^ 2 := Finset.sum_le_sum (fun i _ => by
      rw [Real.norm_eq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) hB).mpr (hv i))
    _ = _ := by simp

 theorem designStatistic_measurable (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) {n : ℕ} (z : Fin n → Covariate A.d → ℝ)
    (hz : ∀ i, Measurable (z i)) (C : Set (Covariate A.d)) (hC : MeasurableSet C) (K : ℝ) :
    Measurable (designStatistic A F z C K) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro i
  cases i with
  | inl ij =>
    change Measurable (fun o : Observation A Z => K * (Prod.fst ⁻¹' C).indicator
      (fun o => F.D o.2 * z ij.1.1 o.1 * z ij.1.2 o.1) o)
    exact measurable_const.mul ((((F.measurableD.comp measurable_snd).mul
      ((hz _).comp measurable_fst)).mul ((hz _).comp measurable_fst)).indicator
        (hC.preimage measurable_fst))
  | inr i =>
    cases i with
    | inl i =>
      change Measurable (fun o : Observation A Z => K * (Prod.fst ⁻¹' C).indicator
        (fun o => F.U o.2 * z i o.1) o)
      exact measurable_const.mul (((F.measurableU.comp measurable_snd).mul
        ((hz i).comp measurable_fst)).indicator (hC.preimage measurable_fst))
    | inr i =>
      change Measurable (fun o : Observation A Z => K * (Prod.fst ⁻¹' C).indicator
        (fun o => F.V o.2 * z i o.1) o)
      exact measurable_const.mul (((F.measurableV.comp measurable_snd).mul
        ((hz i).comp measurable_fst)).indicator (hC.preimage measurable_fst))

 theorem designRawCoordinate_bound (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) {n : ℕ} (z : Fin n → Covariate A.d → ℝ)
    (B : ℝ) (hB : 1 ≤ B) (hz : ∀ i x, |z i x| ≤ B) (o : Observation A Z)
    (i : DesignMomentIndex n) : |designRawCoordinate A F z o i| ≤ A.M0 * B ^ 2 := by
  cases i with
  | inl ij =>
    dsimp only [designRawCoordinate]
    rw [abs_mul, abs_mul]
    have hd : |F.D o.2| ≤ A.M0 := by rw [abs_of_nonneg (F.boundD o.2).1]; exact (F.boundD o.2).2
    calc
      |F.D o.2| * |z ij.1.1 o.1| * |z ij.1.2 o.1| ≤ (A.M0 * B) * B :=
        mul_le_mul (mul_le_mul hd (hz _ _) (abs_nonneg _) A.hM0.le) (hz _ _) (abs_nonneg _)
          (mul_nonneg A.hM0.le (by linarith))
      _ = _ := by ring
  | inr i =>
    have hBB : B ≤ B ^ 2 := by nlinarith
    cases i with
    | inl i =>
      dsimp only [designRawCoordinate]
      rw [abs_mul]
      exact (mul_le_mul (F.boundU _) (hz _ _) (abs_nonneg _) A.hM0.le).trans
        (mul_le_mul_of_nonneg_left hBB A.hM0.le)
    | inr i =>
      dsimp only [designRawCoordinate]
      rw [abs_mul]
      exact (mul_le_mul (F.boundV _) (hz _ _) (abs_nonneg _) A.hM0.le).trans
        (mul_le_mul_of_nonneg_left hBB A.hM0.le)

 theorem designStatistic_norm_bound (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) {n : ℕ} (z : Fin n → Covariate A.d → ℝ)
    (B : ℝ) (hB : 1 ≤ B) (hz : ∀ i x, |z i x| ≤ B)
    (C : Set (Covariate A.d)) (K : ℝ) (hK : 0 ≤ K) (o : Observation A Z) :
    ‖designStatistic A F z C K o‖ ≤
      (Real.sqrt (Fintype.card (DesignMomentIndex n)) * (A.M0 * B ^ 2)) *
        K * C.indicator (fun _ => (1 : ℝ)) o.1 := by
  by_cases ho : o.1 ∈ C
  · simp only [Set.indicator_of_mem ho, mul_one]
    have hv : ∀ i, |designStatistic A F z C K o i| ≤ K * (A.M0 * B ^ 2) := by
      intro i
      change |K * C.indicator _ o.1| ≤ _
      rw [Set.indicator_of_mem ho, abs_mul, abs_of_nonneg hK]
      exact mul_le_mul_of_nonneg_left (designRawCoordinate_bound A F z B hB hz o i) hK
    exact (finiteEuclidean_norm_le_uniform _ _
      (mul_nonneg hK (mul_nonneg A.hM0.le (sq_nonneg _))) hv).trans_eq (by ring)
  · have he : designStatistic A F z C K o = 0 := by
      ext i
      change K * C.indicator _ o.1 = 0
      simp [Set.indicator_of_notMem ho]
    simp [he, Set.indicator_of_notMem ho]

 theorem designStatistic_integrable (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) {n : ℕ}
    (z : Fin n → Covariate A.d → ℝ) (hz : ∀ i, Measurable (z i))
    (B : ℝ) (hB : 1 ≤ B) (hzB : ∀ i x, |z i x| ≤ B)
    (C : Set (Covariate A.d)) (hC : MeasurableSet C) (K : ℝ) (hK : 0 ≤ K) :
    Integrable (designStatistic A F z C K) (P : Measure (Observation A Z)) := by
  apply Integrable.of_bound (designStatistic_measurable A F z hz C hC K).aestronglyMeasurable
    ((Real.sqrt (Fintype.card (DesignMomentIndex n)) * (A.M0 * B ^ 2)) * K)
  apply Filter.Eventually.of_forall
  intro o
  have hh := designStatistic_norm_bound A F z B hB hzB C K hK o
  by_cases ho : o.1 ∈ C
  · simpa only [Set.indicator_of_mem ho, mul_one] using hh
  · simp only [Set.indicator_of_notMem ho, mul_zero] at hh
    exact hh.trans (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg A.hM0.le (sq_nonneg _))) hK)

 theorem designStatistic_coordinate_integral (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (h : ModelWitness A F P)
    {n : ℕ} (z : Fin n → Covariate A.d → ℝ) (hz : ∀ i, Measurable (z i))
    (B : ℝ) (hB : 1 ≤ B) (hzB : ∀ i x, |z i x| ≤ B)
    (C : Set (Covariate A.d)) (hC : MeasurableSet C) (K : ℝ) (hK : 0 ≤ K)
    (i : DesignMomentIndex n) :
    (∫ o, designStatistic A F z C K o i ∂(P : Measure (Observation A Z))) =
      designPopulation A (ENNReal.ofReal K • (cubeVolume A.d).restrict C)
        (fun x => h.w x * h.p x) h.a h.b z i := by
  cases i with
  | inl ij =>
    let φ := C.indicator (fun x => z ij.1.1 x * z ij.1.2 x)
    have hφ : Measurable φ := ((hz _).mul (hz _)).indicator hC
    have hφB : ∀ x, |φ x| ≤ B ^ 2 := by
      intro x
      by_cases hx : x ∈ C
      · dsimp only [φ]
        rw [Set.indicator_of_mem hx, abs_mul, pow_two]
        exact mul_le_mul (hzB _ _) (hzB _ _) (abs_nonneg _) (by linarith)
      · simp [φ, Set.indicator_of_notMem hx, sq_nonneg]
    change (∫ o, K * C.indicator (fun x => F.D o.2 * z ij.1.1 x * z ij.1.2 x) o.1
      ∂(P : Measure (Observation A Z))) = ∫ x, (h.w x * h.p x) * z ij.1.1 x * z ij.1.2 x
        ∂(ENNReal.ofReal K • (cubeVolume A.d).restrict C)
    rw [integral_const_mul, integral_smul_measure, ENNReal.toReal_ofReal hK, smul_eq_mul]
    congr 1
    calc
      _ = ∫ o, F.D o.2 * φ o.1 ∂(P : Measure (Observation A Z)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun o => by
          by_cases ho : o.1 ∈ C <;> simp [φ, Set.indicator_of_mem, Set.indicator_of_notMem, ho] <;> ring
      _ = ∫ x, (h.w x * h.p x) * φ x ∂cubeVolume A.d :=
        design_D_integral A F P h φ hφ (B ^ 2) (sq_nonneg _) hφB
      _ = _ := by
        rw [← integral_indicator hC]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by
          by_cases hx : x ∈ C <;> simp [φ, Set.indicator_of_mem, Set.indicator_of_notMem, hx] <;> ring
  | inr i =>
    cases i with
    | inl q =>
      let φ := C.indicator (z q)
      have hφ : Measurable φ := (hz q).indicator hC
      have hφB : ∀ x, |φ x| ≤ B := by
        intro x
        by_cases hx : x ∈ C
        · simpa [φ, Set.indicator_of_mem hx] using hzB q x
        · simp [φ, Set.indicator_of_notMem hx]; linarith
      change (∫ o, K * C.indicator (fun x => F.U o.2 * z q x) o.1
        ∂(P : Measure (Observation A Z))) = ∫ x, (h.w x * h.p x) * z q x * h.a x
          ∂(ENNReal.ofReal K • (cubeVolume A.d).restrict C)
      rw [integral_const_mul, integral_smul_measure, ENNReal.toReal_ofReal hK, smul_eq_mul]
      congr 1
      calc
        _ = ∫ o, F.U o.2 * φ o.1 ∂(P : Measure (Observation A Z)) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun o => by
            by_cases ho : o.1 ∈ C <;> simp [φ, Set.indicator_of_mem, Set.indicator_of_notMem, ho]
        _ = ∫ x, h.a x * (h.w x * h.p x) * φ x ∂cubeVolume A.d :=
          design_U_integral A F P h φ hφ B (by linarith) hφB
        _ = _ := by
          rw [← integral_indicator hC]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            by_cases hx : x ∈ C <;> simp [φ, Set.indicator_of_mem, Set.indicator_of_notMem, hx] <;> ring
    | inr q =>
      let φ := C.indicator (z q)
      have hφ : Measurable φ := (hz q).indicator hC
      have hφB : ∀ x, |φ x| ≤ B := by
        intro x
        by_cases hx : x ∈ C
        · simpa [φ, Set.indicator_of_mem hx] using hzB q x
        · simp [φ, Set.indicator_of_notMem hx]; linarith
      change (∫ o, K * C.indicator (fun x => F.V o.2 * z q x) o.1
        ∂(P : Measure (Observation A Z))) = ∫ x, (h.w x * h.p x) * z q x * h.b x
          ∂(ENNReal.ofReal K • (cubeVolume A.d).restrict C)
      rw [integral_const_mul, integral_smul_measure, ENNReal.toReal_ofReal hK, smul_eq_mul]
      congr 1
      calc
        _ = ∫ o, F.V o.2 * φ o.1 ∂(P : Measure (Observation A Z)) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun o => by
            by_cases ho : o.1 ∈ C <;> simp [φ, Set.indicator_of_mem, Set.indicator_of_notMem, ho]
        _ = ∫ x, h.b x * (h.w x * h.p x) * φ x ∂cubeVolume A.d :=
          design_V_integral A F P h φ hφ B (by linarith) hφB
        _ = _ := by
          rw [← integral_indicator hC]
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => by
            by_cases hx : x ∈ C <;> simp [φ, Set.indicator_of_mem, Set.indicator_of_notMem, hx] <;> ring

/-- The literal packed observable's true vector expectation is the population
Gram/moment packing, obtained from the model conditional expectations. -/
 theorem designStatistic_integral (A : Parameters) {Z : Type*} [MeasurableSpace Z]
    (F : Observables Z A) (P : ProbabilityMeasure (Observation A Z)) (h : ModelWitness A F P)
    {n : ℕ} (z : Fin n → Covariate A.d → ℝ) (hz : ∀ i, Measurable (z i))
    (B : ℝ) (hB : 1 ≤ B) (hzB : ∀ i x, |z i x| ≤ B)
    (C : Set (Covariate A.d)) (hC : MeasurableSet C) (K : ℝ) (hK : 0 ≤ K) :
    (∫ o, designStatistic A F z C K o ∂(P : Measure (Observation A Z))) =
      designPopulation A (ENNReal.ofReal K • (cubeVolume A.d).restrict C)
        (fun x => h.w x * h.p x) h.a h.b z := by
  ext i
  have hi := designStatistic_integrable A F P z hz B hB hzB C hC K hK
  have he := (PiLp.proj (p := 2) (β := fun _ : DesignMomentIndex n => ℝ) (𝕜 := ℝ) i).integral_comp_comm hi
  change (∫ o, designStatistic A F z C K o i ∂(P : Measure (Observation A Z))) =
    (∫ o, designStatistic A F z C K o ∂(P : Measure (Observation A Z))) i at he
  rw [← he]
  exact designStatistic_coordinate_integral A F P h z hz B hB hzB C hC K hK i

end RoughRegime.Model
