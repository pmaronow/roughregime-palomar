module

public import RoughRegime.PoissonPairProducts
public import RoughRegime.FuzzyTesting


@[expose] public section
/-! Markov observation kernels for the actual count-and-mark Poisson laws. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

variable {W Y : Type*} [MeasurableSpace W] [MeasurableSpace Y]
variable (μ : Measure Y) [IsProbabilityMeasure μ]

def pointLaw (ψ : W → Y → ℝ) (hψ : Measurable (Function.uncurry ψ))
    (C : ℝ) (hbψ : ∀ w y, |ψ w y| ≤ C) (hψ0 : ∀ w y, 0 ≤ ψ w y)
    (hmean : ∀ w, (∫ y, ψ w y ∂μ) = 1) (w : W) : GeneralTesting.DensityLaw μ where
  density := ψ w
  measurable := hψ.comp (measurable_const.prodMk measurable_id)
  integrable := bounded_integrable μ _
    (hψ.comp (measurable_const.prodMk measurable_id)) C (hbψ w)
  nonneg := Filter.Eventually.of_forall (hψ0 w)
  integral_one := hmean w

/-- The number of points is Poisson with fixed rate, and conditional on that
number their marked positions have density ψ. -/
def observationKernel (ψ : W → Y → ℝ) (_hψ : Measurable (Function.uncurry ψ))
    (rate : ℝ≥0) : Kernel W (PointConfiguration Y) :=
  Kernel.sum fun n =>
    ((Kernel.const W (ENNReal.ofReal (Lower.poissonMass rate n) •
      Measure.pi (fun _ : Fin n => μ))).withDensity
        (fun w xs => ENNReal.ofReal (tensor ψ n w xs))).map (@Sigma.mk ℕ (fun k => Fin k → Y) n)

theorem observationKernel_apply (ψ : W → Y → ℝ) (hψ : Measurable (Function.uncurry ψ))
    (C : ℝ) (hbψ : ∀ w y, |ψ w y| ≤ C) (hψ0 : ∀ w y, 0 ≤ ψ w y)
    (hmean : ∀ w, (∫ y, ψ w y ∂μ) = 1) (rate : ℝ≥0) (w : W) :
    observationKernel μ ψ hψ rate w = Measure.sum fun n =>
      ENNReal.ofReal (Lower.poissonMass rate n) •
        ((LowerMeasure.iidDensityLaw (pointLaw μ ψ hψ C hbψ hψ0 hmean w) n).measure).map (@Sigma.mk ℕ (fun k => Fin k → Y) n) := by
  rw [observationKernel, Kernel.sum_apply]
  congr 1
  funext n
  rw [Kernel.map_apply _ (measurable_point_mk n), Kernel.withDensity_apply _
    (tensor_measurable ψ hψ n).ennreal_ofReal, Kernel.const_apply,
    withDensity_smul_measure, Measure.map_smul]
  · rfl
  · exact (measurable_point_mk n).aemeasurable

theorem observationKernel_isMarkov (ψ : W → Y → ℝ) (hψ : Measurable (Function.uncurry ψ))
    (C : ℝ) (hbψ : ∀ w y, |ψ w y| ≤ C) (hψ0 : ∀ w y, 0 ≤ ψ w y)
    (hmean : ∀ w, (∫ y, ψ w y ∂μ) = 1) (rate : ℝ≥0) :
    IsMarkovKernel (observationKernel μ ψ hψ rate) where
  isProbabilityMeasure w := ⟨by
    rw [observationKernel_apply μ ψ hψ C hbψ hψ0 hmean, Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (measurable_point_mk _) MeasurableSet.univ,
      Set.preimage_univ, measure_univ, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => Lower.poissonMass_nonneg rate rate.2 n)
      (Lower.poissonMass_hasSum rate).summable, (Lower.poissonMass_hasSum rate).tsum_eq]
    norm_num⟩

theorem point_mk_embedding (n : ℕ) : MeasurableEmbedding
    (@Sigma.mk ℕ (fun k => Fin k → Y) n) where
  injective := fun _ _ h => by cases h; rfl
  measurable := measurable_point_mk n
  measurableSet_image' s hs := by
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro m
    change MeasurableSet ((@Sigma.mk ℕ (fun k => Fin k → Y) m) ⁻¹'
      ((@Sigma.mk ℕ (fun k => Fin k → Y) n) '' s))
    by_cases h : m = n
    · subst m
      have he : (@Sigma.mk ℕ (fun k => Fin k → Y) n) ⁻¹'
          ((@Sigma.mk ℕ (fun k => Fin k → Y) n) '' s) = s := by
        ext xs
        constructor
        · rintro ⟨ys, hy, he⟩
          cases he
          exact hy
        · intro hx
          exact ⟨xs, hx, rfl⟩
      rw [he]
      exact hs
    · have he : (@Sigma.mk ℕ (fun k => Fin k → Y) m) ⁻¹'
          ((@Sigma.mk ℕ (fun k => Fin k → Y) n) '' s) = ∅ := by
        ext xs
        constructor
        · rintro ⟨ys, _, he⟩
          have he' := congrArg Sigma.fst he
          exact False.elim (h he'.symm)
        · exact False.elim
      rw [he]
      exact MeasurableSet.empty

/-- Joint measurability on parameter × count-and-mark configurations is
obtained from the actual countable measurable partition. -/
theorem measurable_point_product_function (f : W × PointConfiguration Y → ℝ)
    (hf : ∀ n, Measurable (fun q : W × (Fin n → Y) => f (q.1, ⟨n, q.2⟩))) : Measurable f := by
  intro s hs
  have he : f ⁻¹' s = ⋃ n : ℕ,
      (fun q : W × (Fin n → Y) => (q.1, (⟨n, q.2⟩ : PointConfiguration Y))) ''
        ((fun q : W × (Fin n → Y) => f (q.1, ⟨n, q.2⟩)) ⁻¹' s) := by
    ext q
    constructor
    · intro hq
      exact Set.mem_iUnion.mpr ⟨q.2.1, (q.1, q.2.2), hq, rfl⟩
    · intro hq
      obtain ⟨n, r, hr, heq⟩ := Set.mem_iUnion.mp hq
      change f q ∈ s
      rw [← heq]
      exact hr
  rw [he]
  apply MeasurableSet.iUnion
  intro n
  exact (MeasurableEmbedding.id.prodMap (point_mk_embedding n)).measurableSet_image.mpr (hf n hs)

omit [IsProbabilityMeasure μ] in
theorem processDensityLaw_measure (rate : ℝ≥0)
    (L : ∀ n, GeneralTesting.DensityLaw (Measure.pi (fun _ : Fin n => μ)))
    (hL : ∀ n xs, 0 ≤ (L n).density xs) :
    (processDensityLaw μ rate L hL).measure = Measure.sum fun n =>
      ENNReal.ofReal (Lower.poissonMass rate n) • (L n).measure.map
        (@Sigma.mk ℕ (fun k => Fin k → Y) n) := by
  change (referenceProcess μ rate).withDensity
    (fun x => ENNReal.ofReal ((L x.1).density x.2)) = _
  have hm : Measurable (fun x : PointConfiguration Y => ENNReal.ofReal ((L x.1).density x.2)) :=
    (measurable_point_function _ (fun n => (L n).measurable)).ennreal_ofReal
  rw [referenceProcess, withDensity_sum]
  congr 1
  funext n
  rw [withDensity_smul_measure]
  congr 1
  ext s hs
  rw [withDensity_apply _ hs, Measure.map_apply (measurable_point_mk n) hs,
    GeneralTesting.DensityLaw.measure, withDensity_apply _ ((measurable_point_mk n) hs),
    setLIntegral_map hs hm (measurable_point_mk n)]

theorem observationKernel_eq_withDensity (ψ : W → Y → ℝ) (hψ : Measurable (Function.uncurry ψ))
    (C : ℝ) (hbψ : ∀ w y, |ψ w y| ≤ C) (hψ0 : ∀ w y, 0 ≤ ψ w y)
    (hmean : ∀ w, (∫ y, ψ w y ∂μ) = 1) (rate : ℝ≥0) :
    observationKernel μ ψ hψ rate = (Kernel.const W (referenceProcess μ rate)).withDensity
      (fun w x => ENNReal.ofReal (tensor ψ x.1 w x.2)) := by
  have hm : Measurable (Function.uncurry (fun (w : W) (x : PointConfiguration Y) => tensor ψ x.1 w x.2)) :=
    measurable_point_product_function _ (fun n => tensor_measurable ψ hψ n)
  ext w : 1
  rw [Kernel.withDensity_apply _ hm.ennreal_ofReal, Kernel.const_apply,
    observationKernel_apply μ ψ hψ C hbψ hψ0 hmean]
  let L := fun n => LowerMeasure.iidDensityLaw (pointLaw μ ψ hψ C hbψ hψ0 hmean w) n
  have hL (n : ℕ) (xs : Fin n → Y) : 0 ≤ (L n).density xs := by
    change 0 ≤ ∏ i, ψ w (xs i)
    exact Finset.prod_nonneg fun i _ => hψ0 w (xs i)
  rw [← processDensityLaw_measure μ rate L hL]
  rfl

end RoughRegime.PoissonMeasure
