module

public import RoughRegime.PoissonProcess


@[expose] public section
open MeasureTheory Set
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace RoughRegime.PoissonCountProduct
open RoughRegime.PoissonMeasure

/-- Finite products of arbitrary nonnegative series expand over every
count vector. Empty products and zero rates are included. -/
theorem prod_tsum {ι : Type*} [Fintype ι] (f : ι → ℕ → ℝ≥0∞) :
    (∏ i, ∑' n, f i n) = ∑' c : ι → ℕ, ∏ i, f i (c i) := by
  classical
  revert f
  refine Fintype.induction_empty_option (P := fun α _ =>
    ∀ f : α → ℕ → ℝ≥0∞, (∏ i, ∑' n, f i n) = ∑' c : α → ℕ, ∏ i, f i (c i)) ?_ ?_ ?_ ι
  · intro α β hβ e h f
    let := Fintype.ofEquiv β e.symm
    rw [← e.prod_comp (fun i => ∑' n, f i n),h]
    rw [← (e.piCongrLeft (fun _ => ℕ)).tsum_eq (fun c => ∏ i, f i (c i))]
    apply tsum_congr
    intro c
    simpa using e.prod_comp (fun i => f i (((e.piCongrLeft (fun _ => ℕ)) c) i))
  · intro f
    simp
  · intro α hα h f
    rw [Fintype.prod_option,h]
    rw [← (Equiv.piOptionEquivProd (β := fun _ : Option α => ℕ)).symm.tsum_eq
      (fun c => ∏ i, f i (c i))]
    simp only [Fintype.prod_option,Equiv.piOptionEquivProd,Equiv.coe_fn_symm_mk]
    rw [ENNReal.tsum_prod',← ENNReal.tsum_mul_right]
    congr 1
    funext a
    dsimp only
    rw [ENNReal.tsum_mul_left]

abbrev CountData (ι Y : Type*) := Σ c : ι → ℕ, (i : ι) → Fin (c i) → Y

/-- Bundle a count vector and its independent mark arrays into component
point configurations. -/
def bundle {ι Y : Type*} (x : CountData ι Y) : ι → PointConfiguration Y :=
  fun i => ⟨x.1 i,x.2 i⟩

def countEquiv {ι Y : Type*} : CountData ι Y ≃ (ι → PointConfiguration Y) where
  toFun := bundle
  invFun x := ⟨fun i => (x i).1,fun i => (x i).2⟩
  left_inv := by rintro ⟨c,xs⟩; rfl
  right_inv := by intro x; funext i; rfl

lemma measurable_bundle_stratum {ι Y : Type*} [MeasurableSpace Y] (c : ι → ℕ) :
    Measurable (fun xs : (i : ι) → Fin (c i) → Y => bundle ⟨c,xs⟩) := by
  apply measurable_pi_iff.mpr
  intro i
  exact (measurable_point_mk (Y := Y) (c i)).comp (measurable_pi_apply i)

lemma measurable_bundle {ι Y : Type*} [MeasurableSpace Y] :
    Measurable (bundle (ι := ι) (Y := Y)) := by
  intro s hs
  exact MeasurableSpace.measurableSet_iInf.mpr (fun c => measurable_bundle_stratum c hs)

/-- Actual count-stratified law of the independent component Poisson
processes. The right side samples the true independent counts, then true
independent mark arrays, then bundles them. -/
theorem referenceProcess_product {ι Y : Type*} [Fintype ι] [MeasurableSpace Y]
    (P : ι → Measure Y) [∀ i, IsProbabilityMeasure (P i)] (rates : ι → ℝ≥0) :
    Measure.pi (fun i => referenceProcess (P i) (rates i)) =
      Measure.sum (fun c : ι → ℕ => (∏ i, ENNReal.ofReal (RoughRegime.Lower.poissonMass (rates i) (c i))) •
        (Measure.pi (fun i => Measure.pi (fun _ : Fin (c i) => P i))).map
          (fun xs => bundle ⟨c,xs⟩)) := by
  classical
  apply Measure.pi_eq
  intro s hs
  rw [Measure.sum_apply _ (MeasurableSet.univ_pi hs)]
  simp only [Measure.smul_apply,smul_eq_mul]
  have hrect (c : ι → ℕ) : (fun xs : (i : ι) → Fin (c i) → Y => bundle ⟨c,xs⟩) ⁻¹' pi univ s =
      pi univ (fun i => (Sigma.mk (c i)) ⁻¹' s i) := by
    ext xs
    simp [bundle,Set.mem_pi]
  simp_rw [Measure.map_apply (measurable_bundle_stratum _) (MeasurableSet.univ_pi hs),hrect,
    Measure.pi_pi]
  simp_rw [← Finset.prod_mul_distrib]
  rw [← prod_tsum (fun i n => ENNReal.ofReal (RoughRegime.Lower.poissonMass (rates i) n) *
    (Measure.pi (fun _ : Fin n => P i)) ((@Sigma.mk ℕ (fun k => Fin k → Y) n) ⁻¹' s i))]
  apply Finset.prod_congr rfl
  intro i _
  rw [referenceProcess,Measure.sum_apply _ (hs i)]
  simp only [Measure.smul_apply,smul_eq_mul,Measure.map_apply (measurable_point_mk _) (hs i)]



lemma point_mk_embedding {Y : Type*} [MeasurableSpace Y] (n : ℕ) :
    MeasurableEmbedding (@Sigma.mk ℕ (fun k => Fin k → Y) n) := by
  classical
  refine ⟨sigma_mk_injective,measurable_point_mk n,?_⟩
  intro s hs
  apply MeasurableSpace.measurableSet_iInf.mpr
  intro k
  change MeasurableSet ((@Sigma.mk ℕ (fun l => Fin l → Y) k) ⁻¹'
    ((@Sigma.mk ℕ (fun l => Fin l → Y) n) '' s))
  by_cases hk : k = n
  · subst k
    simpa only [sigma_mk_injective.preimage_image] using hs
  · have he : (@Sigma.mk ℕ (fun l => Fin l → Y) k) ⁻¹'
        ((@Sigma.mk ℕ (fun l => Fin l → Y) n) '' s) = ∅ := by
      ext xs
      constructor
      · rintro ⟨ys,_,hy⟩
        exact False.elim (hk (congrArg Sigma.fst hy).symm)
      · simp
    rw [he]
    exact MeasurableSet.empty

/-- Products of finitely many measurable embeddings remain measurable
embeddings, without any regularity assumption on the mark spaces. -/
lemma pi_embedding {ι : Type*} [Fintype ι] {X Z : ι → Type*}
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSpace (Z i)]
    (f : (i : ι) → X i → Z i) (hf : ∀ i, MeasurableEmbedding (f i)) :
    MeasurableEmbedding (fun x : (i : ι) → X i => fun i => f i (x i)) := by
  classical
  let F : ((i : ι) → X i) → ((i : ι) → Z i) := fun x i => f i (x i)
  have hm : Measurable F := measurable_pi_iff.mpr (fun i => (hf i).measurable.comp (measurable_pi_apply i))
  have hr : range F = pi univ (fun i => range (f i)) := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact fun i _ => ⟨x i,rfl⟩
    · intro hy
      have hc : ∀ i, ∃ x, f i x = y i := fun i => hy i (mem_univ i)
      refine ⟨fun i => Classical.choose (hc i),?_⟩
      funext i
      exact Classical.choose_spec (hc i)
  have hR : MeasurableSet (range F) := by
    rw [hr]
    exact MeasurableSet.univ_pi (fun i => (hf i).measurableSet_range)
  have hcoord (y : range F) (i : ι) : y.1 i ∈ range (f i) := by
    obtain ⟨x,hx⟩ := y.2
    exact ⟨x i,congrFun hx i⟩
  let G : range F → ((i : ι) → X i) := fun y i => rangeSplitting (f i) ⟨y.1 i,hcoord y i⟩
  have hG : Measurable G := by
    apply measurable_pi_iff.mpr
    intro i
    exact (hf i).measurable_rangeSplitting.comp
      (((measurable_pi_apply i).comp measurable_subtype_coe).subtype_mk)
  apply MeasurableEmbedding.of_measurable_inverse_on_range hm hR hG
  intro x
  funext i
  exact (rightInverse_rangeSplitting (hf i).injective) (x i)

lemma bundle_stratum_embedding {ι Y : Type*} [Fintype ι] [MeasurableSpace Y] (c : ι → ℕ) :
    MeasurableEmbedding (fun xs : (i : ι) → Fin (c i) → Y => bundle ⟨c,xs⟩) :=
  pi_embedding (fun i => Sigma.mk (c i)) (fun i => point_mk_embedding (c i))

lemma bundle_embedding {ι Y : Type*} [Fintype ι] [MeasurableSpace Y] :
    MeasurableEmbedding (bundle (ι := ι) (Y := Y)) := by
  classical
  refine ⟨countEquiv.injective,measurable_bundle,?_⟩
  intro s hs
  have he : bundle '' s = ⋃ c : ι → ℕ,
      (fun xs : (i : ι) → Fin (c i) → Y => bundle ⟨c,xs⟩) '' ((@Sigma.mk (ι → ℕ) (fun c => (i : ι) → Fin (c i) → Y) c) ⁻¹' s) := by
    ext y
    constructor
    · rintro ⟨⟨c,xs⟩,hx,rfl⟩
      exact mem_iUnion.mpr ⟨c,⟨xs,hx,rfl⟩⟩
    · intro hy
      obtain ⟨c,xs,hx,he⟩ := mem_iUnion.mp hy
      exact ⟨⟨c,xs⟩,hx,he⟩
  rw [he]
  apply MeasurableSet.iUnion
  intro c
  apply (bundle_stratum_embedding c).measurableSet_image'
  exact (MeasurableSpace.measurableSet_iInf.mp hs) c

/-- Actual measurable equivalence between count-stratified arrays and
independent count-and-mark configurations. -/
def countMeasurableEquiv {ι Y : Type*} [Fintype ι] [MeasurableSpace Y] :
    CountData ι Y ≃ᵐ (ι → PointConfiguration Y) where
  toEquiv := countEquiv
  measurable_toFun := measurable_bundle
  measurable_invFun := (bundle_embedding (ι := ι) (Y := Y)).measurable_comp_iff.mp (by
    have he : bundle (ι := ι) (Y := Y) ∘ (countEquiv (ι := ι) (Y := Y)).symm = id :=
      (countEquiv (ι := ι) (Y := Y)).self_comp_symm
    rw [he]
    exact measurable_id)

lemma measurable_count_mk {ι Y : Type*} [MeasurableSpace Y] (c : ι → ℕ) :
    Measurable (@Sigma.mk (ι → ℕ) (fun c => (i : ι) → Fin (c i) → Y) c) := by
  intro s hs
  exact (MeasurableSpace.measurableSet_iInf.mp hs) c

/-- The source count-and-mark mixture on the count-stratified space. -/
def countLaw {ι Y : Type*} [Fintype ι] [MeasurableSpace Y]
    (P : ι → Measure Y) (rates : ι → ℝ≥0) : Measure (CountData ι Y) :=
  Measure.sum (fun c : ι → ℕ => (∏ i, ENNReal.ofReal (RoughRegime.Lower.poissonMass (rates i) (c i))) •
    (Measure.pi (fun i => Measure.pi (fun _ : Fin (c i) => P i))).map (Sigma.mk c))

/-- The genuine independent component processes and the genuine countdata
law are related by the actual measurable bundling bijection. -/
theorem map_countLaw_bundle {ι Y : Type*} [Fintype ι] [MeasurableSpace Y]
    (P : ι → Measure Y) [∀ i, IsProbabilityMeasure (P i)] (rates : ι → ℝ≥0) :
    (countLaw P rates).map bundle = Measure.pi (fun i => referenceProcess (P i) (rates i)) := by
  rw [referenceProcess_product,countLaw,Measure.map_sum measurable_bundle.aemeasurable]
  congr 1
  funext c
  rw [Measure.map_smul _ measurable_bundle.aemeasurable,
    Measure.map_map measurable_bundle (measurable_count_mk c)]
  rfl



instance countLaw_isProbabilityMeasure {ι Y : Type*} [Fintype ι] [MeasurableSpace Y]
    (P : ι → Measure Y) [∀ i, IsProbabilityMeasure (P i)] (rates : ι → ℝ≥0) :
    IsProbabilityMeasure (countLaw P rates) where
  measure_univ := by
    have he := congrArg (fun μ : Measure (ι → PointConfiguration Y) => μ univ)
      (map_countLaw_bundle P rates)
    simpa only [Measure.map_apply measurable_bundle MeasurableSet.univ,preimage_univ,measure_univ] using he

/-- Unpacking the independent component processes gives exactly the true
count-stratified mixture, rather than only an equality of count marginals. -/
theorem map_referenceProcess_unpack {ι Y : Type*} [Fintype ι] [MeasurableSpace Y]
    (P : ι → Measure Y) [∀ i, IsProbabilityMeasure (P i)] (rates : ι → ℝ≥0) :
    (Measure.pi (fun i => referenceProcess (P i) (rates i))).map
      (countMeasurableEquiv (ι := ι) (Y := Y)).symm = countLaw P rates := by
  rw [← map_countLaw_bundle P rates,Measure.map_map
    (countMeasurableEquiv (ι := ι) (Y := Y)).symm.measurable measurable_bundle]
  have he : (countMeasurableEquiv (ι := ι) (Y := Y)).symm ∘ bundle = id :=
    (countMeasurableEquiv (ι := ι) (Y := Y)).symm_comp_self
  rw [he,Measure.map_id]

end RoughRegime.PoissonCountProduct
