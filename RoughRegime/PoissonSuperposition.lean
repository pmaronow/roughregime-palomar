module

public import RoughRegime.PoissonProcess
public import RoughRegime.PoissonInterleaving
public import RoughRegime.PoissonCountProduct
public import RoughRegime.PoissonWordCounts
public import RoughRegime.PoissonShuffleWeights
public import RoughRegime.PoissonMarkMaps


@[expose] public section
/-! Actual finite-component superposition of ordered Poisson observations.
The ordering randomization uses only the observed counts and named slots. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace RoughRegime.PoissonSuperposition
open PoissonMeasure PoissonInterleaving
set_option backward.isDefEq.respectTransparency false

variable {ι Y : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Y]

/-- Forget the component grouping but retain every named point slot. -/
def flattenMarks (c : ι → ℕ) (xs : (i : ι) → Fin (c i) → Y) : Slots c → Y :=
  fun s => xs s.1 s.2

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_flattenMarks (c : ι → ℕ) : Measurable (flattenMarks (Y := Y) c) := by
  apply Measurable.of_eval
  intro s
  exact (measurable_pi_apply s.2).comp (measurable_pi_apply s.1)

omit [DecidableEq ι] in
/-- The nested independent component-mark law is precisely the independent
law on all named point slots. -/
theorem flattenMarks_map (c : ι → ℕ) (P : ι → Measure Y)
    [∀ i, IsProbabilityMeasure (P i)] :
    (Measure.pi (fun i => Measure.pi (fun _ : Fin (c i) => P i))).map
      (flattenMarks c) = Measure.pi (fun s : Slots c => P s.1) := by
  classical
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (measurable_flattenMarks c)]
  · have he : (flattenMarks c) ⁻¹' (univ.pi s) =
        univ.pi (fun i => univ.pi (fun j : Fin (c i) => s ⟨i,j⟩)) := by
      ext x
      simp only [mem_preimage,mem_pi,mem_univ,true_implies,flattenMarks]
      exact ⟨fun h i j => h ⟨i,j⟩,fun h a => h a.1 a.2⟩
    rw [he,Measure.pi_pi]
    simp only [Measure.pi_pi]
    exact (Fintype.prod_sigma (fun a : Slots c => P a.1 (s a))).symm
  · exact MeasurableSet.pi (Set.to_countable _) (fun i _ => hs i)

omit [DecidableEq ι] in
/-- Read every named point in a chosen bijective order. -/
def orderedMarks (c : ι → ℕ) (e : Fin (∑ i, c i) ≃ Slots c)
    (xs : (i : ι) → Fin (c i) → Y) : Fin (∑ i, c i) → Y :=
  fun k => xs (e k).1 (e k).2

omit [DecidableEq ι] in
theorem measurable_orderedMarks (c : ι → ℕ) (e : Fin (∑ i, c i) ≃ Slots c) :
    Measurable (orderedMarks (Y := Y) c e) := by
  apply Measurable.of_eval
  intro k
  exact (measurable_pi_apply (e k).2).comp (measurable_pi_apply (e k).1)

omit [DecidableEq ι] in
/-- Given an ordering, all marks remain independent and their laws are the
laws indexed by the component-label word of that ordering. -/
theorem orderedMarks_map (c : ι → ℕ) (e : Fin (∑ i, c i) ≃ Slots c)
    (P : ι → Measure Y) [∀ i, IsProbabilityMeasure (P i)] :
    (Measure.pi (fun i => Measure.pi (fun _ : Fin (c i) => P i))).map
      (orderedMarks c e) = Measure.pi (fun k => P (e k).1) := by
  have h := (measurePreserving_piCongrLeft (fun k : Fin (∑ i, c i) => P (e k).1) e.symm).map_eq
  have hf : orderedMarks (Y := Y) c e =
      (MeasurableEquiv.piCongrLeft (fun _ : Fin (∑ i, c i) => Y) e.symm) ∘ flattenMarks c := by
    funext xs k
    simp [orderedMarks,flattenMarks,MeasurableEquiv.piCongrLeft,Equiv.piCongrLeft]
  rw [hf,← Measure.map_map (MeasurableEquiv.measurable _) (measurable_flattenMarks c),
    flattenMarks_map]
  simpa only [Equiv.apply_symm_apply] using h

/-- A finite mixture of mark probability laws. -/
def markMixture (w : ι → ℝ≥0) (P : ι → Measure Y) : Measure Y :=
  ∑ i, (w i : ℝ≥0∞) • P i

omit [DecidableEq ι] in
theorem markMixture_probability (w : ι → ℝ≥0) (P : ι → Measure Y)
    [∀ i, IsProbabilityMeasure (P i)] (hw : ∑ i, w i = 1) :
    IsProbabilityMeasure (markMixture w P) where
  measure_univ := by
    simp only [markMixture,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one]
    rw [← ENNReal.ofNNReal_finsetSum,hw]
    rfl

omit [DecidableEq ι] in
/-- Expand the actual independent law of mixture marks into all finite
component-label words. This is a measure identity, including arbitrary
measurable mark spaces. -/
theorem pi_markMixture (w : ι → ℝ≥0) (P : ι → Measure Y)
    [∀ i, IsProbabilityMeasure (P i)] (hw : ∑ i, w i = 1) (N : ℕ) :
    Measure.pi (fun _ : Fin N => markMixture w P) =
      ∑ a : Fin N → ι, (∏ k, (w (a k) : ℝ≥0∞)) •
        Measure.pi (fun k => P (a k)) := by
  have : IsProbabilityMeasure (markMixture w P) := markMixture_probability w P hw
  apply Measure.pi_eq
  intro s hs
  simp only [Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul,Measure.pi_pi]
  simp only [markMixture,Measure.finsetSum_apply,Measure.smul_apply,smul_eq_mul]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact (Finset.prod_mul_distrib).symm

/-- The conditional uniform shuffle law. All named points are retained;
each bijective ordering has probability 1/N!. -/
def shuffleMeasure (c : ι → ℕ) (xs : (i : ι) → Fin (c i) → Y) :
    Measure (PointConfiguration Y) :=
  ((∑ i, c i).factorial : ℝ≥0∞)⁻¹ •
    ∑ e : Fin (∑ i, c i) ≃ Slots c,
      Measure.dirac ⟨∑ i, c i,orderedMarks c e xs⟩

theorem measurable_shuffleMeasure (c : ι → ℕ) :
    Measurable (shuffleMeasure (Y := Y) c) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [shuffleMeasure,Measure.smul_apply,Measure.finsetSum_apply,smul_eq_mul,
    Measure.dirac_apply' _ hs]
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro e _
  exact measurable_const.indicator
    (((measurable_point_mk (Y := Y) (∑ i, c i)).comp (measurable_orderedMarks c e)) hs)

instance shuffleMeasure_probability (c : ι → ℕ) (xs : (i : ι) → Fin (c i) → Y) :
    IsProbabilityMeasure (shuffleMeasure c xs) where
  measure_univ := by
    classical
    simp only [shuffleMeasure,Measure.smul_apply,Measure.finsetSum_apply,smul_eq_mul,
      Measure.dirac_apply_of_mem (Set.mem_univ _),Finset.sum_const,Finset.card_univ,
      slotEquivCard,nsmul_eq_mul,mul_one]
    exact ENNReal.inv_mul_cancel (by simp [Nat.factorial_ne_zero]) (by simp)

/-- A genuine parameter-independent Markov kernel for a fixed count vector. -/
def shuffleAt (c : ι → ℕ) : Kernel ((i : ι) → Fin (c i) → Y) (PointConfiguration Y) :=
  ⟨shuffleMeasure c,measurable_shuffleMeasure c⟩

instance shuffleAt_markov (c : ι → ℕ) : IsMarkovKernel (shuffleAt (Y := Y) c) :=
  ⟨fun _ => shuffleMeasure_probability _ _⟩

/-- The source and target configuration count bundles; the index is
countable and the sigma measurable space makes each fixed-count kernel
measurable without imposing a topology on marks. -/
abbrev CountData (ι Y : Type*) := Σ c : ι → ℕ, (i : ι) → Fin (c i) → Y

/-- Uniformly interleave all component observations, conditionally on their
actual observed counts. Its definition is independent of every component
probability law and all statistical parameters. -/
def shuffleKernel : Kernel (CountData ι Y) (PointConfiguration Y) where
  toFun z := shuffleAt z.1 z.2
  measurable' := by
    intro s hs
    exact MeasurableSpace.measurableSet_iInf.mpr fun c => (shuffleAt (Y := Y) c).measurable' hs

instance shuffleKernel_markov : IsMarkovKernel (shuffleKernel (ι := ι) (Y := Y)) :=
  ⟨fun z => shuffleAt_markov z.1 |>.isProbabilityMeasure z.2⟩

/-- Exact fixed-count output law of the actual uniform shuffle kernel. -/
theorem shuffleAt_comp (c : ι → ℕ) (P : ι → Measure Y)
    [∀ i, IsProbabilityMeasure (P i)] :
    shuffleAt c ∘ₘ Measure.pi (fun i => Measure.pi (fun _ : Fin (c i) => P i)) =
      ((∑ i, c i).factorial : ℝ≥0∞)⁻¹ •
        ∑ e : Fin (∑ i, c i) ≃ Slots c,
          (Measure.pi (fun k => P (e k).1)).map (Sigma.mk (∑ i, c i)) := by
  classical
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  simp only [shuffleAt,Kernel.coe_mk,shuffleMeasure,Measure.smul_apply,
    Measure.finsetSum_apply,smul_eq_mul]
  rw [lintegral_const_mul']
  · rw [lintegral_finsetSum]
    · apply congrArg (fun z : ℝ≥0∞ => ((∑ i, c i).factorial : ℝ≥0∞)⁻¹ * z)
      apply Finset.sum_congr rfl
      intro e _
      rw [Measure.map_apply (measurable_point_mk _) hs,
        ← orderedMarks_map c e P,
        Measure.map_apply (measurable_orderedMarks c e) ((measurable_point_mk _) hs)]
      simp only [Measure.dirac_apply' _ hs]
      rw [← lintegral_indicator_one]
      · rfl
      · exact (measurable_orderedMarks c e) ((measurable_point_mk _) hs)
    · intro e _
      exact (Measure.measurable_coe hs).comp
        (Measure.measurable_dirac.comp ((measurable_point_mk _).comp (measurable_orderedMarks c e)))
  · exact ENNReal.inv_ne_top.mpr (by simp [Nat.factorial_ne_zero])

/-- Grouping the uniform orderings by their label words gives the exact
multinomial fixed-count output law. -/
theorem shuffleAt_comp_labels (c : ι → ℕ) (P : ι → Measure Y)
    [∀ i, IsProbabilityMeasure (P i)] :
    shuffleAt c ∘ₘ Measure.pi (fun i => Measure.pi (fun _ : Fin (c i) => P i)) =
      ((∑ i, c i).factorial : ℝ≥0∞)⁻¹ •
        ∑ a : Fin (∑ i, c i) → ι,
          (if ∀ i, labelCount c a i = c i then ∏ i, (c i).factorial else 0) •
            (Measure.pi (fun k => P (a k))).map (Sigma.mk (∑ i, c i)) := by
  rw [shuffleAt_comp]
  exact congrArg (fun μ : Measure (PointConfiguration Y) => ((∑ i, c i).factorial : ℝ≥0∞)⁻¹ • μ)
    (sum_by_label_word (R := Measure (PointConfiguration Y)) c (fun a : Fin (∑ i, c i) → ι => (Measure.pi (fun k : Fin (∑ i, c i) => P (a k))).map (Sigma.mk (∑ i, c i))))

/-- Product of mark-mixture weights in a compatible label word. -/
theorem prod_word_weights {M : Type*} [CommMonoid M] (c : ι → ℕ)
    (a : Fin (∑ i, c i) → ι) (w : ι → M)
    (ha : ∀ i, labelCount c a i = c i) :
    ∏ k, w (a k) = ∏ i, w i ^ c i := by
  rw [← Fintype.prod_fiberwise' a w]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_subtype]
  rw [← ha i]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem measurable_count_mk (c : ι → ℕ) :
    Measurable (@Sigma.mk (ι → ℕ) (fun c => (i : ι) → Fin (c i) → Y) c) := by
  intro s hs
  exact (MeasurableSpace.measurableSet_iInf.mp hs) c

/-- The joint law of independent component counts and their independent
mark lists, expressed on the actual count-data measurable space. -/
def countProcess (P : ι → Measure Y) (r : ι → ℝ≥0) : Measure (CountData ι Y) :=
  Measure.sum fun c => (∏ i, ENNReal.ofReal (Lower.poissonMass (r i) (c i))) •
    (Measure.pi (fun i => Measure.pi (fun _ : Fin (c i) => P i))).map (Sigma.mk c)

/-- Kernel composition after a measurable data transformation. -/
theorem kernel_comp_map {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (f : A → B) (hf : Measurable f)
    (K : Kernel B C) : K ∘ₘ μ.map f = K.comap f hf ∘ₘ μ := by
  ext s hs
  rw [Measure.bind_apply hs K.aemeasurable,
    lintegral_map (K.measurable_coe hs) hf,
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  rfl

/-- Exact count-stratified output of the genuine common shuffle kernel. -/
theorem shuffleKernel_comp_countProcess (P : ι → Measure Y) (r : ι → ℝ≥0)
    [∀ i, IsProbabilityMeasure (P i)] :
    shuffleKernel ∘ₘ countProcess P r =
      Measure.sum fun c => (∏ i, ENNReal.ofReal (Lower.poissonMass (r i) (c i))) •
        (shuffleAt c ∘ₘ Measure.pi (fun i => Measure.pi (fun _ : Fin (c i) => P i))) := by
  rw [countProcess,Measure.bind_sum _ _ (Kernel.aemeasurable _)]
  congr 1
  funext c
  rw [Measure.bind_smul _ _ (Kernel.aemeasurable _),
    kernel_comp_map _ _ (measurable_count_mk c)]
  rfl

/-- Normalize fixed component intensities into mark-mixture weights. -/
def rateWeights (r : ι → ℝ≥0) : ι → ℝ≥0 := fun i => r i / ∑ j, r j

omit [DecidableEq ι] in
theorem rateWeights_sum (r : ι → ℝ≥0) (hr : 0 < ∑ i, r i) :
    ∑ i, rateWeights r i = 1 := by
  simp only [rateWeights,← Finset.sum_div]
  exact div_self (ne_of_gt hr)

omit [DecidableEq ι] in
/-- The actual ordered total Poisson law, expanded into component-label
words. This gives the target distribution before any superposition proof. -/
theorem referenceProcess_markMixture_apply (w : ι → ℝ≥0) (P : ι → Measure Y)
    [∀ i, IsProbabilityMeasure (P i)] (hw : ∑ i, w i = 1) (rate : ℝ≥0)
    (s : Set (PointConfiguration Y)) (hs : MeasurableSet s) :
    referenceProcess (markMixture w P) rate s =
      ∑' N : ℕ, ∑ a : Fin N → ι, ENNReal.ofReal (Lower.poissonMass rate N) *
        (∏ k, (w (a k) : ℝ≥0∞)) *
          (Measure.pi (fun k => P (a k))).map (Sigma.mk N) s := by
  classical
  have : IsProbabilityMeasure (markMixture w P) := markMixture_probability w P hw
  rw [referenceProcess,Measure.sum_apply _ hs]
  apply tsum_congr
  intro N
  rw [pi_markMixture w P hw N,
    Measure.map_finset_sum' (measurable_point_mk _).aemeasurable]
  simp only [Measure.smul_apply,smul_eq_mul,Measure.finsetSum_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Measure.map_smul _ (measurable_point_mk _).aemeasurable,Measure.smul_apply]
  simp only [smul_eq_mul,mul_assoc]

/-- The true count-process output, expanded into compatible label words.
All intensity dependence is outside the common shuffle kernel. -/
theorem shuffleKernel_comp_countProcess_apply (P : ι → Measure Y) (r : ι → ℝ≥0)
    [∀ i, IsProbabilityMeasure (P i)] (s : Set (PointConfiguration Y))
    (hs : MeasurableSet s) :
    (shuffleKernel ∘ₘ countProcess P r) s =
      ∑' c : ι → ℕ, ∑ a : Fin (∑ i, c i) → ι,
        if ∀ i, labelCount c a i = c i then
          ((∏ i, ENNReal.ofReal (Lower.poissonMass (r i) (c i))) *
            (∏ i, ((c i).factorial : ℝ≥0∞)) / ((∑ i, c i).factorial : ℝ≥0∞)) *
              (Measure.pi (fun k => P (a k))).map (Sigma.mk (∑ i, c i)) s
        else 0 := by
  classical
  rw [shuffleKernel_comp_countProcess,Measure.sum_apply _ hs]
  apply tsum_congr
  intro c
  rw [shuffleAt_comp_labels]
  simp only [Measure.smul_apply,smul_eq_mul,Measure.finsetSum_apply]
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : ∀ i, labelCount c a i = c i
  · rw [ite_eq_left ha,ite_eq_left ha]
    simp only [nsmul_eq_mul,Nat.cast_prod,div_eq_mul_inv]
    ac_rfl
  · simp [ha]

/-- Reindex all compatible label words by their actual total length. -/
theorem tsum_compatible_words (F : PoissonMeasure.LabelWord ι → ℝ≥0∞) :
    (∑' c : ι → ℕ, ∑ a : Fin (∑ i, c i) → ι,
      if ∀ i, labelCount c a i = c i then F ⟨∑ i, c i,a⟩ else 0) =
      ∑' N : ℕ, ∑ a : Fin N → ι, F ⟨N,a⟩ := by
  classical
  calc
    _ = ∑' c : ι → ℕ,
        ∑' a : {a : Fin (∑ i, c i) → ι // ∀ i, WordCount a i = c i},
          F ⟨∑ i, c i,a.1⟩ := by
      apply tsum_congr
      intro c
      have hh := tsum_subtype {a : Fin (∑ i, c i) → ι | ∀ i, WordCount a i = c i}
        (fun a => F ⟨∑ i, c i,a⟩)
      calc
        _ = ∑' a : Fin (∑ i, c i) → ι,
            ({a | ∀ i, WordCount a i = c i} : Set (Fin (∑ i, c i) → ι)).indicator
              (fun a => F ⟨∑ i, c i,a⟩) a := by
          rw [tsum_fintype]
          apply Finset.sum_congr rfl
          intro a _
          simp only [Set.indicator,Set.mem_ofPred_eq]
          have hc : (∀ i, labelCount c a i = c i) ↔ ∀ i, WordCount a i = c i := by
            simp only [WordCount,Fintype.card_subtype,labelCount]
          simp only [hc]
        _ = _ := hh.symm
    _ = ∑' z : ((c : ι → ℕ) × {a : Fin (∑ i, c i) → ι // ∀ i, WordCount a i = c i}),
        F (countWordEquiv z) := by
      rw [ENNReal.tsum_sigma']
      rfl
    _ = ∑' w : PoissonMeasure.LabelWord ι, F w := countWordEquiv.tsum_eq F
    _ = _ := by
      rw [ENNReal.tsum_sigma']
      apply tsum_congr
      intro N
      exact tsum_fintype _

/-- Superposition theorem for the actual count-and-mark processes: sampling
independent component counts and then applying the common uniform shuffle
has exactly the total Poisson law with rate-weighted iid mixture marks. -/
theorem shuffleKernel_comp_countProcess_eq (P : ι → Measure Y) (r : ι → ℝ≥0)
    [∀ i, IsProbabilityMeasure (P i)] (hr : 0 < ∑ i, r i) :
    shuffleKernel ∘ₘ countProcess P r =
      referenceProcess (markMixture (rateWeights r) P) (∑ i, r i) := by
  classical
  ext s hs
  rw [shuffleKernel_comp_countProcess_apply P r s hs,
    referenceProcess_markMixture_apply _ P (rateWeights_sum r hr) _ s hs]
  rw [← tsum_compatible_words (fun w =>
    ENNReal.ofReal (Lower.poissonMass ((∑ i, r i : ℝ≥0) : ℝ) w.1) *
      (∏ k, (rateWeights r (w.2 k) : ℝ≥0∞)) *
        (Measure.pi (fun k => P (w.2 k))).map (Sigma.mk w.1) s)]
  apply tsum_congr
  intro c
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : ∀ i, labelCount c a i = c i
  · rw [ite_eq_left ha,ite_eq_left ha,poisson_shuffle_weight r c hr,
      prod_word_weights c a (fun i => (rateWeights r i : ℝ≥0∞)) ha]
    simp only [rateWeights,NNReal.coe_sum]
  · rw [ite_eq_right ha,ite_eq_right ha]

/-- Actual parameter-independent shuffle kernel on the original independent
component point-configuration data, through its measurable unpacking. -/
def superpositionKernel : Kernel (ι → PointConfiguration Y) (PointConfiguration Y) :=
  shuffleKernel.comap PoissonCountProduct.countMeasurableEquiv.symm
    PoissonCountProduct.countMeasurableEquiv.symm.measurable

instance superpositionKernel_markov : IsMarkovKernel (superpositionKernel (ι := ι) (Y := Y)) := by
  unfold superpositionKernel
  infer_instance

/-- Full actual independent-process superposition law. The kernel depends
only on the observed configurations; component rates and laws may vary. -/
theorem superpositionKernel_comp (P : ι → Measure Y) (r : ι → ℝ≥0)
    [∀ i, IsProbabilityMeasure (P i)] (hr : 0 < ∑ i, r i) :
    superpositionKernel ∘ₘ Measure.pi (fun i => referenceProcess (P i) (r i)) =
      referenceProcess (markMixture (rateWeights r) P) (∑ i, r i) := by
  rw [superpositionKernel,← kernel_comp_map _ _
    PoissonCountProduct.countMeasurableEquiv.symm.measurable,
    PoissonCountProduct.map_referenceProcess_unpack]
  exact shuffleKernel_comp_countProcess_eq P r hr

/-- A fixed measurable spatial transformation of each component followed
by the genuine common uniform superposition kernel. -/
def spatialSuperpositionKernel {X : Type*} [MeasurableSpace X]
    (f : ι → X → Y) (hf : ∀ i, Measurable (f i)) :
    Kernel (ι → PointConfiguration X) (PointConfiguration Y) :=
  superpositionKernel.comap (componentPointMap f) (measurable_componentPointMap f hf)

instance spatialSuperpositionKernel_markov {X : Type*} [MeasurableSpace X]
    (f : ι → X → Y) (hf : ∀ i, Measurable (f i)) :
    IsMarkovKernel (spatialSuperpositionKernel f hf) := by
  unfold spatialSuperpositionKernel
  infer_instance

/-- Actual process law after the local component marks are placed into the
common observation space. Extra fixed outside components are allowed. -/
theorem spatialSuperpositionKernel_comp {X : Type*} [MeasurableSpace X]
    (P : ι → Measure X) [∀ i, IsProbabilityMeasure (P i)] (r : ι → ℝ≥0)
    (hr : 0 < ∑ i, r i) (f : ι → X → Y) (hf : ∀ i, Measurable (f i)) :
    spatialSuperpositionKernel f hf ∘ₘ Measure.pi (fun i => referenceProcess (P i) (r i)) =
      referenceProcess (markMixture (rateWeights r) (fun i => (P i).map (f i))) (∑ i, r i) := by
  rw [spatialSuperpositionKernel,← kernel_comp_map _ _ (measurable_componentPointMap f hf),
    referenceProcess_product_map P r f hf]
  exact superpositionKernel_comp _ r hr

end RoughRegime.PoissonSuperposition
