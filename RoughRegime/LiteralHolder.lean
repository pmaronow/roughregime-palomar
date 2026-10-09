module

public import RoughRegime.BoundaryRegularity
public import RoughRegime.ContinuousPartials

@[expose] public section
/-! Exact closed-cube equivalence for the paper's ordinary coordinate-partial
regularity and Holder norm. The source predicate uses genuine one-dimensional
partials and their continuous cube extensions, with no Frechet regularity gate. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff ENNReal
namespace RoughRegime.Model

abbrev CoordinateJetFields (d : ℕ) :=
  (q : ℕ) → (Fin q → Fin d) → Covariate d → ℝ

/-- Ordinary interior coordinate partials with continuous closed-cube extensions. -/
structure CoordinatePartialJet {d : ℕ} (k : ℕ) (f : Covariate d → ℝ)
    (c : CoordinateJetFields d) : Prop where
  zero_eq : ∀ x ∈ cube d, c 0 Fin.elim0 x = f x
  cont : ∀ q ≤ k, ∀ σ, ContinuousOn (c q σ) (cube d)
  hasPartial : ∀ q < k, ∀ σ, ∀ j, ∀ x ∈ interior (cube d),
    HasDerivAt (fun s => c q σ
      (WithLp.toLp 2 (Function.update (fun i => x i) j s)))
      (c (q + 1) (Fin.cons j σ) x) (x j)

def coordinateGradient {d : ℕ} (a : Fin d → ℝ) : Covariate d →L[ℝ] ℝ :=
  ∑ j, (PiLp.proj 2 (fun _ : Fin d => ℝ) j).smulRight (a j)

lemma coordinateGradient_apply_basis {d : ℕ} (a : Fin d → ℝ) (j : Fin d) :
    coordinateGradient a (EuclideanSpace.single j 1) = a j := by
  classical
  simp [coordinateGradient, PiLp.single_apply]

lemma reconstruction_curryLeft {d q : ℕ} (c : (Fin (q + 1) → Fin d) → ℝ) :
    (∑ σ : Fin q → Fin d,
      (coordinateGradient (fun j => c (Fin.cons j σ))).smulRight
        (coordinateTensor d q σ)) = (coordinateReconstruction d (q + 1) c).curryLeft := by
  classical
  have hb : ∀ j : Fin d,
      (∑ σ : Fin q → Fin d,
        (coordinateGradient (fun j => c (Fin.cons j σ))).smulRight
          (coordinateTensor d q σ)) (EuclideanSpace.single j 1) =
        (coordinateReconstruction d (q + 1) c).curryLeft
          (EuclideanSpace.single j 1) := by
    intro j
    apply coordinateEvaluation_injective d q
    funext τ
    change (∑ σ : Fin q → Fin d,
      (coordinateGradient (fun j => c (Fin.cons j σ))).smulRight
        (coordinateTensor d q σ)) (EuclideanSpace.single j 1)
      (fun i => EuclideanSpace.single (τ i) 1) = _
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
    coordinateGradient_apply_basis, smul_apply, coordinateTensor_apply,
    smul_eq_mul]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
    change c (Fin.cons j τ) = (coordinateReconstruction d (q + 1) c).curryLeft
      (EuclideanSpace.single j 1) (fun i => EuclideanSpace.single (τ i) 1)
    rw [ContinuousMultilinearMap.curryLeft_apply]
    have heq : Fin.cons (EuclideanSpace.single j (1 : ℝ))
      (fun i => EuclideanSpace.single (τ i) (1 : ℝ)) =
      (fun i => EuclideanSpace.single ((Fin.cons j τ : Fin (q + 1) → Fin d) i) (1 : ℝ)) := by
      funext i
      refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
    rw [heq]
    exact (congrFun (coordinateEvaluation_reconstruction d (q + 1) c)
    (Fin.cons j τ)).symm
  apply ContinuousLinearMap.ext
  intro v
  have hv := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
  rw [← hv, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [map_smul, EuclideanSpace.basisFun_apply]
  rw [hb j]

lemma hasFDerivAt_coordinateReconstruction {d q : ℕ}
    (c : (Fin q → Fin d) → Covariate d → ℝ)
    (c' : (Fin (q + 1) → Fin d) → ℝ) (x : Covariate d)
    (hc : ∀ σ, HasFDerivAt (c σ)
      (coordinateGradient (fun j => c' (Fin.cons j σ))) x) :
    HasFDerivAt (fun y => coordinateReconstruction d q (fun σ => c σ y))
      (coordinateReconstruction d (q + 1) c').curryLeft x := by
  classical
  rw [← reconstruction_curryLeft]
  simpa only [coordinateReconstruction] using
    HasFDerivAt.fun_sum (u := Finset.univ)
      (fun σ _ => (hc σ).smul_const (coordinateTensor d q σ))

def coordinateJetSeries {d : ℕ} (c : CoordinateJetFields d) :
    Covariate d → FormalMultilinearSeries ℝ (Covariate d) ℝ :=
  fun x q => coordinateReconstruction d q (fun σ => c q σ x)

lemma coordinateJetSeries_zero {d : ℕ} (c : CoordinateJetFields d) (x : Covariate d) :
    (coordinateJetSeries c x 0).curry0 = c 0 Fin.elim0 x := by
  exact congrFun (coordinateEvaluation_reconstruction d 0 (fun σ => c 0 σ x)) Fin.elim0

lemma CoordinatePartialJet.toInteriorTaylorJet_of_fderiv {d k : ℕ}
    {f : Covariate d → ℝ} {c : CoordinateJetFields d}
    (h : CoordinatePartialJet k f c)
    (hd : ∀ q < k, ∀ σ, ∀ x ∈ interior (cube d),
      HasFDerivAt (c q σ)
        (coordinateGradient (fun j => c (q + 1) (Fin.cons j σ) x)) x) :
    InteriorTaylorJet k f (coordinateJetSeries c) where
  zero_eq x hx := (coordinateJetSeries_zero c x).trans (h.zero_eq x hx)
  cont q hq := continuousOn_coordinateReconstruction d q
    (fun x σ => c q σ x) (cube d) (h.cont q hq)
  fderivInterior q hq x hx := hasFDerivAt_coordinateReconstruction
    (c q) (fun σ => c (q + 1) σ x) x (fun σ => hd q hq σ x hx)

lemma CoordinatePartialJet.coordinate_eq_of_fderiv {d k : ℕ}
    {f : Covariate d → ℝ} {c : CoordinateJetFields d}
    (h : CoordinatePartialJet k f c)
    (hd : ∀ q < k, ∀ σ, ∀ x ∈ interior (cube d),
      HasFDerivAt (c q σ)
        (coordinateGradient (fun j => c (q + 1) (Fin.cons j σ) x)) x)
    {q : ℕ} (hq : q ≤ k) (σ : Fin q → Fin d)
    {x : Covariate d} (hx : x ∈ cube d) :
    c q σ x = coordinateDerivative f q σ x := by
  rw [← (h.toInteriorTaylorJet_of_fderiv hd).coordinate_eq hq σ hx]
  exact (congrFun (coordinateEvaluation_reconstruction d q
    (fun σ => c q σ x)) σ).symm

/-- Existence of ordinary mixed partials through order k, continuous on the cube. -/
def CoordinatePartialRegularity {d : ℕ} (k : ℕ) (f : Covariate d → ℝ) : Prop :=
  ∃ c, CoordinatePartialJet k f c

/-- The paper's derivative maximum, computed solely from ordinary partial fields. -/
def literalDerivativeSup {d : ℕ} (c : CoordinateJetFields d) (k : ℕ) : ℝ≥0∞ :=
  ⨆ (q : ℕ) (_ : q ≤ k) (ν : MultiIndex d q) (x : Covariate d) (_ : x ∈ cube d),
    ENNReal.ofReal |c q (multiIndexWord ν) x|

/-- The paper's highest-order Hölder seminorm, from ordinary partial fields. -/
def literalHolderSeminorm {d : ℕ} (c : CoordinateJetFields d) (t : ℝ) : ℝ≥0∞ :=
  ⨆ (ν : MultiIndex d (holderOrder t)) (x : Covariate d) (_ : x ∈ cube d)
    (y : Covariate d) (_ : y ∈ cube d) (_ : x ≠ y),
    ENNReal.ofReal (|c (holderOrder t) (multiIndexWord ν) x -
      c (holderOrder t) (multiIndexWord ν) y| / ‖x-y‖ ^ holderExponent t)

/-- Literal partial-derivative regularity and max-plus-max norm. Invalid regularity
or nonpositive exponent gives infinity; no Fréchet regularity gate is used. -/
def literalHolderNorm {d : ℕ} (f : Covariate d → ℝ) (t : ℝ) : ℝ≥0∞ := by
  classical
  exact if h : 0 < t ∧ CoordinatePartialRegularity (holderOrder t) f then
    literalDerivativeSup (Classical.choose h.2) (holderOrder t) +
      literalHolderSeminorm (Classical.choose h.2) t else ∞

lemma literalDerivativeSup_eq_of_coefficients {d k : ℕ}
    (f : Covariate d → ℝ) (c : CoordinateJetFields d)
    (hc : ∀ q ≤ k, ∀ σ, ∀ x ∈ cube d, c q σ x = coordinateDerivative f q σ x) :
    literalDerivativeSup c k = classicalDerivativeSup f k := by
  unfold literalDerivativeSup classicalDerivativeSup
  apply iSup_congr; intro q
  apply iSup_congr; intro hq
  apply iSup_congr; intro ν
  apply iSup_congr; intro x
  apply iSup_congr; intro hx
  rw [hc q hq (multiIndexWord ν) x hx]
  rfl

lemma literalHolderSeminorm_eq_of_coefficients {d : ℕ}
    (f : Covariate d → ℝ) (c : CoordinateJetFields d) (t : ℝ)
    (hc : ∀ σ, ∀ x ∈ cube d,
      c (holderOrder t) σ x = coordinateDerivative f (holderOrder t) σ x) :
    literalHolderSeminorm c t = classicalHolderSeminorm f t := by
  unfold literalHolderSeminorm classicalHolderSeminorm
  apply iSup_congr; intro ν
  apply iSup_congr; intro x
  apply iSup_congr; intro hx
  apply iSup_congr; intro y
  apply iSup_congr; intro hy
  apply iSup_congr; intro hxy
  rw [hc (multiIndexWord ν) x hx, hc (multiIndexWord ν) y hy]
  rfl


lemma CoordinatePartialJet.fderivInterior {d k : ℕ}
    {f : Covariate d → ℝ} {c : CoordinateJetFields d}
    (h : CoordinatePartialJet k f c) {q : ℕ} (hq : q < k)
    (σ : Fin q → Fin d) {x : Covariate d} (hx : x ∈ interior (cube d)) :
    HasFDerivAt (c q σ)
      (coordinateGradient (fun j => c (q + 1) (Fin.cons j σ) x)) x := by
  exact (RoughRegime.Calculus.continuous_partials_hasStrictFDerivAt_euclidean d
    (c q σ) (fun y j => c (q + 1) (Fin.cons j σ) y)
    (interior (cube d)) isOpen_interior
    (fun j => (h.cont (q + 1) (Nat.succ_le_of_lt hq) (Fin.cons j σ)).mono interior_subset)
    (fun y hy j => h.hasPartial q hq σ j y hy) x hx).hasFDerivAt

theorem CoordinatePartialJet.toInteriorTaylorJet {d k : ℕ}
    {f : Covariate d → ℝ} {c : CoordinateJetFields d}
    (h : CoordinatePartialJet k f c) : InteriorTaylorJet k f (coordinateJetSeries c) :=
  h.toInteriorTaylorJet_of_fderiv (fun _ hq σ _ hx => h.fderivInterior hq σ hx)

theorem CoordinatePartialJet.coordinate_eq {d k : ℕ}
    {f : Covariate d → ℝ} {c : CoordinateJetFields d}
    (h : CoordinatePartialJet k f c) {q : ℕ} (hq : q ≤ k)
    (σ : Fin q → Fin d) {x : Covariate d} (hx : x ∈ cube d) :
    c q σ x = coordinateDerivative f q σ x :=
  h.coordinate_eq_of_fderiv (fun _ hq σ _ hx => h.fderivInterior hq σ hx) hq σ hx

end RoughRegime.Model

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace RoughRegime.Model

theorem continuousOn_coordinateDerivative_of_contDiffOn
    {d k q : ℕ} {f : Covariate d → ℝ}
    (hf : ContDiffOn ℝ k f (cube d)) (hq : q ≤ k) (σ : Fin q → Fin d) :
    ContinuousOn (coordinateDerivative f q σ) (cube d) := by
  have hp := hf.continuousOn_iteratedFDerivWithin
    (show (q : ℕ∞ω) ≤ k by exact_mod_cast hq) (uniqueDiffOn_cube d)
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Covariate d) ℝ
    (fun i => EuclideanSpace.single (σ i) 1)).continuous.comp_continuousOn hp

theorem hasLineDerivAt_coordinateDerivative_of_contDiffOn
    {d k q : ℕ} {f : Covariate d → ℝ}
    (hf : ContDiffOn ℝ k f (cube d)) (hq : q < k) (σ : Fin q → Fin d)
    (j : Fin d) {x : Covariate d} (hx : x ∈ interior (cube d)) :
    HasLineDerivAt ℝ (coordinateDerivative f q σ)
      (coordinateDerivative f (q + 1) (Fin.cons j σ) x) x
      (EuclideanSpace.single j 1) := by
  have hfx : ContDiffAt ℝ k f x := hf.contDiffAt (mem_interior_iff_mem_nhds.mp hx)
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ q f) x :=
    hfx.differentiableAt_iteratedFDeriv (by exact_mod_cast hq)
  let v : Fin q → Covariate d := fun i => EuclideanSpace.single (σ i) 1
  have hg : DifferentiableAt ℝ (fun y => iteratedFDeriv ℝ q f y v) x :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin q => Covariate d) ℝ v).differentiableAt.comp x hd
  have he : coordinateDerivative f q σ =ᶠ[𝓝 x]
      (fun y => iteratedFDeriv ℝ q f y v) := by
    filter_upwards [isOpen_interior.mem_nhds hx] with y hy
    unfold coordinateDerivative
    rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_cube d)
      ((hf.of_le (by exact_mod_cast hq.le)).contDiffAt (mem_interior_iff_mem_nhds.mp hy))
      (interior_subset hy)]
  have hgg : HasFDerivAt (coordinateDerivative f q σ)
      (fderiv ℝ (fun y => iteratedFDeriv ℝ q f y v) x) x :=
    hg.hasFDerivAt.congr_of_eventuallyEq he
  have hnext : coordinateDerivative f (q + 1) (Fin.cons j σ) x =
      fderiv ℝ (fun y => iteratedFDeriv ℝ q f y v) x (EuclideanSpace.single j 1) := by
    unfold coordinateDerivative
    rw [iteratedFDerivWithin_eq_iteratedFDeriv (uniqueDiffOn_cube d)
      (hfx.of_le (by exact_mod_cast (Nat.succ_le_of_lt hq))) (interior_subset hx)]
    have hm : (fun i : Fin (q + 1) =>
        (EuclideanSpace.single ((Fin.cons j σ : Fin (q + 1) → Fin d) i) (1 : ℝ) : Covariate d)) =
        Fin.cons (EuclideanSpace.single j (1 : ℝ) : Covariate d) v := by
      funext i
      refine Fin.cases ?_ (fun _ => ?_) i <;> rfl
    rw [hm]
    simpa only [Fin.tail_cons, Fin.cons_zero] using
      hd.iteratedFDeriv_succ_apply_left' (m := Fin.cons (EuclideanSpace.single j 1) v)
  rw [hnext]
  exact hgg.hasLineDerivAt _

lemma update_eq_add_coordinate {d : ℕ} (x : Covariate d) (j : Fin d) (s : ℝ) :
    WithLp.toLp 2 (Function.update (fun i => x i) j s) =
      x + (s - x j) • EuclideanSpace.single j 1 := by
  classical
  ext i
  by_cases hi : i = j
  · subst i
    simp [PiLp.add_apply, PiLp.smul_apply]
  · simp [hi, PiLp.add_apply, PiLp.smul_apply]

theorem hasDerivAt_coordinateDerivative_update_of_contDiffOn
    {d k q : ℕ} {f : Covariate d → ℝ}
    (hf : ContDiffOn ℝ k f (cube d)) (hq : q < k) (σ : Fin q → Fin d)
    (j : Fin d) {x : Covariate d} (hx : x ∈ interior (cube d)) :
    HasDerivAt (fun s => coordinateDerivative f q σ
      (WithLp.toLp 2 (Function.update (fun i => x i) j s)))
      (coordinateDerivative f (q + 1) (Fin.cons j σ) x) (x j) := by
  have hd := hasLineDerivAt_coordinateDerivative_of_contDiffOn hf hq σ j hx
  change HasDerivAt (fun s => coordinateDerivative f q σ
    (x + s • EuclideanSpace.single j 1)) _ 0 at hd
  have hshift : HasDerivAt (fun s : ℝ => s - x j) 1 (x j) :=
    (hasDerivAt_id (x j)).sub_const (x j)
  simpa only [Function.comp_def, mul_one, update_eq_add_coordinate] using
    hd.comp_of_eq (x j) hshift (by simp)


/-- The paper's ordinary partial regularity equals finite within-cube smoothness. -/
theorem coordinatePartialRegularity_iff_contDiffOn {d : ℕ}
    (k : ℕ) (f : Covariate d → ℝ) :
    CoordinatePartialRegularity k f ↔ ContDiffOn ℝ k f (cube d) := by
  constructor
  · rintro ⟨c, hc⟩
    exact hc.toInteriorTaylorJet.contDiffOn
  · intro hf
    refine ⟨fun q σ x => coordinateDerivative f q σ x, ?_⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      rfl
    · intro q hq σ
      exact continuousOn_coordinateDerivative_of_contDiffOn hf hq σ
    · intro q hq σ j x hx
      exact hasDerivAt_coordinateDerivative_update_of_contDiffOn hf hq σ j hx

/-- Ordinary partial extensions are unique on the closed cube. -/
theorem CoordinatePartialJet.unique {d k : ℕ}
    {f : Covariate d → ℝ} {c c' : CoordinateJetFields d}
    (h : CoordinatePartialJet k f c) (h' : CoordinatePartialJet k f c')
    {q : ℕ} (hq : q ≤ k) (σ : Fin q → Fin d)
    {x : Covariate d} (hx : x ∈ cube d) : c q σ x = c' q σ x := by
  rw [h.coordinate_eq hq σ hx, h'.coordinate_eq hq σ hx]

/-- Exact equality with the literal ordinary-partial definition, including
the closed-cube boundary, finite orders, integer exponents, and infinity. -/
theorem holderNorm_eq_literalHolderNorm {d : ℕ} (f : Covariate d → ℝ) (t : ℝ) :
    holderNorm f t = literalHolderNorm f t := by
  classical
  rw [holderNorm_eq_classicalHolderNorm]
  unfold classicalHolderNorm literalHolderNorm
  by_cases h : 0 < t ∧ CoordinatePartialRegularity (holderOrder t) f
  · have hc : 0 < t ∧ ContDiffOn ℝ (holderOrder t) f (cube d) :=
      ⟨h.1, (coordinatePartialRegularity_iff_contDiffOn _ _).mp h.2⟩
    rw [ite_eq_left hc, dite_eq_left h]
    have hj := Classical.choose_spec h.2
    rw [literalDerivativeSup_eq_of_coefficients f _
      (fun q hq σ x hx => hj.coordinate_eq hq σ hx)]
    rw [literalHolderSeminorm_eq_of_coefficients f _ t
      (fun σ x hx => hj.coordinate_eq le_rfl σ hx)]
  · have hc : ¬ (0 < t ∧ ContDiffOn ℝ (holderOrder t) f (cube d)) := by
      rintro ⟨ht, hf⟩
      exact h ⟨ht, (coordinatePartialRegularity_iff_contDiffOn _ _).mpr hf⟩
    rw [ite_eq_right hc, dite_eq_right h]

end RoughRegime.Model
