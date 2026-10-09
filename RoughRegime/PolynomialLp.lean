module

public import RoughRegime.PolynomialSpace


@[expose] public section
/-! Genuine polynomial subspaces of the cube's Lebesgue L² space. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RoughRegime.Model

def polynomialEvaluation {d : ℕ} (p : MvPolynomial (Fin d) ℝ) (x : Covariate d) : ℝ :=
  MvPolynomial.eval (fun i => x i) p

@[fun_prop] theorem polynomialEvaluation_continuous {d : ℕ}
    (p : MvPolynomial (Fin d) ℝ) : Continuous (polynomialEvaluation p) := by
  exact p.continuous_eval.comp (continuous_pi fun i => (EuclideanSpace.proj i).continuous)

theorem polynomialEvaluation_memLp {d : ℕ} (p : MvPolynomial (Fin d) ℝ) :
    MemLp (polynomialEvaluation p) 2 (cubeVolume d) := by
  obtain ⟨B, hB⟩ := (isCompact_cube d).bddAbove_image
    (polynomialEvaluation_continuous p).norm.continuousOn
  apply MemLp.of_bound (polynomialEvaluation_continuous p).aestronglyMeasurable B
  filter_upwards [ae_restrict_mem (measurableSet_cube d)] with x hx
  exact hB ⟨x, hx, rfl⟩

def polynomialToLp (d : ℕ) : MvPolynomial (Fin d) ℝ →ₗ[ℝ] Lp ℝ 2 (cubeVolume d) where
  toFun p := (polynomialEvaluation_memLp p).toLp (polynomialEvaluation p)
  map_add' p q := by
    have h : polynomialEvaluation (p + q) = polynomialEvaluation p + polynomialEvaluation q := by
      ext x
      exact map_add _ _ _
    simpa only [h] using (polynomialEvaluation_memLp p).toLp_add (polynomialEvaluation_memLp q)
  map_smul' a p := by
    have h : polynomialEvaluation (a • p) = a • polynomialEvaluation p := by
      ext x
      simp [polynomialEvaluation, Algebra.smul_def]
    simpa only [h, RingHom.id_apply] using (polynomialEvaluation_memLp p).toLp_const_smul a

@[simp] theorem polynomialToLp_ae {d : ℕ} (p : MvPolynomial (Fin d) ℝ) :
    polynomialToLp d p =ᵐ[cubeVolume d] polynomialEvaluation p :=
  (polynomialEvaluation_memLp p).coeFn_toLp

theorem polynomialToLp_injective (d : ℕ) : Function.Injective (polynomialToLp d) := by
  intro p q hpq
  have hae : polynomialEvaluation p =ᵐ[cubeVolume d] polynomialEvaluation q :=
    (polynomialToLp_ae p).symm.trans (hpq ▸ polynomialToLp_ae q)
  have hcl : closure (interior (cube d)) = cube d := by
    rw [(convex_cube d).closure_interior_eq_closure_of_nonempty_interior
      (cube_nonempty_interior d)]
    exact (isCompact_cube d).isClosed.closure_eq
  have heq := Measure.eqOn_of_ae_eq hae
    (polynomialEvaluation_continuous p).continuousOn
    (polynomialEvaluation_continuous q).continuousOn (by rw [hcl])
  apply MvPolynomial.funext_set (fun _ : Fin d => Icc (0 : ℝ) 1)
    (fun _ => Icc_infinite (by norm_num : (0 : ℝ) < 1))
  intro x hx
  exact heq (x := WithLp.toLp 2 x) (fun i => hx i (mem_univ i))

def polynomialLpSpace (d k : ℕ) : Submodule ℝ (Lp ℝ 2 (cubeVolume d)) :=
  (polynomialSpace d k).map (polynomialToLp d)

instance (d k : ℕ) : FiniteDimensional ℝ (polynomialLpSpace d k) := by
  unfold polynomialLpSpace
  infer_instance

theorem polynomialLpSpace_finrank_le (d k : ℕ) :
    Module.finrank ℝ (polynomialLpSpace d k) ≤ (d + k).choose d := by
  exact (Submodule.finrank_map_le _ _).trans (polynomialSpace_finrank_le d k)

theorem polynomialLpSpace_finrank (d k : ℕ) :
    Module.finrank ℝ (polynomialLpSpace d k) = (d + k).choose d := by
  rw [polynomialLpSpace]
  exact (Submodule.equivMapOfInjective (polynomialToLp d) (polynomialToLp_injective d)
    (polynomialSpace d k)).finrank_eq.symm.trans (polynomialSpace_finrank d k)

theorem polynomialLpSpace_mono (d : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    polynomialLpSpace d k ≤ polynomialLpSpace d l :=
  Submodule.map_mono (polynomialSpace_mono d hkl)

def polynomialLpBasis (d k : ℕ) :
    OrthonormalBasis (Fin (Module.finrank ℝ (polynomialLpSpace d k))) ℝ (polynomialLpSpace d k) :=
  stdOrthonormalBasis ℝ (polynomialLpSpace d k)

theorem polynomialLpBasis_representatives (d k : ℕ)
    (i : Fin (Module.finrank ℝ (polynomialLpSpace d k))) :
    ∃ p : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ k ∧
      polynomialToLp d p = (polynomialLpBasis d k i : Lp ℝ 2 (cubeVolume d)) := by
  obtain ⟨p, hp, he⟩ := (polynomialLpBasis d k i).property
  exact ⟨p, polynomialSpace_degree p hp, he⟩

def basisPolynomial (d k : ℕ)
    (i : Fin (Module.finrank ℝ (polynomialLpSpace d k))) : MvPolynomial (Fin d) ℝ :=
  (polynomialLpBasis_representatives d k i).choose

theorem basisPolynomial_degree (d k : ℕ)
    (i : Fin (Module.finrank ℝ (polynomialLpSpace d k))) :
    (basisPolynomial d k i).totalDegree ≤ k :=
  (polynomialLpBasis_representatives d k i).choose_spec.1

theorem basisPolynomial_toLp (d k : ℕ)
    (i : Fin (Module.finrank ℝ (polynomialLpSpace d k))) :
    polynomialToLp d (basisPolynomial d k i) =
      (polynomialLpBasis d k i : Lp ℝ 2 (cubeVolume d)) :=
  (polynomialLpBasis_representatives d k i).choose_spec.2

theorem basisPolynomial_orthonormal (d k : ℕ) :
    Orthonormal ℝ (fun i => polynomialToLp d (basisPolynomial d k i)) := by
  have h := (polynomialLpSpace d k).subtypeₗᵢ.orthonormal_comp_iff.mpr
    (polynomialLpBasis d k).orthonormal
  change Orthonormal ℝ (fun i => (polynomialLpBasis d k i : Lp ℝ 2 (cubeVolume d))) at h
  simpa only [basisPolynomial_toLp] using h

theorem basisPolynomial_uniform_bound (d k : ℕ) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ i x, x ∈ cube d →
      |polynomialEvaluation (basisPolynomial d k i) x| ≤ B := by
  classical
  have hb (i : Fin (Module.finrank ℝ (polynomialLpSpace d k))) :
      ∃ B : ℝ, ∀ x ∈ cube d, |polynomialEvaluation (basisPolynomial d k i) x| ≤ B := by
    obtain ⟨B, hB⟩ := (isCompact_cube d).bddAbove_image
      (polynomialEvaluation_continuous (basisPolynomial d k i)).abs.continuousOn
    exact ⟨B, fun x hx => hB ⟨x, hx, rfl⟩⟩
  choose B hB using hb
  refine ⟨1 + ∑ i, |B i|, le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => abs_nonneg _)), ?_⟩
  intro i x hx
  have hs : |B i| ≤ ∑ j, |B j| := Finset.single_le_sum
    (fun j _ => abs_nonneg (B j)) (Finset.mem_univ i)
  exact (hB i x hx).trans ((le_abs_self _).trans (by linarith))

end RoughRegime.Model
