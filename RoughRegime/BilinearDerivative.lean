module

public import RoughRegime.ComplexDerivativeBridge
public import RoughRegime.ProjectionApproximation
public import RoughRegime.ProjectionFrame


@[expose] public section
/-! Genuine product-rule and Cauchy bounds for the scalar bilinear polynomial
used in the projection increment of Lemma 6. -/
noncomputable section
open RoughRegime.ComplexDerivativeBridge RoughRegime.ProjectionFrame

namespace RoughRegime.BilinearDerivative

lemma polynomial_eval_differentiable {p : ℕ} (F : MvPolynomial (Fin p) ℝ) :
    Differentiable ℝ (fun x => MvPolynomial.eval x F) :=
  (RoughRegime.PolynomialDerivatives.polynomial_contDiff F).differentiable (by simp)

lemma bilinearPolynomial_eval_sum {p n : ℕ}
    (u v : Fin n → MvPolynomial (Fin p) ℝ) (S : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (x : Fin p → ℝ) :
    MvPolynomial.eval x (RoughRegime.ProjectionApproximation.bilinearPolynomial u S v) =
      ∑ i : Fin n, ∑ j : Fin n, MvPolynomial.eval x (u i) * MvPolynomial.eval x (S i j) * MvPolynomial.eval x (v j) := by
  classical
  simp [RoughRegime.ProjectionApproximation.bilinearPolynomial, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- Exact derivative formula for the actual scalar bilinear polynomial. -/
theorem bilinearPolynomial_fderiv_apply {p n : ℕ}
    (u v : Fin n → MvPolynomial (Fin p) ℝ) (S : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (x w : Fin p → ℝ) :
    fderiv ℝ (fun y => MvPolynomial.eval y (RoughRegime.ProjectionApproximation.bilinearPolynomial u S v)) x w =
      ∑ i : Fin n, ∑ j : Fin n,
        (fderiv ℝ (fun y => MvPolynomial.eval y (u i)) x w * MvPolynomial.eval x (S i j) * MvPolynomial.eval x (v j) +
        MvPolynomial.eval x (u i) * fderiv ℝ (fun y => MvPolynomial.eval y (S i j)) x w * MvPolynomial.eval x (v j) +
        MvPolynomial.eval x (u i) * MvPolynomial.eval x (S i j) * fderiv ℝ (fun y => MvPolynomial.eval y (v j)) x w) := by
  classical
  have hu (i : Fin n) := polynomial_eval_differentiable (u i) x
  have hv (j : Fin n) := polynomial_eval_differentiable (v j) x
  have hS (i j : Fin n) := polynomial_eval_differentiable (S i j) x
  have heq : (fun y => MvPolynomial.eval y (RoughRegime.ProjectionApproximation.bilinearPolynomial u S v)) =
      (fun y => ∑ i : Fin n, ∑ j : Fin n, MvPolynomial.eval y (u i) * MvPolynomial.eval y (S i j) * MvPolynomial.eval y (v j)) := by
    funext y
    exact bilinearPolynomial_eval_sum u v S y
  rw [heq, fderiv_fun_sum (u := Finset.univ) (A := fun i y => ∑ j : Fin n, MvPolynomial.eval y (u i) * MvPolynomial.eval y (S i j) * MvPolynomial.eval y (v j))
    (fun i _ => DifferentiableAt.fun_sum (fun j _ => ((hu i).mul (hS i j)).mul (hv j)))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun j y => MvPolynomial.eval y (u i) * MvPolynomial.eval y (S i j) * MvPolynomial.eval y (v j)) (fun j _ => ((hu i).mul (hS i j)).mul (hv j))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fun_mul (c := fun y => MvPolynomial.eval y (u i) * MvPolynomial.eval y (S i j))
    (d := fun y => MvPolynomial.eval y (v j)) ((hu i).mul (hS i j)) (hv j),
    fderiv_fun_mul (c := fun y => MvPolynomial.eval y (u i)) (d := fun y => MvPolynomial.eval y (S i j)) (hu i) (hS i j)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma real_fderiv_apply_bound {p : ℕ} (F : MvPolynomial (Fin p) ℝ) (x w : Fin p → ℝ)
    (ε A : ℝ) (hε : 0 < ε)
    (hbound : ∀ y : Fin p → ℂ, ‖y - (fun j => (x j : ℂ))‖ < ε → ‖MvPolynomial.eval y (complexify F)‖ ≤ A) :
    ‖fderiv ℝ (fun y => MvPolynomial.eval y F) x w‖ ≤ A * (Real.exp 1 / ε) * ‖w‖ := by
  have h := real_polynomial_derivative_bound F x ε A hε hbound (by decide : 0 < 1) (fun _ => w)
  simpa only [iteratedFDeriv_one_apply, Nat.factorial_one, Nat.cast_one, mul_one, pow_one, Fin.prod_univ_one] using h

lemma real_eval_bound {p : ℕ} (F : MvPolynomial (Fin p) ℝ) (x : Fin p → ℝ)
    (ε A : ℝ) (hε : 0 < ε)
    (hbound : ∀ y : Fin p → ℂ, ‖y - (fun j => (x j : ℂ))‖ < ε → ‖MvPolynomial.eval y (complexify F)‖ ≤ A) :
    ‖MvPolynomial.eval x F‖ ≤ A := by
  have h := hbound (fun j => (x j : ℂ)) (by simpa using hε)
  rw [complexify, MvPolynomial.eval_map] at h
  change ‖MvPolynomial.eval₂ Complex.ofRealHom (Complex.ofRealHom ∘ x) F‖ ≤ A at h
  rw [← MvPolynomial.eval₂_comp] at h
  change ‖(MvPolynomial.eval x F : ℂ)‖ ≤ A at h
  simpa only [Complex.norm_real] using h

lemma coordinate_le_euclidean_norm {n : ℕ} (x : Fin n → ℝ) (i : Fin n) : ‖x i‖ ≤ ‖euclidean x‖ := by
  exact PiLp.norm_apply_le (euclidean x) i

lemma euclidean_norm_le_sqrt_card {p : ℕ} (x : Fin p → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ i, ‖x i‖ ≤ B) : ‖euclidean x‖ ≤ Real.sqrt p * B := by
  classical
  rw [EuclideanSpace.norm_eq]
  have hsum : ∑ i : Fin p, ‖x i‖ ^ 2 ≤ (p : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _i : Fin p, B ^ 2 := Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hb i) 2)
      _ = (p : ℝ) * B ^ 2 := by simp
  have h := Real.sqrt_le_sqrt hsum
  rw [Real.sqrt_mul (Nat.cast_nonneg p), Real.sqrt_sq hB] at h
  exact h

lemma norm_triple_add_le (a b c : ℝ) : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
  (norm_add_le (a + b) c).trans (add_le_add (norm_add_le a b) (le_refl ‖c‖))

def derivativeConstant (n : ℕ) (A ε : ℝ) : ℝ :=
  (n : ℝ) ^ 2 * (A * (Real.exp 1 / ε)) * (A + 1)

/-- Small residual factors are retained by the genuine polynomial product rule;
all entry derivative estimates are derived from their complex ball bounds. -/
theorem bilinearPolynomial_fderiv_direction_bound {p n : ℕ}
    (u v : Fin n → MvPolynomial (Fin p) ℝ) (S : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (x w : Fin p → ℝ) (ε A : ℝ) (hε : 0 < ε) (hA : 0 ≤ A)
    (hu : ∀ i y, ‖y - (fun j => (x j : ℂ))‖ < ε → ‖MvPolynomial.eval y (complexify (u i))‖ ≤ A)
    (hv : ∀ i y, ‖y - (fun j => (x j : ℂ))‖ < ε → ‖MvPolynomial.eval y (complexify (v i))‖ ≤ A)
    (hS : ∀ i j y, ‖y - (fun j => (x j : ℂ))‖ < ε → ‖MvPolynomial.eval y (complexify (S i j))‖ ≤ A) :
    ‖fderiv ℝ (fun y => MvPolynomial.eval y (RoughRegime.ProjectionApproximation.bilinearPolynomial u S v)) x w‖ ≤
      derivativeConstant n A ε *
        (‖euclidean (fun i => MvPolynomial.eval x (u i))‖ + ‖euclidean (fun i => MvPolynomial.eval x (v i))‖ +
          ‖euclidean (fun i => MvPolynomial.eval x (u i))‖ * ‖euclidean (fun i => MvPolynomial.eval x (v i))‖) * ‖w‖ := by
  classical
  let U := ‖euclidean (fun i => MvPolynomial.eval x (u i))‖
  let V := ‖euclidean (fun i => MvPolynomial.eval x (v i))‖
  let D := A * (Real.exp 1 / ε)
  have hUp : 0 ≤ U := norm_nonneg _
  have hVp : 0 ≤ V := norm_nonneg _
  have hDp : 0 ≤ D := by dsimp [D]; positivity
  have hu0 (i : Fin n) : ‖MvPolynomial.eval x (u i)‖ ≤ U := coordinate_le_euclidean_norm (fun i => MvPolynomial.eval x (u i)) i
  have hv0 (j : Fin n) : ‖MvPolynomial.eval x (v j)‖ ≤ V := coordinate_le_euclidean_norm (fun j => MvPolynomial.eval x (v j)) j
  have hS0 (i j : Fin n) : ‖MvPolynomial.eval x (S i j)‖ ≤ A := real_eval_bound (S i j) x ε A hε (hS i j)
  have hdu (i : Fin n) : ‖fderiv ℝ (fun y => MvPolynomial.eval y (u i)) x w‖ ≤ D * ‖w‖ := real_fderiv_apply_bound (u i) x w ε A hε (hu i)
  have hdv (j : Fin n) : ‖fderiv ℝ (fun y => MvPolynomial.eval y (v j)) x w‖ ≤ D * ‖w‖ := real_fderiv_apply_bound (v j) x w ε A hε (hv j)
  have hdS (i j : Fin n) : ‖fderiv ℝ (fun y => MvPolynomial.eval y (S i j)) x w‖ ≤ D * ‖w‖ := real_fderiv_apply_bound (S i j) x w ε A hε (hS i j)
  have hterm (i j : Fin n) :
      ‖fderiv ℝ (fun y => MvPolynomial.eval y (u i)) x w * MvPolynomial.eval x (S i j) * MvPolynomial.eval x (v j) +
        MvPolynomial.eval x (u i) * fderiv ℝ (fun y => MvPolynomial.eval y (S i j)) x w * MvPolynomial.eval x (v j) +
        MvPolynomial.eval x (u i) * MvPolynomial.eval x (S i j) * fderiv ℝ (fun y => MvPolynomial.eval y (v j)) x w‖ ≤
      D * (A + 1) * (U + V + U * V) * ‖w‖ := by
    calc
      _ ≤ ‖fderiv ℝ (fun y => MvPolynomial.eval y (u i)) x w‖ * ‖MvPolynomial.eval x (S i j)‖ * ‖MvPolynomial.eval x (v j)‖ +
        ‖MvPolynomial.eval x (u i)‖ * ‖fderiv ℝ (fun y => MvPolynomial.eval y (S i j)) x w‖ * ‖MvPolynomial.eval x (v j)‖ +
        ‖MvPolynomial.eval x (u i)‖ * ‖MvPolynomial.eval x (S i j)‖ * ‖fderiv ℝ (fun y => MvPolynomial.eval y (v j)) x w‖ := by
        simpa only [norm_mul] using norm_triple_add_le
          (fderiv ℝ (fun y => MvPolynomial.eval y (u i)) x w * MvPolynomial.eval x (S i j) * MvPolynomial.eval x (v j))
          (MvPolynomial.eval x (u i) * fderiv ℝ (fun y => MvPolynomial.eval y (S i j)) x w * MvPolynomial.eval x (v j))
          (MvPolynomial.eval x (u i) * MvPolynomial.eval x (S i j) * fderiv ℝ (fun y => MvPolynomial.eval y (v j)) x w)
      _ ≤ (D * ‖w‖) * A * V + U * (D * ‖w‖) * V + U * A * (D * ‖w‖) := by
        gcongr <;> first | exact hdu i | exact hdv j | exact hdS i j | exact hu0 i | exact hv0 j | exact hS0 i j
      _ ≤ D * (A + 1) * (U + V + U * V) * ‖w‖ := by
        have hc : A * V + U * V + U * A ≤ (A + 1) * (U + V + U * V) := by
          nlinarith [mul_nonneg hA (mul_nonneg hUp hVp)]
        have hm := mul_le_mul_of_nonneg_left hc (mul_nonneg hDp (norm_nonneg w))
        convert hm using 1 <;> ring
  rw [bilinearPolynomial_fderiv_apply]
  calc
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
      ‖fderiv ℝ (fun y => MvPolynomial.eval y (u i)) x w * MvPolynomial.eval x (S i j) * MvPolynomial.eval x (v j) +
        MvPolynomial.eval x (u i) * fderiv ℝ (fun y => MvPolynomial.eval y (S i j)) x w * MvPolynomial.eval x (v j) +
        MvPolynomial.eval x (u i) * MvPolynomial.eval x (S i j) * fderiv ℝ (fun y => MvPolynomial.eval y (v j)) x w‖ := by
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => norm_sum_le _ _))
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, D * (A + 1) * (U + V + U * V) * ‖w‖ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; dsimp [derivativeConstant, D, U, V]; ring

/-- Genuine operator norm bound, with small residuals on both sides. -/
theorem bilinearPolynomial_fderiv_norm_bound {p n : ℕ}
    (u v : Fin n → MvPolynomial (Fin p) ℝ) (S : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (x : Fin p → ℝ) (ε A : ℝ) (hε : 0 < ε) (hA : 0 ≤ A)
    (hu : ∀ i y, ‖y - (fun j => (x j : ℂ))‖ < ε → ‖MvPolynomial.eval y (complexify (u i))‖ ≤ A)
    (hv : ∀ i y, ‖y - (fun j => (x j : ℂ))‖ < ε → ‖MvPolynomial.eval y (complexify (v i))‖ ≤ A)
    (hS : ∀ i j y, ‖y - (fun j => (x j : ℂ))‖ < ε → ‖MvPolynomial.eval y (complexify (S i j))‖ ≤ A) :
    ‖fderiv ℝ (fun y => MvPolynomial.eval y (RoughRegime.ProjectionApproximation.bilinearPolynomial u S v)) x‖ ≤
      derivativeConstant n A ε *
        (‖euclidean (fun i => MvPolynomial.eval x (u i))‖ + ‖euclidean (fun i => MvPolynomial.eval x (v i))‖ +
          ‖euclidean (fun i => MvPolynomial.eval x (u i))‖ * ‖euclidean (fun i => MvPolynomial.eval x (v i))‖) := by
  apply ContinuousLinearMap.opNorm_le_bound
  · unfold derivativeConstant
    positivity
  · intro w
    exact bilinearPolynomial_fderiv_direction_bound u v S x w ε A hε hA hu hv hS

/-- The Euclidean gradient bound required in Lemma 6. -/
theorem bilinearPolynomial_gradient_norm_bound {p n : ℕ}
    (u v : Fin n → MvPolynomial (Fin p) ℝ) (S : Matrix (Fin n) (Fin n) (MvPolynomial (Fin p) ℝ))
    (x : Fin p → ℝ) (ε A : ℝ) (hε : 0 < ε) (hA : 0 ≤ A)
    (hu : ∀ i y, ‖y - (fun j => (x j : ℂ))‖ < ε → ‖MvPolynomial.eval y (complexify (u i))‖ ≤ A)
    (hv : ∀ i y, ‖y - (fun j => (x j : ℂ))‖ < ε → ‖MvPolynomial.eval y (complexify (v i))‖ ≤ A)
    (hS : ∀ i j y, ‖y - (fun j => (x j : ℂ))‖ < ε → ‖MvPolynomial.eval y (complexify (S i j))‖ ≤ A) :
    ‖euclidean (fun j => fderiv ℝ (fun y => MvPolynomial.eval y (RoughRegime.ProjectionApproximation.bilinearPolynomial u S v)) x (Pi.single j 1))‖ ≤
      (Real.sqrt p * derivativeConstant n A ε) *
        (‖euclidean (fun i => MvPolynomial.eval x (u i))‖ + ‖euclidean (fun i => MvPolynomial.eval x (v i))‖ +
          ‖euclidean (fun i => MvPolynomial.eval x (u i))‖ * ‖euclidean (fun i => MvPolynomial.eval x (v i))‖) := by
  have h := euclidean_norm_le_sqrt_card
    (fun j => fderiv ℝ (fun y => MvPolynomial.eval y (RoughRegime.ProjectionApproximation.bilinearPolynomial u S v)) x (Pi.single j 1))
    (derivativeConstant n A ε *
        (‖euclidean (fun i => MvPolynomial.eval x (u i))‖ + ‖euclidean (fun i => MvPolynomial.eval x (v i))‖ +
          ‖euclidean (fun i => MvPolynomial.eval x (u i))‖ * ‖euclidean (fun i => MvPolynomial.eval x (v i))‖))
    (by unfold derivativeConstant; positivity) (fun j => by
      simpa only [Pi.norm_single, norm_one, mul_one] using bilinearPolynomial_fderiv_direction_bound u v S x (Pi.single j 1) ε A hε hA hu hv hS)
  simpa only [mul_assoc] using h

end RoughRegime.BilinearDerivative
