module

public import RoughRegime.GateLaw
public import RoughRegime.SelectorDerivatives
public import RoughRegime.Model


@[expose] public section
/-! Concrete smooth block functions in the lattice prior construction. The
finite coefficients are actual points of the sampled lattice, and the selector
is proved equal to the source's nearest-integer selector. -/

noncomputable section
namespace RoughRegime.LatticePriors
open Set MeasureTheory
open scoped BigOperators ContDiff
open RoughRegime.LatticeFourier RoughRegime.Lattice

variable {d : ℕ} {ι : Type*} [Fintype ι]

 def coordinateSoftDigit (U : SmoothStep) (γ : ℝ) (a : ℕ) (q : Fin d)
    (x : Model.Covariate d) : ℝ := softDigit U γ ((2 : ℝ) ^ a * x q)

 theorem coordinateSoftDigit_smooth (U : SmoothStep) (γ : ℝ) (a : ℕ) (q : Fin d)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1 / 4) :
    ContDiff ℝ ∞ (coordinateSoftDigit U γ a q) := by
  unfold coordinateSoftDigit
  exact (softDigit_smooth U γ hγ hγ1).comp
    (contDiff_const.mul (contDiff_piLp_apply (𝕜 := ℝ) 2))

 def blockPhase (U : SmoothStep) (M : ℕ) (a : ι → ℕ) (q : ι → Fin d)
    (γ : ι → ℝ) (z : ι → ℤ) (x : Model.Covariate d) : ℝ :=
  ∑ i, latticeStep M * z i * coordinateSoftDigit U (γ i) (a i) (q i) x

 theorem blockPhase_smooth (U : SmoothStep) (M : ℕ) (a : ι → ℕ) (q : ι → Fin d)
    (γ : ι → ℝ) (z : ι → ℤ) (hγ : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i ≤ 1 / 4) :
    ContDiff ℝ ∞ (blockPhase U M a q γ z) := by
  unfold blockPhase
  apply ContDiff.sum
  intro i hi
  exact contDiff_const.mul (coordinateSoftDigit_smooth U (γ i) (a i) (q i) (hγ i) (hγ1 i))

 def blockCoherentSet (a : ι → ℕ) (q : ι → Fin d) (γ : ι → ℝ) :
    Set (Model.Covariate d) :=
  {x | ∀ i, ∀ k : ℤ, γ i ≤ |(2 : ℝ) ^ a i * x (q i) - k|}

 theorem blockPhase_coherence (U : SmoothStep) (M : ℕ) (a : ι → ℕ) (q : ι → Fin d)
    (γ : ι → ℝ) (z : ι → ℤ) (hM : 0 < M)
    (hγ : ∀ i, 0 < γ i) (hγ1 : ∀ i, γ i ≤ 1 / 4)
    (x : Model.Covariate d) (hx : x ∈ blockCoherentSet a q γ) :
    Real.cos ((M : ℝ) * blockPhase U M a q γ z x) = 1 := by
  classical
  let digit : ι → Bool := fun i => decide (Int.floor ((2 : ℝ) ^ a i * x (q i)) % 2 = 1)
  have hd (i : ι) : coordinateSoftDigit U (γ i) (a i) (q i) x =
      if digit i then 1 else 0 := by
    rw [coordinateSoftDigit, softDigit_eq_hardDigit_off_collar U _ _ (hγ i) (hγ1 i) (hx i)]
    have hmod : Int.floor ((2 : ℝ) ^ a i * x (q i)) % 2 = 0 ∨
      Int.floor ((2 : ℝ) ^ a i * x (q i)) % 2 = 1 := by omega
    rcases hmod with h | h <;> simp [digit, h]
  have heq : blockPhase U M a q γ z x =
      ∑ i, (2 * Real.pi / (M : ℝ)) * (z i : ℝ) * if digit i then 1 else 0 := by
    unfold blockPhase latticeStep
    simp_rw [hd]
  rw [heq]
  exact finite_lattice_coherence Finset.univ (M : ℝ) (by exact_mod_cast Nat.ne_of_gt hM) z digit

 def blockGate (Q M : ℕ) (lam η : ι → ℝ) (z : ι → ℤ) : ℝ :=
  ∏ i, gate Q (lam i * η i) (latticeStep M * z i)

 theorem blockGate_range (Q M : ℕ) (lam η : ι → ℝ) (z : ι → ℤ) :
    0 ≤ blockGate Q M lam η z ∧ blockGate Q M lam η z ≤ 1 := by
  unfold blockGate
  exact ⟨Finset.prod_nonneg (fun i _ => gate_nonneg _ _ _),
    Finset.prod_le_one₀ (fun i _ => gate_nonneg _ _ _) (fun i _ => gate_le_one _ _ _)⟩

/-- The finite product estimate allows repeated powers of each coefficient,
with no independence requirement. It implies the paper's bound for distinct indices. -/
 theorem blockGate_weighted_product (Q M : ℕ) (lam η : ι → ℝ) (z : ι → ℤ)
    (r : ι → ℕ) (hr : ∀ i, r i ≤ 2 * Q) (hscale : ∀ i, 0 < lam i * η i) :
    blockGate Q M lam η z * (∏ i, |latticeStep M * z i| ^ r i) ≤
      ∏ i, (lam i * η i) ^ r i := by
  unfold blockGate
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod₀
  · intro i hi
    exact mul_nonneg (gate_nonneg _ _ _) (pow_nonneg (abs_nonneg _) _)
  · intro i hi
    exact gate_weighted_power Q (r i) (hr i) _ _ (hscale i)

 def blockOscillatingDensity (r0 h θ : ℝ) (phase : Model.Covariate d → ℝ)
    (sign : ℝ) (x : Model.Covariate d) : ℝ :=
  r0 + sign * h * Real.cos (θ + phase x)

 def blockDensity (p0 r0 h θ : ℝ) (phase iotaOut : Model.Covariate d → ℝ)
    (sign : ℝ) (x : Model.Covariate d) : ℝ :=
  p0 + iotaOut x * (blockOscillatingDensity r0 h θ phase sign x - p0)

 theorem blockDensity_smooth (p0 r0 h θ sign : ℝ)
    (phase iotaOut : Model.Covariate d → ℝ)
    (hphase : ContDiff ℝ ∞ phase) (hiota : ContDiff ℝ ∞ iotaOut) :
    ContDiff ℝ ∞ (blockDensity p0 r0 h θ phase iotaOut sign) := by
  unfold blockDensity blockOscillatingDensity
  exact contDiff_const.add (hiota.mul (contDiff_const.add
    (contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.add hphase))) |>.sub contDiff_const))

 theorem blockOscillatingDensity_bounds (r0 h θ sign : ℝ)
    (phase : Model.Covariate d → ℝ) (hsign : |sign| ≤ 1) (x : Model.Covariate d) :
    r0 - |h| ≤ blockOscillatingDensity r0 h θ phase sign x ∧
      blockOscillatingDensity r0 h θ phase sign x ≤ r0 + |h| := by
  have hc : |sign * h * Real.cos (θ + phase x)| ≤ |h| := by
    rw [abs_mul, abs_mul]
    calc
      |sign| * |h| * |Real.cos (θ + phase x)| ≤ 1 * |h| * 1 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hsign (abs_nonneg _))
          (Real.abs_cos_le_one _) (abs_nonneg _) (by positivity)
      _ = |h| := by ring
  unfold blockOscillatingDensity
  rcases abs_le.mp hc with ⟨hc0, hc1⟩
  constructor <;> linarith

 theorem blockDensity_bounds (p0 r0 h θ sign lo hi : ℝ)
    (phase iotaOut : Model.Covariate d → ℝ) (hsign : |sign| ≤ 1)
    (hp0 : lo ≤ p0 ∧ p0 ≤ hi) (hr : lo ≤ r0 - |h| ∧ r0 + |h| ≤ hi)
    (hiota : ∀ x, 0 ≤ iotaOut x ∧ iotaOut x ≤ 1) (x : Model.Covariate d) :
    lo ≤ blockDensity p0 r0 h θ phase iotaOut sign x ∧
      blockDensity p0 r0 h θ phase iotaOut sign x ≤ hi := by
  have hb := blockOscillatingDensity_bounds r0 h θ sign phase hsign x
  have ht := hiota x
  unfold blockDensity
  constructor <;> nlinarith

 theorem blockDensity_outside (p0 r0 h θ sign : ℝ)
    (phase iotaOut : Model.Covariate d → ℝ) (x : Model.Covariate d)
    (hx : iotaOut x = 0) : blockDensity p0 r0 h θ phase iotaOut sign x = p0 := by
  simp [blockDensity, hx]

/-- Pointwise cancellation proves that each pair's mass is independent of
all density parameters before taking any expectation. -/
 theorem blockDensity_pair_cancellation (p0 r0 h θ : ℝ)
    (phase iotaOut : Model.Covariate d → ℝ) (x : Model.Covariate d) :
    blockDensity p0 r0 h θ phase iotaOut 1 x +
      blockDensity p0 r0 h θ phase iotaOut (-1) x =
      2 * (p0 + iotaOut x * (r0 - p0)) := by
  unfold blockDensity blockOscillatingDensity
  ring

 theorem total_density_mass (p0 r0 v0 barIota : ℝ)
    (hden : 1 - v0 * barIota ≠ 0)
    (hp0 : p0 = (1 - v0 * barIota * r0) / (1 - v0 * barIota)) :
    p0 * (1 - v0) + v0 * (p0 + barIota * (r0 - p0)) = 1 := by
  rw [hp0]
  field_simp
  ring

/-- The required affine first Fourier mode representation is an identity
of the actual density functions. -/
 theorem blockDensity_theta_decomposition (p0 r0 h θ sign : ℝ)
    (phase iotaOut : Model.Covariate d → ℝ) (x : Model.Covariate d) :
    blockDensity p0 r0 h θ phase iotaOut sign x =
      (p0 + iotaOut x * (r0 - p0)) +
      (sign * h * iotaOut x * Real.cos (phase x)) * Real.cos θ +
      (-(sign * h * iotaOut x * Real.sin (phase x))) * Real.sin θ := by
  unfold blockDensity blockOscillatingDensity
  rw [Real.cos_add]
  ring

 def blockProfile (A σ S : ℝ) (iotaIn p : Model.Covariate d → ℝ)
    (x : Model.Covariate d) : ℝ := A * σ * S * iotaIn x / p x

 theorem blockProfile_smooth (A σ S : ℝ) (iotaIn p : Model.Covariate d → ℝ)
    (hiota : ContDiff ℝ ∞ iotaIn) (hp : ContDiff ℝ ∞ p) (hp0 : ∀ x, p x ≠ 0) :
    ContDiff ℝ ∞ (blockProfile A σ S iotaIn p) := by
  unfold blockProfile
  exact (contDiff_const.mul hiota).div hp hp0

 theorem blockProfile_sup_bound (A σ S rminus : ℝ) (iotaIn p : Model.Covariate d → ℝ)
    (hA : 0 ≤ A) (hrminus : 0 < rminus) (hσ : |σ| ≤ 1)
    (hS : 0 ≤ S ∧ S ≤ 1) (hiota : ∀ x, 0 ≤ iotaIn x ∧ iotaIn x ≤ 1)
    (hp : ∀ x, rminus ≤ p x) (x : Model.Covariate d) :
    |blockProfile A σ S iotaIn p x| ≤ A / rminus := by
  have hp0 : 0 < p x := lt_of_lt_of_le hrminus (hp x)
  have hi := hiota x
  unfold blockProfile
  rw [abs_div, abs_mul, abs_mul, abs_mul, abs_of_nonneg hA,
    abs_of_nonneg hS.1, abs_of_nonneg hi.1, abs_of_pos hp0]
  apply div_le_div₀ hA
  · calc
      A * |σ| * S * iotaIn x ≤ A * 1 * 1 * 1 := by
        apply mul_le_mul
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hσ hA) hS.2 hS.1 (by positivity)
        · exact hi.2
        · exact hi.1
        · positivity
      _ = A := by ring
  · exact hrminus
  · exact hp x

 theorem blockProfile_density_product (A σ S : ℝ) (iotaIn p : Model.Covariate d → ℝ)
    (x : Model.Covariate d) (hp : p x ≠ 0) :
    p x * blockProfile A σ S iotaIn p x = A * σ * S * iotaIn x := by
  unfold blockProfile
  exact mul_div_cancel₀ _ hp

 theorem blockProfile_zero (A σ S : ℝ) (iotaIn p : Model.Covariate d → ℝ)
    (x : Model.Covariate d) (hx : iotaIn x = 0) : blockProfile A σ S iotaIn p x = 0 := by
  simp [blockProfile, hx]

end RoughRegime.LatticePriors
