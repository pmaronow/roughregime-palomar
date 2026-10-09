module

public import RoughRegime.LatticeFourier
public import RoughRegime.SincDecay


@[expose] public section
namespace RoughRegime.LatticeFourier

open MeasureTheory Set Real Complex
open scoped FourierTransform Convolution Pointwise

/-- Compactly supported inverse-transform kernel for an even sinc power. -/
noncomputable def sincKernel (Q : ℕ) (η : ℝ) : ℝ → ℂ :=
  trianglePower (1 / (2 * Real.pi * η)) (Q - 1)

theorem sincKernel_continuous (Q : ℕ) (η : ℝ) : Continuous (sincKernel Q η) :=
  trianglePower_continuous _ _

theorem sincKernel_integrable (Q : ℕ) (η : ℝ) : Integrable (sincKernel Q η) :=
  trianglePower_integrable _ _

theorem sincKernel_hasCompactSupport (Q : ℕ) (η : ℝ) : HasCompactSupport (sincKernel Q η) :=
  trianglePower_hasCompactSupport _ _

theorem sincKernel_fourier (Q : ℕ) (η : ℝ) (hQ : 1 ≤ Q) (hη : 0 < η) (w : ℝ) :
    𝓕 (sincKernel Q η) w = scaledSincPower Q η w := by
  unfold sincKernel
  rw [trianglePower_fourier _ (by positivity)]
  unfold scaledSincPower
  have hsub : Q - 1 + 1 = Q := by omega
  rw [hsub]
  congr 3
  field_simp

theorem sincKernel_support_subset (Q : ℕ) (η : ℝ) (hQ : 1 ≤ Q) :
    Function.support (sincKernel Q η) ⊆ Icc (-(Q : ℝ) / (Real.pi * η)) (Q / (Real.pi * η)) := by
  have hsub : Q - 1 + 1 = Q := by omega
  have hsubR : ((Q - 1 : ℕ) : ℝ) + 1 = Q := by exact_mod_cast hsub
  have h := trianglePower_support_subset (1 / (2 * Real.pi * η)) (Q - 1)
  rw [hsubR] at h
  unfold sincKernel
  convert h using 1
  congr 1 <;> simp [div_eq_mul_inv, mul_inv_rev] <;> ring

theorem scaledSincPower_fourier (Q : ℕ) (η : ℝ) (hQ : 1 ≤ Q) (hη : 0 < η) (w : ℝ) :
    𝓕 (scaledSincPower Q η) w = sincKernel Q η (-w) := by
  have hfun : 𝓕 (sincKernel Q η) = scaledSincPower Q η :=
    funext (sincKernel_fourier Q η hQ hη)
  have hFi : Integrable (𝓕 (sincKernel Q η)) := by
    rw [hfun]
    exact scaledSincPower_integrable Q η hQ hη
  have h := (sincKernel_integrable Q η).fourierInv_fourier_eq hFi
    ((sincKernel_continuous Q η).continuousAt (x := -w))
  rw [Real.fourierInv_eq_fourier_neg, neg_neg, hfun] at h
  exact h

/-- Exact Fourier support of the even sinc power. -/
theorem scaledSincPower_fourier_eq_zero (Q : ℕ) (η : ℝ) (hQ : 1 ≤ Q) (hη : 0 < η)
    (w : ℝ) (hw : (Q : ℝ) / (Real.pi * η) < |w|) :
    𝓕 (scaledSincPower Q η) w = 0 := by
  rw [scaledSincPower_fourier Q η hQ hη]
  by_contra hn
  have hx := sincKernel_support_subset Q η hQ hn
  have hb : |w| ≤ (Q : ℝ) / (Real.pi * η) := by
    rw [abs_le]
    simp only [mem_Icc, neg_div] at hx
    constructor <;> linarith [hx.1, hx.2]
  linarith

noncomputable def productSincKernel (Q P : ℕ) (η ζ : ℝ) : ℝ → ℂ :=
  MeasureTheory.convolution (sincKernel Q η) (sincKernel P ζ)
    (ContinuousLinearMap.mul ℂ ℂ) volume

theorem productSincKernel_fourier (Q P : ℕ) (η ζ : ℝ)
    (hQ : 1 ≤ Q) (hP : 1 ≤ P) (hη : 0 < η) (hζ : 0 < ζ) (w : ℝ) :
    𝓕 (productSincKernel Q P η ζ) w = scaledSincPower Q η w * scaledSincPower P ζ w := by
  unfold productSincKernel
  rw [Real.fourier_mul_convolution_eq (sincKernel_integrable Q η) (sincKernel_integrable P ζ),
    sincKernel_fourier Q η hQ hη, sincKernel_fourier P ζ hP hζ]

theorem productSincKernel_support_subset (Q P : ℕ) (η ζ : ℝ)
    (hQ : 1 ≤ Q) (hP : 1 ≤ P) :
    Function.support (productSincKernel Q P η ζ) ⊆
      Icc (-(Q / (Real.pi * η) + P / (Real.pi * ζ)))
        (Q / (Real.pi * η) + P / (Real.pi * ζ)) := by
  intro x hx
  have h := MeasureTheory.support_convolution_subset
    (f := sincKernel Q η) (g := sincKernel P ζ) (μ := volume) (ContinuousLinearMap.mul ℂ ℂ) hx
  rcases h with ⟨y, hy, z, hz, rfl⟩
  have hy' := sincKernel_support_subset Q η hQ hy
  have hz' := sincKernel_support_subset P ζ hP hz
  simp only [mem_Icc, neg_div] at hy' hz' ⊢
  constructor <;> linarith [hy'.1, hy'.2, hz'.1, hz'.2]

theorem scaledSincProduct_fourier (Q P : ℕ) (η ζ : ℝ)
    (hQ : 1 ≤ Q) (hP : 1 ≤ P) (hη : 0 < η) (hζ : 0 < ζ) (w : ℝ) :
    𝓕 (fun x => scaledSincPower Q η x * scaledSincPower P ζ x) w =
      productSincKernel Q P η ζ (-w) := by
  have hfun : 𝓕 (productSincKernel Q P η ζ) =
      (fun x => scaledSincPower Q η x * scaledSincPower P ζ x) :=
    funext (productSincKernel_fourier Q P η ζ hQ hP hη hζ)
  have hi : Integrable (productSincKernel Q P η ζ) :=
    (sincKernel_integrable Q η).integrable_convolution (ContinuousLinearMap.mul ℂ ℂ)
      (sincKernel_integrable P ζ)
  have hc : Continuous (productSincKernel Q P η ζ) :=
    (sincKernel_hasCompactSupport P ζ).continuous_convolution_right (ContinuousLinearMap.mul ℂ ℂ)
      (sincKernel_integrable Q η).locallyIntegrable (sincKernel_continuous P ζ)
  have hFi : Integrable (𝓕 (productSincKernel Q P η ζ)) := by
    rw [hfun]
    apply scaledSincPower_mul_integrable Q η hQ hη _
      (scaledSincPower_continuous P ζ).aestronglyMeasurable
    intro x
    rw [scaledSincPower_norm]
    exact RoughRegime.Lattice.gate_le_one P ζ x
  have h := hi.fourierInv_fourier_eq hFi (hc.continuousAt (x := -w))
  rw [Real.fourierInv_eq_fourier_neg, neg_neg, hfun] at h
  exact h

theorem scaledSincProduct_fourier_eq_zero (Q P : ℕ) (η ζ : ℝ)
    (hQ : 1 ≤ Q) (hP : 1 ≤ P) (hη : 0 < η) (hζ : 0 < ζ) (w : ℝ)
    (hw : Q / (Real.pi * η) + P / (Real.pi * ζ) < |w|) :
    𝓕 (fun x => scaledSincPower Q η x * scaledSincPower P ζ x) w = 0 := by
  rw [scaledSincProduct_fourier Q P η ζ hQ hP hη hζ]
  by_contra hn
  have hx := productSincKernel_support_subset Q P η ζ hQ hP hn
  have hb : |w| ≤ Q / (Real.pi * η) + P / (Real.pi * ζ) := by
    rw [abs_le]
    simp only [mem_Icc] at hx
    constructor <;> linarith [hx.1, hx.2]
  linarith

/-- The sinc product appearing in G^k times the unnormalized lattice density. -/
noncomputable def gatedSinc (Q : ℕ) (η lam : ℝ) (k : ℕ) (x : ℝ) : ℂ :=
  scaledSincPower Q η x * scaledSincPower Q (lam * η) x ^ k

theorem gatedSinc_continuous (Q : ℕ) (η lam : ℝ) (k : ℕ) : Continuous (gatedSinc Q η lam k) := by
  unfold gatedSinc
  exact (scaledSincPower_continuous Q η).mul ((scaledSincPower_continuous Q (lam * η)).pow k)

theorem gatedSinc_integrable (Q : ℕ) (η lam : ℝ) (k : ℕ) (hQ : 1 ≤ Q) (hη : 0 < η) :
    Integrable (gatedSinc Q η lam k) := by
  apply scaledSincPower_mul_integrable Q η hQ hη _
    ((scaledSincPower_continuous Q (lam * η)).pow k).aestronglyMeasurable
  intro x
  change ‖scaledSincPower Q (lam * η) x ^ k‖ ≤ 1
  rw [norm_pow, scaledSincPower_norm]
  exact pow_le_one₀ (RoughRegime.Lattice.gate_nonneg Q (lam * η) x)
    (RoughRegime.Lattice.gate_le_one Q (lam * η) x)

theorem gatedSinc_isBigO (Q : ℕ) (η lam : ℝ) (k : ℕ) (hQ : 1 ≤ Q) (hη : 0 < η) :
    Asymptotics.IsBigO (Filter.cocompact ℝ) (gatedSinc Q η lam k)
      (fun x : ℝ => |x| ^ (-(2 : ℝ))) := by
  apply scaledSincPower_mul_isBigO Q η hQ hη _
  intro x
  rw [norm_pow, scaledSincPower_norm]
  exact pow_le_one₀ (RoughRegime.Lattice.gate_nonneg Q (lam * η) x)
    (RoughRegime.Lattice.gate_le_one Q (lam * η) x)

theorem gatedSinc_as_product (Q k : ℕ) (η lam : ℝ) :
    gatedSinc Q η lam k = fun x => scaledSincPower Q η x * scaledSincPower (Q * k) (lam * η) x := by
  ext x
  unfold gatedSinc scaledSincPower
  push_cast
  congr 1
  rw [← pow_mul]
  congr 1
  ring

/-- All three gate powers k=0,1,2 obey the uniform cutoff used in Lemma 13. -/
theorem gatedSinc_fourier_eq_zero (Q : ℕ) (η lam : ℝ) (k : ℕ)
    (hQ : 1 ≤ Q) (hη : 0 < η) (hlam : 1 ≤ lam) (hk : k ≤ 2)
    (w : ℝ) (hw : 3 * Q / (Real.pi * η) < |w|) :
    𝓕 (gatedSinc Q η lam k) w = 0 := by
  by_cases hk0 : k = 0
  · subst k
    have heq : gatedSinc Q η lam 0 = scaledSincPower Q η := by ext x; simp [gatedSinc]
    rw [heq]
    apply scaledSincPower_fourier_eq_zero Q η hQ hη w
    have hd : 0 < Real.pi * η := mul_pos Real.pi_pos hη
    have hQr : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
    have hcmp : (Q : ℝ) / (Real.pi * η) ≤ 3 * Q / (Real.pi * η) := by
      apply div_le_div_of_nonneg_right _ hd.le
      nlinarith
    exact hcmp.trans_lt hw
  have hk1 : 1 ≤ k := by omega
  have hP : 1 ≤ Q * k := by simpa using Nat.mul_le_mul hQ hk1
  have hζη : 0 < lam * η := mul_pos (by linarith) hη
  rw [gatedSinc_as_product]
  apply scaledSincProduct_fourier_eq_zero Q (Q * k) η (lam * η) hQ hP hη hζη w
  have hkr : (k : ℝ) ≤ 2 := by exact_mod_cast hk
  have hQr : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have hd : 0 < Real.pi * η := mul_pos Real.pi_pos hη
  have hdl : 0 < Real.pi * (lam * η) := mul_pos Real.pi_pos hζη
  have hcmp : ((Q * k : ℕ) : ℝ) / (Real.pi * (lam * η)) ≤
      2 * Q / (Real.pi * η) := by
    apply (div_le_div_iff₀ hdl hd).2
    push_cast
    nlinarith [mul_nonneg hQr (sub_nonneg.mpr hkr),
      mul_nonneg hQr (sub_nonneg.mpr hlam)]
  calc
    Q / (Real.pi * η) + ((Q * k : ℕ) : ℝ) / (Real.pi * (lam * η))
        ≤ Q / (Real.pi * η) + 2 * Q / (Real.pi * η) := by linarith
    _ = 3 * Q / (Real.pi * η) := by ring
    _ < |w| := hw

end RoughRegime.LatticeFourier
