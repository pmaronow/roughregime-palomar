module

public import RoughRegime.PhaseInputs


@[expose] public section
/-! Genuine reciprocal profile increment jets. Uniform constants arise from
actual smooth outer families and the finite derivative composition formula. -/
noncomputable section
open Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.Calculus RoughRegime.Upper
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def oscillatorProfile (κ : ℝ → ℝ) (center S h θ : ℝ) (cut φ : E → ℝ) : E → ℝ :=
  oscillatorOuter κ center S ∘ phaseInput h θ cut φ

/-- The derivative estimate for a true phase increment, under explicit inner
jet estimates. These inner estimates are supplied by the concrete gated
hierarchy, rather than assuming an estimate for the profile itself. -/
theorem oscillatorProfile_difference_jet_bound {A : Type*}
    (κ : ℝ → ℝ) (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (N : Set ℝ) (hN : IsOpen N) (hκ : ContDiffOn ℝ ∞ κ N) (hκ0 : κ 0 = 0)
    (hinterval : Icc (0 : ℝ) (1/lo) ⊆ N) (n : ℕ)
    (S β w L h θ : A → ℝ) (cut φ ψ : A → E → ℝ) (x : A → E)
    (C : ℝ) (hC : 0 ≤ C)
    (hS : ∀ a, S a ∈ Ioc (0:ℝ) 1) (hβ : ∀ a, 0 < β a) (hβ1 : ∀ a, β a ≤ 1)
    (hw : ∀ a, 0 ≤ w a) (hL : ∀ a, 1 ≤ L a)
    (hh : ∀ a, h a ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi))
    (hcut : ∀ a, cut a (x a) ∈ Icc (0:ℝ) 1)
    (hc : ∀ a, ContDiffAt ℝ ∞ (cut a) (x a))
    (hp : ∀ a, ContDiffAt ℝ ∞ (φ a) (x a)) (hq : ∀ a, ContDiffAt ℝ ∞ (ψ a) (x a))
    (hcutjets : ∀ k, 0 < k → k ≤ n → ∀ a, ‖iteratedFDeriv ℝ k (cut a) (x a)‖ ≤ C)
    (hphasejets : ∀ k, 0 < k → k ≤ n → ∀ a,
      β a * ‖iteratedFDeriv ℝ k (φ a) (x a)‖ ≤ C*L a^k ∧
      β a * ‖iteratedFDeriv ℝ k (ψ a) (x a)‖ ≤ C*L a^k)
    (hincjets : ∀ k, k ≤ n → ∀ a,
      β a * ‖iteratedFDeriv ℝ k (φ a) (x a) - iteratedFDeriv ℝ k (ψ a) (x a)‖ ≤ C*w a*L a^k)
    (hbudget : ∀ a, S a / β a^(n+1) ≤ 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ a,
      ‖iteratedFDeriv ℝ n
        (oscillatorProfile κ (intervalCenter lo hi) (S a) (h a) (θ a) (cut a) (φ a) -
         oscillatorProfile κ (intervalCenter lo hi) (S a) (h a) (θ a) (cut a) (ψ a)) (x a)‖ ≤ D*w a*L a^n := by
  obtain ⟨B,hB,houter⟩ := oscillatorOuter_finite_jet_bound κ lo hi hlo hlt N hN hκ hκ0 hinterval n
  let C' : ℝ := B*(C+1)+C+1
  have hC' : 0 ≤ C' := by dsimp [C']; positivity
  have hBC : B*C ≤ C' := by dsimp [C']; nlinarith
  have hCB : B ≤ C' := by dsimp [C']; nlinarith
  have hCC : C ≤ C' := by dsimp [C']; nlinarith
  let f₁ (a : A) := phaseInput (h a) (θ a) (cut a) (φ a)
  let f₂ (a : A) := phaseInput (h a) (θ a) (cut a) (ψ a)
  let g (a : A) := oscillatorOuter κ (intervalCenter lo hi) (S a)
  let q₁ (a : A) := ftaylorSeries ℝ (g a) (f₁ a (x a))
  let q₂ (a : A) := ftaylorSeries ℝ (g a) (f₂ a (x a))
  let p₁ (a : A) := ftaylorSeries ℝ (f₁ a) (x a)
  let p₂ (a : A) := ftaylorSeries ℝ (f₂ a) (x a)
  have hS' (a : A) : S a ∈ Icc (0:ℝ) 1 := ⟨(hS a).1.le,(hS a).2⟩
  have hp₁ (a : A) : ContDiffAt ℝ ∞ (f₁ a) (x a) := phaseInput_contDiffAt _ _ _ _ _ (hc a) (hp a)
  have hp₂ (a : A) : ContDiffAt ℝ ∞ (f₂ a) (x a) := phaseInput_contDiffAt _ _ _ _ _ (hc a) (hq a)
  have hg₁ (a : A) : ContDiffAt ℝ ∞ (g a) (f₁ a (x a)) :=
    oscillatorOuter_contDiffAt κ lo hi hlo hlt N hN hκ hinterval _ (hS' a) _ _ _ (hh a) (hcut a)
  have hg₂ (a : A) : ContDiffAt ℝ ∞ (g a) (f₂ a (x a)) :=
    oscillatorOuter_contDiffAt κ lo hi hlo hlt N hN hκ hinterval _ (hS' a) _ _ _ (hh a) (hcut a)
  have hqb (k : ℕ) (hk : k ≤ n) (a : A) : ‖q₁ a k‖ ≤ C'*S a := by
    exact (houter k hk (S a) (hS' a) (h a) (hh a) (cut a (x a)) (hcut a)
      (θ a+φ a (x a)) (θ a+ψ a (x a))).1.trans (mul_le_mul_of_nonneg_right hCB (hS a).1.le)
  have hpb (p : A → E → ℝ) (hsmooth : ∀ a, ContDiffAt ℝ ∞ (p a) (x a))
      (hb : ∀ k, 0 < k → k ≤ n → ∀ a, β a*‖iteratedFDeriv ℝ k (p a) (x a)‖ ≤ C*L a^k)
      (k : ℕ) (hk0 : 0 < k) (hk : k ≤ n) (a : A) :
      β a*‖iteratedFDeriv ℝ k (phaseInput (h a) (θ a) (cut a) (p a)) (x a)‖ ≤ C'*L a^k := by
    rw [norm_phaseInput_jet _ _ _ _ _ _ hk0 (hc a) (hsmooth a), mul_max_of_nonneg _ _ (hβ a).le]
    apply max_le
    · calc
        _ ≤ β a*C := mul_le_mul_of_nonneg_left (hcutjets k hk0 hk a) (hβ a).le
        _ ≤ C := by nlinarith [hβ1 a]
        _ ≤ C*L a^k := by nlinarith [pow_le_pow_right₀ (hL a) (Nat.zero_le k)]
        _ ≤ C'*L a^k := mul_le_mul_of_nonneg_right hCC (pow_nonneg (zero_lt_one.trans_le (hL a)).le k)
    · exact (hb k hk0 hk a).trans (mul_le_mul_of_nonneg_right hCC (pow_nonneg (zero_lt_one.trans_le (hL a)).le k))
  have hqd (k : ℕ) (hk : k ≤ n) (a : A) : ‖q₁ a k-q₂ a k‖ ≤ C'*S a*(w a/β a) := by
    have hi := hincjets 0 (Nat.zero_le n) a
    have hz : ‖iteratedFDeriv ℝ 0 (φ a) (x a)-iteratedFDeriv ℝ 0 (ψ a) (x a)‖ = |φ a (x a)-ψ a (x a)| := by
      rw [← iteratedFDeriv_sub_apply ((hp a).of_le (by simp)) ((hq a).of_le (by simp)), norm_iteratedFDeriv_zero]
      rfl
    rw [hz,pow_zero,mul_one] at hi
    have hd : |φ a (x a)-ψ a (x a)| ≤ C*(w a/β a) := by
      have hi' : |φ a (x a)-ψ a (x a)| ≤ (C*w a)/β a := (le_div_iff₀ (hβ a)).mpr (by nlinarith [hi])
      convert hi' using 1 <;> ring
    calc
      _ ≤ B*S a*|(θ a+φ a (x a))-(θ a+ψ a (x a))| :=
        (houter k hk (S a) (hS' a) (h a) (hh a) (cut a (x a)) (hcut a) _ _).2
      _ = B*S a*|φ a (x a)-ψ a (x a)| := by congr 2; ring
      _ ≤ B*S a*(C*(w a/β a)) := mul_le_mul_of_nonneg_left hd (mul_nonneg hB.le (hS a).1.le)
      _ = (B*C)*S a*(w a/β a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBC (hS a).1.le) (div_nonneg (hw a) (hβ a).le)
  have hpd (k : ℕ) (hk0 : 0 < k) (hk : k ≤ n) (a : A) : β a*‖p₁ a k-p₂ a k‖ ≤ C'*w a*L a^k := by
    change β a*‖iteratedFDeriv ℝ k (f₁ a) (x a)-iteratedFDeriv ℝ k (f₂ a) (x a)‖ ≤ _
    rw [norm_phaseInput_jet_difference _ _ _ _ _ _ _ hk0 (hc a) (hp a) (hq a)]
    exact (hincjets k hk a).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC (hw a)) (pow_nonneg (zero_lt_one.trans_le (hL a)).le k))
  obtain ⟨D,hD,hbound⟩ := weighted_taylorComp_difference_bound q₁ q₂ p₁ p₂ S β w L n C' hC'
    (fun a => (hS a).1) hβ hβ1 hw (fun a => zero_lt_one.trans_le (hL a)) hbudget
    hqb (hpb φ hp (fun k hk0 hk a => (hphasejets k hk0 hk a).1))
    (hpb ψ hq (fun k hk0 hk a => (hphasejets k hk0 hk a).2)) hqd hpd
  refine ⟨D,hD,fun a => ?_⟩
  change ‖iteratedFDeriv ℝ n ((g a ∘ f₁ a)-(g a ∘ f₂ a)) (x a)‖ ≤ _
  rw [iteratedFDeriv_sub_apply ((hg₁ a).comp _ (hp₁ a) |>.of_le (by simp))
    ((hg₂ a).comp _ (hp₂ a) |>.of_le (by simp)),
    iteratedFDeriv_comp (hg₁ a) (hp₁ a) (by simp),
    iteratedFDeriv_comp (hg₂ a) (hp₂ a) (by simp)]
  exact hbound a

end RoughRegime.LatticePriors
