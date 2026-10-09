module

public import RoughRegime.JetComposition
public import RoughRegime.GateRoot


@[expose] public section
/-! The genuine finite Faà di Bruno difference estimate with a gate-degree
budget. This is an analytic helper; actual phase and reciprocal jets are
established independently before its application. -/
noncomputable section
open scoped ContDiff
namespace RoughRegime.Calculus
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Zeroth inner jets do not enter derivative composition. -/
theorem taylorComp_congr_positive (q : FormalMultilinearSeries ℝ F G)
    (p p' : FormalMultilinearSeries ℝ E F) (hp : ∀ k, 0 < k → p k = p' k) (n : ℕ) :
    q.taylorComp p n = q.taylorComp p' n := by
  unfold FormalMultilinearSeries.taylorComp
  apply Finset.sum_congr rfl
  intro c _
  unfold FormalMultilinearSeries.compAlongOrderedFinpartition
  congr 1
  funext i
  exact hp _ (Nat.pos_of_ne_zero (c.neZero_partSize i).out)

/-- A uniform finite-jet composition bound only needs positive inner orders. -/
theorem uniform_taylorComp_difference_bound_positive {A : Type*}
    (q₁ q₂ : A → FormalMultilinearSeries ℝ F G)
    (p₁ p₂ : A → FormalMultilinearSeries ℝ E F) (δ : A → ℝ)
    (n : ℕ) (C : ℝ) (hC : 0 ≤ C) (hδ : ∀ a, 0 ≤ δ a)
    (hq₁ : ∀ k, k ≤ n → ∀ a, ‖q₁ a k‖ ≤ C)
    (hp₁ : ∀ k, 0 < k → k ≤ n → ∀ a, ‖p₁ a k‖ ≤ C)
    (hp₂ : ∀ k, 0 < k → k ≤ n → ∀ a, ‖p₂ a k‖ ≤ C)
    (hqdiff : ∀ k, k ≤ n → ∀ a, ‖q₁ a k - q₂ a k‖ ≤ C * δ a)
    (hpdiff : ∀ k, 0 < k → k ≤ n → ∀ a, ‖p₁ a k - p₂ a k‖ ≤ C * δ a) :
    ∃ D : ℝ, 0 < D ∧ ∀ a,
      ‖(q₁ a).taylorComp (p₁ a) n - (q₂ a).taylorComp (p₂ a) n‖ ≤ D * δ a := by
  let p₁' (a : A) : FormalMultilinearSeries ℝ E F := fun k => if k = 0 then 0 else p₁ a k
  let p₂' (a : A) : FormalMultilinearSeries ℝ E F := fun k => if k = 0 then 0 else p₂ a k
  have h₁ (k : ℕ) (hk : k ≤ n) (a : A) : ‖p₁' a k‖ ≤ C := by
    dsimp [p₁']; split_ifs with hz
    · simpa using hC
    · exact hp₁ k (Nat.pos_of_ne_zero hz) hk a
  have h₂ (k : ℕ) (hk : k ≤ n) (a : A) : ‖p₂' a k‖ ≤ C := by
    dsimp [p₂']; split_ifs with hz
    · simpa using hC
    · exact hp₂ k (Nat.pos_of_ne_zero hz) hk a
  have hdiff (k : ℕ) (hk : k ≤ n) (a : A) : ‖p₁' a k - p₂' a k‖ ≤ C * δ a := by
    dsimp [p₁', p₂']; split_ifs with hz
    · simpa using mul_nonneg hC (hδ a)
    · exact hpdiff k (Nat.pos_of_ne_zero hz) hk a
  obtain ⟨D, hD, hb⟩ := uniform_taylorComp_difference_bound q₁ q₂ p₁' p₂' δ n C hδ hq₁ h₁ h₂ hqdiff hdiff
  refine ⟨D, hD, fun a => ?_⟩
  have e₁ := taylorComp_congr_positive (q₁ a) (p₁' a) (p₁ a) (by intro k hk; simp [p₁', hk.ne']) n
  have e₂ := taylorComp_congr_positive (q₂ a) (p₂' a) (p₂ a) (by intro k hk; simp [p₂', hk.ne']) n
  simpa only [e₁, e₂] using hb a

/-- True outer jets retain the gate amplitude, and true inner jets consume at
most one gate root per derivative. The finite composition therefore keeps a
uniform O(w L^n) bound whenever n+1 is within the gate budget. -/
theorem weighted_taylorComp_difference_bound {A : Type*}
    (q₁ q₂ : A → FormalMultilinearSeries ℝ F G)
    (p₁ p₂ : A → FormalMultilinearSeries ℝ E F)
    (S β w L : A → ℝ) (n : ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hS : ∀ a, 0 < S a) (hβ : ∀ a, 0 < β a) (hβ1 : ∀ a, β a ≤ 1)
    (hw : ∀ a, 0 ≤ w a) (hL : ∀ a, 0 < L a)
    (hbudget : ∀ a, S a / β a ^ (n+1) ≤ 1)
    (hq₁ : ∀ k, k ≤ n → ∀ a, ‖q₁ a k‖ ≤ C * S a)
    (hp₁ : ∀ k, 0 < k → k ≤ n → ∀ a, β a * ‖p₁ a k‖ ≤ C * L a ^ k)
    (hp₂ : ∀ k, 0 < k → k ≤ n → ∀ a, β a * ‖p₂ a k‖ ≤ C * L a ^ k)
    (hqdiff : ∀ k, k ≤ n → ∀ a,
      ‖q₁ a k - q₂ a k‖ ≤ C * S a * (w a / β a))
    (hpdiff : ∀ k, 0 < k → k ≤ n → ∀ a,
      β a * ‖p₁ a k - p₂ a k‖ ≤ C * w a * L a ^ k) :
    ∃ D : ℝ, 0 < D ∧ ∀ a,
      ‖(q₁ a).taylorComp (p₁ a) n - (q₂ a).taylorComp (p₂ a) n‖ ≤ D * w a * L a ^ n := by
  let q₁' (a : A) : FormalMultilinearSeries ℝ F G := fun k => (S a)⁻¹ • q₁ a k
  let q₂' (a : A) : FormalMultilinearSeries ℝ F G := fun k => (S a)⁻¹ • q₂ a k
  let p₁' (a : A) : FormalMultilinearSeries ℝ E F := fun k => (β a / L a)^k • p₁ a k
  let p₂' (a : A) : FormalMultilinearSeries ℝ E F := fun k => (β a / L a)^k • p₂ a k
  let δ (a : A) := w a / β a
  have hq (k : ℕ) (hk : k ≤ n) (a : A) : ‖q₁' a k‖ ≤ C := by
    simp only [q₁', norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hS a))]
    calc
      _ ≤ (S a)⁻¹ * (C * S a) := mul_le_mul_of_nonneg_left (hq₁ k hk a) (inv_nonneg.mpr (hS a).le)
      _ = C := by field_simp [(hS a).ne']
  have hp (p : A → FormalMultilinearSeries ℝ E F)
      (hb : ∀ k, 0 < k → k ≤ n → ∀ a, β a * ‖p a k‖ ≤ C * L a^k)
      (k : ℕ) (hk0 : 0 < k) (hk : k ≤ n) (a : A) :
      ‖((β a/L a)^k) • p a k‖ ≤ C := by
    have hpow : β a ^ k ≤ β a := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
      simpa [pow_succ] using mul_le_mul_of_nonneg_right (pow_le_one₀ (hβ a).le (hβ1 a) : β a ^ j ≤ 1) (hβ a).le
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (div_pos (hβ a) (hL a)) k)]
    rw [div_pow, div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos (hL a) k)).mpr
    calc
      β a ^ k * ‖p a k‖ ≤ β a * ‖p a k‖ := mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ C * L a ^ k := hb k hk0 hk a
  have hqd (k : ℕ) (hk : k ≤ n) (a : A) : ‖q₁' a k - q₂' a k‖ ≤ C * δ a := by
    rw [show q₁' a k - q₂' a k = (S a)⁻¹ • (q₁ a k - q₂ a k) by simp [q₁', q₂', smul_sub]]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hS a))]
    calc
      _ ≤ (S a)⁻¹ * (C * S a * (w a / β a)) := mul_le_mul_of_nonneg_left (hqdiff k hk a) (inv_nonneg.mpr (hS a).le)
      _ = C * δ a := by dsimp [δ]; field_simp [(hS a).ne', (hβ a).ne']
  have hpd (k : ℕ) (hk0 : 0 < k) (hk : k ≤ n) (a : A) : ‖p₁' a k - p₂' a k‖ ≤ C * δ a := by
    rw [show p₁' a k - p₂' a k = (β a/L a)^k • (p₁ a k - p₂ a k) by simp [p₁', p₂', smul_sub]]
    have hpow : β a ^ k ≤ 1 := pow_le_one₀ (hβ a).le (hβ1 a)
    simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos (div_pos (hβ a) (hL a)) k)]
    rw [div_pow, div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos (hL a) k)).mpr
    have hh := hpdiff k hk0 hk a
    have hz : β a ^ k * ‖p₁ a k - p₂ a k‖ * β a ≤ C * w a * L a ^ k := by
      calc
        _ ≤ β a * ‖p₁ a k - p₂ a k‖ := by
          nlinarith [mul_le_mul_of_nonneg_right hpow (mul_nonneg (norm_nonneg (p₁ a k-p₂ a k)) (hβ a).le)]
        _ ≤ _ := hh
    have hz' := (le_div_iff₀ (hβ a)).mpr hz
    convert hz' using 1
    dsimp [δ]
    ring
  obtain ⟨D, hD, hb⟩ := uniform_taylorComp_difference_bound_positive q₁' q₂' p₁' p₂' δ n C hC
    (fun a => div_nonneg (hw a) (hβ a).le) hq (hp p₁ hp₁) (hp p₂ hp₂) hqd hpd
  refine ⟨D, hD, fun a => ?_⟩
  have e₁ := taylorComp_smul_graded (q₁ a) (p₁ a) ((S a)⁻¹) (β a/L a) n
  have e₂ := taylorComp_smul_graded (q₂ a) (p₂ a) ((S a)⁻¹) (β a/L a) n
  have hh := hb a
  change ‖(q₁' a).taylorComp (p₁' a) n - (q₂' a).taylorComp (p₂' a) n‖ ≤ D * δ a at hh
  rw [e₁, e₂, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_pos (mul_pos (inv_pos.mpr (hS a)) (pow_pos (div_pos (hβ a) (hL a)) n))] at hh
  have hbp := (div_le_one (pow_pos (hβ a) (n+1))).mp (hbudget a)
  have ht : ‖(q₁ a).taylorComp (p₁ a) n - (q₂ a).taylorComp (p₂ a) n‖ ≤
      D * w a * L a^n * (S a / β a^(n+1)) := by
    dsimp [δ] at hh
    have hc : 0 < (S a)⁻¹ * (β a/L a)^n := mul_pos (inv_pos.mpr (hS a)) (pow_pos (div_pos (hβ a) (hL a)) n)
    apply (mul_le_mul_iff_right₀ hc).mp
    calc
      _ ≤ D * (w a/β a) := hh
      _ = _ := by rw [div_pow, pow_succ]; field_simp [(hS a).ne', (hβ a).ne', (hL a).ne']
  exact ht.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left (hbudget a) (mul_nonneg (mul_nonneg hD.le (hw a)) (pow_nonneg (hL a).le n)))

end RoughRegime.Calculus
