module

public import RoughRegime.ProfileJets
public import RoughRegime.HierarchicalPhases
public import RoughRegime.HolderGeometry


@[expose] public section
/-! The fully instantiated true local source-profile increment jet bound,
uniform over every hierarchy depth, lattice realization and phase. -/
noncomputable section
open Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.Calculus RoughRegime.Upper

structure HierarchyPoint (d : ℕ) where
  J : ℕ
  M : ℕ
  b : ℕ
  m : ℝ
  h : ℝ
  θ : ℝ
  z : Fin d × Fin J → ℤ
  x : Model.Covariate d

/-- All constants in the actual local profile increment estimate are uniform
in J,M,m and every unbounded lattice realization. -/
theorem source_profile_increment_jet_bound (U : SmoothStep) (d Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
    (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
    (hK : 0 < K) (hKQ : K ≤ 2*Q)
    (κ : ℝ → ℝ) (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (N : Set ℝ) (hN : IsOpen N) (hκ : ContDiffOn ℝ ∞ κ N) (hκ0 : κ 0 = 0)
    (hinterval : Icc (0:ℝ) (1/lo) ⊆ N)
    (cut : Model.Covariate d → ℝ) (hcut : ContDiff ℝ ∞ cut)
    (hcut01 : ∀ x, cut x ∈ Icc (0:ℝ) 1) (n : ℕ) (hn : n+1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ J M b : ℕ, b < J → ∀ m : ℝ,
      (2:ℝ)^((J:ℝ)*alpha0) ≤ m → ∀ z : Fin d × Fin J → ℤ,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi), ∀ θ : ℝ,
      ∀ x ∈ Model.cube d,
      ‖iteratedFDeriv ℝ n
        (oscillatorProfile κ (intervalCenter lo hi) (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) h θ cut
            (sourcePartialPhase U d J M gammaStar z b) -
         oscillatorProfile κ (intervalCenter lo hi) (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) h θ cut
            (sourcePartialPhase U d J M gammaStar z (b+1))) x‖ ≤
       C * sourceWeight gammaStar alpha0 m b * sourceRate J gammaStar b^n := by
  have hpartial (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ hk : 0 < k,
      ∀ J M b c : ℕ, b ≤ c → ∀ m : ℝ, 0 < m →
        ∀ z : Fin d × Fin J → ℤ, ∀ x : Model.Covariate d,
        gateRoot (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) K *
          ‖iteratedFDeriv ℝ k (sourcePartialPhase U d J M gammaStar z c) x‖ ≤
          C*(sourceWeight gammaStar alpha0 m b*sourceRate J gammaStar b^k) := by
    by_cases hk : 0 < k
    · obtain ⟨C,hC,hb⟩ := sourcePartialPhase_derivative_bound U d Q K gammaStar lambdaStar alpha0 hγ hγ1 hlam ha1 hK hKQ k hk
      exact ⟨C,hC,fun _ => hb⟩
    · exact ⟨0,le_rfl,fun hk' => (hk hk').elim⟩
  choose P hP hp using hpartial
  choose I hI hi' using fun k => sourcePartialPhase_increment_derivative_bound U d Q K gammaStar lambdaStar alpha0 hγ hγ1 hlam hK hKQ k
  obtain ⟨B,hB,hcutjet⟩ := compact_finite_jet_bound cut (Model.cube d) (Model.isCompact_cube d) hcut n
  let C₀ : ℝ := B+1+∑ k ∈ Finset.range (n+1), (P k+I k)
  have hterm (k : ℕ) : 0 ≤ P k+I k := add_nonneg (hP k) (hI k)
  have hC₀ : 0 ≤ C₀ := by
    have hs := Finset.sum_nonneg (s := Finset.range (n+1)) (fun k _ => hterm k)
    dsimp [C₀]
    linarith
  have hC_B : B ≤ C₀ := by
    have hs := Finset.sum_nonneg (s := Finset.range (n+1)) (fun k _ => hterm k)
    dsimp [C₀]
    linarith
  have hC_PI (k : ℕ) (hk : k ≤ n) : P k ≤ C₀ ∧ I k ≤ C₀ := by
    have hs := Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_range.mpr (show k<n+1 by omega))
    dsimp [C₀]
    constructor <;> linarith [hP k,hI k]
  let A := {p : HierarchyPoint d // p.b<p.J ∧ (2:ℝ)^((p.J:ℝ)*alpha0) ≤ p.m ∧
    p.h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi) ∧ p.x ∈ Model.cube d ∧
    0 < sourceGate d p.J Q p.M gammaStar lambdaStar alpha0 p.m p.z}
  let S (a : A) := sourceGate d a.1.J Q a.1.M gammaStar lambdaStar alpha0 a.1.m a.1.z
  let β (a : A) := gateRoot (S a) K
  let w (a : A) := sourceWeight gammaStar alpha0 a.1.m a.1.b
  let L (a : A) := sourceRate a.1.J gammaStar a.1.b
  let φ (a : A) := sourcePartialPhase U d a.1.J a.1.M gammaStar a.1.z a.1.b
  let ψ (a : A) := sourcePartialPhase U d a.1.J a.1.M gammaStar a.1.z (a.1.b+1)
  have hm (a : A) : 0 < a.1.m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le a.2.2.1
  have hSrange (a : A) : S a ∈ Ioc (0:ℝ) 1 := by
    exact ⟨a.2.2.2.2.2,(blockGate_range Q a.1.M _ _ a.1.z).2⟩
  have hβ (a : A) : 0 < β a := Real.rpow_pos_of_pos (hSrange a).1 _
  have hβ1 (a : A) : β a ≤ 1 := (gateRoot_bounds (S a) K (hSrange a).1.le (hSrange a).2).2
  have hw (a : A) : 0 ≤ w a := by
    have hma := hm a
    dsimp [w,sourceWeight,sourceGamma]
    positivity
  have hw1 (a : A) : w a ≤ 1 :=
    (sourceWeight_le_gamma gammaStar alpha0 a.1.m a.1.J a.1.b hγ ha0 (Nat.le_of_lt a.2.1) a.2.2.1).trans (by linarith)
  have hL (a : A) : 1 ≤ L a := sourceRate_ge_one a.1.J a.1.b gammaStar hγ (by linarith) (Nat.le_of_lt a.2.1)
  have hφ (a : A) : ContDiffAt ℝ ∞ (φ a) a.1.x := (sourcePartialPhase_smooth U d a.1.J a.1.M gammaStar hγ hγ1 a.1.z a.1.b).contDiffAt
  have hψ (a : A) : ContDiffAt ℝ ∞ (ψ a) a.1.x := (sourcePartialPhase_smooth U d a.1.J a.1.M gammaStar hγ hγ1 a.1.z (a.1.b+1)).contDiffAt
  have hphase (k : ℕ) (hk0 : 0<k) (hk : k≤n) (a : A) :
      β a*‖iteratedFDeriv ℝ k (φ a) a.1.x‖ ≤ C₀*L a^k ∧ β a*‖iteratedFDeriv ℝ k (ψ a) a.1.x‖ ≤ C₀*L a^k := by
    have hbc := hp k hk0 a.1.J a.1.M a.1.b a.1.b (le_refl _) a.1.m (hm a) a.1.z a.1.x
    have hbd := hp k hk0 a.1.J a.1.M a.1.b (a.1.b+1) (by omega) a.1.m (hm a) a.1.z a.1.x
    have hc : P k*w a ≤ C₀ := (mul_le_mul_of_nonneg_left (hw1 a) (hP k)).trans_eq (by ring) |>.trans (hC_PI k hk).1
    constructor
    · exact hbc.trans (by dsimp [w,L] at hc ⊢; nlinarith [mul_le_mul_of_nonneg_right hc (pow_nonneg (zero_lt_one.trans_le (hL a)).le k)])
    · exact hbd.trans (by dsimp [w,L] at hc ⊢; nlinarith [mul_le_mul_of_nonneg_right hc (pow_nonneg (zero_lt_one.trans_le (hL a)).le k)])
  have hinc (k : ℕ) (hk : k≤n) (a : A) :
      β a*‖iteratedFDeriv ℝ k (φ a) a.1.x-iteratedFDeriv ℝ k (ψ a) a.1.x‖ ≤ C₀*w a*L a^k := by
    exact (hi' k a.1.J a.1.M a.1.b a.2.1 a.1.m (hm a) a.1.z a.1.x).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC_PI k hk).2 (hw a)) (pow_nonneg (zero_lt_one.trans_le (hL a)).le k))
  obtain ⟨D,hD,hbound⟩ := oscillatorProfile_difference_jet_bound κ lo hi hlo hlt N hN hκ hκ0 hinterval n
    S β w L (fun a : A => a.1.h) (fun a => a.1.θ) (fun _ => cut) φ ψ (fun a => a.1.x) C₀ hC₀
    hSrange hβ hβ1 hw hL (fun a => a.2.2.2.1) (fun a => hcut01 a.1.x)
    (fun a => hcut.contDiffAt) hφ hψ
    (fun k _ hk a => (hcutjet k hk a.1.x a.2.2.2.2.1).trans hC_B) hphase hinc
    (fun a => gateRoot_power_budget (S a) K (n+1) (hSrange a).1 (hSrange a).2 hK hn)
  refine ⟨D,hD,?_⟩
  intro J M b hb m hm' z h hh θ x hx
  let SG := sourceGate d J Q M gammaStar lambdaStar alpha0 m z
  by_cases hSG : 0 < SG
  · exact hbound ⟨⟨J,M,b,m,h,θ,z,x⟩,hb,hm',hh,hx,hSG⟩
  · have hz : SG=0 := le_antisymm (le_of_not_gt hSG) (blockGate_range Q M _ _ z).1
    have he (f : Model.Covariate d → ℝ) : oscillatorProfile κ (intervalCenter lo hi) SG h θ cut f = 0 := by
      funext y
      simp [oscillatorProfile,oscillatorOuter,hz,hκ0]
    change ‖iteratedFDeriv ℝ n (oscillatorProfile κ (intervalCenter lo hi) SG h θ cut _ - oscillatorProfile κ (intervalCenter lo hi) SG h θ cut _) x‖ ≤ _
    rw [he,he,sub_self,iteratedFDeriv_zero]
    simp only [Pi.zero_apply,norm_zero]
    have hm0 : 0 < m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hm'
    unfold sourceWeight sourceRate sourceGamma
    positivity

/-- The same true bound holds on the whole ambient space for a compactly
supported cutoff, enabling affine rescaling and disjoint block gluing. -/
theorem source_profile_increment_jet_bound_global (U : SmoothStep) (d Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
    (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
    (hK : 0 < K) (hKQ : K ≤ 2*Q)
    (κ : ℝ → ℝ) (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (N : Set ℝ) (hN : IsOpen N) (hκ : ContDiffOn ℝ ∞ κ N) (hκ0 : κ 0 = 0)
    (hinterval : Icc (0:ℝ) (1/lo) ⊆ N)
    (cut : Model.Covariate d → ℝ) (hcut : ContDiff ℝ ∞ cut) (hcompact : HasCompactSupport cut)
    (hcut01 : ∀ x, cut x ∈ Icc (0:ℝ) 1) (n : ℕ) (hn : n+1 ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ J M b : ℕ, b < J → ∀ m : ℝ,
      (2:ℝ)^((J:ℝ)*alpha0) ≤ m → ∀ z : Fin d × Fin J → ℤ,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi), ∀ θ : ℝ,
      ∀ x : Model.Covariate d,
      ‖iteratedFDeriv ℝ n
        (oscillatorProfile κ (intervalCenter lo hi) (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) h θ cut
            (sourcePartialPhase U d J M gammaStar z b) -
         oscillatorProfile κ (intervalCenter lo hi) (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) h θ cut
            (sourcePartialPhase U d J M gammaStar z (b+1))) x‖ ≤
       C * sourceWeight gammaStar alpha0 m b * sourceRate J gammaStar b^n := by
  have hpartial (k : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ hk : 0 < k,
      ∀ J M b c : ℕ, b ≤ c → ∀ m : ℝ, 0 < m →
        ∀ z : Fin d × Fin J → ℤ, ∀ x : Model.Covariate d,
        gateRoot (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) K *
          ‖iteratedFDeriv ℝ k (sourcePartialPhase U d J M gammaStar z c) x‖ ≤
          C*(sourceWeight gammaStar alpha0 m b*sourceRate J gammaStar b^k) := by
    by_cases hk : 0 < k
    · obtain ⟨C,hC,hb⟩ := sourcePartialPhase_derivative_bound U d Q K gammaStar lambdaStar alpha0 hγ hγ1 hlam ha1 hK hKQ k hk
      exact ⟨C,hC,fun _ => hb⟩
    · exact ⟨0,le_rfl,fun hk' => (hk hk').elim⟩
  choose P hP hp using hpartial
  choose I hI hi' using fun k => sourcePartialPhase_increment_derivative_bound U d Q K gammaStar lambdaStar alpha0 hγ hγ1 hlam hK hKQ k
  obtain ⟨B,hB,hcutjet⟩ := hcompact.exists_bound_iteratedFDeriv hcut n
  let C₀ : ℝ := B+1+∑ k ∈ Finset.range (n+1), (P k+I k)
  have hterm (k : ℕ) : 0 ≤ P k+I k := add_nonneg (hP k) (hI k)
  have hC₀ : 0 ≤ C₀ := by
    have hs := Finset.sum_nonneg (s := Finset.range (n+1)) (fun k _ => hterm k)
    dsimp [C₀]
    linarith
  have hC_B : B ≤ C₀ := by
    have hs := Finset.sum_nonneg (s := Finset.range (n+1)) (fun k _ => hterm k)
    dsimp [C₀]
    linarith
  have hC_PI (k : ℕ) (hk : k ≤ n) : P k ≤ C₀ ∧ I k ≤ C₀ := by
    have hs := Finset.single_le_sum (fun j _ => hterm j) (Finset.mem_range.mpr (show k<n+1 by omega))
    dsimp [C₀]
    constructor <;> linarith [hP k,hI k]
  let A := {p : HierarchyPoint d // p.b<p.J ∧ (2:ℝ)^((p.J:ℝ)*alpha0) ≤ p.m ∧
    p.h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi) ∧
    0 < sourceGate d p.J Q p.M gammaStar lambdaStar alpha0 p.m p.z}
  let S (a : A) := sourceGate d a.1.J Q a.1.M gammaStar lambdaStar alpha0 a.1.m a.1.z
  let β (a : A) := gateRoot (S a) K
  let w (a : A) := sourceWeight gammaStar alpha0 a.1.m a.1.b
  let L (a : A) := sourceRate a.1.J gammaStar a.1.b
  let φ (a : A) := sourcePartialPhase U d a.1.J a.1.M gammaStar a.1.z a.1.b
  let ψ (a : A) := sourcePartialPhase U d a.1.J a.1.M gammaStar a.1.z (a.1.b+1)
  have hm (a : A) : 0 < a.1.m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le a.2.2.1
  have hSrange (a : A) : S a ∈ Ioc (0:ℝ) 1 := by
    exact ⟨a.2.2.2.2,(blockGate_range Q a.1.M _ _ a.1.z).2⟩
  have hβ (a : A) : 0 < β a := Real.rpow_pos_of_pos (hSrange a).1 _
  have hβ1 (a : A) : β a ≤ 1 := (gateRoot_bounds (S a) K (hSrange a).1.le (hSrange a).2).2
  have hw (a : A) : 0 ≤ w a := by
    have hma := hm a
    dsimp [w,sourceWeight,sourceGamma]
    positivity
  have hw1 (a : A) : w a ≤ 1 :=
    (sourceWeight_le_gamma gammaStar alpha0 a.1.m a.1.J a.1.b hγ ha0 (Nat.le_of_lt a.2.1) a.2.2.1).trans (by linarith)
  have hL (a : A) : 1 ≤ L a := sourceRate_ge_one a.1.J a.1.b gammaStar hγ (by linarith) (Nat.le_of_lt a.2.1)
  have hφ (a : A) : ContDiffAt ℝ ∞ (φ a) a.1.x := (sourcePartialPhase_smooth U d a.1.J a.1.M gammaStar hγ hγ1 a.1.z a.1.b).contDiffAt
  have hψ (a : A) : ContDiffAt ℝ ∞ (ψ a) a.1.x := (sourcePartialPhase_smooth U d a.1.J a.1.M gammaStar hγ hγ1 a.1.z (a.1.b+1)).contDiffAt
  have hphase (k : ℕ) (hk0 : 0<k) (hk : k≤n) (a : A) :
      β a*‖iteratedFDeriv ℝ k (φ a) a.1.x‖ ≤ C₀*L a^k ∧ β a*‖iteratedFDeriv ℝ k (ψ a) a.1.x‖ ≤ C₀*L a^k := by
    have hbc := hp k hk0 a.1.J a.1.M a.1.b a.1.b (le_refl _) a.1.m (hm a) a.1.z a.1.x
    have hbd := hp k hk0 a.1.J a.1.M a.1.b (a.1.b+1) (by omega) a.1.m (hm a) a.1.z a.1.x
    have hc : P k*w a ≤ C₀ := (mul_le_mul_of_nonneg_left (hw1 a) (hP k)).trans_eq (by ring) |>.trans (hC_PI k hk).1
    constructor
    · exact hbc.trans (by dsimp [w,L] at hc ⊢; nlinarith [mul_le_mul_of_nonneg_right hc (pow_nonneg (zero_lt_one.trans_le (hL a)).le k)])
    · exact hbd.trans (by dsimp [w,L] at hc ⊢; nlinarith [mul_le_mul_of_nonneg_right hc (pow_nonneg (zero_lt_one.trans_le (hL a)).le k)])
  have hinc (k : ℕ) (hk : k≤n) (a : A) :
      β a*‖iteratedFDeriv ℝ k (φ a) a.1.x-iteratedFDeriv ℝ k (ψ a) a.1.x‖ ≤ C₀*w a*L a^k := by
    exact (hi' k a.1.J a.1.M a.1.b a.2.1 a.1.m (hm a) a.1.z a.1.x).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC_PI k hk).2 (hw a)) (pow_nonneg (zero_lt_one.trans_le (hL a)).le k))
  obtain ⟨D,hD,hbound⟩ := oscillatorProfile_difference_jet_bound κ lo hi hlo hlt N hN hκ hκ0 hinterval n
    S β w L (fun a : A => a.1.h) (fun a => a.1.θ) (fun _ => cut) φ ψ (fun a => a.1.x) C₀ hC₀
    hSrange hβ hβ1 hw hL (fun a => a.2.2.2.1) (fun a => hcut01 a.1.x)
    (fun a => hcut.contDiffAt) hφ hψ
    (fun k _ hk a => (hcutjet k hk a.1.x).trans hC_B) hphase hinc
    (fun a => gateRoot_power_budget (S a) K (n+1) (hSrange a).1 (hSrange a).2 hK hn)
  refine ⟨D,hD,?_⟩
  intro J M b hb m hm' z h hh θ x
  let SG := sourceGate d J Q M gammaStar lambdaStar alpha0 m z
  by_cases hSG : 0 < SG
  · exact hbound ⟨⟨J,M,b,m,h,θ,z,x⟩,hb,hm',hh,hSG⟩
  · have hz : SG=0 := le_antisymm (le_of_not_gt hSG) (blockGate_range Q M _ _ z).1
    have he (f : Model.Covariate d → ℝ) : oscillatorProfile κ (intervalCenter lo hi) SG h θ cut f = 0 := by
      funext y
      simp [oscillatorProfile,oscillatorOuter,hz,hκ0]
    change ‖iteratedFDeriv ℝ n (oscillatorProfile κ (intervalCenter lo hi) SG h θ cut _ - oscillatorProfile κ (intervalCenter lo hi) SG h θ cut _) x‖ ≤ _
    rw [he,he,sub_self,iteratedFDeriv_zero]
    simp only [Pi.zero_apply,norm_zero]
    have hm0 : 0 < m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hm'
    unfold sourceWeight sourceRate sourceGamma
    positivity

end RoughRegime.LatticePriors
