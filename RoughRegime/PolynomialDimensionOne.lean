module

public import RoughRegime.RatePolynomialConsequences


@[expose] public section
/-! The exact scalar-cell regime stated in Section2: nu=2 if and only if
both smoothness exponents lie in(0,1]. Positivity is part of Parameters. -/
noncomputable section
namespace RoughRegime.Model

theorem holderOrder_eq_zero_iff (t : ℝ) (_ht : 0<t) : holderOrder t=0 ↔ t≤1 := by
  constructor
  · intro h
    have hc : Nat.ceil t ≤ 1 := by unfold holderOrder at h; omega
    simpa using (Nat.ceil_le.mp hc)
  · exact holderOrder_eq_zero_of_le_one t

theorem Parameters.nu_eq_two_iff (A : Parameters) : A.nu=2 ↔ A.α≤1 ∧ A.β≤1 := by
  constructor
  · intro h
    have hd := A.hd
    have ha : 0<(A.d+holderOrder A.α).choose A.d := Nat.choose_pos (Nat.le_add_right _ _)
    have hb : 0<(A.d+holderOrder A.β).choose A.d := Nat.choose_pos (Nat.le_add_right _ _)
    have hsum : (A.d+holderOrder A.α).choose A.d+(A.d+holderOrder A.β).choose A.d=2 := h
    have ha1 : (A.d+holderOrder A.α).choose A.d=1 := by omega
    have hb1 : (A.d+holderOrder A.β).choose A.d=1 := by omega
    have ha0 : holderOrder A.α=0 := by
      rcases Nat.choose_eq_one_iff.mp ha1 with he|he
      · omega
      · omega
    have hb0 : holderOrder A.β=0 := by
      rcases Nat.choose_eq_one_iff.mp hb1 with he|he
      · omega
      · omega
    exact ⟨(holderOrder_eq_zero_iff A.α A.hα).mp ha0,(holderOrder_eq_zero_iff A.β A.hβ).mp hb0⟩
  · rintro ⟨ha,hb⟩
    exact A.nu_eq_two_of_le_one ha hb

end RoughRegime.Model
