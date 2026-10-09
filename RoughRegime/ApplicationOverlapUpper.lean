module

public import RoughRegime.ApplicationOverlapBounds
public import RoughRegime.RatioBracket


@[expose] public section
/-! The genuine overlap-effect upper bracket, with the minimum regularity
index and the exact dimension exponent at its ties. -/
noncomputable section
open MeasureTheory Set
namespace RoughRegime.Applications.Overlap
set_option backward.isDefEq.respectTransparency false

 def effectiveParameters (A : Model.Parameters) : Model.Parameters :=
  {A with β:=min A.α A.β,hβ:=lt_min A.hα A.hβ}
 def bracketParameters (A : Model.Parameters) := (effectiveParameters A).bracketParameters
 def nu (A : Model.Parameters) : ℕ := (effectiveParameters A).nu
 theorem theta_eq (A : Model.Parameters) : (bracketParameters A).theta=
    min ((A.α+A.β)/A.d) (2*A.α/A.d) := by
  have hd : 0<(A.d:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one A.hd)
  change (A.α+min A.α A.β)/A.d=_
  rcases le_total A.α A.β with h | h
  · rw [min_eq_left h,min_eq_right]
    · ring
    · exact (div_le_div_iff_of_pos_right hd).mpr (by linarith)
  · rw [min_eq_right h,min_eq_left]
    exact (div_le_div_iff_of_pos_right hd).mpr (by linarith)
 theorem nu_eq (A : Model.Parameters) : nu A=
    (A.d+Model.holderOrder A.α).choose A.d+
      (A.d+Model.holderOrder (min A.α A.β)).choose A.d := rfl

 theorem upperBracket (A : Model.Parameters) (ε : ℝ) (hε : 0<ε) (hεhalf : ε<1/2)
    (hM : 1≤A.M0) (hδ : A.δ≤1) :
    Model.UpperBracket (effect A.d) (modelClass A ε) (bracketParameters A) (nu A:ℝ) := by
  have hd : 0<(A.d:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one A.hd)
  have htN : (bracketParameters A).theta≤A.bracketParameters.theta :=
    (div_le_div_iff_of_pos_right hd).mpr (by
      change A.α+min A.α A.β≤A.α+A.β
      linarith [min_le_right A.α A.β])
  have htD : (bracketParameters A).theta≤(diagonalParameters A).bracketParameters.theta :=
    (div_le_div_iff_of_pos_right hd).mpr (by
      change A.α+min A.α A.β≤A.α+A.α
      linarith [min_le_left A.α A.β])
  have hnN : (bracketParameters A).theta=A.bracketParameters.theta → (A.nu:ℝ)≤nu A := by
    intro he
    have hm : min A.α A.β=A.β := by
      change (A.α+min A.α A.β)/A.d=(A.α+A.β)/A.d at he
      have hh := (div_left_inj' (ne_of_gt hd)).mp he
      linarith
    simp only [nu,effectiveParameters,Model.Parameters.nu,hm]
    exact le_refl _
  have hnD : (bracketParameters A).theta=(diagonalParameters A).bracketParameters.theta →
      ((diagonalParameters A).nu:ℝ)≤nu A := by
    intro he
    have hm : min A.α A.β=A.α := by
      change (A.α+min A.α A.β)/A.d=(A.α+A.α)/A.d at he
      have hh := (div_left_inj' (ne_of_gt hd)).mp he
      linarith
    simp only [nu,effectiveParameters,Model.Parameters.nu,hm]
    exact le_refl _
  have hc : 0<ε*(1-ε) := mul_pos hε (by linarith)
  have hcu : ε*(1-ε)≤1/4 := by nlinarith [sq_nonneg (ε-1/2)]
  exact Model.ratio_upperBracket_selected (numerator A.d) (denominator A.d) (modelClass A ε)
    A.bracketParameters (diagonalParameters A).bracketParameters (bracketParameters A)
    A.nu (diagonalParameters A).nu (nu A)
    (numerator_upperBracket A ε hM hδ) (denominator_upperBracket A ε hM hδ)
    (by exact_mod_cast (effectiveParameters A).nu_ge_two) rfl rfl rfl rfl htN htD hnN hnD
    (1/4) (ε*(1-ε)) (1/4) (by norm_num) hc hcu
    (fun P _=>abs_le.mp (numerator_bound A P))
    (by rintro P ⟨W⟩;exact denominator_bounds A ε hε hεhalf P W)

end RoughRegime.Applications.Overlap
