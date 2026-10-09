module

public import RoughRegime.RatePolynomialConsequences
public import RoughRegime.ApplicationSeparatedBrackets
public import RoughRegime.ApplicationEtaTreatment


@[expose] public section
/-! The original polynomial-rate and HOIF-exclusion consequences on the
four separated-density rows and three literal eta treatment rows. Other
application rows use `Model.Bracket.log_polynomial_exponent` and
`Model.Bracket.not_hoif_upper` with their proved ordinary brackets. -/
noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace RoughRegime.Applications.SeparatedMAR

private theorem qualified_polynomial_exponent {Ω : Type*} [MeasurableSpace Ω]
    (T : ProbabilityMeasure Ω→ℝ) (C : Set (ProbabilityMeasure Ω))
    (A : Model.Parameters) (ν : ℝ)
    (hb : Model.LowerBracket T C A.bracketParameters ∧
      ∀ (ζ : ℝ) (hζ : 0<ζ) (hζ1 : ζ<1),
        Model.UpperBracket T C (enlargedBracketParameters A ζ hζ hζ1) ν) :
    Tendsto (fun n : ℕ => Real.log (Model.minimaxRMSE n T C).toReal/Real.log n)
      atTop (𝓝 (-min (1/2:ℝ) A.theta)) := by
  apply Model.separated_log_polynomial_exponent T C A.bracketParameters ν hb.1
  exact hb.2

private theorem qualified_not_hoif_upper {Ω : Type*} [MeasurableSpace Ω]
    (T : ProbabilityMeasure Ω→ℝ) (C : Set (ProbabilityMeasure Ω))
    (A : Model.Parameters) (ν : ℝ)
    (hb : Model.LowerBracket T C A.bracketParameters ∧
      ∀ (ζ : ℝ) (hζ : 0<ζ) (hζ1 : ζ<1),
        Model.UpperBracket T C (enlargedBracketParameters A ζ hζ hζ1) ν)
    (hrough : A.theta<1/2) (e : ℕ→ℝ) (he : Tendsto e atTop (𝓝 0)) (K : ℝ) (hK : 0<K) :
    ¬∀ᶠ n : ℕ in atTop,Model.minimaxRMSE n T C≤
      ENNReal.ofReal (K*(n:ℝ)^(-Model.hoifExponent A.theta+e n)) := by
  apply Model.separated_not_hoif_upper T C A.bracketParameters ν hb.1 _ hrough e he K hK
  exact hb.2

theorem log_polynomial_exponent (A : Model.Parameters) (hδ : A.δ<1/2)
    (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H) :
    Tendsto (fun n : ℕ => Real.log (Model.minimaxRMSE n (target A.d) (modelClass A)).toReal/Real.log n)
      atTop (𝓝 (-min (1/2:ℝ) A.theta)) :=
  qualified_polynomial_exponent _ _ A _ (qualified_bracket A hδ hlo hhi hH)

theorem not_hoif_upper (A : Model.Parameters) (hδ : A.δ<1/2)
    (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H)
    (hrough : A.theta<1/2) (e : ℕ→ℝ) (he : Tendsto e atTop (𝓝 0)) (K : ℝ) (hK : 0<K) :
    ¬∀ᶠ n : ℕ in atTop,Model.minimaxRMSE n (target A.d) (modelClass A)≤
      ENNReal.ofReal (K*(n:ℝ)^(-Model.hoifExponent A.theta+e n)) :=
  qualified_not_hoif_upper _ _ A _ (qualified_bracket A hδ hlo hhi hH) hrough e he K hK

end RoughRegime.Applications.SeparatedMAR

namespace RoughRegime.Applications.SeparatedTreatment

theorem treatment_polynomial_exponents (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H) :
    let C := modelClass A β1 hβ1
    Tendsto (fun n : ℕ => Real.log (Model.minimaxRMSE n (MAR.ate A.d) C).toReal/Real.log n)
      atTop (𝓝 (-min (1/2:ℝ) (MAR.treatmentParameters A β1 hβ1).theta)) ∧
    Tendsto (fun n : ℕ => Real.log (Model.minimaxRMSE n (MAR.att A.d) C).toReal/Real.log n)
      atTop (𝓝 (-min (1/2:ℝ) A.theta)) ∧
    Tendsto (fun n : ℕ => Real.log (Model.minimaxRMSE n (MAR.atu A.d) C).toReal/Real.log n)
      atTop (𝓝 (-min (1/2:ℝ) (MAR.parametersWithBeta A β1 hβ1).theta)) := by
  obtain ⟨h0,h1,h2⟩ := qualified_treatment_brackets A β1 hβ1 hδ hlo hhi hH
  exact ⟨SeparatedMAR.qualified_polynomial_exponent _ _ _ _ h0,
    SeparatedMAR.qualified_polynomial_exponent _ _ _ _ h1,
    SeparatedMAR.qualified_polynomial_exponent _ _ _ _ h2⟩

theorem treatment_not_hoif_upper (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H)
    (e : ℕ→ℝ) (he : Tendsto e atTop (𝓝 0)) (K : ℝ) (hK : 0<K) :
    let C := modelClass A β1 hβ1
    ((MAR.treatmentParameters A β1 hβ1).theta<1/2 →
      ¬∀ᶠ n : ℕ in atTop,Model.minimaxRMSE n (MAR.ate A.d) C≤
        ENNReal.ofReal (K*(n:ℝ)^(-Model.hoifExponent (MAR.treatmentParameters A β1 hβ1).theta+e n))) ∧
    (A.theta<1/2 → ¬∀ᶠ n : ℕ in atTop,Model.minimaxRMSE n (MAR.att A.d) C≤
        ENNReal.ofReal (K*(n:ℝ)^(-Model.hoifExponent A.theta+e n))) ∧
    ((MAR.parametersWithBeta A β1 hβ1).theta<1/2 →
      ¬∀ᶠ n : ℕ in atTop,Model.minimaxRMSE n (MAR.atu A.d) C≤
        ENNReal.ofReal (K*(n:ℝ)^(-Model.hoifExponent (MAR.parametersWithBeta A β1 hβ1).theta+e n))) := by
  obtain ⟨h0,h1,h2⟩ := qualified_treatment_brackets A β1 hβ1 hδ hlo hhi hH
  exact ⟨fun hr => SeparatedMAR.qualified_not_hoif_upper _ _ _ _ h0 hr e he K hK,
    fun hr => SeparatedMAR.qualified_not_hoif_upper _ _ _ _ h1 hr e he K hK,
    fun hr => SeparatedMAR.qualified_not_hoif_upper _ _ _ _ h2 hr e he K hK⟩

end RoughRegime.Applications.SeparatedTreatment

namespace RoughRegime.Applications.MAR

theorem eta_treatment_polynomial_exponents (d : ℕ) (α β0 β1 H η : ℝ) (hd : 1≤d)
    (hα : 0<α) (hβ0 : 0<β0) (hβ1 : 0<β1) (hH : 2<H)
    (hη : 0<η) (hηquarter : η<1/4) :
    let hH0 := (by norm_num : (0:ℝ)<2).trans hH
    let A := etaParameters d α β0 H η hd hα hβ0 hH0 hη hηquarter
    let C := etaTreatmentClass d α β0 β1 H η hd hα hβ0 hβ1 hH0 hη hηquarter
    Tendsto (fun n : ℕ => Real.log (Model.minimaxRMSE n (ate d) C).toReal/Real.log n)
      atTop (𝓝 (-min (1/2:ℝ) (treatmentParameters A β1 hβ1).theta)) ∧
    Tendsto (fun n : ℕ => Real.log (Model.minimaxRMSE n (att d) C).toReal/Real.log n)
      atTop (𝓝 (-min (1/2:ℝ) A.theta)) ∧
    Tendsto (fun n : ℕ => Real.log (Model.minimaxRMSE n (atu d) C).toReal/Real.log n)
      atTop (𝓝 (-min (1/2:ℝ) (parametersWithBeta A β1 hβ1).theta)) := by
  obtain ⟨h0,h1,h2⟩ := eta_treatment_brackets d α β0 β1 H η hd hα hβ0 hβ1 hH hη hηquarter
  exact ⟨h0.log_polynomial_exponent,h1.log_polynomial_exponent,h2.log_polynomial_exponent⟩

theorem eta_treatment_not_hoif_upper (d : ℕ) (α β0 β1 H η : ℝ) (hd : 1≤d)
    (hα : 0<α) (hβ0 : 0<β0) (hβ1 : 0<β1) (hH : 2<H)
    (hη : 0<η) (hηquarter : η<1/4) (e : ℕ→ℝ) (he : Tendsto e atTop (𝓝 0))
    (K : ℝ) (hK : 0<K) :
    let hH0 := (by norm_num : (0:ℝ)<2).trans hH
    let A := etaParameters d α β0 H η hd hα hβ0 hH0 hη hηquarter
    let C := etaTreatmentClass d α β0 β1 H η hd hα hβ0 hβ1 hH0 hη hηquarter
    ((treatmentParameters A β1 hβ1).theta<1/2 →
      ¬∀ᶠ n : ℕ in atTop,Model.minimaxRMSE n (ate d) C≤
        ENNReal.ofReal (K*(n:ℝ)^(-Model.hoifExponent (treatmentParameters A β1 hβ1).theta+e n))) ∧
    (A.theta<1/2 → ¬∀ᶠ n : ℕ in atTop,Model.minimaxRMSE n (att d) C≤
        ENNReal.ofReal (K*(n:ℝ)^(-Model.hoifExponent A.theta+e n))) ∧
    ((parametersWithBeta A β1 hβ1).theta<1/2 →
      ¬∀ᶠ n : ℕ in atTop,Model.minimaxRMSE n (atu d) C≤
        ENNReal.ofReal (K*(n:ℝ)^(-Model.hoifExponent (parametersWithBeta A β1 hβ1).theta+e n))) := by
  obtain ⟨h0,h1,h2⟩ := eta_treatment_brackets d α β0 β1 H η hd hα hβ0 hβ1 hH hη hηquarter
  exact ⟨fun hr=>h0.not_hoif_upper hr e he K hK,
    fun hr=>h1.not_hoif_upper hr e he K hK,fun hr=>h2.not_hoif_upper hr e he K hK⟩

theorem treatment_nu_eq_two (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hα : A.α≤1) (hβ0 : A.β≤1) (hβ1le : β1≤1) :
    (treatmentParameters A β1 hβ1).nu=2 ∧ A.nu=2 ∧ (parametersWithBeta A β1 hβ1).nu=2 :=
  ⟨Model.Parameters.nu_eq_two_of_le_one _ hα ((min_le_left _ _).trans hβ0),
    A.nu_eq_two_of_le_one hα hβ0,Model.Parameters.nu_eq_two_of_le_one _ hα hβ1le⟩

end RoughRegime.Applications.MAR
