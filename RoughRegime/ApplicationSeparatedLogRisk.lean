module

public import RoughRegime.SeparatedLogRisk
public import RoughRegime.SeparatedMARLower
public import RoughRegime.ApplicationSeparatedUpper
public import RoughRegime.ApplicationSeparatedTreatmentUpper
public import RoughRegime.SeparatedTreatmentLower


@[expose] public section
/-! The logarithmic risk expansion of Corollary 3 on the literal separated
density classes, derived from their proved lower and qualified upper bounds. -/

noncomputable section
open MeasureTheory Filter Asymptotics
open scoped ENNReal Topology

namespace RoughRegime.Applications.SeparatedMAR

theorem enlargedBracketParameters_eq_widened (A : Model.Parameters)
    (ζ : ℝ) (hζ : 0<ζ) (hζ1 : ζ<1) :
    enlargedBracketParameters A ζ hζ hζ1=
      Model.widenedBracketParameters A.bracketParameters ζ hζ hζ1 := rfl

theorem separated_log_risk (A : Model.Parameters)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H)
    (hrough : A.theta<1/2) :
    (fun n : ℕ => Real.log (Model.minimaxRMSE n (target A.d) (modelClass A)).toReal+
      A.theta*Real.log n+Rates.kappa A.theta (Rates.tau A.gminus A.gplus)*Real.sqrt (Real.log n))
      =o[atTop] (fun n : ℕ => Real.sqrt (Real.log n)) := by
  apply Model.separated_log_risk (target A.d) (modelClass A) A.bracketParameters (A.nu:ℝ) hrough
    (lowerBracket A hδ hlo hhi hH)
  intro ζ hζ hζ1
  rw [←enlargedBracketParameters_eq_widened]
  exact separated_upperBracket A ζ hζ hζ1

end RoughRegime.Applications.SeparatedMAR

namespace RoughRegime.Applications.SeparatedTreatment

theorem ate_log_risk (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H)
    (hrough : (MAR.treatmentParameters A β1 hβ1).theta<1/2) :
    (fun n : ℕ => Real.log (Model.minimaxRMSE n (MAR.ate A.d) (modelClass A β1 hβ1)).toReal+
      (MAR.treatmentParameters A β1 hβ1).theta*Real.log n+
      Rates.kappa (MAR.treatmentParameters A β1 hβ1).theta (Rates.tau A.gminus A.gplus)*
        Real.sqrt (Real.log n)) =o[atTop] (fun n : ℕ => Real.sqrt (Real.log n)) := by
  apply Model.separated_log_risk (MAR.ate A.d) (modelClass A β1 hβ1)
    (MAR.treatmentParameters A β1 hβ1).bracketParameters
    ((MAR.treatmentParameters A β1 hβ1).nu:ℝ) hrough
    (ate_lowerBracket A β1 hβ1 hδ hlo hhi hH)
  intro ζ hζ hζ1
  rw [←SeparatedMAR.enlargedBracketParameters_eq_widened]
  exact ate_upperBracket A β1 hβ1 ζ hζ hζ1

theorem att_log_risk (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H)
    (hrough : A.theta<1/2) :
    (fun n : ℕ => Real.log (Model.minimaxRMSE n (MAR.att A.d) (modelClass A β1 hβ1)).toReal+
      A.theta*Real.log n+Rates.kappa A.theta (Rates.tau A.gminus A.gplus)*Real.sqrt (Real.log n))
      =o[atTop] (fun n : ℕ => Real.sqrt (Real.log n)) := by
  apply Model.separated_log_risk (MAR.att A.d) (modelClass A β1 hβ1) A.bracketParameters (A.nu:ℝ)
    hrough (att_lowerBracket A β1 hβ1 hδ hlo hhi hH)
  intro ζ hζ hζ1
  rw [←SeparatedMAR.enlargedBracketParameters_eq_widened]
  exact att_upperBracket A β1 hβ1 ζ hζ hζ1

theorem atu_log_risk (A : Model.Parameters) (β1 : ℝ) (hβ1 : 0<β1)
    (hδ : A.δ<1/2) (hlo : A.gminus<1) (hhi : 1<A.gplus) (hH : 1<A.H)
    (hrough : (MAR.parametersWithBeta A β1 hβ1).theta<1/2) :
    (fun n : ℕ => Real.log (Model.minimaxRMSE n (MAR.atu A.d) (modelClass A β1 hβ1)).toReal+
      (MAR.parametersWithBeta A β1 hβ1).theta*Real.log n+
      Rates.kappa (MAR.parametersWithBeta A β1 hβ1).theta (Rates.tau A.gminus A.gplus)*
        Real.sqrt (Real.log n)) =o[atTop] (fun n : ℕ => Real.sqrt (Real.log n)) := by
  apply Model.separated_log_risk (MAR.atu A.d) (modelClass A β1 hβ1)
    (MAR.parametersWithBeta A β1 hβ1).bracketParameters
    ((MAR.parametersWithBeta A β1 hβ1).nu:ℝ) hrough
    (atu_lowerBracket A β1 hβ1 hδ hlo hhi hH)
  intro ζ hζ hζ1
  rw [←SeparatedMAR.enlargedBracketParameters_eq_widened]
  exact atu_upperBracket A β1 hβ1 ζ hζ hζ1

end RoughRegime.Applications.SeparatedTreatment
