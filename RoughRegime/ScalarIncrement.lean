module

public import Mathlib


@[expose] public section
/-! The explicit two-child constant-polynomial projection increment displayed
in Section4. The child density means are x1,x2, and the parent mean is their
arithmetic average. This identity explains the four scalar denominator factors
without adding an approximation hypothesis. -/
noncomputable section
namespace RoughRegime.ScalarIncrement

theorem scalar_increment_identity (x1 x2 u1 u2 v1 v2 : ℝ)
    (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0) (hsum : x1+x2 ≠ 0) :
    (u1*v1/x1+u2*v2/x2)/2-
      ((u1+u2)/2)*((v1+v2)/2)/((x1+x2)/2)=
    (x2*u1-x1*u2)*(x2*v1-x1*v2)/(4*x1*x2*((x1+x2)/2)) := by
  field_simp
  ring

end RoughRegime.ScalarIncrement
