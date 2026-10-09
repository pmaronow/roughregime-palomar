module

public import RoughRegime.ModelRateConstants


@[expose] public section
/-! Changing only the two density endpoints, with all remaining statistical
class parameters fixed. -/
noncomputable section
namespace RoughRegime.Model

def densityIntervalDomain : Set (ℝ×ℝ) := {I | 0<I.1 ∧ I.1<I.2}

def densityParameters (A : Parameters) (I : ℝ×ℝ) (hI : I∈densityIntervalDomain) : Parameters :=
  { A with gminus:=I.1, gplus:=I.2, hgminus:=hI.1, hgplus:=hI.2 }

@[simp] theorem densityParameters_theta (A : Parameters) (I : ℝ×ℝ) (hI : I∈densityIntervalDomain) :
    (densityParameters A I hI).theta=A.theta := rfl
@[simp] theorem densityParameters_nu (A : Parameters) (I : ℝ×ℝ) (hI : I∈densityIntervalDomain) :
    (densityParameters A I hI).nu=A.nu := rfl
@[simp] theorem densityParameters_alpha (A : Parameters) (I : ℝ×ℝ) (hI : I∈densityIntervalDomain) :
    (densityParameters A I hI).α=A.α := rfl
@[simp] theorem densityParameters_beta (A : Parameters) (I : ℝ×ℝ) (hI : I∈densityIntervalDomain) :
    (densityParameters A I hI).β=A.β := rfl
@[simp] theorem densityParameters_lo (A : Parameters) (I : ℝ×ℝ) (hI : I∈densityIntervalDomain) :
    (densityParameters A I hI).gminus=I.1 := rfl
@[simp] theorem densityParameters_hi (A : Parameters) (I : ℝ×ℝ) (hI : I∈densityIntervalDomain) :
    (densityParameters A I hI).gplus=I.2 := rfl

end RoughRegime.Model
