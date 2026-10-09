module

public import RoughRegime.SourceLiteralFrame
public import RoughRegime.CanonicalPoissonData
public import RoughRegime.GlobalAffine


@[expose] public section
/-! All deterministic and probability-law parts of admissibility (A1)--(A5)
for the actual canonical source fields. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ContDiff
namespace RoughRegime.LatticePriors
set_option backward.isDefEq.respectTransparency false
namespace CanonicalFrame
variable {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)

 theorem density_outside_region (z : GridPair D N → PairState ι)
     (x : Model.Covariate (D+1)) (hx : x ∉ gridRegion (D+1) N F.offset F.ell) : F.p z x = F.p0 := by
   apply globalDensity_outside F.offset F.ell F.p0 _ _ F.outer F.outer_zero _ _ x
   intro b hxb
   exact hx (gridBlockOpen_subset_region F.offset F.ell F.ell_pos b hxb)

 theorem geometric_pair_mass (z : GridPair D N → PairState ι) (k : GridPair D N) :
     (∫ x in gridBlockClosed F.offset F.ell (k,false) ∪ gridBlockClosed F.offset F.ell (k,true), F.p z x)=F.pairMass := by
   exact globalDensity_geometric_pair_mass F.offset F.ell F.p0 _ _ F.ell_pos F.offset_nonneg F.size_bound
     F.outer F.outer_smooth F.outer_zero (stateAngles z) (statePhases F.U F.M F.a F.q F.gamma z)
     (fun k=>blockPhase_smooth F.U F.M F.a F.q F.gamma (z k).1 F.gamma_pos F.gamma_le) k

 theorem local_density_affine (z : GridPair D N → PairState ι) (b : GridBlock D N)
     (x : Model.Covariate (D+1)) (hx : x ∈ gridBlockClosed F.offset F.ell b) :
     let y := gridCoords F.offset F.ell b x
     let φ := blockPhase F.U F.M F.a F.q F.gamma (z b.1).1 y
     F.p z x = (F.p0+F.outer y*((F.rminus+F.rplus)/2-F.p0)) +
       (Lower.sign b.2*((F.rplus-F.rminus)/2-F.delta)*F.outer y*Real.cos φ)*Real.cos ((z b.1).2.1) +
       (-(Lower.sign b.2*((F.rplus-F.rminus)/2-F.delta)*F.outer y*Real.sin φ))*Real.sin ((z b.1).2.1) :=
   globalDensity_local_affine F.offset F.ell F.p0 _ _ F.ell_pos F.outer F.outer_zero
     (stateAngles z) (statePhases F.U F.M F.a F.q F.gamma z) b x hx

 theorem local_density_profile_products (z : GridPair D N → PairState ι) (b : GridBlock D N)
     (x : Model.Covariate (D+1)) (hx : x ∈ gridBlockClosed F.offset F.ell b) :
     let y := gridCoords F.offset F.ell b x
     let gate := LatticeFourier.jointGate F.Q F.M F.eta F.lambda (z b.1).1
     F.p z x*F.u z x=F.Au*Lower.sign (z b.1).2.2.1*gate*F.inner y ∧
     F.p z x*F.v z x=F.Av*Lower.sign (z b.1).2.2.2*gate*F.inner y := by
   have hp : F.p z x≠0 := ne_of_gt (F.rminus_pos.trans_le
     ((le_add_of_nonneg_right F.delta_pos.le).trans ((F.realization z).margins x).1))
   exact ⟨globalProfile_local_density_product F.offset F.ell F.p0 _ _ F.Au F.ell_pos
     F.inner F.outer F.inner_zero (stateAngles z) (statePhases F.U F.M F.a F.q F.gamma z)
     (stateSignU z) (stateGates F.Q F.M F.eta F.lambda z) b x hx hp,
     globalProfile_local_density_product F.offset F.ell F.p0 _ _ F.Av F.ell_pos
     F.inner F.outer F.inner_zero (stateAngles z) (statePhases F.U F.M F.a F.q F.gamma z)
     (stateSignV z) (stateGates F.Q F.M F.eta F.lambda z) b x hx hp⟩

end CanonicalFrame

namespace SourceLatticeSetup
open RoughRegime.LatticeFourier
variable {D : ℕ} {alpha beta rminus rplus : ℝ} (S : SourceLatticeSetup D alpha beta rminus rplus)

 theorem independent_pairs (N J M : ℕ) (hM : 0<M)
     (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M)
     (positive : Bool) :
     iIndepFun (fun k : GridPair D N=>fun z : GridPair D N → PairState (Fin J × Fin (D+1))=>z k)
       (S.prior N J M hM hscale positive) :=
   globalBlockPrior_independent (S.coefficientPrior J M hM hscale) M positive

 theorem prior_exact_conditional_signs (N J M : ℕ) (hM : 0<M)
     (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M)
     (positive : Bool) :
     S.prior N J M hM hscale positive = Measure.pi (fun _ : GridPair D N=>
       (S.coefficientPrior J M hM hscale).prod (LatticeFourier.angleUniform.compProd (angularSignKernel M positive))) := rfl

end SourceLatticeSetup
end RoughRegime.LatticePriors
