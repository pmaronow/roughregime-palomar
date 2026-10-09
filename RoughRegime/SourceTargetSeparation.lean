module

public import RoughRegime.SourceLiteralFrame


@[expose] public section
/-! The original positive separation constant for the actual globally glued
profiles, with the shrinking margin and fixed source choices discharged. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.LatticeFourier RoughRegime.Upper
set_option backward.isDefEq.respectTransparency false

namespace CanonicalFrame
 def productIntegral {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)
     (z : GridPair D N → PairState ι) : ℝ :=
   ∫ x, F.p z x*F.u z x*F.v z x ∂Model.cubeVolume (D+1)
end CanonicalFrame

namespace SourceLatticeSetup
variable {D : ℕ} {alpha beta rminus rplus : ℝ} (S : SourceLatticeSetup D alpha beta rminus rplus)

 theorem target_separation (N J M : ℕ) (hN : 0<N) (hM : 0<M) (heven : Even M)
    (hscale : sourceFineScale J (min alpha beta) ≤ sourceBandConstant (D+1) alpha beta*M)
    (epsilonU epsilonV delta : ℝ) (heU : 0≤epsilonU) (heV : 0≤epsilonV) (hd : 0<delta)
    (hmargin : delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus) :
    let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
    S.separationConstant*F.Au*F.Av*intervalRho (rminus+delta) (rplus-delta)^M ≤
      (∫ z, F.productIntegral z ∂S.prior N J M hM hscale true) -
      (∫ z, F.productIntegral z ∂S.prior N J M hM hscale false) := by
   dsimp only
   let F := S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
   have hδr : delta ≤ (rplus-rminus)/4 := hmargin.trans (min_le_left _ _)
   have hlo : 0<rminus+delta := add_pos S.lower_pos hd
   have hlt : rminus+delta<rplus-delta := by linarith [S.interval]
   have hp0 : rminus+delta≤F.p0 ∧ F.p0≤rplus-delta := by
     have h0 := F.delta_p0
     have h1 := F.delta_p1
     change delta≤(F.p0-rminus)/2 at h0
     change delta≤(rplus-F.p0)/2 at h1
     constructor <;> linarith
   have hcenter : intervalCenter (rminus+delta) (rplus-delta)=intervalCenter rminus rplus := by
     unfold intervalCenter; ring
   have hhalf : intervalHalfWidth (rminus+delta) (rplus-delta)=(rplus-rminus)/2-delta := by
     unfold intervalHalfWidth; ring
   have htarget : F.productIntegral = canonicalProductTarget (N:=N) canonicalStep
       (sourceGateOrder alpha beta) M (fun i : Fin J × Fin (D+1)=>J-i.1.val) Prod.snd
       (fun i=>sourceGamma (sourceGammaStar (D+1)) i.1.val) (S.eta J)
       (fun i=>sourceLambda (sourceLambdaStar (D+1) alpha beta) i.1.val)
       F.offset F.ell F.p0 (rminus+delta) (rplus-delta) F.Au F.Av
       (innerBump (D+1)) (outerBump (D+1)) := by
     funext z
     unfold CanonicalFrame.productIntegral canonicalProductTarget
     rw [hcenter,hhalf]
     simp only [F,frame,sourceCanonicalFrame,CanonicalFrame.p,CanonicalFrame.u,CanonicalFrame.v,
       globalProductTarget,intervalCenter,SourceLatticeSetup.eta,add_comm rplus rminus]
     rfl
   have hsep := canonical_global_separation (N:=N) canonicalStep (sourceGateOrder alpha beta) M J
     (fun i : Fin J × Fin (D+1)=>J-i.1.val) Prod.snd (S.eta J) (by have:=S.Q_ge_three; omega)
     hM heven (S.eta_pos J) (S.eta_band J M hscale)
     (sourceGammaStar (D+1)) (sourceLambdaStar (D+1) alpha beta)
     S.gamma_bounds.1 S.gamma_bounds.2.1 S.lambda_ge_one (by simpa only [Nat.cast_add,Nat.cast_one] using (sourceLambdaStar_budget (D+1) alpha beta S.alpha_pos))
     F.offset F.ell F.p0 (rminus+delta) (rplus-delta) F.Au F.Av
     F.ell_pos F.offset_nonneg F.size_bound hlo hlt hp0
     (innerBump (D+1)) (outerBump (D+1)) (innerBump_smooth _) (outerBump_smooth _)
     (innerBump_zero_outside _) (outerBump_zero_outside _)
     (fun _=>⟨(outerBump (D+1)).nonneg,(outerBump (D+1)).le_one⟩)
     (outerBump_one_on_inner _)
     (fun _=>by rw [abs_of_nonneg (innerBump (D+1)).nonneg]; exact (innerBump (D+1)).le_one)
     (by simpa only [sourceInnerSquareIntegral,Nat.cast_add,Nat.cast_one] using S.gamma_bounds.2.2) F.Au_nonneg F.Av_nonneg
   dsimp only at hsep
   change _≤(∫ z,F.productIntegral z ∂_)-(∫ z,F.productIntegral z ∂_)
   rw [htarget]
   have hv := S.frame_volume N J M hN epsilonU epsilonV delta heU heV hd hmargin
   change (F.ell*(2*N:ℕ))^(D+1)=S.v0 at hv
   simpa only [sourceGamma,sourceLambda,prior,coefficientPrior,separationConstant,sourceInnerSquareIntegral,
     hv,hcenter] using hsep

end SourceLatticeSetup
end RoughRegime.LatticePriors
