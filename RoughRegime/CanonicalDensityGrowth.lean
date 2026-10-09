module

public import RoughRegime.SourceLiteralFrame
public import RoughRegime.HolderGeometry


@[expose] public section
/-! A concrete existence interpretation of the smooth-design remark:
the zero-phase realization of the actual fixed-cutoff construction has
unbounded first derivatives as its blocks shrink. This does not assert
growth for every possible realization or for a parametric path. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def zeroLatticeState (ι : Type*) : PairState ι := (fun _ => 0, (0, (false, false)))
def cutoffOuterPoint (d : ℕ) : Model.Covariate d := WithLp.toLp 2 (fun _ => (1 : ℝ)/8)

theorem cutoffOuterPoint_open (d : ℕ) : cutoffOuterPoint d ∈ unitCubeOpen d := by
  intro q
  norm_num [cutoffOuterPoint]

theorem cubeCenter_open (d : ℕ) : cubeCenter d ∈ unitCubeOpen d := by
  intro q
  norm_num [cubeCenter]

theorem outerBump_center_one (d : ℕ) : outerBump d (cubeCenter d)=1 :=
  (outerBump d).one_of_mem_closedBall (Metric.mem_closedBall_self (outerBump d).rIn_pos.le)

theorem outerBump_outerPoint_zero (D : ℕ) : outerBump (D+1) (cutoffOuterPoint (D+1))=0 := by
  apply (outerBump (D+1)).zero_of_le_dist
  have hq:=PiLp.norm_apply_le (cutoffOuterPoint (D+1)-cubeCenter (D+1)) (0 : Fin (D+1))
  have hl : (3/8 : ℝ) ≤ ‖cutoffOuterPoint (D+1)-cubeCenter (D+1)‖ := by
    convert hq using 1
    norm_num [cutoffOuterPoint,cubeCenter,Real.norm_eq_abs]
  change (1/4 : ℝ) ≤ dist (cutoffOuterPoint (D+1)) (cubeCenter (D+1))
  rw [dist_eq_norm]
  linarith

theorem contrast_one_label (p0 r0 h : ℝ) :
    ∃ b : Bool, h ≤ |r0 + Lower.sign b * h-p0| := by
  by_cases hp : h ≤ |r0+h-p0|
  · exact ⟨true,by simpa [Lower.sign] using hp⟩
  · refine ⟨false,?_⟩
    simp only [Lower.sign,Bool.false_eq_true,ite_false,neg_one_mul]
    have hp' := (abs_lt.mp (lt_of_not_ge hp)).2
    calc
      h ≤ -(r0 + -h-p0) := by linarith
      _ ≤ |r0 + -h-p0| := neg_le_abs _

namespace CanonicalFrame
variable {D N : ℕ} {ι : Type*} [Fintype ι] (F : CanonicalFrame D N ι)

theorem zero_phase_density_local (b : GridBlock D N) (y : Model.Covariate (D+1))
    (hy : y ∈ unitCubeOpen (D+1)) :
    F.p (fun _=>zeroLatticeState ι) (gridEmbed F.offset F.ell b y)=
      F.p0+F.outer y*((F.rminus+F.rplus)/2+
        Lower.sign b.2*((F.rplus-F.rminus)/2-F.delta)-F.p0) := by
  have hx : gridEmbed F.offset F.ell b y ∈ gridBlockOpen F.offset F.ell b := by
    change ∀q,0<gridCoords F.offset F.ell b (gridEmbed F.offset F.ell b y) q ∧
      gridCoords F.offset F.ell b (gridEmbed F.offset F.ell b y) q<1
    rw [gridCoords_embed _ _ _ F.ell_pos.ne']
    exact hy
  unfold p
  rw [globalDensity_eq_local _ _ _ _ _ F.ell_pos _ F.outer_zero _ _ b _ hx,
    gridCoords_embed _ _ _ F.ell_pos.ne']
  simp [blockDensity,blockOscillatingDensity,stateAngles,statePhases,
    blockPhase,zeroLatticeState]

/-- A bound K on all first derivatives is impossible once the actual block
scale is smaller than its fixed density contrast divided by K. -/
theorem zero_phase_derivative_exceeds (hN : 0<N)
    (houter : F.outer=(outerBump (D+1) : Model.Covariate (D+1)→ℝ))
    (K : ℝ)
    (hsmall : K*F.ell*‖cutoffOuterPoint (D+1)-cubeCenter (D+1)‖ <
      (F.rplus-F.rminus)/2-F.delta) :
    ∃x∈Model.cube (D+1),K<‖fderiv ℝ (F.p (fun _=>zeroLatticeState ι)) x‖ := by
  let k : GridPair D N := (⟨0,hN⟩,fun _=>⟨0,by omega⟩)
  obtain ⟨label,hcontrast⟩:=contrast_one_label F.p0 ((F.rminus+F.rplus)/2)
    ((F.rplus-F.rminus)/2-F.delta)
  let b : GridBlock D N := (k,label)
  let x0:=gridEmbed F.offset F.ell b (cubeCenter (D+1))
  let x1:=gridEmbed F.offset F.ell b (cutoffOuterPoint (D+1))
  have hopen (y : Model.Covariate (D+1))(hy : y∈unitCubeOpen (D+1)) :
      gridEmbed F.offset F.ell b y ∈ gridBlockOpen F.offset F.ell b := by
    change ∀q,0<gridCoords F.offset F.ell b (gridEmbed F.offset F.ell b y) q ∧
      gridCoords F.offset F.ell b (gridEmbed F.offset F.ell b y) q<1
    rw [gridCoords_embed _ _ _ F.ell_pos.ne']
    exact hy
  have hx0 : x0∈Model.cube (D+1) := gridBlockOpen_subset_cube _ _ b F.ell_pos
    F.offset_nonneg F.size_bound (hopen _ (cubeCenter_open _))
  have hx1 : x1∈Model.cube (D+1) := gridBlockOpen_subset_cube _ _ b F.ell_pos
    F.offset_nonneg F.size_bound (hopen _ (cutoffOuterPoint_open _))
  have hv0 : F.p (fun _=>zeroLatticeState ι) x0 =
      (F.rminus+F.rplus)/2+Lower.sign label*((F.rplus-F.rminus)/2-F.delta) := by
    rw [zero_phase_density_local F b _ (cubeCenter_open _),houter,outerBump_center_one]
    ring
  have hv1 : F.p (fun _=>zeroLatticeState ι) x1=F.p0 := by
    rw [zero_phase_density_local F b _ (cutoffOuterPoint_open _),houter,outerBump_outerPoint_zero]
    ring
  have hdist : ‖x1-x0‖=F.ell*‖cutoffOuterPoint (D+1)-cubeCenter (D+1)‖ := by
    have he : x1-x0=F.ell • (cutoffOuterPoint (D+1)-cubeCenter (D+1)) := by
      dsimp [x1,x0,gridEmbed]
      module
    rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos F.ell_pos]
  by_contra hn
  push Not at hn
  have hmv := (Model.convex_cube (D+1)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _=>(F.realization (fun _=>zeroLatticeState ι)).density_smooth.differentiable
      (by norm_num) x) hn hx0 hx1
  rw [hv0,hv1,hdist,Real.norm_eq_abs,abs_sub_comm] at hmv
  rw [← mul_assoc] at hmv
  exact (hsmall.trans_le (hcontrast.trans hmv)).false

end CanonicalFrame

namespace SourceLatticeSetup
variable {D : ℕ} {alpha beta rminus rplus : ℝ}
    (S : SourceLatticeSetup D alpha beta rminus rplus)

/-- For one actual zero-phase realization at every sufficiently fine grid,
the first density derivative exceeds every prescribed bound. All source
levels, frequencies, margins and amplitudes remain literal source choices. -/
theorem source_density_derivatives_unbounded (K : ℝ) :
    ∃N0:ℕ,0<N0 ∧ ∀(N:ℕ)(hN:0<N),N0≤N→∀J M:ℕ,∀epsilonU epsilonV delta:ℝ,
      ∀heU:0≤epsilonU,∀heV:0≤epsilonV,∀hd:0<delta,
      ∀hmargin:delta ≤ sourceMarginBound (D+1) S.v0 rminus rplus,
      let F:=S.frame N J M hN epsilonU epsilonV delta heU heV hd hmargin
      ∃x∈Model.cube (D+1),K<‖fderiv ℝ (F.p
        (fun _=>zeroLatticeState (Fin J×Fin (D+1)))) x‖ := by
  let L:=‖cutoffOuterPoint (D+1)-cubeCenter (D+1)‖
  let side:=sourceGridSide S.v0 (D+1)
  have hw : 0<(rplus-rminus)/4 := by linarith [S.interval]
  obtain ⟨N0,hN0⟩:=exists_nat_gt (max 1 (max 0 K*side*L/((rplus-rminus)/4)))
  have hN0pos : 0<N0 := by
    have h1 : (1:ℝ)<N0 := (le_max_left _ _).trans_lt hN0
    exact_mod_cast (zero_lt_one.trans h1)
  refine ⟨N0,hN0pos,?_⟩
  intro N hn hN J M epsilonU epsilonV delta heU heV hd hmargin
  dsimp only
  let F:=S.frame N J M hn epsilonU epsilonV delta heU heV hd hmargin
  have hnR : 0<(N:ℝ) := by exact_mod_cast hn
  have hlarge : max 0 K*side*L < ((rplus-rminus)/4)*(N:ℝ) := by
    have hq : max 0 K*side*L/((rplus-rminus)/4)<(N:ℝ) :=
      (le_max_right _ _).trans_lt (hN0.trans_le (by exact_mod_cast hN))
    nlinarith [(div_lt_iff₀ hw).mp hq]
  have hell : F.ell*(2*(N:ℝ))=side := by
    simpa only [F,frame,sourceCanonicalFrame,Nat.cast_mul,Nat.cast_ofNat] using
      sourceBlockScale_grid_side S.v0 N (D+1) S.volume_pos.le hn (Nat.succ_pos _)
  have hmargin' : delta≤(rplus-rminus)/4 :=
    hmargin.trans (min_le_left _ _)
  apply F.zero_phase_derivative_exceeds hn rfl K
  change K*F.ell*L<(rplus-rminus)/2-delta
  have hK : K*F.ell*L ≤ max 0 K*F.ell*L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) F.ell_pos.le)
      (norm_nonneg _)
  have hm : max 0 K*F.ell*L < (rplus-rminus)/4 := by
    have he : (max 0 K*F.ell*L)*(2*(N:ℝ))=max 0 K*side*L := by
      rw [show max 0 K*F.ell*L*(2*(N:ℝ))=max 0 K*(F.ell*(2*(N:ℝ)))*L by ring,hell]
    have hpos:=F.ell_pos
    nlinarith [hlarge,show 0 ≤ max 0 K*F.ell*L by positivity]
  linarith

end SourceLatticeSetup
end RoughRegime.LatticePriors
