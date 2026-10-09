module

public import RoughRegime.SpatialScores
public import RoughRegime.MeasureScores


@[expose] public section
/-! The supplied dual score identities imply genuine covariance
nondegeneracy; no positive covariance assumption is added. -/
noncomputable section
open MeasureTheory Filter
namespace RoughRegime.MeasureScores

 theorem square_integral_pos_of_score {Z : Type*} [MeasurableSpace Z] (μ:Measure Z)
    (r s:Z→ℝ)(hr:MemLp r 2 μ)(hcross:(∫z,r z*s z ∂μ)=1) :
    0<∫z,(r z)^2 ∂μ := by
  have hn : 0≤∫z,(r z)^2 ∂μ:=integral_nonneg (fun _=>sq_nonneg _)
  by_contra h
  have he : (∫z,(r z)^2 ∂μ)=0:=le_antisymm (le_of_not_gt h) hn
  have hz := (integral_eq_zero_iff_of_nonneg (fun z=>sq_nonneg (r z)) hr.integrable_sq).mp he
  have hec : (fun z=>r z*s z)=ᵐ[μ]fun _=>0 := by
    filter_upwards [hz] with z hz
    change (r z)^2=0 at hz
    have hr0 : r z=0 := by nlinarith
    simp [hr0]
  rw [integral_congr_ae hec,integral_zero] at hcross
  norm_num at hcross

 theorem covariance_positive_of_dual_scores {Z : Type*} [MeasurableSpace Z] (μ:Measure Z)
    (r s su sv:Z→ℝ)(hr:MemLp r 2 μ)(hs:MemLp s 2 μ)
    (hsu:MemLp su 2 μ)(hsv:MemLp sv 2 μ)
    (hru:(∫z,r z*su z ∂μ)=1)(hrv:(∫z,r z*sv z ∂μ)=0)
    (_hsu:(∫z,s z*su z ∂μ)=0)(hsv1:(∫z,s z*sv z ∂μ)=1) :
    0<(∫z,(r z)^2 ∂μ) ∧
      0<(∫z,(r z)^2 ∂μ)*(∫z,(s z)^2 ∂μ)-(∫z,r z*s z ∂μ)^2 := by
  let uu:=∫z,(r z)^2 ∂μ
  let uv:=∫z,r z*s z ∂μ
  let vv:=∫z,(s z)^2 ∂μ
  have huu : 0<uu:=square_integral_pos_of_score μ r su hr hru
  let k:=uv/uu
  let q:=fun z=>s z-k*r z
  have hq : MemLp q 2 μ:=hs.sub (hr.const_mul k)
  have hi_sv:=memLp_one_iff_integrable.mp (hs.mul hsv)
  have hi_rv:=memLp_one_iff_integrable.mp (hr.mul hsv)
  have hqv : (∫z,q z*sv z ∂μ)=1 := by
    have heq : (fun z=>q z*sv z)=fun z=>s z*sv z-k*(r z*sv z) := by funext z;dsimp [q];ring
    rw [heq,integral_sub (f:=fun z=>s z*sv z) (g:=fun z=>k*(r z*sv z)) hi_sv (hi_rv.const_mul k),integral_const_mul,hsv1,hrv]
    ring
  have hqq:=square_integral_pos_of_score μ q sv hq hqv
  have hi_rs:=memLp_one_iff_integrable.mp (hr.mul hs)
  have hex : (fun z=>(q z)^2)=fun z=>(s z)^2-(2*k)*(r z*s z)+k^2*(r z)^2 := by
    funext z;dsimp [q];ring
  rw [hex,integral_add (f:=fun z=>(s z)^2-(2*k)*(r z*s z)) (g:=fun z=>k^2*(r z)^2)
    (hs.integrable_sq.sub (hi_rs.const_mul (2*k)))
    (hr.integrable_sq.const_mul (k^2)),integral_sub (f:=fun z=>(s z)^2) (g:=fun z=>(2*k)*(r z*s z)) hs.integrable_sq (hi_rs.const_mul (2*k)),
    integral_const_mul,integral_const_mul] at hqq
  have hid : vv-2*k*uv+k^2*uu=(uu*vv-uv^2)/uu := by
    dsimp [k]
    field_simp [huu.ne']
    ring
  change 0<vv-2*k*uv+k^2*uu at hqq
  rw [hid] at hqq
  exact ⟨huu,(div_pos_iff_of_pos_right huu).mp hqq⟩

end RoughRegime.MeasureScores
