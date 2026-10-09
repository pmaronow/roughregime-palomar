module

public import RoughRegime.SpatialScores


@[expose] public section
/-! The actual hard-law target integrand has the required nonzero mixed
interaction derivative, derived from the residual score identities. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RoughRegime.SpatialAffine
set_option backward.isDefEq.respectTransparency false
variable (A : Model.Parameters) {Z : Type*} [MeasurableSpace Z]
  (O : Model.Observables Z A) (π : ProbabilityMeasure Z) (S : Scores (π : Measure Z))

 theorem affineIntegrand_eq_embedded (hbase : Model.baselineW A O π ≠ 0)
     (huu : residualMomentU A O π S true=1) (huv : residualMomentU A O π S false=0)
     (hvu : residualMomentV A O π S true=0) (hvv : residualMomentV A O π S false=1)
     (u v : ℝ) (hw : affineMean π S O.D u v ≠ 0) :
     affineIntegrand A O π S u v = AffineResponseLower.embeddedIntegrand (π : Measure Z)
       S.su S.sv O.D O.W O.lam (Model.baselineA A O π) (Model.baselineB A O π) u v := by
   unfold affineIntegrand
   rw [affineMean_U A O π S hbase,affineMean_V A O π S hbase,huu,huv,hvu,hvv]
   simp only [one_mul,zero_mul,add_zero]
   unfold affineMean AffineResponseLower.embeddedIntegrand Applications.localIntegrand
   have hw' : (∫ z, O.D z ∂(π : Measure Z))+(∫ z, O.D z*S.su z ∂(π : Measure Z))*u+
       (∫ z, O.D z*S.sv z ∂(π : Measure Z))*v ≠ 0 := by simpa [affineMean,mul_comm] using hw
   unfold affineMean at hw
   field_simp [hw,hw']
   ring

 theorem nested_deriv_eq_of_eq_on_open (F G : ℝ → ℝ → ℝ) (V : Set (ℝ×ℝ))
     (hV : IsOpen V) (h0 : (0:ℝ×ℝ)∈V) (he : ∀ p∈V, F p.1 p.2=G p.1 p.2) :
     deriv (fun u => deriv (F u) 0) 0=deriv (fun u => deriv (G u) 0) 0 := by
   apply Filter.EventuallyEq.deriv_eq
   have hU : IsOpen ((fun u : ℝ => (u,(0:ℝ))) ⁻¹' V) := hV.preimage (continuous_id.prodMk continuous_const)
   have hU0 : (0:ℝ)∈((fun u : ℝ => (u,(0:ℝ))) ⁻¹' V) := h0
   filter_upwards [hU.mem_nhds hU0] with u hu
   apply Filter.EventuallyEq.deriv_eq
   have hW : IsOpen ((fun v : ℝ => (u,v)) ⁻¹' V) := hV.preimage (continuous_const.prodMk continuous_id)
   filter_upwards [hW.mem_nhds hu] with v hv
   exact he (u,v) hv

 theorem affineIntegrand_mixed_derivative (hbase : Model.baselineW A O π ≠ 0)
     (huu : residualMomentU A O π S true=1) (huv : residualMomentU A O π S false=0)
     (hvu : residualMomentV A O π S true=0) (hvv : residualMomentV A O π S false=1) :
     deriv (fun u => deriv (fun v => affineIntegrand A O π S u v) 0) 0 = O.lam/Model.baselineW A O π := by
   rw [nested_deriv_eq_of_eq_on_open _ _ (denominatorDomain A O π S)
     (denominatorDomain_open A O π S) (denominatorDomain_zero A O π S hbase)
     (fun p hp => affineIntegrand_eq_embedded A O π S hbase huu huv hvu hvv p.1 p.2 hp)]
   unfold AffineResponseLower.embeddedIntegrand
   exact Applications.localIntegrand_mixed_derivative _ _ _ _ _ _ _ hbase

 theorem affineIntegrand_interaction_nonzero (hbase : Model.baselineW A O π ≠ 0)
     (huu : residualMomentU A O π S true=1) (huv : residualMomentU A O π S false=0)
     (hvu : residualMomentV A O π S true=0) (hvv : residualMomentV A O π S false=1) :
     deriv (fun u => deriv (fun v => affineIntegrand A O π S u v) 0) 0 ≠ 0 := by
   rw [affineIntegrand_mixed_derivative A O π S hbase huu huv hvu hvv]
   exact div_ne_zero O.hlam hbase

 theorem affineIntegrand_eq_embedded_diagonal (hbase : Model.baselineW A O π ≠ 0)
     (hUV : O.U=O.V) (hS : S.su=S.sv) (huu : residualMomentU A O π S true=1)
     (u v : ℝ) (hw : affineMean π S O.D u v ≠ 0) :
     affineIntegrand A O π S u v = AffineResponseLower.embeddedDiagonalIntegrand (π : Measure Z)
       S.su O.D O.W O.lam (Model.baselineA A O π) u v := by
   have huv : residualMomentU A O π S false=1 := by
     have he : residualMomentU A O π S false=residualMomentU A O π S true := by simp [residualMomentU,hS]
     exact he.trans huu
   unfold affineIntegrand
   rw [← hUV,affineMean_U A O π S hbase,huu,huv]
   simp only [one_mul]
   unfold affineMean AffineResponseLower.embeddedDiagonalIntegrand Applications.diagonalIntegrand
   rw [← hS]
   unfold affineMean at hw
   rw [← hS] at hw
   have hw' : (∫ z, O.D z ∂(π : Measure Z))+(∫ z, O.D z*S.su z ∂(π : Measure Z))*u+
       (∫ z, O.D z*S.su z ∂(π : Measure Z))*v ≠ 0 := by simpa [mul_comm] using hw
   field_simp [hw,hw']
   ring

 theorem affineIntegrand_mixed_derivative_diagonal (hbase : Model.baselineW A O π ≠ 0)
     (hUV : O.U=O.V) (hS : S.su=S.sv) (huu : residualMomentU A O π S true=1) :
     deriv (fun u => deriv (fun v => affineIntegrand A O π S u v) 0) 0 = 2*O.lam/Model.baselineW A O π := by
   rw [nested_deriv_eq_of_eq_on_open _ _ (denominatorDomain A O π S)
     (denominatorDomain_open A O π S) (denominatorDomain_zero A O π S hbase)
     (fun p hp => affineIntegrand_eq_embedded_diagonal A O π S hbase hUV hS huu p.1 p.2 hp)]
   unfold AffineResponseLower.embeddedDiagonalIntegrand
   exact Applications.diagonalIntegrand_mixed_derivative _ _ _ _ _ _ _ hbase

 theorem affineIntegrand_interaction_nonzero_diagonal (hbase : Model.baselineW A O π ≠ 0)
     (hUV : O.U=O.V) (hS : S.su=S.sv) (huu : residualMomentU A O π S true=1) :
     deriv (fun u => deriv (fun v => affineIntegrand A O π S u v) 0) 0 ≠ 0 := by
   rw [affineIntegrand_mixed_derivative_diagonal A O π S hbase hUV hS huu]
   exact div_ne_zero (mul_ne_zero (by norm_num) O.hlam) hbase

 theorem nondegenerate_exists_spatial_scores (hnd : Model.Nondegenerate A O π) :
     ∃ S : Scores (π : Measure Z),
       ((residualMomentU A O π S true=1 ∧ residualMomentU A O π S false=0 ∧
         residualMomentV A O π S true=0 ∧ residualMomentV A O π S false=1) ∨
        (O.U=O.V ∧ S.su=S.sv ∧ residualMomentU A O π S true=1)) := by
   obtain ⟨su,sv,C,hsu,hsv,hC,hbu,hbv,hmu,hmv,hscore⟩ :=
     MeasureScores.nondegenerate_has_scores A O π hnd
   refine ⟨⟨su,sv,hsu,hsv,C,hC,hbu,hbv,hmu,hmv⟩,?_⟩
   simpa only [residualMomentU,residualMomentV,Bool.true_eq_false,Bool.false_eq_true,
     ite_true,ite_false] using hscore


end RoughRegime.SpatialAffine
