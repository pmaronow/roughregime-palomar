module

public import RoughRegime.SourceFrame
public import RoughRegime.CanonicalKHolder
public import RoughRegime.SpatialLocalClass


@[expose] public section
/-! Actual canonical source laws belong to the statistical model. The Hölder
bounds are proved from the literal oscillatory construction; only scalar
source tuning inequalities occur among the localization hypotheses. -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace RoughRegime.Model

def Parameters.withDimension (A : Parameters) (D : ℕ) : Parameters :=
  { A with d := D+1, hd := Nat.succ_le_succ (Nat.zero_le _) }

 theorem Parameters.withDimension_self (A : Parameters) : A.withDimension (A.d-1)=A := by
   cases A with
   | mk d α β H δ gminus gplus M0 hd hα hβ hH hδ hgminus hgplus hM0 =>
     cases d with
     | zero => omega
     | succ D => rfl

end RoughRegime.Model
namespace RoughRegime.LatticePriors
open RoughRegime.SpatialAffine RoughRegime.Upper
set_option backward.isDefEq.respectTransparency false

 theorem source_positive_model_localization (A0 : Model.Parameters) (D Q K : ℕ)
     {Z : Type*} [MeasurableSpace Z]
     (O : Model.Observables Z (A0.withDimension D)) (π : ProbabilityMeasure Z)
     (S : Scores (π : Measure Z))
     (gammaStar lambdaStar alpha0 v0 rminus rplus : ℝ)
     (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4) (hlam : 0 < lambdaStar)
     (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
     (hK : 0 < K) (hKQ : K ≤ 2*Q)
     (ht : alpha0 < A0.α) (hs : alpha0 < A0.β)
     (hbudgetU : Model.holderOrder A0.α+2 ≤ K) (hbudgetV : Model.holderOrder A0.β+2 ≤ K)
     (hv : 0 < v0) (hv1 : v0 ≤ 1) (hrminus : 0 < rminus) (hlt : rminus < rplus)
     (hden : 0 < 1-v0*sourceOuterIntegral (D+1))
     (hbase : 0 < Model.baselineW (A0.withDimension D) O π)
     (hcrossU : residualMomentU (A0.withDimension D) O π S false=0)
     (hcrossV : residualMomentV (A0.withDimension D) O π S true=0)
     (ha : |Model.baselineA (A0.withDimension D) O π| ≤ A0.H)
     (hb : |Model.baselineB (A0.withDimension D) O π| ≤ A0.H)
     (hinterval : A0.gminus ≤ Model.baselineW (A0.withDimension D) O π*rminus ∧
       Model.baselineW (A0.withDimension D) O π*rplus ≤ A0.gplus) :
     ∃ ε Cu Cv : ℝ, 0 < ε ∧ 0 < Cu ∧ 0 < Cv ∧
       ∀ (N J M : ℕ) (hN : 0 < N) (m epsilonU epsilonV delta r : ℝ),
       ∀ (hm : 0 < m) (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
         (hmargin : delta ≤ sourceMarginBound (D+1) v0 rminus rplus),
       (2:ℝ)^((J:ℝ)*alpha0) ≤ m →
       m ≤ (2:ℝ)^((J:ℝ)*A0.α) → m ≤ (2:ℝ)^((J:ℝ)*A0.β) →
       Cu*epsilonU ≤ A0.H-|Model.baselineA (A0.withDimension D) O π| →
       Cv*epsilonV ≤ A0.H-|Model.baselineB (A0.withDimension D) O π| →
       let F := sourceCanonicalFrame D N J Q M hN gammaStar lambdaStar alpha0 m
         epsilonU epsilonV A0.α A0.β v0 rminus rplus delta hγ hγ1 hm heU heV hv hv1 hrminus hlt hd hmargin hden
       F.Au+F.Av ≤ ε →
       ∀ (hsmall : (F.Au+F.Av)/rminus*S.C ≤ 1/4),
       2*((F.Au+F.Av)/rminus)*A0.M0*S.C ≤ Model.baselineW (A0.withDimension D) O π-A0.δ →
       (2*((F.Au+F.Av)/rminus)*A0.M0*S.C)*rplus ≤ Model.baselineW (A0.withDimension D) O π*delta →
       2*((F.Au+F.Av)/rminus)*A0.M0*S.C ≤ r →
       ((F.Au+F.Av)/rminus)*(|residualMomentU (A0.withDimension D) O π S true|+
         |residualMomentU (A0.withDimension D) O π S false|)/(Model.baselineW (A0.withDimension D) O π/2) ≤ r →
       ((F.Au+F.Av)/rminus)*(|residualMomentV (A0.withDimension D) O π S true|+
         |residualMomentV (A0.withDimension D) O π S false|)/(Model.baselineW (A0.withDimension D) O π/2) ≤ r →
       ∀ z : GridPair D N → PairState (Fin J × Fin (D+1)),
       (law S (F.field z) hsmall).probabilityMeasure ∈ Model.localClass (A0.withDimension D) O π r := by
   let A := A0.withDimension D
   have hinner (x : Model.Covariate (D+1)) : innerBump (D+1) x ∈ Icc (0:ℝ) 1 :=
     ⟨(innerBump (D+1)).nonneg,(innerBump (D+1)).le_one⟩
   obtain ⟨εu,Cu,hεu,hCu,hU⟩ := canonical_source_K_holder_first canonicalStep D Q K
     gammaStar lambdaStar alpha0 hγ hγ1 hlam ha0 ha1 hK hKQ rminus rplus hrminus hlt
     (innerBump (D+1)) (outerBump (D+1)) (outerBump_one_on_inner (D+1))
     (innerBump_zero_outside (D+1)) (outerBump_zero_outside (D+1))
     (innerBump_smooth (D+1)) (innerBump_compact (D+1)) hinner (innerBump_tsupport_subset (D+1))
     A0.α A0.β ht hbudgetU v0 hv (regressionChangeU A O π S) 0 (denominatorDomain A O π S)
     (denominatorDomain_open A O π S) (denominatorDomain_zero A O π S hbase.ne')
     (regressionChangeU_smooth A O π S) (fun v _ => regressionChangeU_zero_axis A O π S hcrossU v)
   obtain ⟨εv,Cv,hεv,hCv,hV⟩ := canonical_source_K_holder_second canonicalStep D Q K
     gammaStar lambdaStar alpha0 hγ hγ1 hlam ha0 ha1 hK hKQ rminus rplus hrminus hlt
     (innerBump (D+1)) (outerBump (D+1)) (outerBump_one_on_inner (D+1))
     (innerBump_zero_outside (D+1)) (outerBump_zero_outside (D+1))
     (innerBump_smooth (D+1)) (innerBump_compact (D+1)) hinner (innerBump_tsupport_subset (D+1))
     A0.α A0.β hs hbudgetV v0 hv (regressionChangeV A O π S) 0 (denominatorDomain A O π S)
     (denominatorDomain_open A O π S) (denominatorDomain_zero A O π S hbase.ne')
     (regressionChangeV_smooth A O π S) (fun u _ => regressionChangeV_zero_axis A O π S hcrossV u)
   refine ⟨min εu εv,Cu,Cv,lt_min hεu hεv,hCu,hCv,?_⟩
   intro N J M hN m epsilonU epsilonV delta r hm heU heV hd hmargin hm0 hmU hmV heHU heHV
   dsimp only
   let F := sourceCanonicalFrame D N J Q M hN gammaStar lambdaStar alpha0 m epsilonU epsilonV
     A0.α A0.β v0 rminus rplus delta hγ hγ1 hm heU heV hv hv1 hrminus hlt hd hmargin hden
   change F.Au+F.Av ≤ min εu εv → _
   intro hsmallK hsmall hoverlap hdmargin hwr har hbr z
   have hB := sourceGridCount_pos N (D+1) hN
   have hell := sourceBlockScale_grid_le_one v0 N (D+1) hv hv1 hN
   have hh : (rplus-rminus)/2-delta ∈ Icc (-intervalHalfWidth rminus rplus) (intervalHalfWidth rminus rplus) := by
     have he := hmargin.trans (min_le_left _ _)
     unfold intervalHalfWidth
     constructor <;> linarith
   have hu := hU N (sourceGridOffset v0 (D+1)) (sourceGridCount N (D+1))
     (sourceFixedBaseline (D+1) v0 rminus rplus) epsilonU epsilonV hB heU heV hell J M m hm0 hmU
     (hsmallK.trans (min_le_left _ _)) z _ hh (stateSignU z) (stateSignV z)
     (fun b => (stateSignU_abs z b).le) (fun b => (stateSignV_abs z b).le)
   have hv' := hV N (sourceGridOffset v0 (D+1)) (sourceGridCount N (D+1))
     (sourceFixedBaseline (D+1) v0 rminus rplus) epsilonU epsilonV hB heU heV hell J M m hm0 hmV
     (hsmallK.trans (min_le_right _ _)) z _ hh (stateSignU z) (stateSignV z)
     (fun b => (stateSignU_abs z b).le) (fun b => (stateSignV_abs z b).le)
   have hu' : ContDiff ℝ ∞ (fun x => regressionChangeU A O π S ((F.field z).u x,(F.field z).v x)) ∧
       Model.holderNorm (fun x => regressionChangeU A O π S ((F.field z).u x,(F.field z).v x)) A.α ≤
         ENNReal.ofReal (Cu*epsilonU) := by
     simpa only [sub_zero,F,sourceCanonicalFrame,CanonicalFrame.field,CanonicalFrame.u,CanonicalFrame.v,
       canonicalSourceProfile,intervalCenter,A,Model.Parameters.withDimension,add_comm rplus rminus] using hu
   have hv'' : ContDiff ℝ ∞ (fun x => regressionChangeV A O π S ((F.field z).u x,(F.field z).v x)) ∧
       Model.holderNorm (fun x => regressionChangeV A O π S ((F.field z).u x,(F.field z).v x)) A.β ≤
         ENNReal.ofReal (Cv*epsilonV) := by
     simpa only [sub_zero,F,sourceCanonicalFrame,CanonicalFrame.field,CanonicalFrame.u,CanonicalFrame.v,
       canonicalSourceProfile,intervalCenter,A,Model.Parameters.withDimension,add_comm rplus rminus] using hv'
   exact law_localClass_from_source_bounds A O π S (F.field z) hsmall hbase rminus rplus delta
     (hrminus.le.trans hlt.le) hd.le (F.realization z).margins hinterval hoverlap hdmargin ha hb
     hu'.1 hv''.1 (hu'.2.trans (ENNReal.ofReal_le_ofReal heHU))
     (hv''.2.trans (ENNReal.ofReal_le_ofReal heHV)) r hwr har hbr

end RoughRegime.LatticePriors
