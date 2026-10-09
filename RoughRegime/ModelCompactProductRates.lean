module

public import RoughRegime.ModelEstimatorControls
public import RoughRegime.ModelProductRates
public import RoughRegime.CompactDesignConstants
public import RoughRegime.CompactIntervalRates
public import RoughRegime.CompactParametricNumerics


@[expose] public section
/-! The same concrete shared-sample estimator, with common population
constants and common tuning on a compact family of original density intervals. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model
universe u
open RoughRegime.UpperDegreeRules RoughRegime.UpperTuning RoughRegime.LiftVariance
open RoughRegime.UpperParametric
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def CompactProductRisk (A : Parameters) (hαβ : A.α≤A.β) (G : Set (ℝ×ℝ))
    (hdom : G⊆densityIntervalDomain) (Cb Cv Cproj : ℝ) : Prop :=
  ∀(I:ℝ×ℝ)(hI:I∈G),let B:=densityParameters A I (hdom hI)
    ∀(Z:Type u)[MeasurableSpace Z](F:Observables Z B)
      (P:ProbabilityMeasure (Observation B Z))(W:ModelWitness B F P)
      (J:ℕ)(m:Fin (J+1)→ℕ)(n:ℕ),(∀j,2*(m j+B.nu+2)≤n)→
      lpNorm (fun xs=>productEstimator B hαβ F J m n xs-W.productTarget) 2
        (Measure.pi (fun _:Fin n=>(P:Measure (Observation B Z))))≤
        Cproj*((2:ℝ)^J)^(-A.theta)+
          Cb*(∑j,approximationWeight (parentCells J j) A.theta (Rates.tau I.1 I.2) A.nu (m j))+
          ∑j,Real.sqrt (variance (levelEstimator B hαβ F J m n j)
            (Measure.pi (fun _:Fin n=>(P:Measure (Observation B Z))))) ∧
      (∀j,variance (levelEstimator B hαβ F J m n j)
        (Measure.pi (fun _:Fin n=>(P:Measure (Observation B Z))))≤
        Cv*(parentCells J j:ℝ)^(-2*modelSmoothnessExponent A)/n+
          ∑k∈Finset.range (m j+A.nu+2-1),varianceTerm Cv (parentCells J j) n (k+2))

def compactParametricProductEstimator (A : Parameters) (hαβ : A.α≤A.β)
    {Z:Type*}[MeasurableSpace Z](F:Observables Z A)(D Cv:ℝ)(n:ℕ) :=
  let J:=terminalLevel (terminalConstant D Cv A.nu) n
  productEstimator A hαβ F J (fun j=>biasDegree D (levelDistance J j)) n

def compactSubcriticalProductEstimator (A : Parameters) (hαβ : A.α≤A.β)
    {Z:Type*}[MeasurableSpace Z](F:Observables Z A)(D Cv:ℝ)(n:ℕ) :=
  let τ:=Rates.tau A.gminus A.gplus
  productEstimator A hαβ F (UpperSubcritical.terminal n A.theta τ)
    (UpperSubcritical.chosenOrder n A.theta τ D Cv A.nu) n

theorem compact_productRisk_from_controls (A : Parameters) (hαβ : A.α≤A.β)
    (G:Set (ℝ×ℝ))(hdom:G⊆densityIntervalDomain)(Cp Co Cproj:ℝ)
    (hCp:1≤Cp)(hCproj:0<Cproj)
    (hobsLocal:∀I(hI:I∈G),dyadicDesignConstant (densityParameters A I (hdom hI)) (holderOrder A.β)≤Co)
    (hobsBase:baseDesignConstant A (holderOrder A.β)≤Co)
    (hlocal:∀I(hI:I∈G),LocalPolynomialControl.{u} (densityParameters A I (hdom hI)) hαβ Cp)
    (hbase:∀I(hI:I∈G),BasePolynomialControl.{u} (densityParameters A I (hdom hI)) Cp)
    (hproj:∀I(hI:I∈G),let B:=densityParameters A I (hdom hI)
      ∀(Z:Type u)[MeasurableSpace Z](F:Observables Z B)(P:ProbabilityMeasure (Observation B Z))
        (W:ModelWitness B F P)(J:ℕ),
        |W.productTarget-(W.levelProjectionTarget (holderOrder A.β) 0+
          ∑j∈Finset.range J,W.levelProjectionIncrement j)|≤Cproj*((2:ℝ)^J)^(-A.theta)) :
    CompactProductRisk.{u} A hαβ G hdom Cp (varianceConstant (max Cp Co)) Cproj := by
  intro I hI
  have ht:=productEstimator_risk_from_controls.{u} (densityParameters A I (hdom hI)) hαβ
    Cp Co Cproj hCp hCproj (hobsLocal I hI) hobsBase (hlocal I hI) (hbase I hI) (hproj I hI)
  dsimp only
  intro Z inst F P W J m n hdegree
  have hr:=ht Z F P W J m n hdegree
  simpa only [max_self,modelSmoothnessExponent,Parameters.theta,Parameters.nu,densityParameters] using hr


lemma compact_commonDegreeSlope (θ τlo : ℝ) (hθ:0<θ)(hτlo:0<τlo) :
    0≤(θ*Real.log 2+1)/τlo ∧ θ*Real.log 2+1≤τlo*((θ*Real.log 2+1)/τlo) := by
  have hl:=Real.log_pos (by norm_num : (1:ℝ)<2)
  constructor
  · positivity
  · rw [mul_div_cancel₀ _ hτlo.ne']

theorem compact_parametricProductEstimator_risk_from_finite
    (A:Parameters)(hαβ:A.α≤A.β)(hθ:1/2≤A.theta)
    (G:Set (ℝ×ℝ))(hG:IsCompact G)(hdom:G⊆densityIntervalDomain)
    (Cb Cv Cproj:ℝ)(hCb:1≤Cb)(hCv:1≤Cv)(hCproj:0<Cproj)
    (hfinite:CompactProductRisk.{u} A hαβ G hdom Cb Cv Cproj) :
    ∃D C:ℝ,0≤D ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,∀I(hI:I∈G),
      let B:=densityParameters A I (hdom hI)
      ∀(Z:Type u)[MeasurableSpace Z](F:Observables Z B)(P:ProbabilityMeasure (Observation B Z))
        (W:ModelWitness B F P),
        lpNorm (fun xs=>compactParametricProductEstimator B hαβ F D Cv n xs-W.productTarget) 2
          (Measure.pi (fun _:Fin n=>(P:Measure (Observation B Z))))≤C/Real.sqrt n := by
  obtain ⟨τlo,τhi,hτlo,_,hτ⟩:=compact_density_tau_bounds G hG hdom
  let D:=(A.theta*Real.log 2+1)/τlo
  have hD:=compact_commonDegreeSlope A.theta τlo A.theta_pos hτlo
  obtain ⟨C,hC,he⟩:=uncapped_total_error_bound_eventually_uniform A.theta τlo D Cv Cb Cproj
    (modelSmoothnessExponent A) A.nu hθ hτlo hD.1 hCv (zero_le_one.trans hCb) hCproj.le
    (modelSmoothnessExponent_pos A) hD.2
  refine ⟨D,C,hD.1,hC,he.mono ?_⟩
  intro n hn I hI
  dsimp only
  intro Z _ F P W
  let B:=densityParameters A I (hdom hI)
  let J:=terminalLevel (terminalConstant D Cv A.nu) n
  let m:Fin (J+1)→ℕ:=fun j=>biasDegree D (levelDistance J j)
  have ht:=hn (Rates.tau I.1 I.2) (hτ I hI).1
  have hr:=hfinite I hI Z F P W J m n ht.1
  exact hr.1.trans (ht.2 _ hr.2)

theorem compact_subcriticalProductEstimator_risk_from_finite
    (A:Parameters)(hαβ:A.α≤A.β)(hθ:A.theta<1/2)
    (G:Set (ℝ×ℝ))(hG:IsCompact G)(hdom:G⊆densityIntervalDomain)
    (Cb Cv Cproj:ℝ)(hCb:1≤Cb)(hCv:1≤Cv)(hCproj:0<Cproj)
    (hfinite:CompactProductRisk.{u} A hαβ G hdom Cb Cv Cproj) :
    ∃D C:ℝ,0≤D ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,∀I(hI:I∈G),
      let B:=densityParameters A I (hdom hI)
      ∀(Z:Type u)[MeasurableSpace Z](F:Observables Z B)(P:ProbabilityMeasure (Observation B Z))
        (W:ModelWitness B F P),
        lpNorm (fun xs=>compactSubcriticalProductEstimator B hαβ F D Cv n xs-W.productTarget) 2
          (Measure.pi (fun _:Fin n=>(P:Measure (Observation B Z))))≤
          C*UpperSubcritical.rate n A.theta (Rates.tau I.1 I.2) A.nu := by
  obtain ⟨τlo,τhi,hτlo,_,hτ⟩:=compact_density_tau_bounds G hG hdom
  let D:=(A.theta*Real.log 2+1)/τlo
  have hD:=compact_commonDegreeSlope A.theta τlo A.theta_pos hτlo
  have hvalid:=UpperSubcritical.tuning_valid_eventually_uniform A.theta τlo τhi D Cv A.nu
    A.theta_pos hθ hτlo hD.1 hCv
  obtain ⟨C,hC,he⟩:=UpperSubcritical.chosen_total_error_bound_eventually_uniform A.theta τlo τhi
    D Cv Cb Cproj (modelSmoothnessExponent A) A.nu A.theta_pos hθ hτlo hD.1 hCv
    (zero_le_one.trans hCb) hCproj.le (modelSmoothnessExponent_pos A).le A.nu_ge_two hD.2
  have hnValid:=tendsto_natCast_atTop_atTop.eventually hvalid
  have hnError:=tendsto_natCast_atTop_atTop.eventually he
  refine ⟨D,C,hD.1,hC,?_⟩
  filter_upwards [hnValid,hnError] with n hn hb
  intro I hI
  dsimp only
  intro Z _ F P W
  let B:=densityParameters A I (hdom hI)
  let τ:=Rates.tau I.1 I.2
  let J:=UpperSubcritical.terminal n A.theta τ
  let m:=UpperSubcritical.chosenOrder n A.theta τ D Cv A.nu
  have ht:=hn τ (hτ I hI)
  have hdeg:∀j:Fin (J+1),2*(m j+A.nu+2)≤n := by
    intro j
    have hd:=ht.degree_sample j
    unfold UpperSubcritical.chosenDegree at hd
    exact_mod_cast hd
  have hr:=hfinite I hI Z F P W J m n hdeg
  exact hr.1.trans (hb τ (hτ I hI) _ hr.2)

theorem compact_basicProductEstimator_risk_from_finite
    (A:Parameters)(hαβ:A.α≤A.β)
    (G:Set (ℝ×ℝ))(hG:IsCompact G)(hdom:G⊆densityIntervalDomain)
    (Cb Cv Cproj:ℝ)(hCb:1≤Cb)(hCv:1≤Cv)(hCproj:0<Cproj)
    (hfinite:CompactProductRisk.{u} A hαβ G hdom Cb Cv Cproj) :
    ∃D C:ℝ,0≤D ∧ 0<C ∧ ∀ᶠn:ℕ in atTop,∀I(hI:I∈G),
      let B:=densityParameters A I (hdom hI)
      ∀(Z:Type u)[MeasurableSpace Z](F:Observables Z B)(P:ProbabilityMeasure (Observation B Z))
        (W:ModelWitness B F P),
        lpNorm (fun xs=>compactParametricProductEstimator B hαβ F D Cv n xs-W.productTarget) 2
          (Measure.pi (fun _:Fin n=>(P:Measure (Observation B Z))))≤C*((n:ℝ)^(-A.theta)+(n:ℝ)^(-(1/2:ℝ))) := by
  obtain ⟨τlo,τhi,hτlo,_,hτ⟩:=compact_density_tau_bounds G hG hdom
  let D:=(A.theta*Real.log 2+1)/τlo
  have hD:=compact_commonDegreeSlope A.theta τlo A.theta_pos hτlo
  obtain ⟨C,hC,he⟩:=uncapped_basic_total_error_bound_eventually_uniform A.theta τlo D Cv Cb Cproj
    (modelSmoothnessExponent A) A.nu A.theta_pos hτlo hD.1 hCv (zero_le_one.trans hCb) hCproj.le
    (modelSmoothnessExponent_pos A) hD.2
  refine ⟨D,C,hD.1,hC,he.mono ?_⟩
  intro n hn I hI
  dsimp only
  intro Z _ F P W
  let B:=densityParameters A I (hdom hI)
  let J:=terminalLevel (terminalConstant D Cv A.nu) n
  let m:Fin (J+1)→ℕ:=fun j=>biasDegree D (levelDistance J j)
  have ht:=hn (Rates.tau I.1 I.2) (hτ I hI).1
  have hr:=hfinite I hI Z F P W J m n ht.1
  exact hr.1.trans (ht.2 _ hr.2)

end RoughRegime.Model
