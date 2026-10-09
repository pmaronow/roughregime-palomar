module

public import RoughRegime.ModelCompactUpper
public import RoughRegime.CovariateObservables


@[expose] public section
/-! Every-n basic estimators and covariate-dependent observables, with one
constant before the compact family of original density endpoints. The
sharp upper keeps each endpoint pair's own rate parameters. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators ENNReal
namespace RoughRegime.Model
universe u
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem compact_uniform_basic_upper (A:Parameters)(G:Set (ℝ×ℝ))(hG:IsCompact G)
    (hdom:G⊆densityIntervalDomain)(L MW:ℝ) :
    ∃C:ℝ,0<C ∧ ∀I(hI:I∈G),let B:=densityParameters A I (hdom hI)
      ∀(Z:Type u)[MeasurableSpace Z](F:Observables Z B),
        |F.lam|=L→(∀z,|F.W z|≤MW)→∀n:ℕ,3≤n→
        ∃E:Estimator (Observation B Z) n,∀P∈modelClass B F,
          eLpNorm (fun o=>E.val o-target B F P) 2 (randomizedExperiment n P)≤
            ENNReal.ofReal (C*basicUpperScale A n) := by
  obtain ⟨C,hC,hupper⟩:=compact_eventual_basic_minimax.{u} A G hG hdom L MW
  obtain ⟨N,hN⟩:=eventually_atTop.mp hupper
  obtain ⟨lo,hi,hlo,hlt,henvelope⟩:=compact_density_envelope G hG hdom
  have hhi:0<hi:=hlo.trans hlt
  let B0:=|MW|+|L| *A.H^2*hi
  have hB0:0≤B0:=by dsimp [B0];positivity
  let C0:=C+1+∑k∈Finset.range N,B0/basicUpperScale A k
  have hsum:0≤∑k∈Finset.range N,B0/basicUpperScale A k:=
    Finset.sum_nonneg (fun k _=>div_nonneg hB0 (basicUpperScale_nonneg A k))
  have hC0:0<C0:=by dsimp [C0];linarith
  refine ⟨2*C0,by positivity,?_⟩
  intro I hI
  dsimp only
  intro Z mZ F hL hMW n hn
  let B:=densityParameters A I (hdom hI)
  have hr:=basicUpperScale_pos A n (by omega)
  have hb:minimaxRMSE n (target B F) (modelClass B F)≤
      ENNReal.ofReal (C0*basicUpperScale A n) := by
    by_cases hNn:N≤n
    · exact (hN n hNn I hI Z F hL hMW).trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by dsimp [C0];linarith) hr.le))
    · let E:Estimator (Observation B Z) n:=⟨fun _=>0,measurable_const⟩
      apply minimaxRMSE_le_fixed_estimator n _ _ E
      intro P hP
      obtain ⟨W⟩:=hP
      have ht:=target_uniform_bound B F P W MW hMW
      have hLabs:|L|=L:=by rw [←hL,abs_abs]
      have hLn:0≤L:=by rw [←hL];exact abs_nonneg _
      have htB:|target B F P|≤B0:=by
        apply ht.trans
        change |MW|+|F.lam| *A.H^2*I.2≤B0
        rw [hL]
        dsimp [B0]
        rw [hLabs]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (henvelope I hI).2
          (mul_nonneg hLn (sq_nonneg A.H)))
      have hquot:B0/basicUpperScale A n≤C0:=by
        have ht:=Finset.single_le_sum (s:=Finset.range N)
          (fun k _=>div_nonneg hB0 (basicUpperScale_nonneg A k))
          (Finset.mem_range.mpr (lt_of_not_ge hNn))
        dsimp [C0]
        linarith
      have hscale:B0≤C0*basicUpperScale A n:=(div_le_iff₀ hr).mp hquot
      let : IsProbabilityMeasure (randomizedExperiment n P):=by
        change IsProbabilityMeasure ((Measure.pi (fun _:Fin n=>(P:Measure (Observation B Z)))).prod KernelSeedBridge.seedLaw)
        infer_instance
      have he:=eLpNorm_le_of_ae_bound (μ:=randomizedExperiment n P) (p:=(2:ℝ≥0∞))
        (f:=fun o=>E.val o-target B F P)
        (by change AEStronglyMeasurable (fun _=>0-target B F P) _;exact aestronglyMeasurable_const)
        (ae_of_all _ (fun _=>by simpa [E,Real.norm_eq_abs] using htB.trans hscale))
      simpa only [measure_univ,ENNReal.one_rpow,one_mul] using he
  have hlt:minimaxRMSE n (target B F) (modelClass B F)<
      ENNReal.ofReal ((2*C0)*basicUpperScale A n):=
    hb.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity:0<(2*C0)*basicUpperScale A n)).mpr
      (by nlinarith [mul_pos hC0 hr]))
  change (⨅E:Estimator (Observation B Z) n,⨆P,⨆hP:P∈modelClass B F,
    eLpNorm (fun o=>E.val o-target B F P) 2 (randomizedExperiment n P))<_ at hlt
  obtain ⟨E,hE⟩:=iInf_lt_iff.mp hlt
  refine ⟨E,fun P hP=>?_⟩
  apply le_trans _ hE.le
  exact le_iSup_of_le P (le_iSup_of_le hP le_rfl)

theorem covariate_dependent_compact_uniform_upper (A:Parameters)(G:Set (ℝ×ℝ))
    (hG:IsCompact G)(hdom:G⊆densityIntervalDomain)(L MW:ℝ) :
    ∃C:ℝ,0<C ∧ ∃n0:ℕ,3≤n0 ∧ ∀I(hI:I∈G),let B:=densityParameters A I (hdom hI)
      ∀(Z:Type u)[MeasurableSpace Z](F:Observables (Observation B Z) B),
        |F.lam|=L→(∀o,|F.W o|≤MW)→∀n:ℕ,n0≤n→
        (1/2≤A.theta→minimaxRMSE n (covariateDependentTarget B F) (covariateDependentClass B F)≤
          ENNReal.ofReal (C*(n:ℝ)^(-(1/2:ℝ)))) ∧
        (A.theta<1/2→minimaxRMSE n (covariateDependentTarget B F) (covariateDependentClass B F)≤
          ENNReal.ofReal (C*Rates.subcriticalScale n A.theta (Rates.tau I.1 I.2)*
            (Real.log n)^((A.nu:ℝ)/2+1/4))) := by
  obtain ⟨C,hC,n0,hn0,hupper⟩:=compact_uniformUpperClaim.{u} A G hG hdom L MW
  refine ⟨C,hC,n0,hn0,?_⟩
  intro I hI
  dsimp only
  intro Z mZ F hL hMW n hn
  let B:=densityParameters A I (hdom hI)
  have hr:=covariate_dependent_risk_transfer B F n
  by_cases hnonempty:(modelClass B F).Nonempty
  · obtain ⟨hcrit,hrough⟩:=hupper I hI (Observation B Z) inferInstance F hL hMW n hn hnonempty
    exact ⟨fun ht=>hr.trans (hcrit ht),fun ht=>hr.trans (hrough ⟨A.theta_pos,ht⟩)⟩
  · have hz:minimaxRMSE n (target B F) (modelClass B F)=0:=by
      simp [Set.not_nonempty_iff_eq_empty.mp hnonempty,minimaxRMSE]
    rw [hz] at hr
    exact ⟨fun _=>hr.trans bot_le,fun _=>hr.trans bot_le⟩

theorem covariate_dependent_compact_uniform_basic_upper (A:Parameters)(G:Set (ℝ×ℝ))
    (hG:IsCompact G)(hdom:G⊆densityIntervalDomain)(L MW:ℝ) :
    ∃C:ℝ,0<C ∧ ∀I(hI:I∈G),let B:=densityParameters A I (hdom hI)
      ∀(Z:Type u)[MeasurableSpace Z](F:Observables (Observation B Z) B),
        |F.lam|=L→(∀o,|F.W o|≤MW)→∀n:ℕ,3≤n→
        ∃E:Estimator (Observation B Z) n,∀P∈covariateDependentClass B F,
          eLpNorm (fun o=>E.val o-covariateDependentTarget B F P) 2 (randomizedExperiment n P)≤
            ENNReal.ofReal (C*basicUpperScale A n) := by
  obtain ⟨C,hC,hupper⟩:=compact_uniform_basic_upper.{u} A G hG hdom L MW
  refine ⟨2*C,by positivity,?_⟩
  intro I hI
  dsimp only
  intro Z mZ F hL hMW n hn
  let B:=densityParameters A I (hdom hI)
  obtain ⟨E,hE⟩:=hupper I hI (Observation B Z) F hL hMW n hn
  have hb:minimaxRMSE n (target B F) (modelClass B F)≤ENNReal.ofReal (C*basicUpperScale A n):=by
    apply iInf_le_of_le E
    exact iSup_le (fun P=>iSup_le (fun hP=>hE P hP))
  have hr:=(covariate_dependent_risk_transfer B F n).trans hb
  have hpos:=basicUpperScale_pos A n (by omega)
  have hlt:minimaxRMSE n (covariateDependentTarget B F) (covariateDependentClass B F)<
      ENNReal.ofReal ((2*C)*basicUpperScale A n):=
    hr.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity:0<(2*C)*basicUpperScale A n)).mpr
      (by nlinarith [mul_pos hC hpos]))
  change (⨅E:Estimator (Observation B Z) n,⨆P,⨆hP:P∈covariateDependentClass B F,
    eLpNorm (fun o=>E.val o-covariateDependentTarget B F P) 2 (randomizedExperiment n P))<_ at hlt
  obtain ⟨E,hE⟩:=iInf_lt_iff.mp hlt
  refine ⟨E,fun P hP=>?_⟩
  apply le_trans _ hE.le
  exact le_iSup_of_le P (le_iSup_of_le hP le_rfl)

end RoughRegime.Model
