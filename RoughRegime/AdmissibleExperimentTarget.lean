module

public import RoughRegime.AdmissiblePhaseExperiment
public import RoughRegime.AdmissiblePriorTargets


@[expose] public section
/-! The literal observation-law integral equals the physically rescaled sum
of local nonlinear targets. This is derived from normalized response scores,
constant spatial pair mass and fixed placement profile identities. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace AdmissiblePhasePair
variable {H X Z : Type*} [MeasurableSpace H] [MeasurableSpace X] [MeasurableSpace Z]
    {μ : Measure X} [IsProbabilityMeasure μ] {π : Measure Z} [IsProbabilityMeasure π]
    {lo hi barp C0 : ℝ}

 theorem local_observation_target (A : AdmissiblePhasePair (H:=H) μ lo hi barp C0)
    (S : SpatialAffine.Scores π) (hlo : 0<lo) (hhi : 0 ≤ hi) (hbarp : 0<barp) (hC0 : 0 ≤ C0)
    (Au Av : ℝ) (hAu : 0 ≤ Au) (hAv : 0 ≤ Av) (hsmall : C0*(Au+Av)*S.C ≤ 1/4)
    (Phi : ℝ×ℝ→ℝ) (hPhi : Measurable Phi) (B : ℝ)
    (hbound : ∀ u v,|u| ≤ C0*Au→|v| ≤ C0*Av→|Phi (u,v)-Phi 0| ≤ B)
    (q : PhaseParameter H) :
    let F:=A.spatialField hlo hhi hbarp hC0 Au Av hAu hAv q
    (∫ o,Phi (F.u o.1,F.v o.1) ∂(A.markLaw S hlo hhi hbarp hC0 Au Av hAu hAv hsmall q).measure)=
      Phi 0+A.localTarget Phi Au Av q/barp := by
  let F:=A.spatialField hlo hhi hbarp hC0 Au Av hAu hAv q
  let g : X→ℝ:=fun x=>Phi (F.u x,F.v x)
  have hg : Measurable g:=hPhi.comp (F.measurableU.prodMk F.measurableV)
  have hsign (s : Bool) (u : ℝ) : |Lower.sign s*u|=|u| := by cases s <;> simp [Lower.sign]
  have hgb : ∀ x,|g x-Phi 0| ≤ B:=by
    intro x
    apply hbound
    · change |Lower.sign q.2.1*A.unsignedProfileU Au q.1 x| ≤ C0*Au
      rw [hsign];exact A.unsignedProfileU_bound hlo Au hAu q.1 x
    · change |Lower.sign q.2.2*A.unsignedProfileV Av q.1 x| ≤ C0*Av
      rw [hsign];exact A.unsignedProfileV_bound hlo Av hAv q.1 x
  have hp : Integrable (A.field.designDensity barp q.1) μ :=
    bounded_integrable μ _ (A.designDensity_measurable.comp (measurable_const.prodMk measurable_id)) hi
      (fun x=>by rw [abs_of_nonneg (hlo.trans_le (A.densityBounds q.1 x).1).le];exact (A.densityBounds q.1 x).2)
  have hc : Integrable (fun x=>A.field.designDensity barp q.1 x*(g x-Phi 0)) μ := by
    apply bounded_integrable μ _
      ((A.designDensity_measurable.comp (measurable_const.prodMk measurable_id)).mul (hg.sub measurable_const)) (hi*B)
    intro x
    change |A.field.designDensity barp q.1 x*(g x-Phi 0)| ≤ hi*B
    rw [abs_mul,abs_of_nonneg (hlo.trans_le (A.densityBounds q.1 x).1).le]
    exact mul_le_mul (A.densityBounds q.1 x).2 (hgb x) (abs_nonneg _) hhi
  have hi:=SpatialAffine.law_integral_fst S F hsmall g hg Set.univ MeasurableSet.univ
  simp only [Set.preimage_univ,Measure.restrict_univ] at hi
  change (∫ o,g o.1 ∂(SpatialAffine.law S F hsmall).measure)=Phi 0+A.localTarget Phi Au Av q/barp
  rw [hi]
  have he : (fun x=>F.p x*g x)=
      fun x=>(A.field.designDensity barp q.1 x*(g x-Phi 0)+Phi 0*A.field.designDensity barp q.1 x)/barp := by
    funext x
    change A.field.designDensity barp q.1 x/barp*g x=_
    ring
  rw [he,integral_div,integral_add hc (hp.const_mul _),integral_const_mul,A.constantMass]
  change (A.localTarget Phi Au Av q+Phi 0*barp)/barp=_
  field_simp
  ring

end AdmissiblePhasePair

namespace AdmissiblePhaseExperiment
variable {H X Z Y : Type*} [MeasurableSpace H] [MeasurableSpace X]
    [MeasurableSpace Z] [MeasurableSpace Y] {p : ℕ} [NeZero p]
    {μ : Measure X} [IsProbabilityMeasure μ] {π : ProbabilityMeasure Z}
    (E : AdmissiblePhaseExperiment (H:=H) (Y:=Y) p μ π)

 def targetFunctional (Phi : ℝ×ℝ→ℝ) (q : Fin p→PhaseParameter H) : ℝ:=
   Phi 0+E.v0/(p:ℝ)*∑ i,(E.pairs i).localTarget Phi E.Au E.Av (q i)

 theorem observation_target_eq (Phi : ℝ×ℝ→ℝ) (hPhi : Measurable Phi) (B : ℝ)
    (hbound : ∀ u v,|u| ≤ E.C0*E.Au→|v| ≤ E.C0*E.Av→|Phi (u,v)-Phi 0| ≤ B)
    (q : Fin p→PhaseParameter H) (uv : Y→ℝ×ℝ) (huv : Measurable uv)
    (houtside : ∀ᵐ y ∂(E.outside:Measure Y),uv y=0)
    (hplace : ∀ i,∀ᵐ o ∂(E.pairProbability i (q i):Measure (X×Z)),
      uv (E.placement i o)=
        (((E.pairs i).spatialField E.lo_pos E.hi_nonneg E.barp_pos E.C0_nonneg
          E.Au E.Av E.amplitudeU_nonneg E.amplitudeV_nonneg (q i)).u o.1,
         ((E.pairs i).spatialField E.lo_pos E.hi_nonneg E.barp_pos E.C0_nonneg
          E.Au E.Av E.amplitudeU_nonneg E.amplitudeV_nonneg (q i)).v o.1)) :
    (∫ y,Phi (uv y) ∂(E.observationProbability q:Measure Y))=E.targetFunctional Phi q := by
  let F:=fun i=>(E.pairs i).spatialField E.lo_pos E.hi_nonneg E.barp_pos E.C0_nonneg
    E.Au E.Av E.amplitudeU_nonneg E.amplitudeV_nonneg (q i)
  have hsign (s : Bool) (u : ℝ) : |Lower.sign s*u|=|u| := by cases s <;> simp [Lower.sign]
  have hlocalBound : ∀ i x,|Phi ((F i).u x,(F i).v x)| ≤ B+|Phi 0| := by
    intro i x
    have hb : |Phi ((F i).u x,(F i).v x)-Phi 0| ≤ B:=by
      apply hbound
      · change |Lower.sign (q i).2.1*(E.pairs i).unsignedProfileU E.Au (q i).1 x| ≤ E.C0*E.Au
        rw [hsign];exact (E.pairs i).unsignedProfileU_bound E.lo_pos E.Au E.amplitudeU_nonneg _ _
      · change |Lower.sign (q i).2.2*(E.pairs i).unsignedProfileV E.Av (q i).1 x| ≤ E.C0*E.Av
        rw [hsign];exact (E.pairs i).unsignedProfileV_bound E.lo_pos E.Av E.amplitudeV_nonneg _ _
    calc
      _ = |Phi ((F i).u x,(F i).v x)-Phi 0+Phi 0| := by congr 1; ring
      _ ≤ |Phi ((F i).u x,(F i).v x)-Phi 0|+|Phi 0| := abs_add_le _ _
      _ ≤ _ := add_le_add hb le_rfl
  have houti : Integrable (fun y=>Phi (uv y)) (E.outside:Measure Y) :=
    (integrable_const (Phi 0)).congr (houtside.mono (fun _ h=>by dsimp only; rw [h]))
  have hpairi : ∀ i,Integrable (fun o=>Phi (uv (E.placement i o))) (E.pairProbability i (q i):Measure (X×Z)) := by
    intro i
    apply Integrable.of_bound ((hPhi.comp huv).comp (E.placement_measurable i)).aestronglyMeasurable (B+|Phi 0|)
    filter_upwards [hplace i] with o ho
    change |Phi (uv (E.placement i o))| ≤ B+|Phi 0|
    rw [ho]
    exact hlocalBound i o.1
  have houte : (∫ y,Phi (uv y) ∂(E.outside:Measure Y))=Phi 0:=by
    have he : (fun y=>Phi (uv y)) =ᵐ[(E.outside:Measure Y)] (fun _=>Phi 0) :=
      houtside.mono (fun _ h=>congrArg Phi h)
    rw [integral_congr_ae he]
    simp
  have hpaire : ∀ i,(∫ o,Phi (uv (E.placement i o)) ∂(E.pairProbability i (q i):Measure (X×Z)))=
      Phi 0+(E.pairs i).localTarget Phi E.Au E.Av (q i)/E.barp := by
    intro i
    rw [integral_congr_ae ((hplace i).mono (fun _ h=>congrArg Phi h))]
    exact (E.pairs i).local_observation_target E.scores E.lo_pos E.hi_nonneg E.barp_pos E.C0_nonneg
      E.Au E.Av E.amplitudeU_nonneg E.amplitudeV_nonneg E.small Phi hPhi B hbound (q i)
  rw [observationProbability,placementObservation_integral E.weights E.weights_sum E.outside _
    E.placement E.placement_measurable (fun y=>Phi (uv y)) (hPhi.comp huv) houti hpairi,houte]
  simp_rw [hpaire]
  rw [E.outside_weight]
  simp only [weights,uniformPairWeights,NNReal.coe_div,NNReal.coe_natCast]
  have hmass : (E.pairMass:ℝ)=E.v0*E.barp:=rfl
  rw [hmass]
  rw [← Finset.mul_sum]
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [← Finset.sum_div]
  unfold targetFunctional
  have hp : (p:ℝ)≠0 := by exact_mod_cast NeZero.ne p
  field_simp [hp,E.barp_pos.ne']
  ring

end AdmissiblePhaseExperiment
end RoughRegime.PoissonMeasure
