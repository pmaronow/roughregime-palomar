module

public import RoughRegime.ApplicationNormalizedMAR
public import RoughRegime.SmoothPilotFull
public import RoughRegime.HolderQuotient
public import RoughRegime.CubeAE


@[expose] public section
/-! The actual fixed-accuracy pilot gives a uniform normalized generic model
for the separated-density MAR class on its good event. All pilot constants,
Holder radii and the enlarged design interval are selected before the law. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ContDiff ENNReal
namespace RoughRegime.Applications.SeparatedMAR
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

def pilotClip (A : Model.Parameters) : ℝ := A.δ/2
theorem pilotClip_pos (A : Model.Parameters) : 0 < pilotClip A := div_pos A.hδ (by norm_num)
theorem pilotClip_valid (A : Model.Parameters) (hδ : A.δ ≤ 1/2) : pilotClip A ≤ 1-pilotClip A := by
  unfold pilotClip
  linarith

def separatedPilot (A : Model.Parameters) (hδ : A.δ ≤ 1/2) (k n : ℕ)
    (data : Fin n → Model.Covariate A.d × Response) (x : Model.Covariate A.d) : ℝ :=
  smoothGridPilot A.d k Prod.fst (MAR.observed ∘ Prod.snd) (pilotClip A) (pilotClip_valid A hδ) x data

def normalizedParameters (A : Model.Parameters) (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (Hq : ℝ) (hHq : 0 < Hq) : Model.Parameters where
  d := A.d
  α := A.α
  β := A.β
  H := max A.H Hq
  δ := A.δ
  gminus := (1-ζ)*A.gminus
  gplus := (1+ζ)*A.gplus
  M0 := 1+2/A.δ
  hd := A.hd
  hα := A.hα
  hβ := A.hβ
  hH := A.hH.trans_le (le_max_left _ _)
  hδ := A.hδ
  hgminus := mul_pos (sub_pos.mpr hζ1) A.hgminus
  hgplus := by
    have hgplus : 0 < A.gplus := A.hgminus.trans A.hgplus
    have hplus : 0 < 1+ζ := by linarith
    have hfirst : (1-ζ)*A.gminus < (1+ζ)*A.gminus :=
      mul_lt_mul_of_pos_right (by linarith) A.hgminus
    exact hfirst.trans (mul_lt_mul_of_pos_left A.hgplus hplus)
  hM0 := by have hd := A.hδ; positivity

theorem normalizedParameters_M0_ge_one (A : Model.Parameters) (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (Hq : ℝ) (hHq : 0 < Hq) : 1 ≤ (normalizedParameters A ζ hζ hζ1 Hq hHq).M0 := by
  change 1 ≤ 1+2/A.δ
  have hd := A.hδ
  linarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hd.le]

theorem normalizedParameters_M0_ge_invClip (A : Model.Parameters) (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (Hq : ℝ) (hHq : 0 < Hq) : 1/pilotClip A ≤ (normalizedParameters A ζ hζ hζ1 Hq hHq).M0 := by
  unfold pilotClip
  change 1/(A.δ/2) ≤ 1+2/A.δ
  rw [div_div_eq_mul_div]
  norm_num

structure PilotSetup (A : Model.Parameters) (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (hδ : A.δ ≤ 1/2) where
  k : ℕ
  H1 : ℝ
  Hq : ℝ
  c : ℝ
  hk : 0 < k
  hH1 : 0 ≤ H1
  hHq : 0 < Hq
  hc : 0 < c
  measurable : ∀ n, Measurable (Function.uncurry (separatedPilot A hδ k n))
  smooth : ∀ n data, ContDiff ℝ ∞ (separatedPilot A hδ k n data)
  range : ∀ n data x, separatedPilot A hδ k n data x ∈ Icc (pilotClip A) (1-pilotClip A)
  holder : ∀ n data, separatedPilot A hδ k n data ∈ Model.holderBall A.α H1
  quotient : ∀ f g : Model.Covariate A.d → ℝ, f ∈ Model.holderBall A.α H1 →
    g ∈ Model.holderBall A.α A.H → (∀ x ∈ Model.cube A.d,A.δ ≤ g x) →
      (fun x => f x/g x) ∈ Model.holderBall A.α Hq
  bad_probability : ∀ (P : ProbabilityMeasure (Model.Covariate A.d × Response))
    (W : Witness A P) (n : ℕ), n ≠ 0 →
    (Measure.pi (fun _ : Fin n => (P : Measure _))).real
      {data | ∃ x ∈ Model.cube A.d, ζ*pilotClip A < |separatedPilot A hδ k n data x-W.w x|} ≤
        c⁻¹*Real.exp (-c*n)

theorem exists_pilotSetup (A : Model.Parameters) (ζ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ < 1)
    (hδ : A.δ ≤ 1/2) : Nonempty (PilotSetup A ζ hζ hζ1 hδ) := by
  have htol : 0 < ζ*pilotClip A := mul_pos hζ (pilotClip_pos A)
  have htol1 : ζ*pilotClip A ≤ 1 := by
    unfold pilotClip
    nlinarith [A.hδ]
  obtain ⟨k,H1,c,hk,hH1,hc,hknown,htail⟩ := fixed_accuracy_smooth_pilot A.d A.α A.H
    (pilotClip A) A.gminus (ζ*pilotClip A) A.hα A.hH.le (pilotClip_pos A).le
    (pilotClip_valid A hδ) A.hgminus htol htol1 Prod.fst measurable_fst
    (MAR.observed ∘ Prod.snd) (MAR.observed_measurable.comp measurable_snd)
    (fun o => MAR.observed_range o.2)
  obtain ⟨Hq,hHq,hquot⟩ := Model.uniform_holder_quotient A.d A.α H1 A.H A.δ A.hα hH1 A.hH.le A.hδ
  refine ⟨⟨k,H1,Hq,c,hk,hH1,hHq,hc,?_,?_,?_,?_,hquot,?_⟩⟩
  · intro n
    have hs : Measurable (fun q : (Fin n → Model.Covariate A.d × Response) × Model.Covariate A.d => (q.2,q.1)) :=
      measurable_snd.prodMk measurable_fst
    exact (hknown n).1.comp (f := fun q : (Fin n → Model.Covariate A.d × Response) × Model.Covariate A.d => (q.2,q.1)) hs
  · intro n data
    exact ((hknown n).2 data).1
  · intro n data x
    exact (((hknown n).2 data).2.1 x)
  · intro n data
    exact ((hknown n).2 data).2.2
  · intro P W n hn
    have hrange := Model.holderBall_ae_mem_Icc_cube W.w A.α A.H A.δ (1-A.δ) W.smoothW W.overlap
    apply htail (P : Measure _) inferInstance W.p W.w W.marginal
      (W.densityBounds.mono (fun _ h => h.1)) W.momentD W.smoothW _ n hn
    intro x hx
    have hp := hrange x hx
    unfold pilotClip
    constructor <;> linarith [hp.1,hp.2,A.hδ]

namespace PilotSetup
variable {A : Model.Parameters} {ζ : ℝ} {hζ : 0 < ζ} {hζ1 : ζ < 1} {hδ : A.δ ≤ 1/2}
abbrev parameters (S : PilotSetup A ζ hζ hζ1 hδ) : Model.Parameters :=
  normalizedParameters A ζ hζ hζ1 S.Hq S.hHq
abbrev pilot (S : PilotSetup A ζ hζ hζ1 hδ) (n : ℕ) := separatedPilot A hδ S.k n
abbrev observables (S : PilotSetup A ζ hζ hζ1 hδ) (n : ℕ)
    (data : Fin n → Model.Covariate A.d × Response) :=
  normalizedObservables S.parameters (S.pilot n data)
    ((S.smooth n data).continuous.measurable) (pilotClip A) (pilotClip_pos A)
    (fun x => (S.range n data x).1)
    (normalizedParameters_M0_ge_one A ζ hζ hζ1 S.Hq S.hHq)
    (normalizedParameters_M0_ge_invClip A ζ hζ hζ1 S.Hq S.hHq)

def Good (S : PilotSetup A ζ hζ hζ1 hδ) (P : ProbabilityMeasure (Model.Covariate A.d × Response))
    (W : Witness A P) (n : ℕ) (data : Fin n → Model.Covariate A.d × Response) : Prop :=
  ∀ x ∈ Model.cube A.d, |S.pilot n data x-W.w x| ≤ ζ*pilotClip A

theorem density_ratio_good (S : PilotSetup A ζ hζ hζ1 hδ)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A P)
    (n : ℕ) (data : Fin n → Model.Covariate A.d × Response) (hgood : S.Good P W n data)
    (x : Model.Covariate A.d) (hx : x ∈ Model.cube A.d) :
    1-ζ ≤ W.w x/S.pilot n data x ∧ W.w x/S.pilot n data x ≤ 1+ζ := by
  have hr := S.range n data x
  have hp : 0 < S.pilot n data x := (pilotClip_pos A).trans_le hr.1
  have he := abs_le.mp (hgood x hx)
  have hζh : ζ*pilotClip A ≤ ζ*S.pilot n data x := mul_le_mul_of_nonneg_left hr.1 hζ.le
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith
  · apply (div_le_iff₀ hp).mpr
    nlinarith

def normalizedWitness (S : PilotSetup A ζ hζ hζ1 hδ)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A P)
    (n : ℕ) (data : Fin n → Model.Covariate A.d × Response) (hgood : S.Good P W n data) :
    Model.ModelWitness S.parameters (S.observables n data) (normalizedLaw A.d P) := by
  have hwrange := Model.holderBall_ae_mem_Icc_cube W.w A.α A.H A.δ (1-A.δ) W.smoothW W.overlap
  have hoverlap : ∀ᵐ x ∂Model.cubeVolume A.d,A.δ ≤ W.w x/S.pilot n data x := by
    filter_upwards [ae_restrict_mem (Model.isCompact_cube A.d).isClosed.measurableSet] with x hx
    have hw := (hwrange x hx).1
    have hp : 0 < S.pilot n data x := (pilotClip_pos A).trans_le (S.range n data x).1
    apply (le_div_iff₀ hp).mpr
    have hh : S.pilot n data x ≤ 1 := (S.range n data x).2.trans (by linarith [pilotClip_pos A])
    exact (mul_le_mul_of_nonneg_left hh A.hδ.le).trans (by simpa only [mul_one] using hw)
  have hqa := S.quotient (S.pilot n data) W.w (S.holder n data) W.smoothW (fun x hx => (hwrange x hx).1)
  have hsmoothA : (fun x => S.pilot n data x/W.w x) ∈ Model.holderBall S.parameters.α S.parameters.H :=
    hqa.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))
  have hsmoothB : W.b ∈ Model.holderBall S.parameters.β S.parameters.H :=
    W.smoothB.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hdensity : ∀ᵐ x ∂Model.cubeVolume A.d,
      S.parameters.gminus ≤ W.w x/S.pilot n data x*W.p x ∧
        W.w x/S.pilot n data x*W.p x ≤ S.parameters.gplus := by
    filter_upwards [W.densityBounds,ae_restrict_mem (Model.isCompact_cube A.d).isClosed.measurableSet]
      with x hp hx
    have hr := S.density_ratio_good P W n data hgood x hx
    have hpp : 0 ≤ W.p x := A.hgminus.le.trans hp.1
    have hlow : 0 ≤ 1-ζ := (sub_pos.mpr hζ1).le
    have hhigh : 0 ≤ 1+ζ := by linarith
    exact ⟨mul_le_mul hr.1 hp.1 A.hgminus.le (hlow.trans hr.1),mul_le_mul hr.2 hp.2 hpp hhigh⟩
  exact (W.moments A P).normalizedModel S.parameters P (S.pilot n data)
    ((S.smooth n data).continuous.measurable) (pilotClip A) (pilotClip_pos A)
    (fun x => (S.range n data x).1)
    (normalizedParameters_M0_ge_one A ζ hζ hζ1 S.Hq S.hHq)
    (normalizedParameters_M0_ge_invClip A ζ hζ hζ1 S.Hq S.hHq)
    hoverlap hsmoothA hsmoothB hdensity

theorem good_compl_eq_bad (S : PilotSetup A ζ hζ hζ1 hδ)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A P) (n : ℕ) :
    {data | S.Good P W n data}ᶜ =
      {data | ∃ x ∈ Model.cube A.d, ζ*pilotClip A < |S.pilot n data x-W.w x|} := by
  classical
  ext data
  simp only [mem_compl_iff,mem_setOf_eq,Good,not_forall,not_le,exists_prop]

theorem good_measurable (S : PilotSetup A ζ hζ hζ1 hδ)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A P) (n : ℕ) :
    MeasurableSet {data | S.Good P W n data} := by
  have hm := smoothGridPilot_error_event_measurable A.d S.k (n := n) Prod.fst measurable_fst
    (MAR.observed ∘ Prod.snd) (MAR.observed_measurable.comp measurable_snd)
    (pilotClip A) (pilotClip_valid A hδ) W.w
    (Model.holderBall_regular W.w A.α A.H W.smoothW).2.continuousOn (ζ*pilotClip A)
  have he := S.good_compl_eq_bad P W n
  apply MeasurableSet.of_compl
  rw [he]
  exact hm

theorem bad_probability_bound (S : PilotSetup A ζ hζ hζ1 hδ)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A P)
    (n : ℕ) (hn : n ≠ 0) :
    (Measure.pi (fun _ : Fin n => (P : Measure _))).real {data | S.Good P W n data}ᶜ ≤
      S.c⁻¹*Real.exp (-S.c*n) := by
  rw [S.good_compl_eq_bad P W n]
  exact S.bad_probability P W n hn

theorem normalizedWitness_productTarget_eq_target (S : PilotSetup A ζ hζ hζ1 hδ)
    (P : ProbabilityMeasure (Model.Covariate A.d × Response)) (W : Witness A P)
    (n : ℕ) (data : Fin n → Model.Covariate A.d × Response) (hgood : S.Good P W n data) :
    (S.normalizedWitness P W n data hgood).productTarget = target A.d P := by
  let WM := S.normalizedWitness P W n data hgood
  have ht := (W.moments A P).normalizedModel_target_eq_mean S.parameters P (S.pilot n data)
    ((S.smooth n data).continuous.measurable) (pilotClip A) (pilotClip_pos A)
    (fun x => (S.range n data x).1)
    (normalizedParameters_M0_ge_one A ζ hζ hζ1 S.Hq S.hHq)
    (normalizedParameters_M0_ge_invClip A ζ hζ hζ1 S.Hq S.hHq)
    WM.overlap WM.smoothA WM.smoothB WM.densityBounds
  have hp : Model.target S.parameters (S.observables n data) (normalizedLaw A.d P) = WM.productTarget := by
    simpa only [observables,normalizedObservables,integral_zero,zero_add,one_mul] using WM.target_eq_linear_product
  exact hp.symm.trans (ht.trans (W.target_eq_mean A P).symm)

end PilotSetup
end RoughRegime.Applications.SeparatedMAR
