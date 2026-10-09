module

public import RoughRegime.ModelLipschitzCombination


@[expose] public section
/-! Exact approximate reverse-risk transfer on the actual seeded iid model,
with no empirical nuisance moments. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace RoughRegime.Model
set_option backward.isDefEq.respectTransparency false

 theorem zero_moment_reverse_tail {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T0 T1 : ProbabilityMeasure Ω→ℝ) (C : Set (ProbabilityMeasure Ω))
    (lo hi : ℝ) (hlohi : lo≤hi) (Φ : Icc lo hi→ℝ)
    (L t e : ℝ) (hL : 0<L) (ht : 0<t) (he : e≤t/2)
    (hLip : ∀ a b,|Φ a-Φ b|≤L*|(a:ℝ)-b|)
    (hmem : ∀ P∈C,T0 P∈Icc lo hi)
    (hrel : ∀ P∈C,|T1 P-Φ (projIcc lo hi hlohi (T0 P))|≤e) :
    minimaxTail n T1 C t≤ minimaxTail n T0 C (t/(4*L)) := by
  have : ∀ P : ProbabilityMeasure Ω,IsProbabilityMeasure (randomizedExperiment n P) := fun P=>by
    change IsProbabilityMeasure ((Measure.pi (fun _ : Fin n=>(P:Measure Ω))).prod KernelSeedBridge.seedLaw)
    infer_instance
  let Ψ : Icc lo hi→Unit→ℝ:=fun a _=>Φ a
  have hl : ∀ a b (q r:Unit),|Ψ a q-Ψ b r|≤L*(|(a:ℝ)-b|+dist q r) := by
    intro a b q r;simpa only [Ψ,Subsingleton.elim q r,dist_self,add_zero] using hLip a b
  have he := Applications.reverse_transfer_minimax (randomizedExperiment n) T0 T1 C
    lo hi hlohi Ψ (Applications.lipschitz_reverse_measurable lo hi Ψ L hL.le hl)
    (fun _=>()) measurable_const (fun _=>()) L t e 0 1 hL ht zero_lt_one he hl hmem hrel
    (by intro P _;simp) (by intro P _;simp)
  rw [minimaxTail_eq_experimentTail,minimaxTail_eq_experimentTail]
  simpa only [zero_pow (by decide : (2:ℕ)≠0),mul_zero,zero_div,ENNReal.ofReal_zero,add_zero] using he

 theorem zero_moment_reverse_rmse {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T0 T1 : ProbabilityMeasure Ω→ℝ) (C : Set (ProbabilityMeasure Ω))
    (lo hi : ℝ) (hlohi : lo≤hi) (Φ : Icc lo hi→ℝ)
    (L e : ℝ) (hL : 0≤L) (he : 0≤e)
    (hLip : ∀ a b,|Φ a-Φ b|≤L*|(a:ℝ)-b|)
    (hmem : ∀ P∈C,T0 P∈Icc lo hi)
    (hrel : ∀ P∈C,|T1 P-Φ (projIcc lo hi hlohi (T0 P))|≤e) :
    minimaxRMSE n T1 C≤ENNReal.ofReal L*minimaxRMSE n T0 C+ENNReal.ofReal e := by
  have : ∀ P : ProbabilityMeasure Ω,IsProbabilityMeasure (randomizedExperiment n P) := fun P=>by
    change IsProbabilityMeasure ((Measure.pi (fun _ : Fin n=>(P:Measure Ω))).prod KernelSeedBridge.seedLaw)
    infer_instance
  let Ψ : Icc lo hi→Unit→ℝ:=fun a _=>Φ a
  have hl : ∀ a b (q r:Unit),|Ψ a q-Ψ b r|≤L*(|(a:ℝ)-b|+dist q r) := by
    intro a b q r;simpa only [Ψ,Subsingleton.elim q r,dist_self,add_zero] using hLip a b
  have h := Applications.lipschitz_reverse_minimax (randomizedExperiment n) T0 T1 C lo hi hlohi Ψ
    (Applications.lipschitz_reverse_measurable lo hi Ψ L hL hl)
    (fun _=>()) measurable_const (fun _=>()) L e 0 hL he hl hmem hrel
    (by intro P _;simp)
  simpa only [← minimaxRMSE_eq_squaredRisk,mul_zero,add_zero] using h

end RoughRegime.Model
