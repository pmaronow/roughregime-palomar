module

public import RoughRegime.ProductHardVariance
public import RoughRegime.SourceSelectedExtras


@[expose] public section
/-! The actual selected quadratic hard laws have response variance tending
uniformly to one over every realization of the source prior. Their response
second moment is exactly one; the vanishing mean is derived from source
localization at every positive radius. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace RoughRegime.Applications.Products
open RoughRegime.LatticePriors RoughRegime.LatticePriors.SourceModelFamily
open RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Quantitative finite-law form of the source variance assertion. -/
theorem canonical_local_responseVariance_abs_sub_one_le (A0 : Model.Parameters) {D N : ℕ}
    {ι : Type*} [Fintype ι] (G : LatticePriors.CanonicalFrame D N ι)
    (S : SpatialAffine.Scores (boundedDiagonalBaseline : Measure BoundedResponse))
    (hsmall : (G.Au+G.Av)/G.rminus*S.C≤1/4)
    (z : LatticePriors.GridPair D N → LatticePriors.PairState ι)
    (hM : 1≤(A0.withDimension D).M0) (r : ℝ) (hr : 0≤r)
    (hlocal : G.observationProbability boundedDiagonalBaseline S hsmall z ∈
      Model.localClass (A0.withDimension D) (quadraticObservables _ hM) boundedDiagonalBaseline r) :
    |responseVariance (A0.withDimension D)
      (G.observationProbability boundedDiagonalBaseline S hsmall z)-1|≤r^2 := by
  let A:=A0.withDimension D
  let P : ProbabilityMeasure (Model.Observation A BoundedResponse):=
    G.observationProbability boundedDiagonalBaseline S hsmall z
  have hsecond:responseSecondMoment A P=1:=canonical_responseSecondMoment_one A0 G S hsmall z
  have hm:=quadratic_local_responseMean_abs_le A hM r P hlocal
  have hsq: (responseMean A P)^2≤r^2:=by
    have hs:=(sq_le_sq₀ (abs_nonneg (responseMean A P)) hr).mpr hm
    simpa only [sq_abs] using hs
  change |responseVariance A P-1|≤r^2
  rw [responseVariance_identity A P,hsecond]
  have he:1-(responseMean A P)^2-1= -(responseMean A P)^2:=by ring
  rw [he,abs_neg,abs_of_nonneg (sq_nonneg _)]
  exact hsq

/-- Uniform convergence on all actual selected hard laws. The validity and
positivity arguments are arbitrary proof witnesses, and the bound holds for
every complete realization of the spatial/response prior. -/
def UniformSelectedVarianceClaim (A0 : Model.Parameters) (D : ℕ)
    (hM : 1≤(A0.withDimension D).M0)
    (F : SourceModelFamily A0 D (quadraticObservables (A0.withDimension D) hM) boundedDiagonalBaseline)
    (θ τ c0 : ℝ) : Prop :=
  ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
    ∀ V : F.SelectedValidity θ τ c0 n,
      let G:=F.selectedFrame θ τ c0 n V
      ∀ hsmall : (G.Au+G.Av)/G.rminus*F.scores.C≤1/4,
      ∀ z : GridPair D (selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n) →
        PairState (Fin (selectedSourceLevel A0 (D+1) θ τ n)×Fin (D+1)),
      |responseVariance (A0.withDimension D)
        (G.observationProbability boundedDiagonalBaseline F.scores hsmall z)-1|<ε

/-- The uniform variance limit is derived from the constructed family's true
local-class membership; no moment-convergence assumption is supplied. -/
theorem uniform_selected_responseVariance_tendsto_one (A0 : Model.Parameters) (D : ℕ)
    (hM : 1≤(A0.withDimension D).M0)
    (F : SourceModelFamily A0 D (quadraticObservables (A0.withDimension D) hM) boundedDiagonalBaseline)
    (hF : F.Localized) (θ τ c0 : ℝ)
    (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ) :
    UniformSelectedVarianceClaim A0 D hM F θ τ c0 := by
  intro ε hε
  let r:=Real.sqrt (ε/2)
  have hr:0<r:=Real.sqrt_pos.mpr (div_pos hε (by norm_num))
  filter_upwards [F.eventually_final_selected_hard_laws hF θ τ c0 r hθ hθhalf hτ hr]
    with n hn
  obtain ⟨hN,hm,hd,hmargin,hsmall,hlocal⟩:=hn
  intro V
  dsimp only
  intro hsmall' z
  let G:=F.selectedFrame θ τ c0 n V
  have hPlocal:G.observationProbability boundedDiagonalBaseline F.scores hsmall' z ∈
      Model.localClass (A0.withDimension D) (quadraticObservables _ hM) boundedDiagonalBaseline r :=
    (hlocal z).1
  have hb:=canonical_local_responseVariance_abs_sub_one_le A0 G F.scores hsmall' z hM r hr.le hPlocal
  have hr2:r^2=ε/2:=Real.sq_sqrt (by positivity)
  apply hb.trans_lt
  rw [hr2]
  linarith

/-- Literal membership in the selected-law family, with actual observation
probabilities rather than a symbolic statistical parameter. -/
def IsSelectedQuadraticLaw (A0 : Model.Parameters) (D : ℕ)
    (hM : 1≤(A0.withDimension D).M0)
    (F : SourceModelFamily A0 D (quadraticObservables (A0.withDimension D) hM) boundedDiagonalBaseline)
    (θ τ c0 : ℝ) (n : ℕ)
    (P : ProbabilityMeasure (Model.Observation (A0.withDimension D) BoundedResponse)) : Prop :=
  ∃ V : F.SelectedValidity θ τ c0 n,
    let G:=F.selectedFrame θ τ c0 n V
    ∃ hsmall : (G.Au+G.Av)/G.rminus*F.scores.C≤1/4,
    ∃ z : GridPair D (selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n) →
      PairState (Fin (selectedSourceLevel A0 (D+1) θ τ n)×Fin (D+1)),
      P=G.observationProbability boundedDiagonalBaseline F.scores hsmall z

/-- Every sequence of actual selected hard laws, with arbitrary prior
realizations at each sample size, has response variance tending to one. -/
theorem selected_law_responseVariance_tendsto_one (A0 : Model.Parameters) (D : ℕ)
    (hM : 1≤(A0.withDimension D).M0)
    (F : SourceModelFamily A0 D (quadraticObservables (A0.withDimension D) hM) boundedDiagonalBaseline)
    (hF : F.Localized) (θ τ c0 : ℝ)
    (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ)
    (P : ℕ → ProbabilityMeasure (Model.Observation (A0.withDimension D) BoundedResponse))
    (hP : ∀ᶠ n in atTop,IsSelectedQuadraticLaw A0 D hM F θ τ c0 n (P n)) :
    Tendsto (fun n => responseVariance (A0.withDimension D) (P n)) atTop (𝓝 1) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hP,
    uniform_selected_responseVariance_tendsto_one A0 D hM F hF θ τ c0 hθ hθhalf hτ ε hε]
    with n hPn hn
  obtain ⟨V,hsmall,z,hid⟩:=hPn
  rw [hid,Real.dist_eq]
  exact hn V hsmall z

/-- The selected-law limit is nonvacuous: admissible actual observation laws
exist at every sufficiently large sample size. -/
theorem selected_quadratic_laws_eventually_exist (A0 : Model.Parameters) (D : ℕ)
    (hM : 1≤(A0.withDimension D).M0)
    (F : SourceModelFamily A0 D (quadraticObservables (A0.withDimension D) hM) boundedDiagonalBaseline)
    (hF : F.Localized) (θ τ c0 : ℝ)
    (hθ : 0<θ) (hθhalf : θ<1/2) (hτ : 0<τ) :
    ∀ᶠ n in atTop,∃ P,IsSelectedQuadraticLaw A0 D hM F θ τ c0 n P := by
  filter_upwards [F.eventually_final_selected_hard_laws hF θ τ c0 1 hθ hθhalf hτ zero_lt_one]
    with n hn
  obtain ⟨hN,hm,hd,hmargin,hsmall,_⟩:=hn
  let V : F.SelectedValidity θ τ c0 n:=⟨hN,hm,hd,hmargin⟩
  let G:=F.selectedFrame θ τ c0 n V
  let z : GridPair D (selectedGridPairs θ τ c0 (selectedSourceVolume A0 (D+1) θ τ) (D+1) n) →
      PairState (Fin (selectedSourceLevel A0 (D+1) θ τ n)×Fin (D+1)):=
    fun _ => (fun _ => 0,0,false,false)
  exact ⟨G.observationProbability boundedDiagonalBaseline F.scores hsmall z,V,hsmall,z,rfl⟩

/-- Original model assumptions construct one fixed hard-law family whose
variance converges uniformly to one, for every source block-count tuning. -/
theorem quadratic_original_uniform_variance_convergence (A0 : Model.Parameters) (D : ℕ)
    (hM : 1≤(A0.withDimension D).M0)
    (hlo : max A0.δ A0.gminus<1) (hhi : 1<A0.gplus) (hab : A0.α=A0.β)
    (hrough : (A0.withDimension D).theta<1/2) :
    ∃ F : SourceModelFamily A0 D (quadraticObservables (A0.withDimension D) hM) boundedDiagonalBaseline,
      F.Localized ∧ ∀ c0 : ℝ, UniformSelectedVarianceClaim A0 D hM F
        (A0.withDimension D).theta (RoughRegime.Rates.tau A0.gminus A0.gplus) c0 := by
  let A:=A0.withDimension D
  let O:=quadraticObservables A hM
  have hnd:Model.Nondegenerate A O boundedDiagonalBaseline:=
    bounded_diagonal_baseline_nondegenerate A O rfl rfl rfl hlo hhi hab
  obtain ⟨F,hF⟩:=nondegenerate_source_model_family A0 D O boundedDiagonalBaseline hnd
  refine ⟨F,hF,?_⟩
  intro c0
  exact uniform_selected_responseVariance_tendsto_one A0 D hM F hF _ _ c0
    A.theta_pos hrough (RoughRegime.Rates.tau_pos _ _ A0.hgminus A0.hgplus)

end RoughRegime.Applications.Products
