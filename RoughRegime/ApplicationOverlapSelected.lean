module

public import RoughRegime.ApplicationOverlapExtras
public import RoughRegime.SourceUniversalExtras


@[expose] public section
/-! Fixed actual source families whose selected laws satisfy every literal
overlap-model restriction, for all admissible later statistical offsets. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace RoughRegime.Applications.Overlap
open RoughRegime.LatticePriors RoughRegime.ReductionScales
set_option backward.isDefEq.respectTransparency false

 theorem independent_selected_family (A0 : Model.Parameters) (D : ℕ) (ε : ℝ)
    (hε : ε<1/2) (hM : 1≤A0.M0) (hlo : max A0.δ A0.gminus<1)
    (hhi : 1<A0.gplus) (hH : 1/2<A0.H) :
    ∃ G : SourceModelFamily A0 D (numeratorObservables (A0.withDimension D) hM) (baseline 0 (by norm_num)),
      G.Localized ∧ G.scores=scores 0 (by norm_num) ∧
      ∀ (θ τ c0 r : ℝ), 0<θ → θ<1/2 → 0<τ → 0<r →
      ∀ᶠ n in atTop, ∃ V : G.SelectedValidity θ τ c0 n,
        let B:=G.selectedFrame θ τ c0 n V
        ∃ hsmall : (B.Au+B.Av)/G.rminus*G.scores.C≤1/4,
          ∀ z, (SpatialAffine.law G.scores (B.field z) hsmall).probabilityMeasure∈
            modelClass (A0.withDimension D) ε := by
  obtain ⟨F,hF,hS⟩ := exists_independent_family A0 D hM hlo hhi hH
  have hrm : F.rminus=A0.gminus := by
    rw [SourceModelFamily.rminus,baselineW_one _ _ rfl];simp
  have hrp : F.rplus=A0.gplus := by
    rw [SourceModelFamily.rplus,baselineW_one _ _ rfl];simp
  have hb : ∀ i,(independentExtras (A0.withDimension D) ε i).condition.baselineAdmissible F.rminus F.rplus := by
    rw [hrm,hrp]
    exact independent_extras_baseline _ ε hε hH
  obtain ⟨G,hG,hGS,_,_,he⟩ := F.exists_universal_selected_extra_family hF
    (independentExtras (A0.withDimension D) ε) hb
  have hS' : G.scores=scores 0 (by norm_num) := hGS.trans hS
  refine ⟨G,hG,hS',?_⟩
  intro θ τ c0 r hθ hθhalf hτ hr
  filter_upwards [he θ τ c0 r hθ hθhalf hτ hr] with n hn
  obtain ⟨V,hsmall,hmem⟩ := hn
  refine ⟨V,hsmall,?_⟩
  intro z
  have hrB : (G.selectedFrame θ τ c0 n V).rminus=G.rminus := by rfl
  simpa only [hS'] using independent_extras_law_mem (A0.withDimension D) ε 0 (by norm_num)
    ((G.selectedFrame θ τ c0 n V).field z) (by simpa only [hS',CanonicalFrame.field,hrB] using hsmall) (hmem z).2

 theorem diagonal_selected_family (A0 : Model.Parameters) (D : ℕ) (ε : ℝ)
    (hε : ε<1/2) (hM : 1≤A0.M0) (hlo : max A0.δ A0.gminus<1)
    (hhi : 1<A0.gplus) (hH : 1/2<A0.H) :
    ∃ G : SourceModelFamily (diagonalParameters A0) D (denominatorObservables (A0.withDimension D) hM)
      (baseline (1/4) (by norm_num)), G.Localized ∧ G.scores=diagonalScores ∧
      ∀ (θ τ c0 r : ℝ), 0<θ → θ<1/2 → 0<τ → 0<r →
      ∀ᶠ n in atTop, ∃ V : G.SelectedValidity θ τ c0 n,
        let B:=G.selectedFrame θ τ c0 n V
        ∃ hsmall : (B.Au+B.Av)/G.rminus*G.scores.C≤1/4,
          ∀ z, (SpatialAffine.law G.scores (B.field z) hsmall).probabilityMeasure∈
            modelClass (A0.withDimension D) ε := by
  obtain ⟨F,hF,hS⟩ := exists_diagonal_family A0 D hM hlo hhi hH
  have hrm : F.rminus=A0.gminus := by
    rw [SourceModelFamily.rminus,baselineW_one _ _ rfl];simp
  have hrp : F.rplus=A0.gplus := by
    rw [SourceModelFamily.rplus,baselineW_one _ _ rfl];simp
  have hb : ∀ i,(diagonalExtras (A0.withDimension D) ε i).condition.baselineAdmissible F.rminus F.rplus := by
    rw [hrm,hrp]
    exact diagonal_extras_baseline _ ε hε hH
  obtain ⟨G,hG,hGS,_,_,he⟩ := F.exists_universal_selected_extra_family hF
    (diagonalExtras (A0.withDimension D) ε) hb
  have hS' : G.scores=diagonalScores := hGS.trans hS
  refine ⟨G,hG,hS',?_⟩
  intro θ τ c0 r hθ hθhalf hτ hr
  filter_upwards [he θ τ c0 r hθ hθhalf hτ hr] with n hn
  obtain ⟨V,hsmall,hmem⟩ := hn
  refine ⟨V,hsmall,?_⟩
  intro z
  have hrB : (G.selectedFrame θ τ c0 n V).rminus=G.rminus := by rfl
  simpa only [hS'] using diagonal_extras_law_mem (A0.withDimension D) ε hH.le
    ((G.selectedFrame θ τ c0 n V).field z) (by simpa only [hS',CanonicalFrame.field,hrB] using hsmall) (hmem z).2

end RoughRegime.Applications.Overlap
