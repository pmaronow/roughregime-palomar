module

public import RoughRegime.ProductHardVariance
public import RoughRegime.ProductVarianceUpper
public import RoughRegime.ModelSourceHardness


@[expose] public section
/-! Genuine quadratic hardness on the literal positive-response-variance
subclass. The source laws retain Rademacher response square one and their
actual local mean controls the variance. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RoughRegime.Applications.Products
open RoughRegime.LatticePriors RoughRegime.LatticePriors.SourceModelFamily
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 theorem quadratic_positiveVariance_rough_hardness_dimension (A0 : Model.Parameters) (D : ℕ)
    (hM : 1≤(A0.withDimension D).M0)
    (hlo : max A0.δ A0.gminus<1) (hhi : 1<A0.gplus) (hab : A0.α=A0.β)
    (hrough : (A0.withDimension D).theta<1/2) (vmin : ℝ) (hv : 0<vmin) (hv1 : vmin<1) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,(3/8:ℝ≥0∞)≤Model.minimaxTail n
      (quadraticTarget (A0.withDimension D)) (positiveVarianceClass (A0.withDimension D) vmin)
      (2*c*Model.lowerBracketScale (A0.withDimension D).bracketParameters n) := by
  let A := A0.withDimension D
  let O := quadraticObservables A hM
  have hnd : Model.Nondegenerate A O boundedDiagonalBaseline :=
    bounded_diagonal_baseline_nondegenerate A O rfl rfl rfl hlo hhi hab
  obtain ⟨F,hF⟩ := nondegenerate_source_model_family A0 D O boundedDiagonalBaseline hnd
  have hθ := A.theta_pos
  have hτ := Rates.tau_pos _ _ F.interval.1 (F.interval.2.1.trans F.interval.2.2)
  let r := Real.sqrt (1-vmin)
  have hr : 0<r := Real.sqrt_pos.mpr (by linarith)
  have hvr : r^2≤1-vmin := by
    dsimp only [r]
    rw [Real.sq_sqrt (by linarith : 0≤1-vmin)]
  have hclass : ∀ c0 : ℝ,F.SelectedClassClaim A.theta (Rates.tau F.rminus F.rplus) c0
      (positiveVarianceClass A vmin) := by
    intro c0
    filter_upwards [F.selectedClassClaim_local hF _ _ c0 r hθ hrough hτ hr] with n hn
    obtain ⟨V,hsmall,hlocal⟩ := hn
    refine ⟨V,hsmall,?_⟩
    intro z
    let G := F.selectedFrame A.theta (Rates.tau F.rminus F.rplus) c0 n V
    refine ⟨?_,?_⟩
    · have hm := Model.localClass_subset A O boundedDiagonalBaseline r (hlocal z)
      rw [←modelClass_eq_generic A O rfl ((le_max_left _ _).trans hlo.le)] at hm
      exact hm
    · exact canonical_local_responseVariance_lower A0 G F.scores hsmall z hM r vmin hr.le hvr (hlocal z)
  obtain ⟨c,hc,n0,_,hb⟩ := F.source_family_rough_lower hF hrough _ hclass
  refine ⟨c,hc,?_⟩
  filter_upwards [eventually_ge_atTop n0] with n hn
  have hs : Model.lowerBracketScale A.bracketParameters n=
      Rates.subcriticalScale n A.theta (Rates.tau A0.gminus A0.gplus)*Real.log n := by
    unfold Model.lowerBracketScale
    change (if A.theta<1/2 then _ else _)=_
    rw [ite_eq_left hrough]
    rfl
  rw [hs]
  have hh := (hb n hn).2
  dsimp only [O] at hh
  rw [quadratic_target] at hh
  convert hh using 1
  congr 1
  ring

 theorem quadratic_positiveVariance_rough_hardness (A : Model.Parameters) (hM : 1≤A.M0)
    (hlo : max A.δ A.gminus<1) (hhi : 1<A.gplus) (hab : A.α=A.β)
    (hrough : A.theta<1/2) (vmin : ℝ) (hv : 0<vmin) (hv1 : vmin<1) :
    ∃ c : ℝ,0<c ∧ ∀ᶠ n : ℕ in atTop,(3/8:ℝ≥0∞)≤Model.minimaxTail n
      (quadraticTarget A) (positiveVarianceClass A vmin)
      (2*c*Model.lowerBracketScale A.bracketParameters n) := by
  cases A with
  | mk d α β H δ gminus gplus M0 hd hα hβ hH hδ hgminus hgplus hM0 => cases d with
    | zero => omega
    | succ D =>
      exact quadratic_positiveVariance_rough_hardness_dimension
        (Model.Parameters.mk (D+1) α β H δ gminus gplus M0 hd hα hβ hH hδ hgminus hgplus hM0)
        D hM hlo hhi hab hrough vmin hv hv1

end RoughRegime.Applications.Products
