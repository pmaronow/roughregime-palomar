module

public import RoughRegime.CompactDensityParameters


@[expose] public section
/-! A compact family of admissible density intervals has a common positive
minimum tau and a finite maximum tau, without changing any interval's rate. -/
noncomputable section
open Set
namespace RoughRegime.Model

lemma density_tau_continuousOn :
    ContinuousOn (fun I:ℝ×ℝ=>Rates.tau I.1 I.2) densityIntervalDomain := by
  have hnum : Continuous (fun I:ℝ×ℝ=>Real.sqrt I.2-Real.sqrt I.1) := by fun_prop
  have hden : Continuous (fun I:ℝ×ℝ=>Real.sqrt I.2+Real.sqrt I.1) := by fun_prop
  have hρ : ContinuousOn (fun I:ℝ×ℝ=>Rates.rho I.1 I.2) densityIntervalDomain := by
    unfold Rates.rho
    apply hnum.continuousOn.div hden.continuousOn
    intro I hI
    have hp:=Real.sqrt_pos.mpr hI.1
    have hn:=Real.sqrt_nonneg I.2
    linarith
  exact (hρ.log (fun I hI=>(Rates.rho_pos I.1 I.2 hI.1 hI.2).ne')).neg

lemma compact_density_tau_bounds (G : Set (ℝ×ℝ)) (hG : IsCompact G)
    (hdom : G⊆densityIntervalDomain) :
    ∃τlo τhi:ℝ,0<τlo ∧ τlo≤τhi ∧ ∀I∈G,Rates.tau I.1 I.2∈Icc τlo τhi := by
  by_cases hne:G.Nonempty
  · have hc:=density_tau_continuousOn.mono hdom
    obtain ⟨Il,hIl,hl⟩:=hG.exists_isMinOn hne hc
    obtain ⟨Iu,hIu,hu⟩:=hG.exists_isMaxOn hne hc
    have hd:=hdom hIl
    refine ⟨Rates.tau Il.1 Il.2,Rates.tau Iu.1 Iu.2,
      Rates.tau_pos Il.1 Il.2 hd.1 hd.2,hl hIu,?_⟩
    intro I hI
    exact ⟨hl hI,hu hI⟩
  · refine ⟨1,1,by norm_num,le_rfl,?_⟩
    intro I hI
    exact False.elim (hne ⟨I,hI⟩)

end RoughRegime.Model
