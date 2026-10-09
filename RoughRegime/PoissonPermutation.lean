module

public import RoughRegime.PoissonLabelMarks


@[expose] public section
/-! Permuting the observation coordinates leaves the labeled tensor L² norm
unchanged. Leading source coefficients therefore have the canonical Gamma norm. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

variable {W Y : Type*} [MeasurableSpace W] [MeasurableSpace Y]
variable (prior : Measure W) (μ : Measure Y) [SigmaFinite μ]

 theorem labeledNormSquared_perm (v : W → ℝ) (e : Fin 3 → W → Y → ℝ)
    (k : ℕ) (labels : Fin k → Fin 3) (p : Fin k ≃ Fin k) :
    labeledNormSquared prior μ v e k (labels ∘ p) =
      labeledNormSquared prior μ v e k labels := by
  let E := MeasurableEquiv.piCongrLeft (fun _ : Fin k => Y) p
  have he (xs : Fin k → Y) : labeledMixture prior v e k labels (E xs) =
      labeledMixture prior v e k (labels ∘ p) xs := by
    unfold labeledMixture
    congr 1
    funext w
    congr 1
    unfold labeledTensor
    have hp := p.prod_comp (fun i => e (labels i) w ((E xs) i))
    simpa [E, Function.comp_def, MeasurableEquiv.piCongrLeft_apply_apply] using hp.symm
  unfold labeledNormSquared
  have hi := (measurePreserving_piCongrLeft (fun _ : Fin k => μ) p).integral_comp'
    (fun xs => labeledMixture prior v e k labels xs ^ 2)
  change (∫ xs, labeledMixture prior v e k labels (E xs) ^ 2 ∂Measure.pi (fun _ : Fin k => μ)) = _ at hi
  simpa only [he] using hi

 def labelCount (k : ℕ) (labels : Fin k → Fin 3) (l : Fin 3) : ℕ :=
  (Finset.univ.filter fun i => labels i = l).card

 theorem labelCount_one (k : ℕ) (labels : Fin k → Fin 3) (l : Fin 3)
    (h : labelCount k labels l = 1) :
    ∃ u : Fin k, ∀ i, labels i = l ↔ i = u := by
  unfold labelCount at h
  obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h
  refine ⟨u, fun i => ?_⟩
  have hi := congrArg (fun t : Finset (Fin k) => i ∈ t) hu
  simpa using hi

 def leadingLabels (j : ℕ) (i : Fin (j + 2)) : Fin 3 :=
   if i = 0 then 1 else if i = 1 then 2 else 0

 theorem leading_labels_perm (j : ℕ) (labels : Fin (j + 2) → Fin 3)
    (hu : labelCount (j + 2) labels 1 = 1) (hv : labelCount (j + 2) labels 2 = 1) :
    ∃ p : Fin (j + 2) ≃ Fin (j + 2), labels ∘ p = leadingLabels j := by
  classical
  obtain ⟨u, hu'⟩ := labelCount_one (j + 2) labels 1 hu
  obtain ⟨v, hv'⟩ := labelCount_one (j + 2) labels 2 hv
  have huv : u ≠ v := by
    intro h
    have h1 := (hu' u).mpr rfl
    have h2 := (hv' u).mpr h
    rw [h1] at h2
    norm_num at h2
  let p₁ : Equiv.Perm (Fin (j + 2)) := Equiv.swap 0 u
  let v' := p₁.symm v
  have hv0 : v' ≠ 0 := by
    intro h
    have hvu : v = u := by
      have he := congrArg p₁ h
      simpa [v', p₁] using he
    exact huv hvu.symm
  let p₂ : Equiv.Perm (Fin (j + 2)) := Equiv.swap 1 v'
  let p := p₂.trans p₁
  have hp0 : p 0 = u := by
    dsimp [p, p₂]
    rw [Equiv.swap_apply_of_ne_of_ne (by norm_num) hv0.symm]
    simp [p₁]
  have hp1 : p 1 = v := by
    simp [p, p₂, v']
  refine ⟨p, ?_⟩
  funext i
  by_cases hi0 : i = 0
  · subst i
    simp [hp0, leadingLabels, (hu' u).mpr rfl]
  by_cases hi1 : i = 1
  · subst i
    simp [hp1, leadingLabels, (hv' v).mpr rfl]
  have hpu : p i ≠ u := by
    intro h
    have h' : p i = p 0 := h.trans hp0.symm
    exact hi0 (p.injective h')
  have hpv : p i ≠ v := by
    intro h
    have h' : p i = p 1 := h.trans hp1.symm
    exact hi1 (p.injective h')
  have hlabel : labels (p i) = 0 := by
    have h1 : labels (p i) ≠ 1 := fun h => hpu ((hu' (p i)).mp h)
    have h2 : labels (p i) ≠ 2 := fun h => hpv ((hv' (p i)).mp h)
    have hr : (labels (p i)).val < 3 := (labels (p i)).isLt
    apply Fin.ext
    have hn1 : (labels (p i)).val ≠ 1 := by intro h; exact h1 (Fin.ext h)
    have hn2 : (labels (p i)).val ≠ 2 := by intro h; exact h2 (Fin.ext h)
    omega
  simp [leadingLabels, hi0, hi1, hlabel]

 theorem leading_labeledNormSquared_eq (v : W → ℝ) (e : Fin 3 → W → Y → ℝ)
    (j : ℕ) (labels : Fin (j + 2) → Fin 3)
    (hu : labelCount (j + 2) labels 1 = 1) (hv : labelCount (j + 2) labels 2 = 1) :
    labeledNormSquared prior μ v e (j + 2) labels =
      labeledNormSquared prior μ v e (j + 2) (leadingLabels j) := by
  obtain ⟨p, hp⟩ := leading_labels_perm j labels hu hv
  rw [← hp]
  exact (labeledNormSquared_perm prior μ v e (j + 2) labels p).symm

end RoughRegime.PoissonMeasure
