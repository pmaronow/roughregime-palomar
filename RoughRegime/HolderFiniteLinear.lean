module

public import RoughRegime.HolderFiniteAffine


@[expose] public section
/-! Exact addition and scalar contractions in the finite coordinate Hölder
norm. These statements apply to every member of the paper's Hölder balls. -/
noncomputable section
open scoped ContDiff
namespace RoughRegime.Model
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

theorem coordinateDerivative_add_finite {d : ℕ} (f g : Covariate d→ℝ) (t:ℝ)
    (hf : ContDiffOn ℝ (holderOrder t) f (cube d)) (hg : ContDiffOn ℝ (holderOrder t) g (cube d))
    (q:ℕ) (hq:q ≤ holderOrder t) (σ:Fin q→Fin d) (x:Covariate d) (hx:x∈cube d) :
    coordinateDerivative (f+g) q σ x=coordinateDerivative f q σ x+coordinateDerivative g q σ x := by
  unfold coordinateDerivative
  rw [iteratedFDerivWithin_add_apply ((hf x hx).of_le (by exact_mod_cast hq))
    ((hg x hx).of_le (by exact_mod_cast hq)) (uniqueDiffOn_cube d) hx]
  rfl

theorem holderBall_add_finite {d : ℕ} (f g : Covariate d→ℝ) (t Hf Hg:ℝ)
    (hHf:0 ≤ Hf) (hHg:0 ≤ Hg) (hf:f∈holderBall t Hf) (hg:g∈holderBall t Hg) :
    (f+g)∈holderBall t (Hf+Hg) := by
  have hrF:=holderBall_regular f t Hf hf
  have hrG:=holderBall_regular g t Hg hg
  have hsup:derivativeSup (f+g) (holderOrder t) ≤ derivativeSup f (holderOrder t)+derivativeSup g (holderOrder t):=by
    apply iSup_le;intro q
    apply iSup_le;intro hq
    apply iSup_le;intro σ
    apply iSup_le;intro x
    apply iSup_le;intro hx
    calc
      _ ≤ ENNReal.ofReal (|coordinateDerivative f q σ x|+|coordinateDerivative g q σ x|):=by
        apply ENNReal.ofReal_le_ofReal
        rw [coordinateDerivative_add_finite f g t hrF.2 hrG.2 q hq σ x hx]
        exact abs_add_le _ _
      _ = ENNReal.ofReal |coordinateDerivative f q σ x|+ENNReal.ofReal |coordinateDerivative g q σ x|:=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ _:=by
        have hF:ENNReal.ofReal |coordinateDerivative f q σ x| ≤ derivativeSup f (holderOrder t):=
          le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le σ (le_iSup_of_le x (le_iSup_of_le hx le_rfl))))
        have hG:ENNReal.ofReal |coordinateDerivative g q σ x| ≤ derivativeSup g (holderOrder t):=
          le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le σ (le_iSup_of_le x (le_iSup_of_le hx le_rfl))))
        exact add_le_add hF hG
  have hsem:holderSeminorm (f+g) t ≤ holderSeminorm f t+holderSeminorm g t:=by
    apply iSup_le;intro σ
    apply iSup_le;intro x
    apply iSup_le;intro hx
    apply iSup_le;intro y
    apply iSup_le;intro hy
    apply iSup_le;intro hxy
    have hp:0 ≤ ‖x-y‖^holderExponent t:=Real.rpow_nonneg (norm_nonneg _) _
    let F:=|coordinateDerivative f (holderOrder t) σ x-coordinateDerivative f (holderOrder t) σ y|
    let G:=|coordinateDerivative g (holderOrder t) σ x-coordinateDerivative g (holderOrder t) σ y|
    calc
      _ ≤ ENNReal.ofReal ((F+G)/‖x-y‖^holderExponent t):=by
        apply ENNReal.ofReal_le_ofReal
        apply div_le_div_of_nonneg_right _ hp
        rw [coordinateDerivative_add_finite f g t hrF.2 hrG.2 _ le_rfl σ x hx,
          coordinateDerivative_add_finite f g t hrF.2 hrG.2 _ le_rfl σ y hy]
        have he:(coordinateDerivative f (holderOrder t) σ x+coordinateDerivative g (holderOrder t) σ x)-
            (coordinateDerivative f (holderOrder t) σ y+coordinateDerivative g (holderOrder t) σ y)=
            (coordinateDerivative f (holderOrder t) σ x-coordinateDerivative f (holderOrder t) σ y)+
            (coordinateDerivative g (holderOrder t) σ x-coordinateDerivative g (holderOrder t) σ y):=by ring
        rw [he];exact abs_add_le _ _
      _ = ENNReal.ofReal (F/‖x-y‖^holderExponent t)+ENNReal.ofReal (G/‖x-y‖^holderExponent t):=by
        rw [add_div,ENNReal.ofReal_add (div_nonneg (abs_nonneg _) hp) (div_nonneg (abs_nonneg _) hp)]
      _ ≤ _:=by
        have hF:ENNReal.ofReal (F/‖x-y‖^holderExponent t) ≤ holderSeminorm f t:=
          le_iSup_of_le σ (le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy (le_iSup_of_le hxy le_rfl)))))
        have hG:ENNReal.ofReal (G/‖x-y‖^holderExponent t) ≤ holderSeminorm g t:=
          le_iSup_of_le σ (le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy (le_iSup_of_le hxy le_rfl)))))
        exact add_le_add hF hG
  change holderNorm (f+g) t ≤ _
  change holderNorm f t ≤ _ at hf
  change holderNorm g t ≤ _ at hg
  rw [holderNorm,ite_eq_left hrF] at hf
  rw [holderNorm,ite_eq_left hrG] at hg
  rw [holderNorm,ite_eq_left ⟨hrF.1,hrF.2.add hrG.2⟩]
  calc
    _ ≤ (derivativeSup f (holderOrder t)+derivativeSup g (holderOrder t))+
        (holderSeminorm f t+holderSeminorm g t):=add_le_add hsup hsem
    _ = (derivativeSup f (holderOrder t)+holderSeminorm f t)+
        (derivativeSup g (holderOrder t)+holderSeminorm g t):=by ac_rfl
    _ ≤ ENNReal.ofReal Hf+ENNReal.ofReal Hg:=add_le_add hf hg
    _ = _ := (ENNReal.ofReal_add hHf hHg).symm

theorem coordinateDerivative_const_mul_finite {d : ℕ} (f : Covariate d→ℝ) (t c:ℝ)
    (hf : ContDiffOn ℝ (holderOrder t) f (cube d)) (q:ℕ) (hq:q ≤ holderOrder t)
    (σ:Fin q→Fin d) (x:Covariate d) (hx:x∈cube d) :
    coordinateDerivative (fun x=>c*f x) q σ x=c*coordinateDerivative f q σ x := by
  unfold coordinateDerivative
  change iteratedFDerivWithin ℝ q (c • f) (cube d) x _=_
  rw [iteratedFDerivWithin_const_smul_apply ((hf x hx).of_le (by exact_mod_cast hq))
    (uniqueDiffOn_cube d) hx]
  rfl

theorem holderBall_const_mul_contraction {d : ℕ} (f : Covariate d→ℝ) (t H c:ℝ)
    (hf:f∈holderBall t H) (hc:|c| ≤ 1) : (fun x=>c*f x)∈holderBall t H := by
  have hr:=holderBall_regular f t H hf
  have hcontract (v:ℝ):|c*v| ≤ |v|:=by
    rw [abs_mul];exact (mul_le_mul_of_nonneg_right hc (abs_nonneg v)).trans_eq (one_mul _)
  have hsup:derivativeSup (fun x=>c*f x) (holderOrder t) ≤ derivativeSup f (holderOrder t):=by
    apply iSup_le;intro q
    apply iSup_le;intro hq
    apply iSup_le;intro σ
    apply iSup_le;intro x
    apply iSup_le;intro hx
    have hp:ENNReal.ofReal |coordinateDerivative (fun x=>c*f x) q σ x| ≤
        ENNReal.ofReal |coordinateDerivative f q σ x|:=by
      apply ENNReal.ofReal_le_ofReal
      rw [coordinateDerivative_const_mul_finite f t c hr.2 q hq σ x hx]
      exact hcontract _
    exact hp.trans (le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le σ (le_iSup_of_le x (le_iSup_of_le hx le_rfl)))))
  have hsem:holderSeminorm (fun x=>c*f x) t ≤ holderSeminorm f t:=by
    apply iSup_le;intro σ
    apply iSup_le;intro x
    apply iSup_le;intro hx
    apply iSup_le;intro y
    apply iSup_le;intro hy
    apply iSup_le;intro hxy
    have hp:ENNReal.ofReal (|coordinateDerivative (fun x=>c*f x) (holderOrder t) σ x-
        coordinateDerivative (fun x=>c*f x) (holderOrder t) σ y|/‖x-y‖^holderExponent t) ≤
        ENNReal.ofReal (|coordinateDerivative f (holderOrder t) σ x-
        coordinateDerivative f (holderOrder t) σ y|/‖x-y‖^holderExponent t):=by
      apply ENNReal.ofReal_le_ofReal
      apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (norm_nonneg _) _)
      rw [coordinateDerivative_const_mul_finite f t c hr.2 _ le_rfl σ x hx,
        coordinateDerivative_const_mul_finite f t c hr.2 _ le_rfl σ y hy,← mul_sub]
      exact hcontract _
    exact hp.trans (le_iSup_of_le σ (le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy (le_iSup_of_le hxy le_rfl))))))
  change holderNorm _ t ≤ _
  change holderNorm f t ≤ _ at hf
  rw [holderNorm,ite_eq_left hr] at hf
  rw [holderNorm,ite_eq_left ⟨hr.1,contDiffOn_const.mul hr.2⟩]
  exact (add_le_add hsup hsem).trans hf

end RoughRegime.Model
