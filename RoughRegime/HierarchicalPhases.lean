module

public import RoughRegime.PhaseDerivatives
public import RoughRegime.HierarchicalDerivativeSums


@[expose] public section
/-! The actual source phase truncations, and their last-level uniform jet
bounds. All coefficients come from the genuine bounded-product lattice gate. -/
noncomputable section
open scoped BigOperators ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.LatticeFourier

 def sourceLevels (d J b : ℕ) : Finset (Fin d × Fin J) :=
   Finset.univ.filter (fun i => b ≤ i.2.val)

 def sourcePartialPhase (U : SmoothStep) (d J M : ℕ) (gammaStar : ℝ)
     (z : Fin d × Fin J → ℤ) (b : ℕ) : Model.Covariate d → ℝ :=
   partialBlockPhase (sourceLevels d J b) U M (fun i => J-i.2.val) Prod.fst
     (fun i => sourceGamma gammaStar i.2.val) z

 def sourceGate (d J Q M : ℕ) (gammaStar lambdaStar alpha0 m : ℝ)
     (z : Fin d × Fin J → ℤ) : ℝ :=
   blockGate Q M (fun i => sourceLambda lambdaStar i.2.val)
     (fun i => sourceEta gammaStar lambdaStar alpha0 m i.2.val) z

 theorem source_scale_product (gammaStar lambdaStar alpha0 m : ℝ) (b : ℕ)
     (hlam : 0 < lambdaStar) :
     sourceLambda lambdaStar b * sourceEta gammaStar lambdaStar alpha0 m b =
       sourceWeight gammaStar alpha0 m b := by
   have hl : sourceLambda lambdaStar b ≠ 0 := by unfold sourceLambda; positivity
   unfold sourceEta sourceWeight
   field_simp

 theorem source_rate_eq (J b : ℕ) (gammaStar : ℝ) (hb : b ≤ J) :
     (2:ℝ)^(J-b)/sourceGamma gammaStar b = sourceRate J gammaStar b := by
   unfold sourceRate
   rw [← Real.rpow_natCast, Nat.cast_sub hb]

 theorem sourcePartialPhase_smooth (U : SmoothStep) (d J M : ℕ) (gammaStar : ℝ)
     (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
     (z : Fin d × Fin J → ℤ) (b : ℕ) :
     ContDiff ℝ ∞ (sourcePartialPhase U d J M gammaStar z b) := by
   unfold sourcePartialPhase partialBlockPhase
   apply ContDiff.sum
   intro i hi
   exact contDiff_const.mul (coordinateSoftDigit_smooth U _ _ _
     (by unfold sourceGamma; positivity) (sourceGamma_le_quarter gammaStar _ hγ hγ1))

 theorem sourcePartialPhase_at_depth (U : SmoothStep) (d J M : ℕ) (gammaStar : ℝ)
     (z : Fin d × Fin J → ℤ) : sourcePartialPhase U d J M gammaStar z J = 0 := by
   have he : sourceLevels d J J = ∅ := by
     ext i
     have hi := i.2.isLt
     simp [sourceLevels]
   funext x
   simp [sourcePartialPhase,partialBlockPhase,he]

 theorem sourceLevels_cost_sum (d J b : ℕ) (f : ℕ → ℝ) :
     (∑ i ∈ sourceLevels d J b, f i.2.val) = (d:ℝ)*∑ k ∈ Finset.Ico b J, f k := by
   classical
   rw [sourceLevels,Finset.sum_filter,← Finset.univ_product_univ,Finset.sum_product]
   simp only
   have he : (∑ i : Fin J, if b ≤ i.val then f i.val else 0) = ∑ k ∈ Finset.Ico b J, f k := by
     rw [Fin.sum_univ_eq_sum_range (fun k => if b ≤ k then f k else 0) J,← Finset.sum_filter]
     congr 1
     ext i
     simp
     omega
   simp only [he, Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

 /-- Every positive-order true partial-phase derivative is controlled by the
last source level, with a constant independent of J,M,m and the realization. -/
 theorem sourcePartialPhase_derivative_bound (U : SmoothStep) (d Q K : ℕ)
     (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
     (hlam : 0 < lambdaStar) (ha : alpha0 < 1) (hK : 0 < K) (hKQ : K ≤ 2*Q)
     (k : ℕ) (hk : 0 < k) :
     ∃ C : ℝ, 0 ≤ C ∧ ∀ J M b c : ℕ, b ≤ c → ∀ m : ℝ, 0 < m →
       ∀ z : Fin d × Fin J → ℤ, ∀ x : Model.Covariate d,
       gateRoot (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) K *
         ‖iteratedFDeriv ℝ k (sourcePartialPhase U d J M gammaStar z c) x‖ ≤
       C * (sourceWeight gammaStar alpha0 m b * sourceRate J gammaStar b^k) := by
   obtain ⟨C,hC,hphase⟩ := gateRoot_phase_derivative_bound U k
   obtain ⟨D,hD,htail⟩ := source_derivative_tail_bound gammaStar alpha0 hγ ha k hk
   refine ⟨C*(d:ℝ)*D,mul_nonneg (mul_nonneg hC.le (Nat.cast_nonneg d)) hD,?_⟩
   intro J M b c hbc m hm z x
   have hg (i : Fin d × Fin J) : 0 < sourceGamma gammaStar i.2.val := by unfold sourceGamma; positivity
   have hs (i : Fin d × Fin J) : 0 < sourceLambda lambdaStar i.2.val * sourceEta gammaStar lambdaStar alpha0 m i.2.val := by
     rw [source_scale_product gammaStar lambdaStar alpha0 m _ hlam]
     unfold sourceWeight sourceGamma
     positivity
   have hb := hphase (sourceLevels d J c) Q M K (fun i => J-i.2.val) Prod.fst
     (fun i => sourceGamma gammaStar i.2.val) (fun i => sourceLambda lambdaStar i.2.val)
     (fun i => sourceEta gammaStar lambdaStar alpha0 m i.2.val) z hK hKQ hg
     (fun i => sourceGamma_le_quarter gammaStar _ hγ hγ1) hs x
   have he : (∑ i ∈ sourceLevels d J c,
       (sourceLambda lambdaStar i.2.val * sourceEta gammaStar lambdaStar alpha0 m i.2.val) *
       ((2:ℝ)^(J-i.2.val)/sourceGamma gammaStar i.2.val)^k) =
       (d:ℝ)*∑ v ∈ Finset.Ico c J,
         sourceWeight gammaStar alpha0 m v*sourceRate J gammaStar v^k := by
     simp_rw [source_scale_product gammaStar lambdaStar alpha0 m _ hlam]
     rw [← sourceLevels_cost_sum d J c (fun v => sourceWeight gammaStar alpha0 m v*sourceRate J gammaStar v^k)]
     apply Finset.sum_congr rfl
     intro i hi
     rw [source_rate_eq J i.2.val gammaStar (Nat.le_of_lt i.2.isLt)]
   rw [he] at hb
   have hsum : (∑ v ∈ Finset.Ico c J, sourceWeight gammaStar alpha0 m v*sourceRate J gammaStar v^k) ≤
       ∑ v ∈ Finset.Ico b J, sourceWeight gammaStar alpha0 m v*sourceRate J gammaStar v^k := by
     apply Finset.sum_le_sum_of_subset_of_nonneg
     · intro v hv
       simp only [Finset.mem_Ico] at hv ⊢
       exact ⟨hbc.trans hv.1,hv.2⟩
     · intro v _ _
       unfold sourceWeight sourceRate sourceGamma
       positivity
   have hb' := hb.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg d)) hC.le)
   rw [Finset.sum_Ico_eq_sum_range] at hb'
   have hh := mul_le_mul_of_nonneg_left (htail J b (J-b) m hm) (mul_nonneg hC.le (Nat.cast_nonneg d))
   exact hb'.trans (by convert hh using 1 <;> ring)

/-- The difference of neighboring truncations is the actual single-level phase. -/
theorem sourcePartialPhase_increment_eq (U : SmoothStep) (d J M : ℕ) (gammaStar : ℝ)
    (z : Fin d × Fin J → ℤ) (b : ℕ) :
    sourcePartialPhase U d J M gammaStar z b - sourcePartialPhase U d J M gammaStar z (b+1) =
      partialBlockPhase (Finset.univ.filter (fun i : Fin d × Fin J => i.2.val = b)) U M
        (fun i => J-i.2.val) Prod.fst (fun i => sourceGamma gammaStar i.2.val) z := by
  funext x
  simp only [sourcePartialPhase,partialBlockPhase,sourceLevels,Finset.sum_filter,Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h₁ : b ≤ i.2.val <;> by_cases h₂ : b+1 ≤ i.2.val <;> by_cases h₃ : i.2.val = b <;>
    simp [h₁,h₂,h₃] <;> omega

/-- Every true single-level increment jet, including order zero, has the exact
weighted last-level scale with no dependence on J,M,m or the realization. -/
theorem sourcePartialPhase_increment_derivative_bound (U : SmoothStep) (d Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
    (hlam : 0 < lambdaStar) (hK : 0 < K) (hKQ : K ≤ 2*Q) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J M b : ℕ, b < J → ∀ m : ℝ, 0 < m →
      ∀ z : Fin d × Fin J → ℤ, ∀ x : Model.Covariate d,
      gateRoot (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) K *
        ‖iteratedFDeriv ℝ k (sourcePartialPhase U d J M gammaStar z b) x -
          iteratedFDeriv ℝ k (sourcePartialPhase U d J M gammaStar z (b+1)) x‖ ≤
      C * sourceWeight gammaStar alpha0 m b * sourceRate J gammaStar b^k := by
  obtain ⟨C,hC,hphase⟩ := gateRoot_phase_derivative_bound U k
  refine ⟨C*(d:ℝ),mul_nonneg hC.le (Nat.cast_nonneg d),?_⟩
  intro J M b hb m hm z x
  have hsmooth (v : ℕ) := sourcePartialPhase_smooth U d J M gammaStar hγ hγ1 z v
  rw [← iteratedFDeriv_sub_apply ((hsmooth b).contDiffAt.of_le (by simp))
    ((hsmooth (b+1)).contDiffAt.of_le (by simp)),sourcePartialPhase_increment_eq]
  have hscale (i : Fin d × Fin J) :
      0 < sourceLambda lambdaStar i.2.val*sourceEta gammaStar lambdaStar alpha0 m i.2.val := by
    rw [source_scale_product gammaStar lambdaStar alpha0 m _ hlam]
    unfold sourceWeight sourceGamma
    positivity
  have ht := hphase (Finset.univ.filter (fun i : Fin d × Fin J => i.2.val = b)) Q M K
    (fun i => J-i.2.val) Prod.fst (fun i => sourceGamma gammaStar i.2.val)
    (fun i => sourceLambda lambdaStar i.2.val) (fun i => sourceEta gammaStar lambdaStar alpha0 m i.2.val)
    z hK hKQ (fun i => by unfold sourceGamma; positivity)
    (fun i => sourceGamma_le_quarter gammaStar _ hγ hγ1) hscale x
  have he : (∑ i ∈ Finset.univ.filter (fun i : Fin d × Fin J => i.2.val = b),
      (sourceLambda lambdaStar i.2.val*sourceEta gammaStar lambdaStar alpha0 m i.2.val)*
      ((2:ℝ)^(J-i.2.val)/sourceGamma gammaStar i.2.val)^k) =
      (d:ℝ)*(sourceWeight gammaStar alpha0 m b*sourceRate J gammaStar b^k) := by
    simp_rw [source_scale_product gammaStar lambdaStar alpha0 m _ hlam]
    have hr (i : Fin d × Fin J) := source_rate_eq J i.2.val gammaStar (Nat.le_of_lt i.2.isLt)
    simp_rw [hr]
    rw [Finset.sum_filter,← Finset.univ_product_univ,Finset.sum_product]
    have hi : (∑ i : Fin J, if i.val = b then sourceWeight gammaStar alpha0 m i.val*sourceRate J gammaStar i.val^k else 0) =
        sourceWeight gammaStar alpha0 m b*sourceRate J gammaStar b^k := by
      rw [Finset.sum_eq_single (⟨b,hb⟩ : Fin J)]
      · simp
      · intro i _ hne
        have hv : i.val ≠ b := by intro he; exact hne (Fin.ext he)
        simp [hv]
      · simp
    simp only [hi,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [he] at ht
  exact ht.trans_eq (by ring)

end RoughRegime.LatticePriors
