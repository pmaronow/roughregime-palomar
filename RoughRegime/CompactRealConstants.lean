module

public import RoughRegime.CompactKernelUniform
public import RoughRegime.ProjectionIncrementError
public import RoughRegime.DesignCells


@[expose] public section
/-! Uniform real approximation constants over compact density intervals.
Only the constants are majorized; every approximant retains its own rho^m. -/
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RoughRegime.Model
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

lemma compact_density_endpoint_bounds (G:Set (ℝ×ℝ)) (hG:IsCompact G)
    (hGood:G⊆densityIntervalDomain):
    ∃ lo hi:ℝ,0<lo ∧ 0<hi ∧ ∀ I∈G,lo ≤ I.1 ∧ I.2 ≤ hi := by
  rcases G.eq_empty_or_nonempty with he|hne
  · exact ⟨1,1,zero_lt_one,zero_lt_one,by simp [he]⟩
  · obtain ⟨Il,hIl,hmin⟩:=hG.exists_isMinOn hne continuous_fst.continuousOn
    obtain ⟨Ih,hIh,hmax⟩:=hG.exists_isMaxOn hne continuous_snd.continuousOn
    exact ⟨Il.1,Ih.2,(hGood hIl).1,(hGood hIh).1.trans (hGood hIh).2,
      fun I hI=>⟨hmin hI,hmax hI⟩⟩

universe u
/-- The actual weighted dyadic Taylor error has one constant for the whole
compact family, chosen before all laws, response spaces, levels and cells. -/
theorem compact_uniform_model_cell_approximation (A:Parameters)
    (G:Set (ℝ×ℝ)) (hG:IsCompact G) (hGood:G⊆densityIntervalDomain) (t:ℝ):
    ∃ C:ℝ,0<C ∧ ∀ (I:ℝ×ℝ) (hI:I∈G) (Z:Type u) [MeasurableSpace Z]
      (F:Observables Z (densityParameters A I (hGood hI)))
      (P:ProbabilityMeasure (Observation (densityParameters A I (hGood hI)) Z))
      (W:ModelWitness (densityParameters A I (hGood hI)) F P)
      (j:ℕ) (c:DyadicCell A.d j) (f:Covariate A.d→ℝ)
      (hf:Measurable f) (hh:f∈holderBall t A.H),
      let q:=holderTaylorPolynomial f (holderOrder t) (dyadicOrigin c)
      ∃ hq:MemLp (polynomialEvaluation q) 2 (W.cellDesignMeasure c),
        q.totalDegree ≤ holderOrder t ∧
        ‖(W.holder_memLp_cell c f hf t hh).toLp f-hq.toLp (polynomialEvaluation q)‖ ≤
          C*((2:ℝ)^(-(j:ℝ)/A.d))^t := by
  obtain ⟨lo,hi,hlo,hhi,hbounds⟩:=compact_density_endpoint_bounds G hG hGood
  obtain ⟨C,hC,herror⟩:=dyadic_holder_polynomial_error
    (lt_of_lt_of_le Nat.zero_lt_one A.hd) t A.H A.hH.le
  refine ⟨Real.sqrt hi*C,mul_pos (Real.sqrt_pos.mpr hhi) hC,?_⟩
  intro I hI Z _ F P W j c f hf hh
  dsimp only
  have :=rectangleVolume_probability (dyadicOrigin c) (dyadicSides c) (dyadicSides_pos c)
  have :=W.cellDesignMeasure_finite c
  let q:=holderTaylorPolynomial f (holderOrder t) (dyadicOrigin c)
  let E:ℝ:=C*((2:ℝ)^(-(j:ℝ)/A.d))^t
  have hE:0 ≤ E:=by unfold E;positivity
  have he:∀ᵐ x ∂rectangleVolume (dyadicOrigin c) (dyadicSides c),
      |f x-polynomialEvaluation q x| ≤ E:=by
    filter_upwards [ae_rectangleVolume_mem (dyadicOrigin c) (dyadicSides c)] with x hx
    exact herror j c f hh x (by rwa [dyadicRectangle_eq_rectangle])
  have hq:MemLp (polynomialEvaluation q) 2 (W.cellDesignMeasure c):=by
    apply MemLp.of_bound (polynomialEvaluation_continuous q).aestronglyMeasurable (A.H+E)
    filter_upwards [(W.cellDesignMeasure_ac c).ae_le he,W.cellDesign_ae_rectangle c] with x hx hr
    rw [Real.norm_eq_abs]
    have hval:=holderNorm_bounds_values f t A.H A.hH.le hh x (dyadicRectangle_subset_cube c hr)
    calc
      _ ≤ |f x|+|f x-polynomialEvaluation q x|:=by
        calc
          _ = |f x+(polynomialEvaluation q x-f x)|:=by congr 1;ring
          _ ≤ |f x|+|polynomialEvaluation q x-f x|:=by
            simpa only [Real.norm_eq_abs] using norm_add_le (f x) (polynomialEvaluation q x-f x)
          _ = _:=by rw [abs_sub_comm]
      _ ≤ _:=add_le_add hval hx
  refine ⟨hq,holderTaylorPolynomial_degree _ _ _,?_⟩
  have hd:∀ᵐ x ∂rectangleVolume (dyadicOrigin c) (dyadicSides c),W.designDensity x ≤ hi:=
    (W.dyadic_density_bounds c).mono fun x hx=>hx.2.trans (hbounds I hI).2
  have hn:=weightedLp_approximation (rectangleVolume (dyadicOrigin c) (dyadicSides c))
    W.designDensity hi hhi.le hd f (polynomialEvaluation q) E hE he
    (W.holder_memLp_cell c f hf t hh) hq
  exact hn.trans_eq (by dsimp only [E];ring)

end RoughRegime.Model
namespace RoughRegime.ProjectionIncrementComplex
open RoughRegime.Model RoughRegime.Upper
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

lemma summable_shifted_power_geometric (n:ℕ) (q:ℝ) (hq:0<q) (hq1:q<1):
    Summable (fun k:ℕ=>((k+1:ℕ):ℝ)^n*q^k):=by
  have hs:=summable_pow_mul_geometric_of_norm_lt_one n
    (show ‖q‖<1 by simpa only [Real.norm_eq_abs,abs_of_pos hq] using hq1)
  have ht:=((summable_nat_add_iff 1).mpr hs).div_const q
  convert ht using 1
  funext k
  simp only [Nat.cast_add,Nat.cast_one,pow_succ]
  field_simp

/-- One error prefactor for all compact endpoints, without replacing the
individual geometric decay rho(I)^m in the actual source error. -/
theorem compact_incrementErrorConstant_bound (G:Set (ℝ×ℝ)) (hG:IsCompact G)
    (hGood:G⊆densityIntervalDomain) (a b:ℕ) (Ha Hb:ℝ) (hHa:0 ≤ Ha) (hHb:0 ≤ Hb):
    ∃ K:ℝ,0 ≤ K ∧ ∀ I∈G,incrementErrorConstant I.1 I.2 a b Ha Hb ≤ K:=by
  obtain ⟨lo,hi,hlo,hhi,hbounds⟩:=compact_density_endpoint_bounds G hG hGood
  obtain ⟨q,hq,hq1,hqbound⟩:=ComplexKernel.compact_intervalRho_bound G hG hGood
  let T:ℝ:=∑' k:ℕ,((k+1:ℕ):ℝ)^(a+b)*q^k
  have hT:0 ≤ T:=tsum_nonneg fun k=>by positivity
  let L:ℝ:=2^(a+b+1)*(lo^(a+b+1))⁻¹*T
  let K:ℝ:=4*hi^(a+b+1)*Ha*Hb*L
  have hL:0 ≤ L:=by dsimp [L];positivity
  refine ⟨K,by dsimp [K];positivity,?_⟩
  intro I hI
  have hIo:0<I.1:=(hGood hI).1
  have hIlt:I.1<I.2:=(hGood hI).2
  have hIhi:0<I.2:=hIo.trans hIlt
  have hgeo:lo ≤ intervalGeometricMean I.1 I.2:=by
    have hp:lo*lo ≤ I.1*I.2:=mul_le_mul (hbounds I hI).1
      ((hbounds I hI).1.trans hIlt.le) hlo.le hIo.le
    have hs:=Real.sqrt_le_sqrt hp
    simpa only [intervalGeometricMean,Real.sqrt_mul_self hlo.le] using hs
  have hρ:0 < intervalRho I.1 I.2:=intervalRho_pos _ _ hIo hIlt
  have hterm (k:ℕ):((k+1:ℕ):ℝ)^(a+b)*intervalRho I.1 I.2^k ≤
      ((k+1:ℕ):ℝ)^(a+b)*q^k:=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hρ.le (hqbound I hI) k) (by positivity)
  have hsQ:=summable_shifted_power_geometric (a+b) q hq hq1
  have hsρ:Summable (fun k:ℕ=>((k+1:ℕ):ℝ)^(a+b)*intervalRho I.1 I.2^k):=
    Summable.of_nonneg_of_le (fun k=>by positivity) hterm hsQ
  have hseries:(∑' k:ℕ,((k+1:ℕ):ℝ)^(a+b)*intervalRho I.1 I.2^k) ≤ T:=
    hsρ.tsum_le_tsum hterm hsQ
  have hinv:(intervalGeometricMean I.1 I.2^(a+b+1))⁻¹ ≤ (lo^(a+b+1))⁻¹:=by
    simpa only [one_div] using one_div_le_one_div_of_le (pow_pos hlo _)
      (pow_le_pow_left₀ hlo.le hgeo (a+b+1))
  have hTail:incrementTailConstant I.1 I.2 a b ≤ L:=by
    unfold incrementTailConstant L
    exact mul_le_mul (mul_le_mul_of_nonneg_left hinv (by positivity)) hseries
      (tsum_nonneg fun k=>by positivity) (by positivity)
  unfold incrementErrorConstant K
  have hTail0:=incrementTailConstant_nonneg I.1 I.2 hIo hIlt a b
  gcongr
  exact (hbounds I hI).2

end RoughRegime.ProjectionIncrementComplex
