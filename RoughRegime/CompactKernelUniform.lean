module

public import RoughRegime.KernelNeighborhoodLocal
public import RoughRegime.KernelUniform
public import RoughRegime.CompactDensityParameters


@[expose] public section
/-! Compact density-endpoint uniformity of the genuine rational kernel.
Every endpoint pair retains its own Chebyshev coefficient and convergence
ratio; one complex tube, disk and coefficient bound work for the whole set. -/
noncomputable section
open Set Metric Filter
open scoped Topology Matrix.Norms.L2Operator
namespace RoughRegime.ComplexKernel
open RoughRegime.Upper RoughRegime.Model RoughRegime.AnalyticCoefficients

lemma densityIntervalDomain_isOpen : IsOpen densityIntervalDomain :=
  (isOpen_lt continuous_const continuous_fst).inter (isOpen_lt continuous_fst continuous_snd)

lemma intervalRho_continuousOn : ContinuousOn (fun I : ℝ×ℝ => intervalRho I.1 I.2)
    densityIntervalDomain := by
  intro I hI
  unfold intervalRho
  exact (((continuous_snd.sqrt.sub continuous_fst.sqrt).continuousAt).div
    ((continuous_snd.sqrt.add continuous_fst.sqrt).continuousAt)
    (ne_of_gt (add_pos (Real.sqrt_pos.mpr (hI.1.trans hI.2))
      (Real.sqrt_pos.mpr hI.1)))).continuousWithinAt

lemma normalizedArgument_eq_smul {n : Type*} [Fintype n] [DecidableEq n]
    (lo hi : ℝ) (M : Matrix n n ℂ) : normalizedArgument lo hi M=
    (intervalHalfWidth lo hi)⁻¹ • (M-intervalCenter lo hi • (1:Matrix n n ℂ)) := by
  simp [normalizedArgument,argumentPolynomial,Algebra.smul_def]

lemma normalizedArgument_continuousOn {E : Type*} [TopologicalSpace E]
    {n : Type*} [Fintype n] [DecidableEq n] (M : E→Matrix n n ℂ) (hM : Continuous M) :
    ContinuousOn (fun p : (ℝ×ℝ)×E => normalizedArgument p.1.1 p.1.2 (M p.2))
      (densityIntervalDomain×ˢuniv) := by
  intro p hp
  apply ContinuousAt.continuousWithinAt
  have hc : ContinuousAt (fun q : (ℝ×ℝ)×E => intervalCenter q.1.1 q.1.2) p := by
    unfold intervalCenter
    fun_prop
  have hd : ContinuousAt (fun q : (ℝ×ℝ)×E => intervalHalfWidth q.1.1 q.1.2) p := by
    unfold intervalHalfWidth
    fun_prop
  have hd0 : intervalHalfWidth p.1.1 p.1.2 ≠ 0 := by
    unfold intervalHalfWidth
    exact (div_pos (sub_pos.mpr hp.1.2) (by norm_num)).ne'
  simp_rw [normalizedArgument_eq_smul]
  exact (hd.inv₀ hd0).smul ((hM.continuousAt.comp continuousAt_snd).sub
    (hc.smul continuousAt_const))

lemma compact_intervalRho_bound (G : Set (ℝ×ℝ)) (hG : IsCompact G)
    (hGood : G⊆densityIntervalDomain) :
    ∃ q : ℝ, 0 < q ∧ q < 1 ∧ ∀ I∈G, intervalRho I.1 I.2 ≤ q := by
  rcases G.eq_empty_or_nonempty with h0|hN
  · exact ⟨1/2,by norm_num,by norm_num,by simp [h0]⟩
  · obtain ⟨I0,hI0,hmax⟩ := hG.exists_isMaxOn hN (intervalRho_continuousOn.mono hGood)
    let q := max (intervalRho I0.1 I0.2) (1/2)
    refine ⟨q,(by dsimp [q]; positivity),?_,?_⟩
    · exact max_lt (intervalRho_lt_one _ _ (hGood hI0).1 (hGood hI0).2) (by norm_num)
    · intro I hI
      exact (hmax hI).trans (le_max_left _ _)

/-- The true matrix coefficients have one geometric bound for all endpoint
pairs in a compact subset of 0<lo<hi, without widening any spectral interval. -/
theorem compact_uniform_kernel_coefficients_normalized
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {n : ℕ} [Nonempty (Fin n)] (G : Set (ℝ×ℝ)) (hG : IsCompact G)
    (hGood : G⊆densityIntervalDomain) (S : Set E) (hS : IsCompact S)
    (M : E→Matrix (Fin n) (Fin n) ℂ) (hM : Continuous M)
    (hHerm : ∀ I∈G, ∀ t∈S, (normalizedArgument I.1 I.2 (M t)).IsHermitian)
    (hNorm : ∀ I∈G, ∀ t∈S, ‖normalizedArgument I.1 I.2 (M t)‖ ≤ 1) :
    ∃ ε B q : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ B ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ I∈G, ∀ t, (∃ t0∈S, ‖t-t0‖ < ε) → ∀ k,
        ‖kernelCoefficient I.1 I.2 (M t) k‖ ≤ B*q^k := by
  obtain ⟨rhoMax,hrhoMax,hrhoMax1,hmax⟩ := compact_intervalRho_bound G hG hGood
  let r := (1+rhoMax⁻¹)/2
  have hr1 : 1 < r := by
    have hh : 1 < rhoMax⁻¹ := (one_lt_inv₀ hrhoMax).mpr hrhoMax1
    dsimp [r]
    linarith
  have hr : 0 < r := zero_lt_one.trans hr1
  have hmr : rhoMax*r < 1 := by
    dsimp [r]
    have hh := mul_inv_cancel₀ hrhoMax.ne'
    nlinarith
  let O : Set ((ℝ×ℝ)×E) := densityIntervalDomain×ˢuniv
  let Q : ℂ×((ℝ×ℝ)×E)→Matrix (Fin n) (Fin n) ℂ :=
    fun p => denominator p.2.1.1 p.2.1.2 (M p.2.2) p.1
  have hO : IsOpen O := densityIntervalDomain_isOpen.prod isOpen_univ
  have hQ : ContinuousOn Q (univ×ˢO) := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    have hρ0 : ContinuousAt (fun I : ℝ×ℝ => intervalRho I.1 I.2) p.2.1 :=
      (intervalRho_continuousOn p.2.1 hp.2.1).continuousAt
        (densityIntervalDomain_isOpen.mem_nhds hp.2.1)
    have hρ : ContinuousAt (fun w : ℂ×((ℝ×ℝ)×E) => intervalRho w.2.1.1 w.2.1.2) p :=
      hρ0.comp (f := fun w : ℂ×((ℝ×ℝ)×E) => w.2.1) (by fun_prop)
    have hA : ContinuousAt (fun w : ℂ×((ℝ×ℝ)×E) =>
        normalizedArgument w.2.1.1 w.2.1.2 (M w.2.2)) p :=
      ((normalizedArgument_continuousOn M hM).continuousAt (hO.mem_nhds hp.2)).comp continuousAt_snd
    unfold Q denominator
    exact (continuousAt_const.add
      (((continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp hρ)).mul
        continuousAt_fst).smul hA)).add
      ((((Complex.continuous_ofReal.continuousAt.comp hρ).pow 2).mul
        (continuousAt_fst.pow 2)).smul continuousAt_const)
  obtain ⟨ε,B0,hε,hε1,hB0,hbound⟩ := KernelNeighborhood.uniform_inverse_tube_on
    O hO (G×ˢS) (hG.prod hS) (fun p hp => ⟨hGood hp.1,mem_univ _⟩) r Q hQ (by
      intro z hz p hp
      change IsUnit (normalizedDenominator (intervalRho p.1.1 p.1.2)
        (normalizedArgument p.1.1 p.1.2 (M p.2)) z)
      apply normalizedDenominator_isUnit _ (intervalRho_pos _ _ (hGood hp.1).1 (hGood hp.1).2)
        _ (hHerm _ hp.1 _ hp.2) (hNorm _ hp.1 _ hp.2)
      have hzn : ‖z‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hz
      exact (mul_le_mul_of_nonneg_left hzn (intervalRho_pos _ _ (hGood hp.1).1 (hGood hp.1).2).le).trans_lt
        ((mul_le_mul_of_nonneg_right (hmax _ hp.1) hr.le).trans_lt hmr))
  let B := (1+rhoMax^2*r^2)*B0
  refine ⟨ε,B,r⁻¹,hε,hε1,by positivity,inv_nonneg.mpr hr.le,(inv_lt_one₀ hr).mpr hr1,?_⟩
  intro I hI t ht k
  have hnear : ∃ p0∈G×ˢS, ‖(I,t)-p0‖ < ε := by
    obtain ⟨t0,ht0,hd⟩ := ht
    refine ⟨(I,t0),⟨hI,ht0⟩,?_⟩
    simpa [Prod.norm_def] using hd
  have hb := hbound (I,t) hnear
  apply coefficient_norm_le (rationalKernel I.1 I.2 (M t)) (kernelCoefficient I.1 I.2 (M t))
    (rationalKernel_hasFPowerSeriesAt I.1 I.2 (M t)) r B hr
    (rationalKernel_differentiableOn _ _ _ _ (fun z hz => (hb z hz).1))
    (fun z hz => ?_) k
  apply (rationalKernel_norm_le I.1 I.2 (M t) r B0 hr.le hB0 z
    (sphere_subset_closedBall hz) (hb z (sphere_subset_closedBall hz)).2).trans
  have hρ0 := (intervalRho_pos _ _ (hGood hI).1 (hGood hI).2).le
  dsimp [B]
  gcongr
  exact hmax I hI

/-- Joint compact centers permit the spectral population set to vary with
the density interval, as it does for the actual packed Gram moments. -/
theorem compact_joint_kernel_coefficients_normalized
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {n : ℕ} [Nonempty (Fin n)] (V : Set ((ℝ×ℝ)×E)) (hV : IsCompact V)
    (hGood : ∀ p∈V, p.1∈densityIntervalDomain)
    (M : E→Matrix (Fin n) (Fin n) ℂ) (hM : Continuous M)
    (hHerm : ∀ p∈V, (normalizedArgument p.1.1 p.1.2 (M p.2)).IsHermitian)
    (hNorm : ∀ p∈V, ‖normalizedArgument p.1.1 p.1.2 (M p.2)‖ ≤ 1) :
    ∃ ε B q : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ B ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ (I : ℝ×ℝ) t, (∃ t0, (I,t0)∈V ∧ ‖t-t0‖ < ε) → ∀ k,
        ‖kernelCoefficient I.1 I.2 (M t) k‖ ≤ B*q^k := by
  let G := Prod.fst '' V
  have hG : IsCompact G := hV.image continuous_fst
  have hGoodG : G⊆densityIntervalDomain := by
    rintro I ⟨p,hp,rfl⟩
    exact hGood p hp
  obtain ⟨rhoMax,hrhoMax,hrhoMax1,hmax⟩ := compact_intervalRho_bound G hG hGoodG
  let r := (1+rhoMax⁻¹)/2
  have hr1 : 1 < r := by
    have hh : 1 < rhoMax⁻¹ := (one_lt_inv₀ hrhoMax).mpr hrhoMax1
    dsimp [r]
    linarith
  have hr : 0 < r := zero_lt_one.trans hr1
  have hmr : rhoMax*r < 1 := by
    dsimp [r]
    have hh := mul_inv_cancel₀ hrhoMax.ne'
    nlinarith
  let O : Set ((ℝ×ℝ)×E) := densityIntervalDomain×ˢuniv
  let Q : ℂ×((ℝ×ℝ)×E)→Matrix (Fin n) (Fin n) ℂ :=
    fun p => denominator p.2.1.1 p.2.1.2 (M p.2.2) p.1
  have hO : IsOpen O := densityIntervalDomain_isOpen.prod isOpen_univ
  have hQ : ContinuousOn Q (univ×ˢO) := by
    intro p hp
    apply ContinuousAt.continuousWithinAt
    have hρ0 : ContinuousAt (fun I : ℝ×ℝ => intervalRho I.1 I.2) p.2.1 :=
      (intervalRho_continuousOn p.2.1 hp.2.1).continuousAt
        (densityIntervalDomain_isOpen.mem_nhds hp.2.1)
    have hρ : ContinuousAt (fun w : ℂ×((ℝ×ℝ)×E) => intervalRho w.2.1.1 w.2.1.2) p :=
      hρ0.comp (f := fun w : ℂ×((ℝ×ℝ)×E) => w.2.1) (by fun_prop)
    have hA : ContinuousAt (fun w : ℂ×((ℝ×ℝ)×E) =>
        normalizedArgument w.2.1.1 w.2.1.2 (M w.2.2)) p :=
      ((normalizedArgument_continuousOn M hM).continuousAt (hO.mem_nhds hp.2)).comp continuousAt_snd
    unfold Q denominator
    exact (continuousAt_const.add
      (((continuousAt_const.mul (Complex.continuous_ofReal.continuousAt.comp hρ)).mul
        continuousAt_fst).smul hA)).add
      ((((Complex.continuous_ofReal.continuousAt.comp hρ).pow 2).mul
        (continuousAt_fst.pow 2)).smul continuousAt_const)
  obtain ⟨ε,B0,hε,hε1,hB0,hbound⟩ := KernelNeighborhood.uniform_inverse_tube_on
    O hO V hV (fun p hp => ⟨hGood p hp,mem_univ _⟩) r Q hQ (by
      intro z hz p hp
      change IsUnit (normalizedDenominator (intervalRho p.1.1 p.1.2)
        (normalizedArgument p.1.1 p.1.2 (M p.2)) z)
      apply normalizedDenominator_isUnit _ (intervalRho_pos _ _ (hGood p hp).1 (hGood p hp).2)
        _ (hHerm p hp) (hNorm p hp)
      have hzn : ‖z‖ ≤ r := by simpa only [mem_closedBall,dist_zero_right] using hz
      exact (mul_le_mul_of_nonneg_left hzn (intervalRho_pos _ _ (hGood p hp).1 (hGood p hp).2).le).trans_lt
        ((mul_le_mul_of_nonneg_right (hmax p.1 ⟨p,hp,rfl⟩) hr.le).trans_lt hmr))
  let B := (1+rhoMax^2*r^2)*B0
  refine ⟨ε,B,r⁻¹,hε,hε1,by positivity,inv_nonneg.mpr hr.le,(inv_lt_one₀ hr).mpr hr1,?_⟩
  intro I t ht k
  obtain ⟨t0,ht0,hd⟩ := ht
  have hI : I∈G := ⟨(I,t0),ht0,rfl⟩
  have hnear : ∃ p0∈V, ‖(I,t)-p0‖ < ε := by
    refine ⟨(I,t0),ht0,?_⟩
    simpa [Prod.norm_def] using hd
  have hb := hbound (I,t) hnear
  apply coefficient_norm_le (rationalKernel I.1 I.2 (M t)) (kernelCoefficient I.1 I.2 (M t))
    (rationalKernel_hasFPowerSeriesAt I.1 I.2 (M t)) r B hr
    (rationalKernel_differentiableOn _ _ _ _ (fun z hz => (hb z hz).1))
    (fun z hz => ?_) k
  apply (rationalKernel_norm_le I.1 I.2 (M t) r B0 hr.le hB0 z
    (sphere_subset_closedBall hz) (hb z (sphere_subset_closedBall hz)).2).trans
  have hρ0 := (intervalRho_pos _ _ (hGoodG hI).1 (hGoodG hI).2).le
  dsimp [B]
  gcongr
  exact hmax I hI

/-- Bounded joint population sets may be nonclosed. Their endpoint coordinates
remain in the supplied compact set, and the normalized Hermitian unit-ball
conditions extend to the actual closure by local continuity. -/
theorem compact_bounded_joint_kernel_coefficients
    {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {n : ℕ} [Nonempty (Fin n)] (G : Set (ℝ×ℝ)) (hG : IsCompact G)
    (hGood : G⊆densityIntervalDomain) (V : Set ((ℝ×ℝ)×E)) (hV : Bornology.IsBounded V)
    (hVG : ∀ p∈V, p.1∈G) (M : E→Matrix (Fin n) (Fin n) ℂ) (hM : Continuous M)
    (hHerm : ∀ p∈V, (M p.2).IsHermitian)
    (hSpec : ∀ p∈V, spectrum ℝ (M p.2)⊆Icc p.1.1 p.1.2) :
    ∃ ε B q : ℝ, 0 < ε ∧ ε ≤ 1 ∧ 0 ≤ B ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ (I : ℝ×ℝ) t, (∃ t0, (I,t0)∈V ∧ ‖t-t0‖ < ε) → ∀ k,
        ‖kernelCoefficient I.1 I.2 (M t) k‖ ≤ B*q^k := by
  let N := fun p : (ℝ×ℝ)×E => normalizedArgument p.1.1 p.1.2 (M p.2)
  let T : Set (Matrix (Fin n) (Fin n) ℂ) := {A | star A=A}∩{A | ‖A‖≤1}
  have hT : IsClosed T := (isClosed_eq continuous_star continuous_id).inter
    (isClosed_le continuous_norm continuous_const)
  have hVT : N '' V⊆T := by
    rintro A ⟨p,hp,rfl⟩
    have hg := hGood (hVG p hp)
    exact ⟨isSelfAdjoint_iff.mp (Matrix.isHermitian_iff_isSelfAdjoint.mp
        (normalizedArgument_hermitian _ _ _ (hHerm p hp))),
      normalizedArgument_norm_le_one _ _ hg.1 hg.2 _ (hHerm p hp) (hSpec p hp)⟩
  have hcloseG : closure V⊆Prod.fst ⁻¹' G :=
    closure_minimal (fun p hp => hVG p hp) (hG.isClosed.preimage continuous_fst)
  have hcloseT (p : (ℝ×ℝ)×E) (hp : p∈closure V) : N p∈T := by
    have hg := hGood (hcloseG hp)
    have hn : ContinuousAt N p :=
      ((normalizedArgument_continuousOn M hM) p ⟨hg,mem_univ _⟩).continuousAt
        ((densityIntervalDomain_isOpen.prod isOpen_univ).mem_nhds ⟨hg,mem_univ _⟩)
    exact closure_minimal hVT hT (mem_closure_image hn hp)
  obtain ⟨ε,B,q,hε,hε1,hB,hq,hq1,hbound⟩ :=
    compact_joint_kernel_coefficients_normalized (closure V) hV.isCompact_closure
      (fun p hp => hGood (hcloseG hp)) M hM
      (fun p hp => Matrix.isHermitian_iff_isSelfAdjoint.mpr (isSelfAdjoint_iff.mpr (hcloseT p hp).1))
      (fun p hp => (hcloseT p hp).2)
  refine ⟨ε,B,q,hε,hε1,hB,hq,hq1,?_⟩
  intro I t ht k
  obtain ⟨t0,ht0,hnear⟩ := ht
  exact hbound I t ⟨t0,subset_closure ht0,hnear⟩ k

end RoughRegime.ComplexKernel
