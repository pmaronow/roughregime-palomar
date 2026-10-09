module

public import RoughRegime.GlobalKComposition
public import RoughRegime.CanonicalHolder


@[expose] public section
open Set
open scoped ContDiff
noncomputable section
namespace RoughRegime.LatticePriors
open RoughRegime.Upper

/-- The literal level-first canonical profile, with the exact block-volume
and amplitude powers from the paper. -/
abbrev canonicalSourceProfile (U : SmoothStep) (D N Q J M : ℕ)
    (gammaStar lambdaStar alpha0 m offset B v0 p0 lo hi h epsilon t : ℝ)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (z : GridPair D N → PairState (Fin J × Fin (D+1))) (σ : GridPair D N → ℝ) :=
  globalProfile offset (sourceBlockScale v0 B (D+1)) p0 (intervalCenter lo hi) h
    (sourceAmplitude epsilon B J (D+1) t m) inner outer (stateAngles z)
    (statePhases U M (fun i => J-i.1.val) Prod.snd (fun i => sourceGamma gammaStar i.1.val) z) σ
    (stateGates Q M (fun i => sourceEta gammaStar lambdaStar alpha0 m i.1.val)
      (fun i => sourceLambda lambdaStar i.1.val) z)

/-- The complete canonical first-axis constant smooth-map estimate of
Lemma14(b). The constants are uniform in all grid and lattice resolutions,
and the only smallness condition is the paper's actual sum of amplitudes. -/
theorem canonical_source_K_holder_first (U : SmoothStep) (D Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
    (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
    (hK : 0 < K) (hKQ : K ≤ 2*Q)
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (hiota : ∀ y, inner y ≠ 0 → outer y = 1)
    (hin : ∀ y, y ∉ unitCubeOpen (D+1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D+1) → outer y = 0)
    (hsmooth : ContDiff ℝ ∞ inner) (hcompact : HasCompactSupport inner)
    (hin01 : ∀ y, inner y ∈ Icc (0 : ℝ) 1) (hsupport : tsupport inner ⊆ unitCubeOpen (D+1))
    (t s : ℝ) (ht : alpha0 < t) (hbudget : Model.holderOrder t+2 ≤ K)
    (v0 : ℝ) (hv : 0 < v0) (map : ℝ × ℝ → ℝ) (k0 : ℝ) (V : Set (ℝ × ℝ))
    (hV : IsOpen V) (hV0 : (0 : ℝ × ℝ) ∈ V) (hmap : ContDiffOn ℝ ∞ map V)
    (hconstant : ∀ v : ℝ, (0,v) ∈ V → map (0,v) = k0) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ N : ℕ, ∀ offset B p0 epsilonU epsilonV : ℝ,
      0 < B → 0 ≤ epsilonU → 0 ≤ epsilonV → sourceBlockScale v0 B (D+1) ≤ 1 →
      ∀ J M : ℕ, ∀ m : ℝ, (2 : ℝ)^((J : ℝ)*alpha0) ≤ m → m ≤ (2 : ℝ)^((J : ℝ)*t) →
      sourceAmplitude epsilonU B J (D+1) t m + sourceAmplitude epsilonV B J (D+1) s m ≤ ε →
      ∀ z : GridPair D N → PairState (Fin J × Fin (D+1)),
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ σu σv : GridPair D N → ℝ, (∀ b, |σu b| ≤ 1) → (∀ b, |σv b| ≤ 1) →
      let u := canonicalSourceProfile U D N Q J M gammaStar lambdaStar alpha0 m offset B v0 p0 lo hi h epsilonU t inner outer z σu
      let v := canonicalSourceProfile U D N Q J M gammaStar lambdaStar alpha0 m offset B v0 p0 lo hi h epsilonV s inner outer z σv
      ContDiff ℝ ∞ (fun x => map (u x,v x)-k0) ∧
        Model.holderNorm (fun x => map (u x,v x)-k0) t ≤ ENNReal.ofReal (C*epsilonU) := by
  obtain ⟨ε,C,hε,_,hC,hbound⟩ := source_global_K_holder_first U D Q K
    gammaStar lambdaStar alpha0 hγ hγ1 hlam ha0 ha1 hK hKQ lo hi hlo hlt
    inner outer hiota hin hout hsmooth hcompact hin01 hsupport t ht hbudget map k0 V hV hV0 hmap hconstant
  refine ⟨ε,2*C*v0^(-(t/(D+1:ℕ))),hε,by positivity,?_⟩
  intro N offset B p0 epsilonU epsilonV hB heU heV hell1 J M m hm hm1 hsmall z h hh σu σv hσu hσv
  dsimp only
  simp only [canonicalSourceProfile,statePhases_eq_source,stateGates_eq_source]
  have hell := sourceBlockScale_pos hv hB (D+1)
  have hm0 : 0 < m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hm
  have hAu : 0 ≤ sourceAmplitude epsilonU B J (D+1) t m := by
    unfold sourceAmplitude sourceSpatialVolume; positivity
  have hAv : 0 ≤ sourceAmplitude epsilonV B J (D+1) s m := by
    unfold sourceAmplitude sourceSpatialVolume; positivity
  have hAu1 : |sourceAmplitude epsilonU B J (D+1) t m| ≤ ε := by rw [abs_of_nonneg hAu]; linarith
  have hAv1 : |sourceAmplitude epsilonV B J (D+1) s m| ≤ ε := by rw [abs_of_nonneg hAv]; linarith
  obtain ⟨hs,hb⟩ := hbound N offset (sourceBlockScale v0 B (D+1)) p0
    (sourceAmplitude epsilonU B J (D+1) t m) (sourceAmplitude epsilonV B J (D+1) s m)
    hell hell1 hAu1 hAv1 J M m hm (fun b => sourceDigitsTranspose (z b).1) h hh
    (stateAngles z) σu σv hσu hσv
  refine ⟨hs,hb.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have he := mul_le_mul_of_nonneg_left
    (sourceAmplitude_scale_le epsilonU B v0 J (D+1) t m heU hB hv (Nat.succ_pos _) hm0 hm1) hC.le
  convert he using 1 <;> ring



/-- The complete canonical second-axis constant smooth-map estimate of
Lemma14(b), allowing the two source amplitudes to have different exponents. -/
theorem canonical_source_K_holder_second (U : SmoothStep) (D Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
    (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
    (hK : 0 < K) (hKQ : K ≤ 2*Q)
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (hiota : ∀ y, inner y ≠ 0 → outer y = 1)
    (hin : ∀ y, y ∉ unitCubeOpen (D+1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D+1) → outer y = 0)
    (hsmooth : ContDiff ℝ ∞ inner) (hcompact : HasCompactSupport inner)
    (hin01 : ∀ y, inner y ∈ Icc (0 : ℝ) 1) (hsupport : tsupport inner ⊆ unitCubeOpen (D+1))
    (t s : ℝ) (hs : alpha0 < s) (hbudget : Model.holderOrder s+2 ≤ K)
    (v0 : ℝ) (hv : 0 < v0) (map : ℝ × ℝ → ℝ) (k0 : ℝ) (V : Set (ℝ × ℝ))
    (hV : IsOpen V) (hV0 : (0 : ℝ × ℝ) ∈ V) (hmap : ContDiffOn ℝ ∞ map V)
    (hconstant : ∀ u : ℝ, (u,0) ∈ V → map (u,0) = k0) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ N : ℕ, ∀ offset B p0 epsilonU epsilonV : ℝ,
      0 < B → 0 ≤ epsilonU → 0 ≤ epsilonV → sourceBlockScale v0 B (D+1) ≤ 1 →
      ∀ J M : ℕ, ∀ m : ℝ, (2 : ℝ)^((J : ℝ)*alpha0) ≤ m → m ≤ (2 : ℝ)^((J : ℝ)*s) →
      sourceAmplitude epsilonU B J (D+1) t m + sourceAmplitude epsilonV B J (D+1) s m ≤ ε →
      ∀ z : GridPair D N → PairState (Fin J × Fin (D+1)),
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ σu σv : GridPair D N → ℝ, (∀ b, |σu b| ≤ 1) → (∀ b, |σv b| ≤ 1) →
      let u := canonicalSourceProfile U D N Q J M gammaStar lambdaStar alpha0 m offset B v0 p0 lo hi h epsilonU t inner outer z σu
      let v := canonicalSourceProfile U D N Q J M gammaStar lambdaStar alpha0 m offset B v0 p0 lo hi h epsilonV s inner outer z σv
      ContDiff ℝ ∞ (fun x => map (u x,v x)-k0) ∧
        Model.holderNorm (fun x => map (u x,v x)-k0) s ≤ ENNReal.ofReal (C*epsilonV) := by
  let W : Set (ℝ × ℝ) := Prod.swap ⁻¹' V
  have hW : IsOpen W := hV.preimage continuous_swap
  have hW0 : (0 : ℝ × ℝ) ∈ W := hV0
  have hswap : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => map (p.2,p.1)) W :=
    hmap.comp (contDiffOn_snd.prodMk contDiffOn_fst) (fun _ hp => hp)
  obtain ⟨ε,C,hε,hC,hbound⟩ := canonical_source_K_holder_first U D Q K
    gammaStar lambdaStar alpha0 hγ hγ1 hlam ha0 ha1 hK hKQ lo hi hlo hlt
    inner outer hiota hin hout hsmooth hcompact hin01 hsupport s t hs hbudget v0 hv
    (fun p : ℝ × ℝ => map (p.2,p.1)) k0 W hW hW0 hswap (fun u hu => hconstant u hu)
  refine ⟨ε,C,hε,hC,?_⟩
  intro N offset B p0 epsilonU epsilonV hB heU heV hell1 J M m hm hm1 hsmall z h hh σu σv hσu hσv
  exact hbound N offset B p0 epsilonV epsilonU hB heV heU hell1 J M m hm hm1
    (by linarith) z h hh σv σu hσv hσu



/-- Increasing the source smoothness exponent decreases its actual amplitude
whenever the grid count is at least one. -/
lemma sourceAmplitude_mono_smoothness (epsilon B : ℝ) (J d : ℕ) (t s m : ℝ)
    (he : 0 ≤ epsilon) (hB : 1 ≤ B) (hd : 0 < d) (hm : 0 ≤ m) (hts : t ≤ s) :
    sourceAmplitude epsilon B J d s m ≤ sourceAmplitude epsilon B J d t m := by
  have hR : 1 ≤ sourceSpatialVolume J d := by
    unfold sourceSpatialVolume
    exact one_le_pow₀ (by norm_num)
  have hbase : 1 ≤ B*sourceSpatialVolume J d := by nlinarith
  have hexp : -(s/(d : ℝ)) ≤ -(t/(d : ℝ)) := by
    apply neg_le_neg
    exact div_le_div_of_nonneg_right hts (Nat.cast_pos.mpr hd).le
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase hexp) he) hm

lemma sourceAmplitude_scale_le_of_smoothness_le (epsilon B v0 : ℝ) (J d : ℕ) (t s m : ℝ)
    (he : 0 ≤ epsilon) (hB : 1 ≤ B) (hv : 0 < v0) (hd : 0 < d) (hm : 0 < m)
    (hbudget : m ≤ (2 : ℝ)^((J : ℝ)*t)) (hts : t ≤ s) :
    |sourceAmplitude epsilon B J d s m| * (sourceBlockScale v0 B d)⁻¹ ^ t *
      (1+(2 : ℝ)^((J : ℝ)*t)/m) ≤ 2*v0^(-(t/(d : ℝ)))*epsilon := by
  have hBs : 0 < B := zero_lt_one.trans_le hB
  have hA : 0 ≤ sourceAmplitude epsilon B J d s m := by
    unfold sourceAmplitude sourceSpatialVolume; positivity
  have hAt : 0 ≤ sourceAmplitude epsilon B J d t m := by
    unfold sourceAmplitude sourceSpatialVolume; positivity
  have hab : |sourceAmplitude epsilon B J d s m| ≤ |sourceAmplitude epsilon B J d t m| := by
    rw [abs_of_nonneg hA,abs_of_nonneg hAt]
    exact sourceAmplitude_mono_smoothness epsilon B J d t s m he hB hd hm.le hts
  have hscale := sourceBlockScale_pos hv hBs d
  exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab (by positivity))
    (by positivity)).trans (sourceAmplitude_scale_le epsilon B v0 J d t m he hBs hv hd hm hbudget)

/-- The unrestricted local map on the literal canonical profiles has the
minimum-smoothness Hölder estimate. The source amplitudes may have different
exponents; their true powers are compared and cancelled in the proof. -/
theorem canonical_source_K_holder_general (U : SmoothStep) (D Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
    (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
    (hK : 0 < K) (hKQ : K ≤ 2*Q)
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (hiota : ∀ y, inner y ≠ 0 → outer y = 1)
    (hin : ∀ y, y ∉ unitCubeOpen (D+1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D+1) → outer y = 0)
    (hsmooth : ContDiff ℝ ∞ inner) (hcompact : HasCompactSupport inner)
    (hin01 : ∀ y, inner y ∈ Icc (0 : ℝ) 1) (hsupport : tsupport inner ⊆ unitCubeOpen (D+1))
    (t s gamma : ℝ) (ht : alpha0 < gamma) (hgt : gamma ≤ t) (hgs : gamma ≤ s)
    (hbudget : Model.holderOrder gamma+2 ≤ K)
    (v0 : ℝ) (hv : 0 < v0) (map : ℝ × ℝ → ℝ) (V : Set (ℝ × ℝ))
    (hV : IsOpen V) (hV0 : (0 : ℝ × ℝ) ∈ V) (hmap : ContDiffOn ℝ ∞ map V) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ N : ℕ, ∀ offset B p0 epsilonU epsilonV : ℝ,
      1 ≤ B → 0 ≤ epsilonU → 0 ≤ epsilonV → sourceBlockScale v0 B (D+1) ≤ 1 →
      ∀ J M : ℕ, ∀ m : ℝ, (2 : ℝ)^((J : ℝ)*alpha0) ≤ m → m ≤ (2 : ℝ)^((J : ℝ)*gamma) →
      sourceAmplitude epsilonU B J (D+1) t m + sourceAmplitude epsilonV B J (D+1) s m ≤ ε →
      ∀ z : GridPair D N → PairState (Fin J × Fin (D+1)),
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ σu σv : GridPair D N → ℝ, (∀ b, |σu b| ≤ 1) → (∀ b, |σv b| ≤ 1) →
      let u := canonicalSourceProfile U D N Q J M gammaStar lambdaStar alpha0 m offset B v0 p0 lo hi h epsilonU t inner outer z σu
      let v := canonicalSourceProfile U D N Q J M gammaStar lambdaStar alpha0 m offset B v0 p0 lo hi h epsilonV s inner outer z σv
      ContDiff ℝ ∞ (fun x => map (u x,v x)-map (0,0)) ∧
        Model.holderNorm (fun x => map (u x,v x)-map (0,0)) gamma ≤ ENNReal.ofReal (C*(epsilonU+epsilonV)) := by
  obtain ⟨ε,C,hε,_,hC,hbound⟩ := source_global_K_holder_general U D Q K
    gammaStar lambdaStar alpha0 hγ hγ1 hlam ha0 ha1 hK hKQ lo hi hlo hlt
    inner outer hiota hin hout hsmooth hcompact hin01 hsupport gamma ht hbudget map V hV hV0 hmap
  refine ⟨ε,2*C*v0^(-(gamma/(D+1:ℕ))),hε,by positivity,?_⟩
  intro N offset B p0 epsilonU epsilonV hB heU heV hell1 J M m hm hm1 hsmall z h hh σu σv hσu hσv
  dsimp only
  simp only [canonicalSourceProfile,statePhases_eq_source,stateGates_eq_source]
  have hBs : 0 < B := zero_lt_one.trans_le hB
  have hell := sourceBlockScale_pos hv hBs (D+1)
  have hm0 : 0 < m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hm
  have hAu : 0 ≤ sourceAmplitude epsilonU B J (D+1) t m := by
    unfold sourceAmplitude sourceSpatialVolume; positivity
  have hAv : 0 ≤ sourceAmplitude epsilonV B J (D+1) s m := by
    unfold sourceAmplitude sourceSpatialVolume; positivity
  have hAu1 : |sourceAmplitude epsilonU B J (D+1) t m| ≤ ε := by rw [abs_of_nonneg hAu]; linarith
  have hAv1 : |sourceAmplitude epsilonV B J (D+1) s m| ≤ ε := by rw [abs_of_nonneg hAv]; linarith
  obtain ⟨hs,hb⟩ := hbound N offset (sourceBlockScale v0 B (D+1)) p0
    (sourceAmplitude epsilonU B J (D+1) t m) (sourceAmplitude epsilonV B J (D+1) s m)
    hell hell1 hAu1 hAv1 J M m hm (fun b => sourceDigitsTranspose (z b).1) h hh
    (stateAngles z) σu σv hσu hσv
  refine ⟨hs,hb.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have heU' := sourceAmplitude_scale_le_of_smoothness_le epsilonU B v0 J (D+1) gamma t m
    heU hB hv (Nat.succ_pos _) hm0 hm1 hgt
  have heV' := sourceAmplitude_scale_le_of_smoothness_le epsilonV B v0 J (D+1) gamma s m
    heV hB hv (Nat.succ_pos _) hm0 hm1 hgs
  have he := mul_le_mul_of_nonneg_left (add_le_add heU' heV') hC.le
  nlinarith



/-- The literal minimum of the two source smoothness exponents. -/
theorem canonical_source_K_holder_min (U : SmoothStep) (D Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
    (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
    (hK : 0 < K) (hKQ : K ≤ 2*Q)
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (hiota : ∀ y, inner y ≠ 0 → outer y = 1)
    (hin : ∀ y, y ∉ unitCubeOpen (D+1) → inner y = 0)
    (hout : ∀ y, y ∉ unitCubeOpen (D+1) → outer y = 0)
    (hsmooth : ContDiff ℝ ∞ inner) (hcompact : HasCompactSupport inner)
    (hin01 : ∀ y, inner y ∈ Icc (0 : ℝ) 1) (hsupport : tsupport inner ⊆ unitCubeOpen (D+1))
    (t s : ℝ) (ht : alpha0 < min t s)
    (hbudget : Model.holderOrder (min t s)+2 ≤ K)
    (v0 : ℝ) (hv : 0 < v0) (map : ℝ × ℝ → ℝ) (V : Set (ℝ × ℝ))
    (hV : IsOpen V) (hV0 : (0 : ℝ × ℝ) ∈ V) (hmap : ContDiffOn ℝ ∞ map V) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ N : ℕ, ∀ offset B p0 epsilonU epsilonV : ℝ,
      1 ≤ B → 0 ≤ epsilonU → 0 ≤ epsilonV → sourceBlockScale v0 B (D+1) ≤ 1 →
      ∀ J M : ℕ, ∀ m : ℝ, (2 : ℝ)^((J : ℝ)*alpha0) ≤ m → m ≤ (2 : ℝ)^((J : ℝ)*min t s) →
      sourceAmplitude epsilonU B J (D+1) t m + sourceAmplitude epsilonV B J (D+1) s m ≤ ε →
      ∀ z : GridPair D N → PairState (Fin J × Fin (D+1)),
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
      ∀ σu σv : GridPair D N → ℝ, (∀ b, |σu b| ≤ 1) → (∀ b, |σv b| ≤ 1) →
      let u := canonicalSourceProfile U D N Q J M gammaStar lambdaStar alpha0 m offset B v0 p0 lo hi h epsilonU t inner outer z σu
      let v := canonicalSourceProfile U D N Q J M gammaStar lambdaStar alpha0 m offset B v0 p0 lo hi h epsilonV s inner outer z σv
      ContDiff ℝ ∞ (fun x => map (u x,v x)-map (0,0)) ∧
        Model.holderNorm (fun x => map (u x,v x)-map (0,0)) (min t s) ≤ ENNReal.ofReal (C*(epsilonU+epsilonV)) :=
  canonical_source_K_holder_general U D Q K gammaStar lambdaStar alpha0 hγ hγ1 hlam
    ha0 ha1 hK hKQ lo hi hlo hlt inner outer hiota hin hout hsmooth hcompact hin01 hsupport
    t s (min t s) ht (min_le_left _ _) (min_le_right _ _) hbudget v0 hv map V hV hV0 hmap

end RoughRegime.LatticePriors
