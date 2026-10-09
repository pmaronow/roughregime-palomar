module

public import RoughRegime.SourceFrame
public import RoughRegime.CanonicalKHolder
public import RoughRegime.Localization


@[expose] public section
/-! Direct smooth - germ localization on the literal canonical source frames.
All Hölder estimates come from the actual source oscillators, including the
full interval of lower exponents in Lemma16.  -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.Localization RoughRegime.Upper
set_option backward.isDefEq.respectTransparency false

inductive GermMode where
  | first
  | second
  | unrestricted

def GermMode.exponent (alpha beta : ℝ) : GermMode → ℝ
  | .first => alpha
  | .second => beta
  | .unrestricted => min alpha beta

def GermMode.axisCondition (G : SmoothGerm) : GermMode → Prop
  | .first => ∀ v : ℝ, (0,v) ∈ G.domain  →  G.K (0,v)=G.baseline
  | .second => ∀ u : ℝ, (u,0) ∈ G.domain  →  G.K (u,0)=G.baseline
  | .unrestricted => True

private def AbstractGermBound (D Q : ℕ) (gammaStar lambdaStar alpha0 alpha beta v0 lo hi : ℝ)
    (G : SmoothGerm) (mode : GermMode) (eta C : ℝ) : Prop :=
  ∀ N : ℕ, ∀ offset B p0 epsilonU epsilonV : ℝ,
    1 ≤ B  →  0 ≤ epsilonU  →  0 ≤ epsilonV  →  sourceBlockScale v0 B (D + 1) ≤ 1  → 
    ∀ J M : ℕ, ∀ m : ℝ, (2:ℝ)^((J:ℝ) * alpha0) ≤ m  →  m ≤ (2:ℝ)^((J:ℝ) * min alpha beta)  → 
    sourceAmplitude epsilonU B J (D + 1) alpha m + sourceAmplitude epsilonV B J (D + 1) beta m ≤ eta  → 
    ∀ z : GridPair D N → PairState (Fin J × Fin (D + 1)),
    ∀ h ∈ Icc ( - intervalHalfWidth lo hi) (intervalHalfWidth lo hi),
    ∀ σu σv : GridPair D N → ℝ, (∀ b, |σu b| ≤ 1)  →  (∀ b, |σv b| ≤ 1)  → 
    let u := canonicalSourceProfile canonicalStep D N Q J M gammaStar lambdaStar alpha0 m offset B v0 p0 lo hi h
      epsilonU alpha (innerBump (D + 1)) (outerBump (D + 1)) z σu
    let v := canonicalSourceProfile canonicalStep D N Q J M gammaStar lambdaStar alpha0 m offset B v0 p0 lo hi h
      epsilonV beta (innerBump (D + 1)) (outerBump (D + 1)) z σv
    ContDiff ℝ ∞ (fun x => G.K (u x,v x) - G.baseline) ∧
      Model.holderNorm (fun x => G.K (u x,v x) - G.baseline) (mode.exponent alpha beta) ≤ 
        ENNReal.ofReal (C * (epsilonU + epsilonV))

private theorem abstract_germ_bound (D Q K : ℕ)
    (gammaStar lambdaStar alpha0 alpha beta v0 lo hi : ℝ)
    (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4) (hlam : 0 < lambdaStar)
    (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1) (hK : 0 < K) (hKQ : K ≤ 2 * Q)
    (hab : alpha0 < min alpha beta)
    (hbudgetU : Model.holderOrder alpha + 2 ≤ K) (hbudgetV : Model.holderOrder beta + 2 ≤ K)
    (hv : 0 < v0) (hlo : 0 < lo) (hlt : lo < hi)
    (G : SmoothGerm) (mode : GermMode) (haxis : mode.axisCondition G) :
    ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧
      AbstractGermBound D Q gammaStar lambdaStar alpha0 alpha beta v0 lo hi G mode eta C := by
  have hinner (x : Model.Covariate (D + 1)) : innerBump (D + 1) x ∈ Icc (0:ℝ) 1 :=
    ⟨(innerBump (D + 1)).nonneg,(innerBump (D + 1)).le_one⟩
  cases mode with
  | first =>
    obtain ⟨eta,C,heta,hC,hbound⟩ := canonical_source_K_holder_first canonicalStep D Q K
      gammaStar lambdaStar alpha0 hγ hγ1 hlam ha0 ha1 hK hKQ lo hi hlo hlt
      (innerBump (D + 1)) (outerBump (D + 1)) (outerBump_one_on_inner (D + 1))
      (innerBump_zero_outside (D + 1)) (outerBump_zero_outside (D + 1))
      (innerBump_smooth (D + 1)) (innerBump_compact (D + 1)) hinner (innerBump_tsupport_subset (D + 1))
      alpha beta (hab.trans_le (min_le_left _ _)) hbudgetU v0 hv G.K G.baseline G.domain
      G.open_domain G.origin_mem G.smooth haxis
    refine ⟨eta,C,heta,hC,?_⟩
    intro N offset B p0 eU eV hB heU heV hell J M m hm0 hm1 hsmall z h hh σu σv hσu hσv
    have hmU : m ≤ (2:ℝ)^((J:ℝ) * alpha) := hm1.trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg J)))
    obtain ⟨hs,hb⟩ := hbound N offset B p0 eU eV (zero_lt_one.trans_le hB) heU heV hell J M m hm0 hmU hsmall z h hh σu σv hσu hσv
    exact ⟨hs,hb.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right heV) hC.le))⟩
  | second =>
    obtain ⟨eta,C,heta,hC,hbound⟩ := canonical_source_K_holder_second canonicalStep D Q K
      gammaStar lambdaStar alpha0 hγ hγ1 hlam ha0 ha1 hK hKQ lo hi hlo hlt
      (innerBump (D + 1)) (outerBump (D + 1)) (outerBump_one_on_inner (D + 1))
      (innerBump_zero_outside (D + 1)) (outerBump_zero_outside (D + 1))
      (innerBump_smooth (D + 1)) (innerBump_compact (D + 1)) hinner (innerBump_tsupport_subset (D + 1))
      alpha beta (hab.trans_le (min_le_right _ _)) hbudgetV v0 hv G.K G.baseline G.domain
      G.open_domain G.origin_mem G.smooth haxis
    refine ⟨eta,C,heta,hC,?_⟩
    intro N offset B p0 eU eV hB heU heV hell J M m hm0 hm1 hsmall z h hh σu σv hσu hσv
    have hmV : m ≤ (2:ℝ)^((J:ℝ) * beta) := hm1.trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (mul_le_mul_of_nonneg_left (min_le_right _ _) (Nat.cast_nonneg J)))
    obtain ⟨hs,hb⟩ := hbound N offset B p0 eU eV (zero_lt_one.trans_le hB) heU heV hell J M m hm0 hmV hsmall z h hh σu σv hσu hσv
    exact ⟨hs,hb.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left heU) hC.le))⟩
  | unrestricted =>
    have hbudget : Model.holderOrder (min alpha beta) + 2 ≤ K := by
      have horder : Model.holderOrder (min alpha beta) ≤ Model.holderOrder alpha :=
        Nat.sub_le_sub_right (Nat.ceil_mono (min_le_left _ _)) 1
      omega
    exact canonical_source_K_holder_min canonicalStep D Q K
      gammaStar lambdaStar alpha0 hγ hγ1 hlam ha0 ha1 hK hKQ lo hi hlo hlt
      (innerBump (D + 1)) (outerBump (D + 1)) (outerBump_one_on_inner (D + 1))
      (innerBump_zero_outside (D + 1)) (outerBump_zero_outside (D + 1))
      (innerBump_smooth (D + 1)) (innerBump_compact (D + 1)) hinner (innerBump_tsupport_subset (D + 1))
      alpha beta hab hbudget v0 hv G.K G.domain G.open_domain G.origin_mem G.smooth

/-- Literal source-frame realization of the smooth-map clause of Lemma16.
The same constant works for every 0 < t ≤ γK, and for every grid resolution,
lattice resolution and pair state.  -/
theorem source_germ_holder (D Q K : ℕ)
    (gammaStar lambdaStar alpha0 alpha beta v0 rminus rplus : ℝ)
    (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4) (hlam : 0 < lambdaStar)
    (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1) (hK : 0 < K) (hKQ : K ≤ 2 * Q)
    (hab : alpha0 < min alpha beta)
    (hbudgetU : Model.holderOrder alpha + 2 ≤ K) (hbudgetV : Model.holderOrder beta + 2 ≤ K)
    (hv : 0 < v0) (hv1 : v0 ≤ 1) (hrminus : 0 < rminus) (hlt : rminus < rplus)
    (hden : 0 < 1 - v0 * sourceOuterIntegral (D + 1))
    (G : SmoothGerm) (mode : GermMode) (haxis : mode.axisCondition G) :
    ∃ eta C : ℝ, 0 < eta ∧ 0 < C ∧
      ∀ (N J M : ℕ) (hN : 0 < N) (m epsilonU epsilonV delta : ℝ),
      ∀ (hm : 0 < m) (heU : 0 ≤ epsilonU) (heV : 0 ≤ epsilonV) (hd : 0 < delta)
        (hmargin : delta ≤ sourceMarginBound (D + 1) v0 rminus rplus),
      (2:ℝ)^((J:ℝ) * alpha0) ≤ m  →  m ≤ (2:ℝ)^((J:ℝ) * min alpha beta)  → 
      let F := sourceCanonicalFrame D N J Q M hN gammaStar lambdaStar alpha0 m epsilonU epsilonV
        alpha beta v0 rminus rplus delta hγ hγ1 hm heU heV hv hv1 hrminus hlt hd hmargin hden
      F.Au + F.Av ≤ eta  →  ∀ z : GridPair D N → PairState (Fin J × Fin (D + 1)),
        ContDiff ℝ ∞ (fun x => G.K ((F.field z).u x,(F.field z).v x) - G.baseline) ∧
          ∀ t : ℝ, 0 < t  →  t ≤ mode.exponent alpha beta  → 
            Model.holderNorm (fun x => G.K ((F.field z).u x,(F.field z).v x) - G.baseline) t ≤ 
              ENNReal.ofReal (C * (epsilonU + epsilonV)) := by
  obtain ⟨eta,C,heta,hC,hbound⟩ := abstract_germ_bound D Q K gammaStar lambdaStar alpha0 alpha beta
    v0 rminus rplus hγ hγ1 hlam ha0 ha1 hK hKQ hab hbudgetU hbudgetV hv hrminus hlt G mode haxis
  refine ⟨eta,((((D + 1 : ℕ):ℝ) + 1)*C),heta,by positivity,?_⟩
  intro N J M hN m epsilonU epsilonV delta hm heU heV hd hmargin hm0 hm1
  dsimp only
  let F := sourceCanonicalFrame D N J Q M hN gammaStar lambdaStar alpha0 m epsilonU epsilonV
    alpha beta v0 rminus rplus delta hγ hγ1 hm heU heV hv hv1 hrminus hlt hd hmargin hden
  intro hsmall z
  have hB : 1 ≤ sourceGridCount N (D + 1) := by
    unfold sourceGridCount
    exact_mod_cast (Nat.one_le_pow _ _ (show 0 < 2 * N by omega))
  have hh : (rplus - rminus)/2 - delta ∈ Icc ( - intervalHalfWidth rminus rplus) (intervalHalfWidth rminus rplus) := by
    have he := hmargin.trans (min_le_left _ _)
    unfold intervalHalfWidth
    constructor  <;> linarith
  obtain ⟨hs,hb⟩ := hbound N (sourceGridOffset v0 (D + 1)) (sourceGridCount N (D + 1))
    (sourceFixedBaseline (D + 1) v0 rminus rplus) epsilonU epsilonV hB heU heV
    (sourceBlockScale_grid_le_one v0 N (D + 1) hv hv1 hN) J M m hm0 hm1 hsmall z _ hh
    (stateSignU z) (stateSignV z) (fun b => (stateSignU_abs z b).le) (fun b => (stateSignV_abs z b).le)
  have hs' : ContDiff ℝ ∞ (fun x => G.K ((F.field z).u x,(F.field z).v x) - G.baseline) := by
    simpa only [F,sourceCanonicalFrame,CanonicalFrame.field,CanonicalFrame.u,CanonicalFrame.v,
      canonicalSourceProfile,intervalCenter,add_comm rplus rminus] using hs
  have hb' : Model.holderNorm (fun x => G.K ((F.field z).u x,(F.field z).v x) - G.baseline)
      (mode.exponent alpha beta) ≤ ENNReal.ofReal (C * (epsilonU + epsilonV)) := by
    simpa only [F,sourceCanonicalFrame,CanonicalFrame.field,CanonicalFrame.u,CanonicalFrame.v,
      canonicalSourceProfile,intervalCenter,add_comm rplus rminus] using hb
  refine ⟨hs',?_⟩
  intro t ht htgamma
  have he := Model.holderBall_lower_exponent _ hs' t (mode.exponent alpha beta) (C * (epsilonU + epsilonV))
    ht htgamma (by positivity) hb'
  change Model.holderNorm (fun x => G.K ((F.field z).u x,(F.field z).v x)-G.baseline) t≤_ at he ⊢
  simpa only [mul_assoc] using he

/-- Uniform true sup and weighted localization on canonical frames. The
threshold and constant depend only on the germ and the fixed lower density
endpoint, and work simultaneously for every dimension, grid and state. -/
theorem canonical_germ_sup_control (G : SmoothGerm) (lo : ℝ) (hlo : 0<lo) :
    ∃ eta C : ℝ, 0<eta ∧ 0<C ∧
      ∀ (D N : ℕ) (ι : Type*) [Fintype ι] (F : CanonicalFrame D N ι), F.rminus=lo →
      F.Au+F.Av≤eta → ∀ z : GridPair D N→PairState ι,
        (∀ x, |G.K ((F.field z).u x,(F.field z).v x)-G.baseline|≤C*(F.Au+F.Av)) ∧
        (0<G.baseline → F.rplus*(C*(F.Au+F.Av))≤G.baseline*F.delta →
          ∀ x, F.rminus*G.baseline≤(F.field z).p x*G.K ((F.field z).u x,(F.field z).v x) ∧
            (F.field z).p x*G.K ((F.field z).u x,(F.field z).v x)≤F.rplus*G.baseline) := by
  obtain ⟨r,C,hr,hC,hlocal⟩ := G.local_sup_bound
  refine ⟨r*lo,C/lo,mul_pos hr hlo,div_pos hC hlo,?_⟩
  intro D N ι _ F hFlo hsmall z
  have hprofile (x : Model.Covariate (D+1)) : |(F.field z).u x|+|(F.field z).v x|≤(F.Au+F.Av)/lo := by
    have hu := (F.realization z).u_bound x
    have hv := (F.realization z).v_bound x
    rw [hFlo] at hu hv
    change |F.u z x|+|F.v z x|≤_
    simpa only [add_div] using add_le_add hu hv
  have hrad : (F.Au+F.Av)/lo≤r := (div_le_iff₀ hlo).mpr (by nlinarith)
  have hsup (x : Model.Covariate (D+1)) :
      |G.K ((F.field z).u x,(F.field z).v x)-G.baseline|≤(C/lo)*(F.Au+F.Av) := by
    have hsum := (hprofile x).trans hrad
    have hu : |(F.field z).u x|≤r := by nlinarith [abs_nonneg ((F.field z).v x)]
    have hv : |(F.field z).v x|≤r := by nlinarith [abs_nonneg ((F.field z).u x)]
    have he := (hlocal ((F.field z).u x,(F.field z).v x) hu hv).trans
      (mul_le_mul_of_nonneg_left (hprofile x) hC.le)
    convert he using 1; ring
  refine ⟨hsup,?_⟩
  intro hbase hmargin
  exact weighted_membership (F.field z).p
    (fun x => G.K ((F.field z).u x,(F.field z).v x)) G.baseline ((C/lo)*(F.Au+F.Av)) F.delta
    F.rminus F.rplus (F.rminus*G.baseline) (F.rplus*G.baseline) hbase
    (mul_nonneg (div_pos hC hlo).le (add_nonneg F.Au_nonneg F.Av_nonneg)) F.rminus_pos.le F.delta_pos.le
    (F.realization z).margins hsup hmargin le_rfl le_rfl

end RoughRegime.LatticePriors
