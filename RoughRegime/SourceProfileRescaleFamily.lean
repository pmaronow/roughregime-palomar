module

public import RoughRegime.SourceProfileRescale
public import RoughRegime.SourceProfileHolderFamily


@[expose] public section
noncomputable section
open Set
open scoped ContDiff
namespace RoughRegime.LatticePriors
open RoughRegime.Calculus RoughRegime.Upper
variable {R : Type*} [NormedAddCommGroup R] [NormedSpace ℝ R]

 theorem source_profile_increment_holder_bound_rescale_family (U : SmoothStep) (d Q K : ℕ)
     (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
     (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
     (hK : 0 < K) (hKQ : K ≤ 2*Q)
     (κ : R → ℝ → ℝ) (KP : Set R) (hKP : IsCompact KP)
    (hκ : ContDiff ℝ ∞ (Function.uncurry κ)) (hκ0 : ∀ p, κ p 0 = 0)
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
     (cut : Model.Covariate d → ℝ) (hcut : ContDiff ℝ ∞ cut) (hcompact : HasCompactSupport cut)
     (hcut01 : ∀ x, cut x ∈ Icc (0:ℝ) 1) (t : ℝ) (ht : 0<t)
     (hbudget : Model.holderOrder t+2 ≤ K) :
     ∃ C : ℝ, 0<C ∧ ∀ p ∈ KP, ∀ ell : ℝ, 0<ell → ell≤1 → ∀ origin : Model.Covariate d, ∀ J M b : ℕ, b<J → ∀ m : ℝ,
       (2:ℝ)^((J:ℝ)*alpha0) ≤ m → ∀ z : Fin d × Fin J → ℤ,
       ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi), ∀ θ : ℝ,
       Model.holderNorm
         ((oscillatorProfile (κ p) (intervalCenter lo hi) (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) h θ cut
             (sourcePartialPhase U d J M gammaStar z b) -
          oscillatorProfile (κ p) (intervalCenter lo hi) (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) h θ cut
             (sourcePartialPhase U d J M gammaStar z (b+1))) ∘ scaleCoords origin ell) t ≤
       ENNReal.ofReal (C*sourceWeight gammaStar alpha0 m b*(sourceRate J gammaStar b/ell)^t) := by
   let n := Model.holderOrder t+1
   have hn : n+1 ≤ K := by dsimp [n]; omega
   have he (i : Fin (n+1)) := source_profile_increment_jet_bound_global_family U d Q K gammaStar lambdaStar alpha0
     hγ hγ1 hlam ha0 ha1 hK hKQ κ KP hKP hκ hκ0 lo hi hlo hlt cut hcut hcompact hcut01 i.val (by omega : i.val+1 ≤ K)
   choose C hC hb using he
   let B : ℝ := ∑ i : Fin (n+1), C i
   have hB : 0<B := by
     have hzero := hC (⟨0,by omega⟩ : Fin (n+1))
     have hs := Finset.single_le_sum (fun i _ => (hC i).le) (Finset.mem_univ (⟨0,by omega⟩ : Fin (n+1)))
     dsimp [B]
     linarith
   refine ⟨3*B,by positivity,?_⟩
   intro p hpParam ell hell hell1 origin J M b hbJ m hm z h hh θ
   let SG := sourceGate d J Q M gammaStar lambdaStar alpha0 m z
   let w := sourceWeight gammaStar alpha0 m b
   let L := sourceRate J gammaStar b
   let f₁ := oscillatorProfile (κ p) (intervalCenter lo hi) SG h θ cut (sourcePartialPhase U d J M gammaStar z b)
   let f₂ := oscillatorProfile (κ p) (intervalCenter lo hi) SG h θ cut (sourcePartialPhase U d J M gammaStar z (b+1))
   have hSG : SG ∈ Icc (0:ℝ) 1 := blockGate_range Q M _ _ z
   have hf₁ : ContDiff ℝ ∞ f₁ := oscillatorProfile_smooth (κ p) lo hi hlo hlt univ isOpen_univ
      (familyScalar_contDiff κ hκ p).contDiffOn (subset_univ _) SG h θ hSG hh cut _ hcut
     (sourcePartialPhase_smooth U d J M gammaStar hγ hγ1 z b) hcut01
   have hf₂ : ContDiff ℝ ∞ f₂ := oscillatorProfile_smooth (κ p) lo hi hlo hlt univ isOpen_univ
      (familyScalar_contDiff κ hκ p).contDiffOn (subset_univ _) SG h θ hSG hh cut _ hcut
     (sourcePartialPhase_smooth U d J M gammaStar hγ hγ1 z (b+1)) hcut01
   have hm0 : 0 < m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hm
   have hw : 0≤w := by dsimp [w,sourceWeight,sourceGamma]; positivity
   have hL : 1≤L := sourceRate_ge_one J b gammaStar hγ (by linarith) (Nat.le_of_lt hbJ)
   have hLscale : 1≤L/ell := (le_div_iff₀ hell).mpr (by simpa only [one_mul] using hell1.trans hL)
   have hjets (k : ℕ) (hk : k≤Model.holderOrder t+1) (x : Model.Covariate d) (_hx : x∈Model.cube d) :
       ‖iteratedFDeriv ℝ k ((f₁-f₂) ∘ scaleCoords origin ell) x‖ ≤ (B*w)*(L/ell)^k := by
     let i : Fin (n+1) := ⟨k,by dsimp [n]; omega⟩
     have hCi : C i≤B := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
     have hi := hb i p hpParam J M b hbJ m hm z h hh θ (scaleCoords origin ell x)
     have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCi hw)
       (pow_nonneg (zero_lt_one.trans_le hL).le k)
     have hpull := norm_iteratedFDeriv_rescale (f₁-f₂) (hf₁.sub hf₂) origin ell hell k x
     calc
       _ ≤ ‖iteratedFDeriv ℝ k (f₁-f₂) (scaleCoords origin ell x)‖*ell⁻¹^k := hpull
       _ ≤ (B*w)*L^k*ell⁻¹^k := mul_le_mul_of_nonneg_right (hi.trans hmul) (by positivity)
       _ = _ := by rw [div_eq_mul_inv,mul_pow]; ring
   have hnorm := Model.holderNorm_le_of_scaled_iteratedFDeriv_bound ((f₁-f₂) ∘ scaleCoords origin ell) t ht
     ((hf₁.sub hf₂).comp (scaleCoords_smooth origin ell)) (B*w) (L/ell) (mul_nonneg hB.le hw) hLscale hjets
   convert hnorm using 1
   dsimp [f₁,f₂,w,L,SG]
   congr 1
   ring


theorem base_profile_jet_bound_global_family {d : ℕ} (κ : R → ℝ → ℝ) (KP : Set R) (hKP : IsCompact KP)
    (hκ : ContDiff ℝ ∞ (Function.uncurry κ)) (hκ0 : ∀ p, κ p 0 = 0)
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (cut : Model.Covariate d → ℝ) (hc : ContDiff ℝ ∞ cut) (hcompact : HasCompactSupport cut) (hcut : ∀ x, cut x ∈ Icc (0:ℝ) 1)
    (n : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ p ∈ KP, ∀ S ∈ Icc (0:ℝ) 1,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi), ∀ θ : ℝ,
      ∀ q ≤ n, ∀ x : Model.Covariate d,
      ‖iteratedFDeriv ℝ q (oscillatorProfile (κ p) (intervalCenter lo hi) S h θ cut 0) x‖ ≤ C := by
  obtain ⟨B,hB,hcutjet⟩ := hcompact.exists_bound_iteratedFDeriv hc n
  let L : ℝ := max B 1
  have hL : 1≤L := le_max_right _ _
  obtain ⟨C,hC,houter⟩ := familyOuter_finite_jet_bound κ hκ hκ0 KP hKP lo hi hlo hlt n
  let cost (q : ℕ) : ℝ := (Fintype.card (OrderedFinpartition q):ℝ)*C*L^q
  let H : ℝ := 1+∑ q ∈ Finset.range (n+1), cost q
  have hcost (q : ℕ) : 0≤cost q := by dsimp [cost]; positivity
  have hH : 0<H := by
    have hs := Finset.sum_nonneg (s := Finset.range (n+1)) (fun q _ => hcost q)
    dsimp [H]
    linarith
  refine ⟨H,hH,?_⟩
  intro p hpParam S hS h hh θ
  let g := oscillatorOuter (κ p) (intervalCenter lo hi) S
  let f := phaseInput h θ cut (0 : Model.Covariate d → ℝ)
  have hgf : ContDiff ℝ ∞ (g ∘ f) := oscillatorProfile_smooth (κ p) lo hi hlo hlt univ isOpen_univ
      (familyScalar_contDiff κ hκ p).contDiffOn (subset_univ _) S h θ hS hh cut 0 hc contDiff_const hcut
  have hjets (q : ℕ) (hq : q≤n) (x : Model.Covariate d)  :
      ‖iteratedFDeriv ℝ q (g ∘ f) x‖ ≤ H := by
    have hg : ContDiffAt ℝ ∞ g (f x) := by
      simpa [g,f,phaseInput] using oscillatorOuter_contDiffAt (κ p) lo hi hlo hlt univ isOpen_univ
        (familyScalar_contDiff κ hκ p).contDiffOn (subset_univ _) S hS h (cut x) θ hh (hcut x)
    have hf : ContDiffAt ℝ ∞ f x := phaseInput_contDiffAt h θ cut 0 x hc.contDiffAt contDiffAt_const
    have ho (k : ℕ) (hk : k≤q) : ‖iteratedFDeriv ℝ k g (f x)‖ ≤ C := by
      have he := (houter p hpParam k (hk.trans hq) S hS h hh (cut x) (hcut x) θ θ).1
      have hCS : C*S ≤ C := by simpa only [mul_one] using mul_le_mul_of_nonneg_left hS.2 hC.le
      simpa [g,f,phaseInput] using he.trans hCS
    have hi (k : ℕ) (hk0 : 1≤k) (hk : k≤q) : ‖iteratedFDeriv ℝ k f x‖ ≤ L^k := by
      have hkpos : 0<k := by omega
      rw [norm_phaseInput_jet h θ cut 0 x k hkpos hc.contDiffAt contDiffAt_const,
        iteratedFDeriv_zero]
      simp only [Pi.zero_apply,norm_zero,max_eq_left (norm_nonneg _)]
      exact (hcutjet k (hk.trans hq) x).trans ((le_max_left B 1).trans
        (by simpa only [pow_one] using pow_le_pow_right₀ hL hk0))
    have hb := local_composition_jet_norm_bound_scaled g f x q hg hf C L hC.le (zero_lt_one.trans_le hL).le ho hi
    have hs : cost q ≤ H := by
      have hh := Finset.single_le_sum (fun i _ => hcost i) (Finset.mem_range.mpr (show q<n+1 by omega))
      dsimp [H]
      linarith
    exact hb.trans hs
  exact hjets

/-- A rescaled base profile has its genuine ell^(-t) Hölder cost. -/
theorem base_profile_holder_bound_rescale_family {d : ℕ} (κ : R → ℝ → ℝ) (KP : Set R) (hKP : IsCompact KP)
    (hκ : ContDiff ℝ ∞ (Function.uncurry κ)) (hκ0 : ∀ p, κ p 0 = 0)
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (cut : Model.Covariate d → ℝ) (hc : ContDiff ℝ ∞ cut) (hcompact : HasCompactSupport cut)
    (hcut : ∀ x, cut x ∈ Icc (0:ℝ) 1) (t : ℝ) (ht : 0<t) :
    ∃ C : ℝ, 0<C ∧ ∀ p ∈ KP, ∀ ell : ℝ, 0<ell → ell≤1 → ∀ origin : Model.Covariate d,
      ∀ S ∈ Icc (0:ℝ) 1, ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi), ∀ θ : ℝ,
      Model.holderNorm ((oscillatorProfile (κ p) (intervalCenter lo hi) S h θ cut 0) ∘ scaleCoords origin ell) t ≤
        ENNReal.ofReal (C*ell⁻¹^t) := by
  obtain ⟨C,hC,hjets⟩ := base_profile_jet_bound_global_family κ KP hKP hκ hκ0 lo hi hlo hlt cut hc hcompact hcut (Model.holderOrder t+1)
  refine ⟨3*C,by positivity,?_⟩
  intro p hpParam ell hell hell1 origin S hS h hh θ
  let f := oscillatorProfile (κ p) (intervalCenter lo hi) S h θ cut 0
  have hf : ContDiff ℝ ∞ f := oscillatorProfile_smooth (κ p) lo hi hlo hlt univ isOpen_univ
      (familyScalar_contDiff κ hκ p).contDiffOn (subset_univ _) S h θ hS hh cut 0 hc contDiff_const hcut
  have hL : 1≤ell⁻¹ := (one_le_inv₀ hell).mpr hell1
  have hb (q : ℕ) (hq : q≤Model.holderOrder t+1) (x : Model.Covariate d) (_hx : x∈Model.cube d) :
      ‖iteratedFDeriv ℝ q (f ∘ scaleCoords origin ell) x‖ ≤ C*ell⁻¹^q := by
    exact (norm_iteratedFDeriv_rescale f hf origin ell hell q x).trans
      (mul_le_mul_of_nonneg_right (hjets p hpParam S hS h hh θ q hq _) (by positivity))
  exact Model.holderNorm_le_of_scaled_iteratedFDeriv_bound (f ∘ scaleCoords origin ell) t ht
    (hf.comp (scaleCoords_smooth origin ell)) C ell⁻¹ hC.le hL hb

theorem source_profile_holder_bound_rescale_family (U : SmoothStep) (d Q K : ℕ)
    (gammaStar lambdaStar alpha0 : ℝ) (hγ : 0 < gammaStar) (hγ1 : gammaStar ≤ 1/4)
    (hlam : 0 < lambdaStar) (ha0 : 0 ≤ alpha0) (ha1 : alpha0 < 1)
    (hK : 0 < K) (hKQ : K ≤ 2*Q)
    (κ : R → ℝ → ℝ) (KP : Set R) (hKP : IsCompact KP)
    (hκ : ContDiff ℝ ∞ (Function.uncurry κ)) (hκ0 : ∀ p, κ p 0 = 0)
    (lo hi : ℝ) (hlo : 0 < lo) (hlt : lo < hi)
    (cut : Model.Covariate d → ℝ) (hcut : ContDiff ℝ ∞ cut) (hcompact : HasCompactSupport cut)
    (hcut01 : ∀ x, cut x ∈ Icc (0:ℝ) 1) (t : ℝ) (ht : alpha0<t)
    (hbudget : Model.holderOrder t+2 ≤ K) :
    ∃ C : ℝ, 0<C ∧ ∀ p ∈ KP, ∀ ell : ℝ, 0<ell → ell≤1 → ∀ origin : Model.Covariate d, ∀ J M : ℕ, ∀ m : ℝ,
      (2:ℝ)^((J:ℝ)*alpha0) ≤ m → ∀ z : Fin d × Fin J → ℤ,
      ∀ h ∈ Icc (-intervalHalfWidth lo hi) (intervalHalfWidth lo hi), ∀ θ : ℝ,
      Model.holderNorm
        ((oscillatorProfile (κ p) (intervalCenter lo hi) (sourceGate d J Q M gammaStar lambdaStar alpha0 m z) h θ cut
          (sourcePartialPhase U d J M gammaStar z 0)) ∘ scaleCoords origin ell) t ≤
      ENNReal.ofReal (C*ell⁻¹^t*(1+(2:ℝ)^((J:ℝ)*t)/m)) := by
  have ht0 : 0<t := ha0.trans_lt ht
  obtain ⟨Cb,hCb,hbase⟩ := base_profile_holder_bound_rescale_family κ KP hKP hκ hκ0 lo hi hlo hlt cut hcut hcompact hcut01 t ht0
  obtain ⟨Ci,hCi,hinc⟩ := source_profile_increment_holder_bound_rescale_family U d Q K gammaStar lambdaStar alpha0 hγ hγ1 hlam ha0 ha1
    hK hKQ κ KP hKP hκ hκ0 lo hi hlo hlt cut hcut hcompact hcut01 t ht0 hbudget
  obtain ⟨D,hD,hcost⟩ := source_holder_cost_sum_bound gammaStar alpha0 t hγ ht
  let C := 2*(Cb+Ci*D+1)
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro p hpParam ell hell hell1 origin J M m hm z h hh θ
  have hm0 : 0 < m := (Real.rpow_pos_of_pos (by norm_num) _).trans_le hm
  let S := sourceGate d J Q M gammaStar lambdaStar alpha0 m z
  let F (b : ℕ) := (oscillatorProfile (κ p) (intervalCenter lo hi) S h θ cut (sourcePartialPhase U d J M gammaStar z b)) ∘ scaleCoords origin ell
  have hS : S ∈ Icc (0:ℝ) 1 := blockGate_range Q M _ _ z
  have hF (b : ℕ) : ContDiff ℝ ∞ (F b) := (oscillatorProfile_smooth (κ p) lo hi hlo hlt univ isOpen_univ
      (familyScalar_contDiff κ hκ p).contDiffOn (subset_univ _) S h θ hS hh cut _ hcut
    (sourcePartialPhase_smooth U d J M gammaStar hγ hγ1 z b) hcut01).comp (scaleCoords_smooth origin ell)
  let f : Option (Fin J) → Model.Covariate d → ℝ
    | none => F J
    | some b => F b.val-F (b.val+1)
  let cost : Option (Fin J) → ℝ
    | none => Cb*ell⁻¹^t
    | some b => Ci*sourceWeight gammaStar alpha0 m b.val*(sourceRate J gammaStar b.val/ell)^t
  have hnonneg (i : Option (Fin J)) : 0≤cost i := by
    cases i with
    | none => exact mul_nonneg hCb.le (Real.rpow_nonneg (inv_nonneg.mpr hell.le) _)
    | some b => dsimp [cost,sourceWeight,sourceRate,sourceGamma]; positivity
  have hbound (i : Option (Fin J)) : Model.holderNorm (f i) t ≤ ENNReal.ofReal (cost i) := by
    cases i with
    | none =>
      dsimp [f,F]
      rw [sourcePartialPhase_at_depth]
      exact hbase p hpParam ell hell hell1 origin S hS h hh θ
    | some b => exact hinc p hpParam ell hell hell1 origin J M b.val b.isLt m hm z h hh θ
  have hf (i : Option (Fin J)) : ContDiff ℝ ∞ (f i) := by
    cases i with
    | none => exact hF J
    | some b => exact (hF b.val).sub (hF (b.val+1))
  have hsum := Model.holderNorm_sum_le Finset.univ f cost t ht0 (fun i _ => hnonneg i) (fun i _ => hf i) (fun i _ => hbound i)
  have he : (fun x => ∑ i, f i x) = F 0 := by
    funext x
    rw [Fintype.sum_option]
    change F J x+(∑ i : Fin J, (F i.val x-F (i.val+1) x)) = F 0 x
    rw [Fin.sum_univ_eq_sum_range (fun b => F b x-F (b+1) x) J,Finset.sum_range_sub']
    ring
  have hc : (∑ i, cost i) = Cb*ell⁻¹^t+Ci*(∑ b ∈ Finset.range J, sourceWeight gammaStar alpha0 m b*(sourceRate J gammaStar b/ell)^t) := by
    rw [Fintype.sum_option]
    change Cb*ell⁻¹^t+(∑ b : Fin J, Ci*sourceWeight gammaStar alpha0 m b.val*(sourceRate J gammaStar b.val/ell)^t) = _
    rw [Fin.sum_univ_eq_sum_range (fun b => Ci*sourceWeight gammaStar alpha0 m b*(sourceRate J gammaStar b/ell)^t) J]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [he,hc] at hsum
  have hscale : 0≤(2:ℝ)^((J:ℝ)*t)/m := by positivity
  have hr : (∑ b ∈ Finset.range J, sourceWeight gammaStar alpha0 m b*(sourceRate J gammaStar b/ell)^t) =
      ell⁻¹^t*(∑ b ∈ Finset.range J, sourceWeight gammaStar alpha0 m b*sourceRate J gammaStar b^t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    have hL : 0 ≤ sourceRate J gammaStar b := by unfold sourceRate sourceGamma; positivity
    rw [Real.div_rpow hL hell.le,Real.inv_rpow hell.le]
    ring
  rw [hr] at hsum
  have hmul := mul_le_mul_of_nonneg_left (hcost J m hm0) hCi.le
  have hmul' : Ci*(∑ b ∈ Finset.range J, sourceWeight gammaStar alpha0 m b*sourceRate J gammaStar b^t) ≤ Ci*D*((2:ℝ)^((J:ℝ)*t)/m) := by
    convert hmul using 1
    ring
  have hcfinal : 2*(Cb+Ci*(∑ b ∈ Finset.range J, sourceWeight gammaStar alpha0 m b*sourceRate J gammaStar b^t)) ≤
      C*(1+(2:ℝ)^((J:ℝ)*t)/m) := by
    dsimp [C]
    nlinarith [mul_nonneg hCb.le hscale,mul_nonneg hCi.le hD]
  have hcfinal' := mul_le_mul_of_nonneg_left hcfinal (Real.rpow_nonneg (inv_nonneg.mpr hell.le) t)
  exact hsum.trans (ENNReal.ofReal_le_ofReal (by convert hcfinal' using 1 <;> ring))

end RoughRegime.LatticePriors
