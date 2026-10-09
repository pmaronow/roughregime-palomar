module

public import RoughRegime.HadamardSmooth
public import RoughRegime.HolderAffine
public import RoughRegime.HolderComparison


@[expose] public section
/-! Smooth-germ localization and the literal finite extra restrictions from
Lemma16. The local sup bound is derived from smoothness, and constant-path
membership is obtained from the actual constant Hölder norm. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace RoughRegime.Localization

structure SmoothGerm where
  K : ℝ × ℝ → ℝ
  domain : Set (ℝ × ℝ)
  open_domain : IsOpen domain
  origin_mem : (0 : ℝ × ℝ)∈domain
  smooth : ContDiffOn ℝ ∞ K domain

def SmoothGerm.baseline (G : SmoothGerm) : ℝ := G.K (0,0)

theorem SmoothGerm.continuousAt_origin (G : SmoothGerm) : ContinuousAt G.K 0 :=
  (G.smooth.contDiffAt (G.open_domain.mem_nhds G.origin_mem)).continuousAt

/-- The actual local Lipschitz sup estimate needed for all the nuisances in
Lemma16; its constant is derived from the two smooth Hadamard factors. -/
theorem SmoothGerm.local_sup_bound (G : SmoothGerm) :
    ∃ r C : ℝ, 0<r ∧ 0<C ∧ ∀ p : ℝ×ℝ, |p.1|≤r → |p.2|≤r →
      |G.K p-G.baseline| ≤ C*(|p.1|+|p.2|) := by
  obtain ⟨r,hr,F,H,hF,hH,he⟩ := Calculus.local_hadamard_two_factors G.K G.domain
    G.open_domain G.origin_mem G.smooth
  let T : Set (ℝ×ℝ) := Icc (-r) r ×ˢ Icc (-r) r
  obtain ⟨B,hB⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (hF.continuous.norm.continuousOn : ContinuousOn (fun p => ‖F p‖) T)
  obtain ⟨D,hD⟩ := (isCompact_Icc.prod isCompact_Icc).bddAbove_image
    (hH.continuous.norm.continuousOn : ContinuousOn (fun p => ‖H p‖) T)
  let C := max 1 (max B D)
  have hC : 0<C := zero_lt_one.trans_le (le_max_left _ _)
  refine ⟨r,C,hr,hC,?_⟩
  intro p hp1 hp2
  have hpT : p∈T := ⟨abs_le.mp hp1,abs_le.mp hp2⟩
  have hFb : |F p|≤C := by
    rw [← Real.norm_eq_abs]
    exact (hB ⟨p,hpT,rfl⟩).trans ((le_max_left _ _).trans (le_max_right _ _))
  have hHb : |H p|≤C := by
    rw [← Real.norm_eq_abs]
    exact (hD ⟨p,hpT,rfl⟩).trans ((le_max_right _ _).trans (le_max_right _ _))
  have h1 := mul_le_mul_of_nonneg_left hFb (abs_nonneg p.1)
  have h2 := mul_le_mul_of_nonneg_left hHb (abs_nonneg p.2)
  rw [he p hp1 hp2]
  change |G.baseline+p.1*F p+p.2*H p-G.baseline|≤_
  have hsum := abs_add_le (p.1*F p) (p.2*H p)
  rw [abs_mul,abs_mul] at hsum
  have hid : G.baseline+p.1*F p+p.2*H p-G.baseline=p.1*F p+p.2*H p := by ring
  rw [hid]
  exact hsum.trans (by nlinarith [h1,h2])

inductive Condition where
  | holder (G : SmoothGerm) (t H : ℝ)
  | interval (G : SmoothGerm) (lo hi : ℝ)
  | weighted (G : SmoothGerm) (lo hi : ℝ)

def Condition.germ : Condition → SmoothGerm
  | .holder G _ _ => G
  | .interval G _ _ => G
  | .weighted G _ _ => G

def Condition.baselineAdmissible (rminus rplus : ℝ) : Condition → Prop
  | .holder G t H => 0<t ∧ |G.baseline|<H
  | .interval G lo hi => lo<G.baseline ∧ G.baseline<hi
  | .weighted G lo hi => 0<G.baseline ∧ lo≤rminus*G.baseline ∧ rplus*G.baseline≤hi

def Condition.Holds {d : ℕ} (c : Condition)
    (p u v : Model.Covariate d → ℝ) : Prop :=
  match c with
  | .holder G t H => (fun x => G.K (u x,v x))∈Model.holderBall t H
  | .interval G lo hi => ∀ x∈Model.cube d, lo≤G.K (u x,v x) ∧ G.K (u x,v x)≤hi
  | .weighted G lo hi => ∀ x∈Model.cube d, lo≤p x*G.K (u x,v x) ∧ p x*G.K (u x,v x)≤hi

theorem interval_membership {X : Type*} (K : X→ℝ) (k0 lo hi eta : ℝ)
    (hb : ∀ x, |K x-k0|≤eta) (hlo : eta≤k0-lo) (hhi : eta≤hi-k0) :
    ∀ x, lo≤K x ∧ K x≤hi := by
  intro x
  have hh := abs_le.mp (hb x)
  constructor <;> linarith

theorem weighted_membership {X : Type*} (p K : X→ℝ) (k0 eta delta rminus rplus lo hi : ℝ)
    (hk0 : 0<k0) (heta : 0≤eta) (hrminus : 0≤rminus) (hdelta : 0≤delta)
    (hp : ∀ x, rminus+delta≤p x ∧ p x≤rplus-delta)
    (hK : ∀ x, |K x-k0|≤eta) (hmargin : rplus*eta≤k0*delta)
    (hlo : lo≤rminus*k0) (hhi : rplus*k0≤hi) :
    ∀ x, lo≤p x*K x ∧ p x*K x≤hi := by
  intro x
  have hpp : 0≤p x := by linarith [(hp x).1]
  have hpr : p x≤rplus := by linarith [(hp x).2]
  have hl := mul_le_mul_of_nonneg_left (abs_le.mp (hK x)).1 hpp
  have hu := mul_le_mul_of_nonneg_left (abs_le.mp (hK x)).2 hpp
  have hb := mul_le_mul_of_nonneg_right hpr heta
  have hpl := mul_le_mul_of_nonneg_right (hp x).1 hk0.le
  have hpu := mul_le_mul_of_nonneg_right (hp x).2 hk0.le
  constructor <;> nlinarith

theorem holder_membership {d : ℕ} (G : SmoothGerm) (u v : Model.Covariate d→ℝ)
    (t H eta : ℝ) (ht : 0<t) (heta : 0≤eta)
    (hs : ContDiff ℝ ∞ (fun x => G.K (u x,v x)-G.baseline))
    (hb : Model.holderNorm (fun x => G.K (u x,v x)-G.baseline) t≤ENNReal.ofReal eta)
    (hmargin : |G.baseline|+eta≤H) :
    (fun x => G.K (u x,v x))∈Model.holderBall t H := by
  have he := Model.holderNorm_const_add_le _ hs G.baseline t eta ht heta hb
  have hfun : (fun x => G.baseline+(G.K (u x,v x)-G.baseline))=(fun x => G.K (u x,v x)) := by
    funext x
    ring
  rw [hfun] at he
  exact he.trans (ENNReal.ofReal_le_ofReal hmargin)

/-- Each extra restriction holds for the actual constant parametric response
path in a neighborhood of the baseline. Weighted restrictions are strict at
the origin because the reference design density equals one. -/
theorem Condition.constant_eventually {d : ℕ} (c : Condition) (rminus rplus : ℝ)
    (hrminus : rminus<1) (hrplus : 1<rplus)
    (hb : c.baselineAdmissible rminus rplus) :
    ∀ᶠ a : ℝ×ℝ in 𝓝 0,
      c.Holds (fun _ : Model.Covariate d => 1) (fun _ => a.1) (fun _ => a.2) := by
  cases c with
  | holder G t H =>
    have he : ∀ᶠ a in 𝓝 (0 : ℝ×ℝ), |G.K a|<H :=
      (G.continuousAt_origin.abs.tendsto).eventually_lt_const hb.2
    filter_upwards [he] with a ha
    exact Model.const_mem_holderBall hb.1 ha.le
  | interval G lo hi =>
    have hl : ∀ᶠ a in 𝓝 (0 : ℝ×ℝ), lo<G.K a :=
      G.continuousAt_origin.tendsto.eventually_const_lt hb.1
    have hh : ∀ᶠ a in 𝓝 (0 : ℝ×ℝ), G.K a<hi :=
      G.continuousAt_origin.tendsto.eventually_lt_const hb.2
    filter_upwards [hl,hh] with a ha hb
    exact fun _ _ => ⟨ha.le,hb.le⟩
  | weighted G lo hi =>
    have hlo : lo<G.baseline := hb.2.1.trans_lt (by nlinarith [hb.1])
    have hhi : G.baseline<hi := (by nlinarith [hb.1] : G.baseline<rplus*G.baseline).trans_le hb.2.2
    have hl : ∀ᶠ a in 𝓝 (0 : ℝ×ℝ), lo<G.K a :=
      G.continuousAt_origin.tendsto.eventually_const_lt hlo
    have hh : ∀ᶠ a in 𝓝 (0 : ℝ×ℝ), G.K a<hi :=
      G.continuousAt_origin.tendsto.eventually_lt_const hhi
    filter_upwards [hl,hh] with a ha hb
    simpa only [Condition.Holds,one_mul] using (fun (_ : Model.Covariate d) (_ : _∈Model.cube d) => And.intro ha.le hb.le)

theorem finite_constant_neighborhood {d : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → Condition) (rminus rplus : ℝ) (hrminus : rminus<1) (hrplus : 1<rplus)
    (hb : ∀ i, (c i).baselineAdmissible rminus rplus) :
    ∃ r : ℝ, 0<r ∧ ∀ a : ℝ×ℝ, |a.1|≤r → |a.2|≤r →
      ∀ i, (c i).Holds (fun _ : Model.Covariate d => 1) (fun _ => a.1) (fun _ => a.2) := by
  have he : ∀ᶠ a : ℝ×ℝ in 𝓝 0, ∀ i,
      (c i).Holds (fun _ : Model.Covariate d => 1) (fun _ => a.1) (fun _ => a.2) :=
    eventually_all.mpr (fun i => Condition.constant_eventually (c i) rminus rplus hrminus hrplus (hb i))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp he
  refine ⟨r/2,half_pos hr,?_⟩
  intro a ha1 ha2
  apply hball
  rw [dist_zero_right,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,max_lt_iff]
  exact ⟨ha1.trans_lt (half_lt_self hr),ha2.trans_lt (half_lt_self hr)⟩

/-- Uniform sup localization of an arbitrary family of actual perturbations.
The dominating sup radius is little-o of the genuine density margin. -/
theorem SmoothGerm.uniform_sup_control {X : Type*} {Θ : ℕ→Type*} (G : SmoothGerm)
    (u v : (n : ℕ)→Θ n→X→ℝ) (a delta : ℕ→ℝ)
    (_ha : ∀ n, 0≤a n) (ha0 : Tendsto a atTop (𝓝 0))
    (hd : ∀ n, 0<delta n) (had : Tendsto (fun n => a n/delta n) atTop (𝓝 0))
    (hb : ∀ n θ x, |u n θ x|+|v n θ x|≤a n) :
    ∃ C : ℝ, 0<C ∧
      (∀ᶠ n in atTop, ∀ θ x, |G.K (u n θ x,v n θ x)-G.baseline|≤C*a n) ∧
      (fun n => C*a n) =o[atTop] delta := by
  obtain ⟨r,C,hr,hC,hlocal⟩ := G.local_sup_bound
  have he : ∀ᶠ n in atTop, a n<r := ha0.eventually_lt_const hr
  refine ⟨C,hC,?_,?_⟩
  · filter_upwards [he] with n hn
    intro θ x
    have hsum := hb n θ x
    have hu : |u n θ x|≤r := by nlinarith [abs_nonneg (v n θ x)]
    have hv : |v n θ x|≤r := by nlinarith [abs_nonneg (u n θ x)]
    exact (hlocal _ hu hv).trans (mul_le_mul_of_nonneg_left hsum hC.le)
  · apply (Asymptotics.isLittleO_iff_tendsto (fun n hh => False.elim ((hd n).ne' hh))).mpr
    have he := had.const_mul C
    simpa only [mul_zero,mul_div_assoc] using he

def Condition.holderBudget : Condition→ℝ
  | .holder G _ H => H-|G.baseline|
  | .interval _ _ _ => 1
  | .weighted _ _ _ => 1

def Condition.perturbationBound {d : ℕ} (c : Condition) (cost epsilon : ℝ)
    (u v : Model.Covariate d→ℝ) : Prop :=
  match c with
  | .holder G t _ =>
      ContDiff ℝ ∞ (fun x => G.K (u x,v x)-G.baseline) ∧
      Model.holderNorm (fun x => G.K (u x,v x)-G.baseline) t≤ENNReal.ofReal (cost*epsilon)
  | .interval _ _ _ => True
  | .weighted _ _ _ => True

theorem Condition.holderBudget_pos (c : Condition) (rminus rplus : ℝ)
    (hb : c.baselineAdmissible rminus rplus) : 0<c.holderBudget := by
  cases c with
  | holder G t H => exact sub_pos.mpr hb.2
  | interval G lo hi => exact zero_lt_one
  | weighted G lo hi => exact zero_lt_one

/-- The simultaneous finite hard-law membership clause of Lemma16.
The smooth perturbation estimates are the actual canonical estimates proved
in CanonicalKHolder; the sup and weighted estimates are derived here from
the smooth germs and the amplitude-to-density-margin asymptotics. -/
theorem finite_hard_membership {d : ℕ} {ι : Type*} [Fintype ι] {Θ : ℕ→Type*}
    (c : ι → Condition) (cost : ι→ℝ) (hcost : ∀ i, 0≤cost i)
    (rminus rplus : ℝ) (hrminus : 0≤rminus) (_hrplus : 0<rplus)
    (hbase : ∀ i, (c i).baselineAdmissible rminus rplus)
    (p u v : ℝ→(n : ℕ)→Θ n→Model.Covariate d→ℝ)
    (a delta : ℕ→ℝ) (ha : ∀ n, 0≤a n) (ha0 : Tendsto a atTop (𝓝 0))
    (hd : ∀ n, 0<delta n) (had : Tendsto (fun n => a n/delta n) atTop (𝓝 0))
    (hamp : ∀ epsilon, 0<epsilon → epsilon≤1 → ∀ n θ x,
      |u epsilon n θ x|+|v epsilon n θ x|≤a n)
    (hp : ∀ epsilon, 0<epsilon → epsilon≤1 → ∀ n θ x,
      rminus+delta n≤p epsilon n θ x ∧ p epsilon n θ x≤rplus-delta n)
    (hh : ∀ epsilon, 0<epsilon → epsilon≤1 → ∀ i,
      ∀ᶠ n in atTop, ∀ θ, (c i).perturbationBound (cost i) epsilon (u epsilon n θ) (v epsilon n θ)) :
    ∃ epsilon0 : ℝ, 0<epsilon0 ∧ epsilon0≤1 ∧
      ∀ epsilon, 0<epsilon → epsilon≤epsilon0 →
        ∀ᶠ n in atTop, ∀ θ i, (c i).Holds (p epsilon n θ) (u epsilon n θ) (v epsilon n θ) := by
  have heps : ∀ᶠ e : ℝ in 𝓝 0, ∀ i, cost i*e<(c i).holderBudget := by
    apply eventually_all.mpr
    intro i
    have hbudget := Condition.holderBudget_pos (c i) rminus rplus (hbase i)
    have hcont : ContinuousAt (fun e : ℝ => cost i*e) 0 := continuousAt_const.mul continuousAt_id
    have hlim : Tendsto (fun e : ℝ => cost i*e) (𝓝 0) (𝓝 0) := by simpa using hcont.tendsto
    exact hlim.eventually_lt_const hbudget
  obtain ⟨r,hr,hepsr⟩ := Metric.eventually_nhds_iff.mp heps
  let epsilon0 := min 1 (r/2)
  have heps0 : 0<epsilon0 := lt_min zero_lt_one (half_pos hr)
  refine ⟨epsilon0,heps0,min_le_left _ _,?_⟩
  intro epsilon hepsilon hepsilon0
  have hepsilon1 : epsilon≤1 := hepsilon0.trans (min_le_left _ _)
  have hbudget : ∀ i, cost i*epsilon<(c i).holderBudget := hepsr (by
    rw [Real.dist_eq,sub_zero,abs_of_pos hepsilon]
    exact (hepsilon0.trans (min_le_right _ _)).trans_lt (half_lt_self hr))
  suffices he : ∀ᶠ n in atTop, ∀ i θ,
      (c i).Holds (p epsilon n θ) (u epsilon n θ) (v epsilon n θ) by
    filter_upwards [he] with n hn
    intro θ i
    exact hn i θ
  apply eventually_all.mpr
  intro i
  cases hci : c i with
  | holder G t H =>
    have hb := hbase i
    rw [hci] at hb
    have he := hh epsilon hepsilon hepsilon1 i
    filter_upwards [he] with n hn
    intro θ
    have hnorm := hn θ
    rw [hci] at hnorm
    apply holder_membership G _ _ t H (cost i*epsilon) hb.1 (mul_nonneg (hcost i) hepsilon.le) hnorm.1 hnorm.2
    have hm := hbudget i
    rw [hci] at hm
    change cost i*epsilon<H-|G.baseline| at hm
    linarith
  | interval G lo hi =>
    have hb := hbase i
    rw [hci] at hb
    obtain ⟨C,hC,hbound,_hsmall⟩ := G.uniform_sup_control (u epsilon) (v epsilon) a delta ha ha0 hd had
      (hamp epsilon hepsilon hepsilon1)
    have hCa : Tendsto (fun n => C*a n) atTop (𝓝 0) := by simpa using ha0.const_mul C
    have hCl : ∀ᶠ n in atTop, C*a n<G.baseline-lo :=
      hCa.eventually_lt_const (sub_pos.mpr hb.1)
    have hCh : ∀ᶠ n in atTop, C*a n<hi-G.baseline :=
      hCa.eventually_lt_const (sub_pos.mpr hb.2)
    filter_upwards [hbound,hCl,hCh] with n hn hnl hnh
    intro θ
    exact fun x _ => interval_membership (fun y => G.K (u epsilon n θ y,v epsilon n θ y))
      G.baseline lo hi (C*a n) (hn θ) hnl.le hnh.le x
  | weighted G lo hi =>
    have hb := hbase i
    rw [hci] at hb
    obtain ⟨C,hC,hbound,_hsmall⟩ := G.uniform_sup_control (u epsilon) (v epsilon) a delta ha ha0 hd had
      (hamp epsilon hepsilon hepsilon1)
    have hrat : Tendsto (fun n => (rplus*C)*(a n/delta n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using had.const_mul (rplus*C)
    have hmargin : ∀ᶠ n in atTop, (rplus*C)*(a n/delta n)<G.baseline := hrat.eventually_lt_const hb.1
    filter_upwards [hbound,hmargin] with n hn hnm
    intro θ
    have hnum : rplus*(C*a n)≤G.baseline*delta n := by
      have hm := mul_le_mul_of_nonneg_right hnm.le (hd n).le
      have he : (rplus*C)*(a n/delta n)*delta n=rplus*(C*a n) := by
        field_simp [(hd n).ne']
      rw [he] at hm
      exact hm
    exact fun x _ => weighted_membership (p epsilon n θ)
      (fun y => G.K (u epsilon n θ y,v epsilon n θ y)) G.baseline (C*a n) (delta n)
      rminus rplus lo hi hb.1 (mul_nonneg hC.le (ha n)) hrminus (hd n).le
      (hp epsilon hepsilon hepsilon1 n θ) (hn θ) hnum hb.2.1 hb.2.2 x

end RoughRegime.Localization
