module

public import RoughRegime.MultiIndexHolder
public import RoughRegime.CoordinateJets
public import Mathlib.Analysis.Calculus.FDeriv.Extend

@[expose] public section
/-! Boundary regularity from continuous finite interior derivative jets.
The predicate below has no boundary derivative or ContDiffOn assumption.
It uses Fréchet jets; the separate classical coordinate-to-Fréchet interior
translation is discussed in docs/boundary-regularity.md. -/
noncomputable section

open Set Filter
open scoped Topology ContDiff ENNReal

namespace RoughRegime.Model

universe u

/-- A continuous finite derivative jet on the closed cube, with ordinary derivative
identities imposed only at interior points. -/
def InteriorJet {d : ℕ} {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : Covariate d → F) : Prop :=
  match k with
  | 0 => ContinuousOn f (cube d)
  | k + 1 => ContinuousOn f (cube d) ∧
      ∃ g : Covariate d → Covariate d →L[ℝ] F,
        InteriorJet k g ∧ ∀ x ∈ interior (cube d), HasFDerivAt f (g x) x

theorem closure_interior_cube (d : ℕ) : closure (interior (cube d)) = cube d := by
  rw [(convex_cube d).closure_interior_eq_closure_of_nonempty_interior
    (cube_nonempty_interior d), (isCompact_cube d).isClosed.closure_eq]

theorem hasFDerivWithinAt_cube_of_interior_jet
    {d : ℕ} {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Covariate d → F} {g : Covariate d → Covariate d →L[ℝ] F}
    (hf : ContinuousOn f (cube d)) (hg : ContinuousOn g (cube d))
    (hd : ∀ x ∈ interior (cube d), HasFDerivAt f (g x) x)
    {x : Covariate d} (hx : x ∈ cube d) : HasFDerivWithinAt f (g x) (cube d) x := by
  have hfcont : ∀ y ∈ closure (interior (cube d)),
      ContinuousWithinAt f (interior (cube d)) y := by
    intro y hy
    rw [closure_interior_cube] at hy
    exact (hf y hy).mono interior_subset
  have hlim : Tendsto (fun y => fderiv ℝ f y) (𝓝[interior (cube d)] x) (𝓝 (g x)) := by
    apply ((hg x hx).mono interior_subset).congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (hd y hy).fderiv.symm
  have h := hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hd y hy).differentiableAt.differentiableWithinAt)
    (convex_cube d).interior isOpen_interior hfcont hlim
  rwa [closure_interior_cube] at h

theorem interiorJet_iff_contDiffOn {d : ℕ} {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : Covariate d → F) :
    InteriorJet k f ↔ ContDiffOn ℝ k f (cube d) := by
  induction k generalizing F with
  | zero => simp [InteriorJet, contDiffOn_zero]
  | succ k ih =>
    rw [InteriorJet]
    constructor
    · rintro ⟨hf, g, hg, hd⟩
      have hgc := (ih g).mp hg
      apply (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
        (n := (k : ℕ∞ω)) (uniqueDiffOn_cube d)).mpr
      refine ⟨by simp, g, hgc, ?_⟩
      intro x hx
      exact hasFDerivWithinAt_cube_of_interior_jet hf hgc.continuousOn hd hx
    · intro hf
      have hs : ContDiffOn ℝ ((k : ℕ∞ω) + 1) f (cube d) := by simpa using hf
      obtain ⟨_, g, hg, hd⟩ :=
        (contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn
          (n := (k : ℕ∞ω)) (uniqueDiffOn_cube d)).mp hs
      refine ⟨hf.continuousOn, g, (ih g).mpr hg, ?_⟩
      intro x hx
      exact (hd x (interior_subset hx)).hasFDerivAt
        (mem_interior_iff_mem_nhds.mp hx)

/-- An explicit finite tensor jet. The derivative linkage is imposed only
in the open interior; continuity and coefficient values are on the cube. -/
structure InteriorTaylorJet {d : ℕ} {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (k : ℕ) (f : Covariate d → F)
    (p : Covariate d → FormalMultilinearSeries ℝ (Covariate d) F) : Prop where
  zero_eq : ∀ x ∈ cube d, (p x 0).curry0 = f x
  cont : ∀ m ≤ k, ContinuousOn (fun x => p x m) (cube d)
  fderivInterior : ∀ m < k, ∀ x ∈ interior (cube d),
    HasFDerivAt (fun y => p y m) (p x (m + 1)).curryLeft x

/-- Every continuous finite interior jet is a genuine within-cube Taylor jet. -/
theorem InteriorTaylorJet.ftaylorSeries {d : ℕ} {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {f : Covariate d → F}
    {p : Covariate d → FormalMultilinearSeries ℝ (Covariate d) F}
    (h : InteriorTaylorJet k f p) : HasFTaylorSeriesUpToOn k f p (cube d) where
  zero_eq := h.zero_eq
  cont m hm := h.cont m (by exact_mod_cast hm)
  fderivWithin m hm x hx := by
    have hmk : m < k := by exact_mod_cast hm
    have hc := h.cont (m + 1) (Nat.succ_le_of_lt hmk)
    have hcc : ContinuousOn (fun y => (p y (m + 1)).curryLeft) (cube d) :=
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (m + 1) => Covariate d) F).continuous.comp_continuousOn hc
    exact hasFDerivWithinAt_cube_of_interior_jet
      (h.cont m hmk.le) hcc (h.fderivInterior m hmk) hx

theorem InteriorTaylorJet.contDiffOn {d : ℕ} {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {f : Covariate d → F}
    {p : Covariate d → FormalMultilinearSeries ℝ (Covariate d) F}
    (h : InteriorTaylorJet k f p) : ContDiffOn ℝ k f (cube d) :=
  h.ftaylorSeries.contDiffOn

/-- The boundary jet values agree exactly with the derivatives used in the
model, rather than merely giving comparable operator norms. -/
theorem InteriorTaylorJet.eq_iteratedFDerivWithin {d : ℕ} {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {f : Covariate d → F}
    {p : Covariate d → FormalMultilinearSeries ℝ (Covariate d) F}
    (h : InteriorTaylorJet k f p) {q : ℕ} (hq : q ≤ k)
    {x : Covariate d} (hx : x ∈ cube d) :
    p x q = iteratedFDerivWithin ℝ q f (cube d) x :=
  h.ftaylorSeries.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (by exact_mod_cast hq) (uniqueDiffOn_cube d) hx

theorem InteriorTaylorJet.coordinate_eq {d : ℕ} {k : ℕ} {f : Covariate d → ℝ}
    {p : Covariate d → FormalMultilinearSeries ℝ (Covariate d) ℝ}
    (h : InteriorTaylorJet k f p) {q : ℕ} (hq : q ≤ k)
    (σ : Fin q → Fin d) {x : Covariate d} (hx : x ∈ cube d) :
    p x q (fun i => EuclideanSpace.single (σ i) 1) = coordinateDerivative f q σ x := by
  rw [h.eq_iteratedFDerivWithin hq hx]
  rfl

/-- Use continuous interior derivative jets as the regularity test, keeping
exactly the same coordinate coefficients and sum-of-maxima normalization. -/
def interiorJetHolderNorm {d : ℕ} (f : Covariate d → ℝ) (t : ℝ) : ℝ≥0∞ := by
  classical
  exact if 0 < t ∧ InteriorJet (holderOrder t) f then
    classicalDerivativeSup f (holderOrder t) + classicalHolderSeminorm f t else ∞

/-- The regularity test can be replaced without changing the norm or radius. -/
theorem holderNorm_eq_interiorJetHolderNorm {d : ℕ} (f : Covariate d → ℝ) (t : ℝ) :
    holderNorm f t = interiorJetHolderNorm f t := by
  rw [holderNorm_eq_classicalHolderNorm]
  unfold classicalHolderNorm interiorJetHolderNorm
  rw [interiorJet_iff_contDiffOn]

/-- In the entire range 0 < t ≤ 1, no positive-order boundary derivatives occur. -/
theorem holderOrder_eq_zero_of_le_one {t : ℝ} (ht : t ≤ 1) : holderOrder t = 0 := by
  exact Nat.sub_eq_zero_of_le (Nat.ceil_le.mpr (by simpa using ht))

/-- The low-smoothness regularity gate is exactly continuity on the closed cube. -/
theorem holderRegularity_le_one_iff {d : ℕ} (f : Covariate d → ℝ) {t : ℝ} (ht : t ≤ 1) :
    ContDiffOn ℝ (holderOrder t) f (cube d) ↔ ContinuousOn f (cube d) := by
  rw [holderOrder_eq_zero_of_le_one ht]
  simp

end RoughRegime.Model
