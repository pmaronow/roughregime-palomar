module

public import RoughRegime.GlobalProduct
public import RoughRegime.PoissonMeasure


@[expose] public section
/-! The literal nonlinear spatial target decomposes into centered local block
responses. Centering cancels the varying individual block density masses. -/
noncomputable section
namespace RoughRegime.LatticePriors
open MeasureTheory Set
open scoped BigOperators ContDiff
variable {D N : ℕ}

def localCenteredResponse (F : (ℝ × ℝ) → ℝ) (p0 r0 h Au Av : ℝ)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (theta : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D+1) → ℝ)
    (su sv gate : GridPair D N → ℝ) (b : GridBlock D N) (y : Model.Covariate (D+1)) : ℝ :=
  let p := blockDensity p0 r0 h (theta b.1) (phase b.1) outer (Lower.sign b.2)
  p y*(F (blockProfile Au (su b.1) (gate b.1) inner p y,
          blockProfile Av (sv b.1) (gate b.1) inner p y)-F 0)

def globalNonlinearTarget (F : (ℝ × ℝ) → ℝ) (offset ell p0 r0 h Au Av : ℝ)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (theta : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D+1) → ℝ)
    (su sv gate : GridPair D N → ℝ) : ℝ :=
  ∫ x, globalDensity offset ell p0 r0 h outer theta phase x*
    F (globalProfile offset ell p0 r0 h Au inner outer theta phase su gate x,
       globalProfile offset ell p0 r0 h Av inner outer theta phase sv gate x)
    ∂Model.cubeVolume (D+1)

theorem localCenteredResponse_zero (F : (ℝ × ℝ) → ℝ) (p0 r0 h Au Av : ℝ)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (hin : ∀ y, y∉unitCubeOpen (D+1) → inner y=0)
    (theta : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D+1) → ℝ)
    (su sv gate : GridPair D N → ℝ) (b : GridBlock D N) (y : Model.Covariate (D+1))
    (hy : y∉unitCubeOpen (D+1)) :
    localCenteredResponse F p0 r0 h Au Av inner outer theta phase su sv gate b y=0 := by
  simp [localCenteredResponse,blockProfile,hin y hy,show (0 : ℝ × ℝ)=(0,0) from rfl]

theorem globalCenteredResponse_eq_sum (F : (ℝ × ℝ) → ℝ)
    (offset ell p0 r0 h Au Av : ℝ) (hell : 0<ell)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (hin : ∀ y, y∉unitCubeOpen (D+1) → inner y=0)
    (hout : ∀ y, y∉unitCubeOpen (D+1) → outer y=0)
    (theta : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D+1) → ℝ)
    (su sv gate : GridPair D N → ℝ) (x : Model.Covariate (D+1)) :
    globalDensity offset ell p0 r0 h outer theta phase x*
      (F (globalProfile offset ell p0 r0 h Au inner outer theta phase su gate x,
          globalProfile offset ell p0 r0 h Av inner outer theta phase sv gate x)-F 0) =
    ∑ b : GridBlock D N, localCenteredResponse F p0 r0 h Au Av inner outer theta phase su sv gate b
      (gridCoords offset ell b x) := by
  by_cases hx : ∃ b : GridBlock D N, x∈gridBlockOpen offset ell b
  · obtain ⟨b,hb⟩ := hx
    rw [globalDensity_eq_local offset ell p0 r0 h hell outer hout theta phase b x hb,
      globalProfile_eq_local offset ell p0 r0 h Au hell inner outer hin hout theta phase su gate b x hb,
      globalProfile_eq_local offset ell p0 r0 h Av hell inner outer hin hout theta phase sv gate b x hb]
    rw [Finset.sum_eq_single b]
    · rfl
    · intro a _ hab
      apply localCenteredResponse_zero F p0 r0 h Au Av inner outer hin theta phase su sv gate a
      intro hxa
      exact Set.disjoint_left.mp (gridBlockOpen_pairwiseDisjoint D N offset ell hell (Ne.symm hab)) hb hxa
    · simp
  · rw [globalProfile_outside offset ell p0 r0 h Au inner outer hin theta phase su gate x (not_exists.mp hx),
      globalProfile_outside offset ell p0 r0 h Av inner outer hin theta phase sv gate x (not_exists.mp hx)]
    simp only [show (0 : ℝ × ℝ)=(0,0) from rfl,sub_self,mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro b _
    exact localCenteredResponse_zero F p0 r0 h Au Av inner outer hin theta phase su sv gate b _ (not_exists.mp hx b)

/-- The actual normalized nonlinear target equals its baseline plus the true
scaled sum of centered local block target integrals. -/
theorem globalNonlinearTarget_integral (F : (ℝ × ℝ) → ℝ)
    (offset ell p0 r0 h Au Av : ℝ) (hell : 0<ell)
    (hoff : 0≤offset) (hsize : offset+ell*(2*N : ℕ)≤1)
    (inner outer : Model.Covariate (D+1) → ℝ)
    (hin : ∀ y, y∉unitCubeOpen (D+1) → inner y=0)
    (hout : ∀ y, y∉unitCubeOpen (D+1) → outer y=0)
    (theta : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D+1) → ℝ)
    (su sv gate : GridPair D N → ℝ)
    (hp : Integrable (globalDensity offset ell p0 r0 h outer theta phase) (Model.cubeVolume (D+1)))
    (hnorm : (∫ x, globalDensity offset ell p0 r0 h outer theta phase x ∂Model.cubeVolume (D+1))=1)
    (hmeas : ∀ b, Measurable (localCenteredResponse F p0 r0 h Au Av inner outer theta phase su sv gate b))
    (K : ℝ) (hbound : ∀ b y, |localCenteredResponse F p0 r0 h Au Av inner outer theta phase su sv gate b y|≤K) :
    globalNonlinearTarget F offset ell p0 r0 h Au Av inner outer theta phase su sv gate =
      F 0+ell^(D+1)*∑ b : GridBlock D N,
        ∫ y, localCenteredResponse F p0 r0 h Au Av inner outer theta phase su sv gate b y ∂Model.cubeVolume (D+1) := by
  let L := localCenteredResponse F p0 r0 h Au Av inner outer theta phase su sv gate
  have hi (b : GridBlock D N) : Integrable (fun x => L b (gridCoords offset ell b x)) (Model.cubeVolume (D+1)) :=
    PoissonMeasure.bounded_integrable _ _ ((hmeas b).comp (gridCoords_smooth offset ell b).continuous.measurable)
      K (fun x => hbound b _)
  have his := integrable_finsetSum Finset.univ (fun b _ => hi b)
  have heq := globalCenteredResponse_eq_sum F offset ell p0 r0 h Au Av hell inner outer hin hout theta phase su sv gate
  have hic : Integrable (fun x => globalDensity offset ell p0 r0 h outer theta phase x*
      (F (globalProfile offset ell p0 r0 h Au inner outer theta phase su gate x,
          globalProfile offset ell p0 r0 h Av inner outer theta phase sv gate x)-F 0)) (Model.cubeVolume (D+1)) := by
    apply his.congr
    exact Filter.Eventually.of_forall fun x => (heq x).symm
  have hid : (fun x => globalDensity offset ell p0 r0 h outer theta phase x*
      F (globalProfile offset ell p0 r0 h Au inner outer theta phase su gate x,
         globalProfile offset ell p0 r0 h Av inner outer theta phase sv gate x)) =
      fun x => globalDensity offset ell p0 r0 h outer theta phase x*
        (F (globalProfile offset ell p0 r0 h Au inner outer theta phase su gate x,
            globalProfile offset ell p0 r0 h Av inner outer theta phase sv gate x)-F 0)+
        F 0*globalDensity offset ell p0 r0 h outer theta phase x := by funext x; ring
  unfold globalNonlinearTarget
  rw [hid,integral_add hic (hp.const_mul (F 0)),integral_const_mul,hnorm,mul_one]
  simp_rw [heq]
  rw [integral_finsetSum Finset.univ (fun b _ => hi b)]
  dsimp only [L]
  simp_rw [grid_pull_integral_cube offset ell hell _ hoff hsize _
    (localCenteredResponse_zero F p0 r0 h Au Av inner outer hin theta phase su sv gate _)]
  rw [←Finset.mul_sum]
  exact add_comm _ _

theorem localCenteredResponse_measurable (F : (ℝ × ℝ) → ℝ) (hF : Measurable F)
    (p0 r0 h Au Av : ℝ) (inner outer : Model.Covariate (D+1) → ℝ)
    (hi : Measurable inner) (ho : Measurable outer)
    (theta : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D+1) → ℝ)
    (hp : ∀ k, Measurable (phase k)) (su sv gate : GridPair D N → ℝ) (b : GridBlock D N) :
    Measurable (localCenteredResponse F p0 r0 h Au Av inner outer theta phase su sv gate b) := by
  have hpd : Measurable (blockDensity p0 r0 h (theta b.1) (phase b.1) outer (Lower.sign b.2)) := by
    unfold blockDensity blockOscillatingDensity
    fun_prop
  unfold localCenteredResponse blockProfile
  fun_prop

/-- A pointwise small response yields a centered local target bound; this
uses the true local density, including its varying individual block mass. -/
theorem localCenteredResponse_bound (F : (ℝ × ℝ) → ℝ)
    (p0 r0 h Au Av : ℝ) (inner outer : Model.Covariate (D+1) → ℝ)
    (theta : GridPair D N → ℝ) (phase : GridPair D N → Model.Covariate (D+1) → ℝ)
    (su sv gate : GridPair D N → ℝ) (b : GridBlock D N) (y : Model.Covariate (D+1))
    (P B : ℝ) (hP : 0≤P)
    (hpd : |blockDensity p0 r0 h (theta b.1) (phase b.1) outer (Lower.sign b.2) y|≤P)
    (hFb : |F (blockProfile Au (su b.1) (gate b.1) inner
                    (blockDensity p0 r0 h (theta b.1) (phase b.1) outer (Lower.sign b.2)) y,
                  blockProfile Av (sv b.1) (gate b.1) inner
                    (blockDensity p0 r0 h (theta b.1) (phase b.1) outer (Lower.sign b.2)) y)-F 0|≤B) :
    |localCenteredResponse F p0 r0 h Au Av inner outer theta phase su sv gate b y|≤P*B := by
  unfold localCenteredResponse
  rw [abs_mul]
  exact mul_le_mul hpd hFb (abs_nonneg _) hP

end RoughRegime.LatticePriors
