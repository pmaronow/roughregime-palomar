module

public import RoughRegime.TreatmentEffectRange
public import RoughRegime.ApplicationsPilot


@[expose] public section
/-! The actual bounded outcome/treatment empirical pilot for ATT and ATU. -/
noncomputable section
open MeasureTheory Set ProbabilityTheory
open scoped BigOperators
namespace RoughRegime.Applications.MAR
set_option maxHeartbeats 1000000

def effectPilot (d : ℕ) : Fin 2→(Model.Covariate d × TreatmentResponse)→ℝ :=
  ![fun o=>(o.2.2:ℝ),fun o=>armIndicator true o.2]

theorem effectPilot_measurable (d : ℕ) (j : Fin 2) : Measurable (effectPilot d j) := by
  fin_cases j
  · exact measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  · exact (armIndicator_measurable true).comp measurable_snd

theorem effectPilot_range (d : ℕ) (j : Fin 2) (o : Model.Covariate d × TreatmentResponse) :
    effectPilot d j o ∈ Icc 0 1 := by
  fin_cases j
  · exact o.2.2.property
  · exact armIndicator_range true o.2

theorem effectPilot_memLp (d : ℕ) (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse))
    (j : Fin 2) : MemLp (effectPilot d j) 2 (P : Measure _) :=
  Applications.bounded_memLp _ _ (effectPilot_measurable d j) 1 (fun o=>by
    rw [abs_of_nonneg (effectPilot_range d j o).1]
    exact (effectPilot_range d j o).2)

theorem effectPilot_mean_range (d : ℕ) (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse))
    (j : Fin 2) : (∫o,effectPilot d j o ∂(P : Measure _)) ∈ Icc 0 1 := by
  have hi := (effectPilot_memLp d P j).integrable one_le_two
  refine ⟨integral_nonneg (fun o=>(effectPilot_range d j o).1),?_⟩
  have h := integral_mono_ae hi (integrable_const (1:ℝ))
    (Filter.Eventually.of_forall (fun o=>(effectPilot_range d j o).2))
  simpa only [integral_const,probReal_univ,one_smul] using h

theorem effectPilot_variance (d : ℕ) (P : ProbabilityMeasure (Model.Covariate d × TreatmentResponse)) :
    (∫o,‖Applications.responseVector (effectPilot d) o-Applications.momentMean (P : Measure _) (effectPilot d)‖^2
      ∂(P : Measure _)) ≤ (2:ℝ)^2 := by
  have hnorm (o : Model.Covariate d × TreatmentResponse) :
      ‖Applications.responseVector (effectPilot d) o-Applications.momentMean (P : Measure _) (effectPilot d)‖^2 ≤ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    have hb (j : Fin 2) : (effectPilot d j o-(∫o,effectPilot d j o ∂(P : Measure _)))^2 ≤ 1 := by
      have hr := effectPilot_range d j o
      have hm := effectPilot_mean_range d P j
      nlinarith only [hr.1,hr.2,hm.1,hm.2]
    change ∑ j : Fin 2,(effectPilot d j o-(∫o,effectPilot d j o ∂(P : Measure _)))^2 ≤ 2
    rw [Fin.sum_univ_two]
    linarith [hb 0,hb 1]
  have hi : Integrable (fun o=>‖Applications.responseVector (effectPilot d) o-
      Applications.momentMean (P : Measure _) (effectPilot d)‖^2) (P : Measure _) := by
    have he : (fun o=>‖Applications.responseVector (effectPilot d) o-
        Applications.momentMean (P : Measure _) (effectPilot d)‖^2) =
        (fun o=>∑ j : Fin 2,(effectPilot d j o-(∫o,effectPilot d j o ∂(P : Measure _)))^2) := by
      funext o
      rw [EuclideanSpace.real_norm_sq_eq]
      rfl
    rw [he]
    exact integrable_finsetSum _ (fun j _=>(effectPilot_memLp d P j |>.sub (memLp_const _)).integrable_sq)
  have h := integral_mono_ae hi (integrable_const (2:ℝ)) (Filter.Eventually.of_forall hnorm)
  norm_num [integral_const,probReal_univ] at h ⊢
  linarith

theorem pilot_coordinate_dist {lo hi : Fin 2→ℝ}
    (q r : Applications.momentRectangle lo hi) (j : Fin 2) : |q.val j-r.val j| ≤ dist q r := by
  simpa only [Real.dist_eq,Subtype.dist_eq] using PiLp.dist_apply_le q.val r.val j

def attReconstruct : Icc (-1:ℝ) 1→Applications.momentRectangle (fun _ : Fin 2=>0) (fun _=>1)→ℝ :=
  fun a q=>q.val 0-q.val 1*(a:ℝ)
def atuReconstruct : Icc (-1:ℝ) 1→Applications.momentRectangle (fun _ : Fin 2=>0) (fun _=>1)→ℝ :=
  fun a q=>q.val 0+(1-q.val 1)*(a:ℝ)

theorem product_reconstruct_lipschitz (a b : Icc (-1:ℝ) 1)
    (q r : Applications.momentRectangle (fun _ : Fin 2=>0) (fun _=>1)) :
    |q.val 1*(a:ℝ)-r.val 1*(b:ℝ)| ≤ |(a:ℝ)-b|+dist q r := by
  have hm : |q.val 1|≤1 := by rw [abs_of_nonneg (q.property 1).1]; exact (q.property 1).2
  have hb : |(b:ℝ)|≤1 := abs_le.mpr b.property
  calc
    _ = |q.val 1*((a:ℝ)-b)+(q.val 1-r.val 1)*(b:ℝ)| := by congr 1;ring
    _ ≤ |q.val 1*((a:ℝ)-b)|+|(q.val 1-r.val 1)*(b:ℝ)| := abs_add_le _ _
    _ = |q.val 1| * |(a:ℝ)-b|+|q.val 1-r.val 1| * |(b:ℝ)| := by rw [abs_mul,abs_mul]
    _ ≤ 1*|(a:ℝ)-b|+dist q r*1 := add_le_add
      (mul_le_mul_of_nonneg_right hm (abs_nonneg _))
      (mul_le_mul (pilot_coordinate_dist q r 1) hb (abs_nonneg _) dist_nonneg)
    _ = _ := by ring

theorem attReconstruct_lipschitz (a b : Icc (-1:ℝ) 1)
    (q r : Applications.momentRectangle (fun _ : Fin 2=>0) (fun _=>1)) :
    |attReconstruct a q-attReconstruct b r| ≤ 2*(|(a:ℝ)-b|+dist q r) := by
  calc
    _ ≤ |q.val 0-r.val 0|+|q.val 1*(a:ℝ)-r.val 1*(b:ℝ)| := by
      dsimp [attReconstruct]
      have he : q.val 0-q.val 1*(a:ℝ)-(r.val 0-r.val 1*(b:ℝ)) =
        (q.val 0-r.val 0)-(q.val 1*(a:ℝ)-r.val 1*(b:ℝ)) := by ring
      rw [he]
      exact abs_sub _ _
    _ ≤ dist q r+(|(a:ℝ)-b|+dist q r) := add_le_add (pilot_coordinate_dist q r 0)
      (product_reconstruct_lipschitz a b q r)
    _ ≤ _ := by linarith [abs_nonneg ((a:ℝ)-b)]

theorem atuReconstruct_lipschitz (a b : Icc (-1:ℝ) 1)
    (q r : Applications.momentRectangle (fun _ : Fin 2=>0) (fun _=>1)) :
    |atuReconstruct a q-atuReconstruct b r| ≤ 3*(|(a:ℝ)-b|+dist q r) := by
  calc
    _ ≤ |q.val 0-r.val 0|+|(a:ℝ)-b|+|q.val 1*(a:ℝ)-r.val 1*(b:ℝ)| := by
      dsimp [atuReconstruct]
      have h := (abs_sub ((q.val 0-r.val 0)+((a:ℝ)-b))
        (q.val 1*(a:ℝ)-r.val 1*(b:ℝ))).trans
        (add_le_add (abs_add_le (q.val 0-r.val 0) ((a:ℝ)-b)) le_rfl)
      have he : q.val 0+(1-q.val 1)*(a:ℝ)-(r.val 0+(1-r.val 1)*(b:ℝ)) =
        ((q.val 0-r.val 0)+((a:ℝ)-b))-(q.val 1*(a:ℝ)-r.val 1*(b:ℝ)) := by ring
      rw [he]
      exact h
    _ ≤ dist q r+|(a:ℝ)-b|+(|(a:ℝ)-b|+dist q r) := add_le_add
      (add_le_add (pilot_coordinate_dist q r 0) le_rfl) (product_reconstruct_lipschitz a b q r)
    _ ≤ _ := by linarith [abs_nonneg ((a:ℝ)-b),dist_nonneg (x:=q) (y:=r)]

end RoughRegime.Applications.MAR
