module

public import RoughRegime.LatticeHolder


@[expose] public section
/-! Disjoint-support gluing of actual Hölder functions. The norm bound does
not grow with the number of blocks. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace RoughRegime.Model

/-- A disjointly supported finite family has at most one nonzero value at a
point. -/
lemma disjoint_sum_value_le {ι X : Type*} (S : Finset ι) (f : ι → X → ℝ)
    (hdis : (S : Set ι).Pairwise (fun i j => Disjoint (Function.support (f i)) (Function.support (f j))))
    (H : ℝ) (hH : 0≤H) (x : X) (hb : ∀ i∈S, |f i x|≤H) : |∑ i∈S, f i x|≤H := by
  classical
  by_cases he : ∃ i∈S, f i x≠0
  · obtain ⟨i,hi,hix⟩ := he
    rw [Finset.sum_eq_single i]
    · exact hb i hi
    · intro j hj hji
      by_contra hjx
      exact Set.disjoint_left.mp (hdis hi hj (Ne.symm hji)) hix hjx
    · exact fun hn => (hn hi).elim
  · have hz : ∀ i∈S, f i x=0 := by simpa using he
    simp only [Finset.sum_eq_zero hz,abs_zero]
    exact hH

/-- Differences of disjointly supported finite sums cost at most two
individual moduli, including points in distinct blocks. -/
lemma disjoint_sum_difference_le {ι X : Type*} (S : Finset ι) (f : ι → X → ℝ)
    (hdis : (S : Set ι).Pairwise (fun i j => Disjoint (Function.support (f i)) (Function.support (f j))))
    (B : ℝ) (hB : 0≤B) (x y : X) (hb : ∀ i∈S, |f i x-f i y|≤B) :
    |(∑ i∈S, f i x)-(∑ i∈S, f i y)|≤2*B := by
  classical
  have single (i : ι) (hi : i∈S) (v : X) (hiv : f i v≠0) : ∑ j∈S, f j v=f i v := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      by_contra hjv
      exact Set.disjoint_left.mp (hdis hi hj (Ne.symm hji)) hiv hjv
    · exact fun hn => (hn hi).elim
  by_cases hx : ∃ i∈S, f i x≠0
  · obtain ⟨i,hi,hix⟩ := hx
    rw [single i hi x hix]
    by_cases hy : ∃ j∈S, f j y≠0
    · obtain ⟨j,hj,hjy⟩ := hy
      rw [single j hj y hjy]
      by_cases hij : i=j
      · subst j
        exact (hb i hi).trans (by linarith)
      · have hiy : f i y=0 := by
          by_contra hiy
          exact Set.disjoint_left.mp (hdis hi hj hij) hiy hjy
        have hjx : f j x=0 := by
          by_contra hjx
          exact Set.disjoint_left.mp (hdis hi hj hij) hix hjx
        have hbi := hb i hi
        have hbj := hb j hj
        rw [hiy,sub_zero] at hbi
        rw [hjx,zero_sub,abs_neg] at hbj
        exact (abs_sub _ _).trans (by linarith)
    · have hz : ∀ j∈S, f j y=0 := by simpa using hy
      rw [Finset.sum_eq_zero hz]
      have hyi := hz i hi
      exact (by simpa [hyi] using hb i hi : |f i x-0|≤B).trans (by linarith)
  · have hz : ∀ i∈S, f i x=0 := by simpa using hx
    rw [Finset.sum_eq_zero hz]
    by_cases hy : ∃ j∈S, f j y≠0
    · obtain ⟨j,hj,hjy⟩ := hy
      rw [single j hj y hjy]
      exact (by simpa [hz j hj] using hb j hj : |0-f j y|≤B).trans (by linarith)
    · have hzy : ∀ j∈S, f j y=0 := by simpa using hy
      rw [Finset.sum_eq_zero hzy]
      simpa using mul_nonneg (by norm_num : (0:ℝ)≤2) hB

/-- Actual smooth Hölder functions with disjoint topological supports glue
with the exact source constant3, uniformly in the number of blocks. -/
theorem holderNorm_disjoint_sum_le {d : ℕ} {ι : Type*} (S : Finset ι)
    (f : ι → Covariate d → ℝ) (t H : ℝ) (ht : 0<t) (hH : 0≤H)
    (hf : ∀ i∈S, ContDiff ℝ ∞ (f i))
    (hbound : ∀ i∈S, holderNorm (f i) t ≤ ENNReal.ofReal H)
    (hdis : (S : Set ι).Pairwise (fun i j => Disjoint (tsupport (f i)) (tsupport (f j)))) :
    holderNorm (fun x => ∑ i∈S, f i x) t ≤ ENNReal.ofReal (3*H) := by
  have hsmooth : ContDiff ℝ ∞ (fun x => ∑ i∈S, f i x) := ContDiff.sum hf
  let J (q : ℕ) (σ : Fin q → Fin d) (i : ι) (x : Covariate d) :=
    iteratedFDeriv ℝ q (f i) x (fun j => EuclideanSpace.single (σ j) 1)
  have hsupp (q : ℕ) (σ : Fin q → Fin d) (i : ι) : Function.support (J q σ i) ⊆ tsupport (f i) := by
    intro x hx
    apply support_iteratedFDeriv_subset (𝕜 := ℝ) (f := f i) q
    intro hz
    apply hx
    dsimp [J]
    rw [hz]
    simp
  have hdisJ (q : ℕ) (σ : Fin q → Fin d) : (S : Set ι).Pairwise (fun i j => Disjoint (Function.support (J q σ i)) (Function.support (J q σ j))) := by
    intro i hi j hj hij
    exact (hdis hi hj hij).mono (hsupp q σ i) (hsupp q σ j)
  have hcoord (q : ℕ) (σ : Fin q → Fin d) (i : ι) (hi : i∈S) (x : Covariate d) (hx : x∈cube d) :
      coordinateDerivative (f i) q σ x=J q σ i x :=
    coordinateDerivative_eq_iteratedFDeriv (f i) q σ x hx ((hf i hi).of_le (by simp)).contDiffAt
  have hsum (q : ℕ) (σ : Fin q → Fin d) (x : Covariate d) (hx : x∈cube d) :
      coordinateDerivative (fun x => ∑ i∈S, f i x) q σ x=∑ i∈S, J q σ i x := by
    rw [coordinateDerivative_eq_iteratedFDeriv _ q σ x hx (hsmooth.of_le (by simp)).contDiffAt,
      iteratedFDeriv_fun_sum_apply (fun i hi => ((hf i hi).of_le (by simp)).contDiffAt),sum_apply]
  have hsup : derivativeSup (fun x => ∑ i∈S, f i x) (holderOrder t) ≤ ENNReal.ofReal H := by
    apply iSup_le; intro q
    apply iSup_le; intro hq
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    apply ENNReal.ofReal_le_ofReal
    rw [hsum q σ x hx]
    apply disjoint_sum_value_le S (J q σ) (hdisJ q σ) H hH x
    intro i hi
    rw [← hcoord q σ i hi x hx]
    exact holderBall_coordinate_bound (f i) t H hH (hbound i hi) q hq σ x hx
  have hsem : holderSeminorm (fun x => ∑ i∈S, f i x) t ≤ ENNReal.ofReal (2*H) := by
    apply iSup_le; intro σ
    apply iSup_le; intro x
    apply iSup_le; intro hx
    apply iSup_le; intro y
    apply iSup_le; intro hy
    apply iSup_le; intro hxy
    apply ENNReal.ofReal_le_ofReal
    have hnorm : 0<‖x-y‖^holderExponent t := Real.rpow_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)) _
    apply (div_le_iff₀ hnorm).mpr
    rw [hsum _ σ x hx,hsum _ σ y hy]
    have he := disjoint_sum_difference_le S (J (holderOrder t) σ) (hdisJ _ σ)
      (H*‖x-y‖^holderExponent t) (mul_nonneg hH hnorm.le) x y (fun i hi => by
        rw [← hcoord _ σ i hi x hx,← hcoord _ σ i hi y hy]
        exact holderBall_coordinate_modulus (f i) t H hH (hbound i hi) σ x y hx hy)
    exact he.trans_eq (by ring)
  unfold holderNorm
  rw [ite_eq_left ⟨ht,(hsmooth.of_le (by simp)).contDiffOn⟩]
  calc
    _ ≤ ENNReal.ofReal H+ENNReal.ofReal (2*H) := add_le_add hsup hsem
    _ = _ := by rw [← ENNReal.ofReal_add hH (by positivity)]; congr 1; ring

end RoughRegime.Model
