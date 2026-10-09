module

public import RoughRegime.NativeSignBridge
public import RoughRegime.OddTaylor


@[expose] public section
/-! Genuine conditional-sign averaging of nonlinear targets. The odd/odd
Taylor remainder is derived from local C4 regularity. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace RoughRegime.PoissonMeasure
set_option backward.isDefEq.respectTransparency false

/-- Averaging an arbitrary nonlinear response against the two actual sign
PMFs isolates its odd/odd part. -/
theorem signLaw_function_difference (F : OddTaylor.Plane → ℝ) (u v c : ℝ)
    (hc : |c| ≤ 1) :
    (∫ st, F (Lower.sign st.1*u, Lower.sign st.2*v)
      ∂(LatticeFourier.signLaw c hc).toMeasure) -
    (∫ st, F (Lower.sign st.1*u, Lower.sign st.2*v)
      ∂(LatticeFourier.signLaw (-c) (by simpa only [abs_neg] using hc)).toMeasure) =
    2*c*OddTaylor.oddOdd F u v := by
  have he (d : ℝ) (hd : |d| ≤ 1) :
      (∫ st, F (Lower.sign st.1*u, Lower.sign st.2*v)
        ∂(LatticeFourier.signLaw d hd).toMeasure) =
        ∑ st : Bool × Bool, Lower.signWeight d st.1 st.2 *
          F (Lower.sign st.1*u, Lower.sign st.2*v) := by
    rw [PMF.integral_eq_sum]
    apply Finset.sum_congr rfl
    intro st _
    rw [LatticeFourier.signLaw_apply,
      ENNReal.toReal_ofReal (Lower.signWeight_nonneg hd st.1 st.2), smul_eq_mul]
  rw [he c hc, he (-c) (by simpa only [abs_neg] using hc)]
  simp [Lower.signWeight, Lower.sign, OddTaylor.oddOdd, Fintype.sum_prod_type]
  ring

def signAverage {H : Type*} (M : ℕ) (positive : Bool)
    (g : H × (ℝ × (Bool × Bool)) → ℝ) (p : H × ℝ) : ℝ :=
  ∑ st : Bool × Bool, Lower.signWeight
    ((if positive then 1 else -1)*Real.cos ((M : ℝ)*p.2)) st.1 st.2 * g (p.1,(p.2,st))

private theorem signAverage_measurable {H : Type*} [MeasurableSpace H]
    (M : ℕ) (positive : Bool) (g : H × (ℝ × (Bool × Bool)) → ℝ)
    (hg : Measurable g) : Measurable (signAverage M positive g) := by
  unfold signAverage
  apply Finset.measurable_sum
  intro st _
  apply Measurable.mul _ (hg.comp (measurable_fst.prodMk (measurable_snd.prodMk measurable_const)))
  unfold Lower.signWeight
  fun_prop

private theorem signAverage_bound {H : Type*} (M : ℕ) (positive : Bool)
    (g : H × (ℝ × (Bool × Bool)) → ℝ) (B : ℝ)
    (hb : ∀ q, |g q| ≤ B) (p : H × ℝ) : |signAverage M positive g p| ≤ B := by
  classical
  let c := (if positive then 1 else -1)*Real.cos ((M : ℝ)*p.2)
  have hc : |c| ≤ 1 := by cases positive <;> simpa [c] using Real.abs_cos_le_one ((M : ℝ)*p.2)
  have hs : (∑ st : Bool × Bool, Lower.signWeight c st.1 st.2) = 1 := by
    rw [Fintype.sum_prod_type]
    exact Lower.signWeight_sum c
  unfold signAverage
  change |∑ st : Bool × Bool, Lower.signWeight c st.1 st.2*g (p.1,(p.2,st))| ≤ B
  calc
    _ ≤ ∑ st : Bool × Bool, |Lower.signWeight c st.1 st.2*g (p.1,(p.2,st))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ st : Bool × Bool, Lower.signWeight c st.1 st.2*B := by
      apply Finset.sum_le_sum
      intro st _
      rw [abs_mul, abs_of_nonneg (Lower.signWeight_nonneg hc st.1 st.2)]
      exact mul_le_mul_of_nonneg_left (hb _) (Lower.signWeight_nonneg hc st.1 st.2)
    _ = B := by rw [← Finset.sum_mul, hs, one_mul]

/-- Exact nonlinear averaging under the genuine continuous-angle/sign prior.
No polynomial representation of the response is assumed. -/
theorem native_function_integral {H : Type*} [MeasurableSpace H]
    (ν : Measure H) [IsProbabilityMeasure ν] (M : ℕ) (positive : Bool)
    (g : H × (ℝ × (Bool × Bool)) → ℝ) (hg : Measurable g)
    (B : ℝ) (hb : ∀ q, |g q| ≤ B) :
    (∫ q, g q ∂ν.prod (LatticeFourier.angleSignLaw M positive)) =
      ∫ p : H × ℝ, signAverage M positive g p ∂ν.prod LatticePriors.angleUniform := by
  have hi := bounded_integrable (ν.prod (LatticeFourier.angleSignLaw M positive)) g hg B hb
  have hsi := bounded_integrable (ν.prod LatticePriors.angleUniform)
    (signAverage M positive g) (signAverage_measurable M positive g hg) B
    (signAverage_bound M positive g B hb)
  rw [integral_prod g hi, integral_prod _ hsi]
  apply integral_congr_ae
  filter_upwards with h
  have hgi := bounded_integrable (LatticeFourier.angleSignLaw M positive)
    (fun q => g (h,q)) (hg.comp (measurable_const.prodMk measurable_id)) B (fun q => hb (h,q))
  rw [LatticeFourier.angleSignLaw, Measure.integral_compProd hgi]
  rw [angleUniform_eq_native]
  apply integral_congr_ae
  filter_upwards with θ
  change (∫ st, g (h,(θ,st)) ∂(LatticeFourier.angularSignLaw M θ positive).toMeasure) = _
  rw [PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro st _
  unfold LatticeFourier.angularSignLaw
  rw [LatticeFourier.signLaw_apply,
    ENNReal.toReal_ofReal (Lower.signWeight_nonneg (by
      cases positive <;> simpa using Real.abs_cos_le_one ((M : ℝ)*θ)) st.1 st.2), smul_eq_mul]

/-- The literal nonlinear response with the source's paired signs. -/
def signedResponse {H : Type*} (F : OddTaylor.Plane → ℝ)
    (p u v : H × ℝ → ℝ) (q : H × (ℝ × (Bool × Bool))) : ℝ :=
  p (q.1,q.2.1) * F (Lower.sign q.2.2.1*u (q.1,q.2.1),
    Lower.sign q.2.2.2*v (q.1,q.2.1))

theorem signedResponse_measurable {H : Type*} [MeasurableSpace H]
    (F : OddTaylor.Plane → ℝ) (hF : Measurable F) (p u v : H × ℝ → ℝ)
    (hp : Measurable p) (hu : Measurable u) (hv : Measurable v) :
    Measurable (signedResponse F p u v) := by
  have hs : Measurable Lower.sign := Measurable.of_discrete
  unfold signedResponse
  fun_prop

/-- The true difference of nonlinear prior means is exactly its odd/odd
angular coefficient. -/
theorem native_oddOdd_difference {H : Type*} [MeasurableSpace H]
    (ν : Measure H) [IsProbabilityMeasure ν] (M : ℕ)
    (F : OddTaylor.Plane → ℝ) (p u v : H × ℝ → ℝ)
    (hg : Measurable (signedResponse F p u v))
    (B : ℝ) (hb : ∀ q, |signedResponse F p u v q| ≤ B) :
    (∫ q, signedResponse F p u v q ∂ν.prod (LatticeFourier.angleSignLaw M true)) -
    (∫ q, signedResponse F p u v q ∂ν.prod (LatticeFourier.angleSignLaw M false)) =
      ∫ z : H × ℝ, 2*Real.cos ((M : ℝ)*z.2)*p z*OddTaylor.oddOdd F (u z) (v z)
        ∂ν.prod LatticePriors.angleUniform := by
  rw [native_function_integral ν M true _ hg B hb, native_function_integral ν M false _ hg B hb]
  have hi (positive : Bool) := bounded_integrable (ν.prod LatticePriors.angleUniform)
    (signAverage M positive (signedResponse F p u v))
    (signAverage_measurable M positive _ hg) B
    (signAverage_bound M positive _ B hb)
  rw [← integral_sub (hi true) (hi false)]
  apply integral_congr_ae
  filter_upwards with z
  simp [signAverage, signedResponse, Fintype.sum_prod_type,
    Lower.signWeight, Lower.sign, OddTaylor.oddOdd]
  ring

theorem local_oddOdd_taylor_and_bound (F : OddTaylor.Plane → ℝ)
    (hF : ContDiffAt ℝ 4 F (0 : OddTaylor.Plane)) :
    ∃ ε > 0, ∃ C ≥ 0, ∃ B ≥ 0, ∀ u v, |u| ≤ ε → |v| ≤ ε →
      |OddTaylor.oddOdd F u v-OddTaylor.mixedDerivative F 0*u*v| ≤
        C * |u*v| * (u^2+v^2) ∧ |F (u,v)| ≤ B := by
  obtain ⟨ε,hε,C,hC,hrem⟩ := OddTaylor.oddOdd_taylor F hF
  have hcont : ContinuousAt (fun x : OddTaylor.Plane => |F x-F 0|) 0 :=
    (hF.continuousAt.sub continuousAt_const).abs
  have hnear : ∀ᶠ x in nhds (0 : OddTaylor.Plane), |F x-F 0| < 1 :=
    hcont.eventually (by simpa using (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨min ε (r/2), lt_min hε (by positivity), C,hC, |F 0|+1,by positivity,?_⟩
  intro u v hu hv
  refine ⟨hrem u v (hu.trans (min_le_left _ _)) (hv.trans (min_le_left _ _)),?_⟩
  have hn : ‖(u,v)‖ ≤ r/2 := by
    rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
    exact max_le (hu.trans (min_le_right _ _)) (hv.trans (min_le_right _ _))
  have hx := hball (y := (u,v)) (by simpa only [dist_eq_norm,sub_zero] using hn.trans_lt (by linarith : r/2 < r))
  calc
    |F (u,v)| ≤ |F (u,v)-F 0|+|F 0| := by
      have hh := abs_add_le (F (u,v)-F 0) (F 0)
      simpa using hh
    _ ≤ |F 0|+1 := by linarith

private theorem oddOdd_bound (F : OddTaylor.Plane → ℝ) (u v B : ℝ)
    (hpp : |F (u,v)| ≤ B) (hnp : |F (-u,v)| ≤ B)
    (hpn : |F (u,-v)| ≤ B) (hnn : |F (-u,-v)| ≤ B) :
    |OddTaylor.oddOdd F u v| ≤ B := by
  unfold OddTaylor.oddOdd
  rw [abs_div,abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mpr
  have h1 : |F (u,v)-F (-u,v)| ≤ |F (u,v)|+|F (-u,v)| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (F (u,v)) (-F (-u,v))
  have h2 : |F (u,v)-F (-u,v)-F (u,-v)| ≤ |F (u,v)-F (-u,v)|+|F (u,-v)| := by
    simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (F (u,v)-F (-u,v)) (-F (u,-v))
  have h3 := abs_add_le (F (u,v)-F (-u,v)-F (u,-v)) (F (-u,-v))
  linarith

/-- The nonlinear prior mean remainder in the reduction, under the genuine
continuous angle/sign laws. Constants come from actual local C4 regularity,
with no assumed Taylor expansion or mean-separation conclusion. -/
theorem native_oddOdd_taylor (F : OddTaylor.Plane → ℝ) (hmF : Measurable F)
    (hF : ContDiffAt ℝ 4 F (0 : OddTaylor.Plane)) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ {H : Type*} [MeasurableSpace H]
      (ν : Measure H) [IsProbabilityMeasure ν] (M : ℕ)
      (p u v : H × ℝ → ℝ) (_hp : Measurable p) (_hu : Measurable u) (_hv : Measurable v)
      (P Au Av : ℝ), 0 ≤ P → 0 ≤ Au → 0 ≤ Av → Au ≤ ε → Av ≤ ε →
      (∀ z, |p z| ≤ P) → (∀ z, |u z| ≤ Au) → (∀ z, |v z| ≤ Av) →
      |((∫ q, signedResponse F p u v q ∂ν.prod (LatticeFourier.angleSignLaw M true)) -
        (∫ q, signedResponse F p u v q ∂ν.prod (LatticeFourier.angleSignLaw M false))) -
        2*OddTaylor.mixedDerivative F 0*
          (∫ z : H × ℝ, Real.cos ((M : ℝ)*z.2)*p z*u z*v z
            ∂ν.prod LatticePriors.angleUniform)| ≤ C*P*Au*Av*(Au^2+Av^2) := by
  obtain ⟨ε,hε,C,hC,B,hB,hlocal⟩ := local_oddOdd_taylor_and_bound F hF
  refine ⟨ε,hε,2*C,by positivity,?_⟩
  intro H _ ν _ M p u v hp hu hv P Au Av hP hAu hAv hAue hAve hpB huB hvB
  let μ := ν.prod LatticePriors.angleUniform
  let d := OddTaylor.mixedDerivative F 0
  have hsign (s : Bool) (x : ℝ) : |Lower.sign s*x| = |x| := by cases s <;> simp [Lower.sign]
  have hFb (z : H × ℝ) (s t : Bool) : |F (Lower.sign s*u z,Lower.sign t*v z)| ≤ B :=
    (hlocal _ _ (by rw [hsign]; exact (huB z).trans hAue)
      (by rw [hsign]; exact (hvB z).trans hAve)).2
  have hg := signedResponse_measurable F hmF p u v hp hu hv
  have hgb (q : H × (ℝ × (Bool × Bool))) : |signedResponse F p u v q| ≤ P*B := by
    unfold signedResponse
    rw [abs_mul]
    exact mul_le_mul (hpB _) (hFb _ _ _) (abs_nonneg _) hP
  rw [native_oddOdd_difference ν M F p u v hg (P*B) hgb]
  have hob (z : H × ℝ) : |OddTaylor.oddOdd F (u z) (v z)| ≤ B := by
    apply oddOdd_bound
    · simpa [Lower.sign] using hFb z true true
    · simpa [Lower.sign] using hFb z false true
    · simpa [Lower.sign] using hFb z true false
    · simpa [Lower.sign] using hFb z false false
  have hpuv (z : H × ℝ) : |p z*u z*v z| ≤ P*Au*Av := by
    simp only [abs_mul]
    exact mul_le_mul (mul_le_mul (hpB z) (huB z) (abs_nonneg _) hP)
      (hvB z) (abs_nonneg _) (mul_nonneg hP hAu)
  have hodd : Integrable (fun z : H × ℝ => 2*Real.cos ((M : ℝ)*z.2)*p z*
      OddTaylor.oddOdd F (u z) (v z)) μ := by
    apply bounded_integrable μ _ (by unfold OddTaylor.oddOdd; fun_prop) (2*P*B)
    intro z
    simp only [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ 2*1*P*B := by gcongr; exact Real.abs_cos_le_one _; exact hpB z; exact hob z
      _ = _ := by ring
  have hlin0 : Integrable (fun z : H × ℝ => Real.cos ((M : ℝ)*z.2)*p z*u z*v z) μ := by
    apply bounded_integrable μ _ (by fun_prop) (P*Au*Av)
    intro z
    have hh := mul_le_mul (Real.abs_cos_le_one ((M : ℝ)*z.2)) (hpuv z)
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [abs_mul,one_mul,mul_assoc] using hh
  have hid : (∫ z : H × ℝ, 2*Real.cos ((M : ℝ)*z.2)*p z*OddTaylor.oddOdd F (u z) (v z) ∂μ) -
      2*d*(∫ z : H × ℝ, Real.cos ((M : ℝ)*z.2)*p z*u z*v z ∂μ) =
      ∫ z : H × ℝ, 2*Real.cos ((M : ℝ)*z.2)*p z*
        (OddTaylor.oddOdd F (u z) (v z)-d*u z*v z) ∂μ := by
    rw [← integral_const_mul,← integral_sub hodd (hlin0.const_mul (2*d))]
    apply integral_congr_ae
    filter_upwards with z
    ring
  change |(∫ z : H × ℝ, 2*Real.cos ((M : ℝ)*z.2)*p z*OddTaylor.oddOdd F (u z) (v z) ∂μ) -
      2*d*(∫ z : H × ℝ, Real.cos ((M : ℝ)*z.2)*p z*u z*v z ∂μ)| ≤ _
  rw [hid]
  have hb (z : H × ℝ) : ‖2*Real.cos ((M : ℝ)*z.2)*p z*
      (OddTaylor.oddOdd F (u z) (v z)-d*u z*v z)‖ ≤ (2*C)*P*Au*Av*(Au^2+Av^2) := by
    have hr := (hlocal (u z) (v z) ((huB z).trans hAue) ((hvB z).trans hAve)).1
    have huv : |u z*v z| ≤ Au*Av := by rw [abs_mul]; exact mul_le_mul (huB z) (hvB z) (abs_nonneg _) hAu
    have hus : (u z)^2 ≤ Au^2 := by nlinarith [sq_abs (u z),abs_nonneg (u z),huB z]
    have hvs : (v z)^2 ≤ Av^2 := by nlinarith [sq_abs (v z),abs_nonneg (v z),hvB z]
    rw [Real.norm_eq_abs,abs_mul,abs_mul,abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      _ ≤ 2*1*P*(C*(Au*Av)*(Au^2+Av^2)) := by
        gcongr
        · exact Real.abs_cos_le_one _
        · exact hpB z
        · exact hr.trans (by gcongr)
      _ = _ := by ring
  have hh := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)
  simpa only [Real.norm_eq_abs,measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using hh

/-- The actual bilinear target prior difference has the expected Fourier
coefficient, under the same genuine sign laws. -/
theorem native_bilinear_difference {H : Type*} [MeasurableSpace H]
    (ν : Measure H) [IsProbabilityMeasure ν] (M : ℕ)
    (p u v : H × ℝ → ℝ) (hp : Measurable p) (hu : Measurable u) (hv : Measurable v)
    (P Au Av : ℝ) (hP : 0 ≤ P) (hAu : 0 ≤ Au) (_hAv : 0 ≤ Av)
    (hpB : ∀ z, |p z| ≤ P) (huB : ∀ z, |u z| ≤ Au) (hvB : ∀ z, |v z| ≤ Av) :
    (∫ q, signedResponse (fun x => x.1*x.2) p u v q ∂ν.prod (LatticeFourier.angleSignLaw M true)) -
    (∫ q, signedResponse (fun x => x.1*x.2) p u v q ∂ν.prod (LatticeFourier.angleSignLaw M false)) =
      2*(∫ z : H × ℝ, Real.cos ((M : ℝ)*z.2)*p z*u z*v z ∂ν.prod LatticePriors.angleUniform) := by
  have hg := signedResponse_measurable (fun x => x.1*x.2) (measurable_fst.mul measurable_snd) p u v hp hu hv
  have hb (q : H × (ℝ × (Bool × Bool))) :
      |signedResponse (fun x => x.1*x.2) p u v q| ≤ P*Au*Av := by
    unfold signedResponse
    dsimp
    simp only [abs_mul,show ∀ s : Bool, |Lower.sign s| = 1 from fun s => by cases s <;> simp [Lower.sign],one_mul]
    have hh := mul_le_mul (hpB (q.1,q.2.1))
      (mul_le_mul (huB (q.1,q.2.1)) (hvB (q.1,q.2.1)) (abs_nonneg _) hAu)
      (by positivity : 0 ≤ |u (q.1,q.2.1)| * |v (q.1,q.2.1)|) hP
    simpa only [mul_assoc] using hh
  rw [native_oddOdd_difference ν M (fun x => x.1*x.2) p u v hg (P*Au*Av) hb,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with z
  unfold OddTaylor.oddOdd
  dsimp
  ring

/-- The remainder is stated directly using the true nonlinear and bilinear
prior means. -/
theorem native_target_taylor_error (F : OddTaylor.Plane → ℝ) (hmF : Measurable F)
    (hF : ContDiffAt ℝ 4 F (0 : OddTaylor.Plane)) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ {H : Type*} [MeasurableSpace H]
      (ν : Measure H) [IsProbabilityMeasure ν] (M : ℕ)
      (p u v : H × ℝ → ℝ) (_hp : Measurable p) (_hu : Measurable u) (_hv : Measurable v)
      (P Au Av : ℝ), 0 ≤ P → 0 ≤ Au → 0 ≤ Av → Au ≤ ε → Av ≤ ε →
      (∀ z, |p z| ≤ P) → (∀ z, |u z| ≤ Au) → (∀ z, |v z| ≤ Av) →
      |((∫ q, signedResponse F p u v q ∂ν.prod (LatticeFourier.angleSignLaw M true)) -
        (∫ q, signedResponse F p u v q ∂ν.prod (LatticeFourier.angleSignLaw M false))) -
        OddTaylor.mixedDerivative F 0*
          ((∫ q, signedResponse (fun x => x.1*x.2) p u v q ∂ν.prod (LatticeFourier.angleSignLaw M true)) -
           (∫ q, signedResponse (fun x => x.1*x.2) p u v q ∂ν.prod (LatticeFourier.angleSignLaw M false)))| ≤
        C*P*Au*Av*(Au^2+Av^2) := by
  obtain ⟨ε,hε,C,hC,hrem⟩ := native_oddOdd_taylor F hmF hF
  refine ⟨ε,hε,C,hC,?_⟩
  intro H _ ν _ M p u v hp hu hv P Au Av hP hAu hAv hAue hAve hpB huB hvB
  rw [native_bilinear_difference ν M p u v hp hu hv P Au Av hP hAu hAv hpB huB hvB]
  simpa only [mul_assoc,mul_left_comm] using
    hrem ν M p u v hp hu hv P Au Av hP hAu hAv hAue hAve hpB huB hvB

/-- Centering the response by its genuine baseline changes neither mixed
Fréchet derivative. -/
theorem mixedDerivative_sub_const (F : OddTaylor.Plane → ℝ) (c : ℝ) :
    OddTaylor.mixedDerivative (fun x => F x-c) 0=OddTaylor.mixedDerivative F 0 := by
  unfold OddTaylor.mixedDerivative OddTaylor.firstPartial OddTaylor.directionalDerivative
  simp only [fderiv_sub_const]

end RoughRegime.PoissonMeasure
