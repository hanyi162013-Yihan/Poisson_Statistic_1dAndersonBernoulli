import FixedCouplingPoisson.JointKernel
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A finite colored block kernel without color independence

When at most one colored arrival occurs, its Laplace factor is exactly
linear in the one-arrival indicators. All nonlinear error is confined to
two or more enclosing arrivals, provided the pathwise domination holds.
These are general probability lemmas; actual phase blocks must separately
verify the explicit measurable-count and domination hypotheses.
-/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Filter Set
open scoped BigOperators

def firstArrivalWeight (t : ℝ) : ℝ := 1 - Real.exp (-t)

def firstArrivalIndicator (x : ℕ) : ℝ := if 1 ≤ x then 1 else 0

def coloredLaplaceFactor {s : ℕ} (t : Fin s → ℝ) (x : Fin s → ℕ) : ℝ :=
  Real.exp (-(∑ i, t i * (x i : ℝ)))

def coloredLinearFactor {s : ℕ} (t : Fin s → ℝ) (x : Fin s → ℕ) : ℝ :=
  1 - ∑ i, firstArrivalWeight (t i) * firstArrivalIndicator (x i)

theorem firstArrivalWeight_bounds {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ firstArrivalWeight t ∧ firstArrivalWeight t ≤ 1 := by
  have he0 := Real.exp_nonneg (-t)
  have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold firstArrivalWeight
  constructor <;> linarith

theorem firstArrivalIndicator_bounds (x : ℕ) :
    0 ≤ firstArrivalIndicator x ∧ firstArrivalIndicator x ≤ 1 := by
  unfold firstArrivalIndicator
  split_ifs <;> norm_num

theorem coloredLaplaceFactor_bounds {s : ℕ} (t : Fin s → ℝ)
    (ht : ∀ i, 0 ≤ t i) (x : Fin s → ℕ) :
    0 ≤ coloredLaplaceFactor t x ∧ coloredLaplaceFactor t x ≤ 1 := by
  refine ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr ?_⟩
  exact neg_nonpos.mpr (Finset.sum_nonneg fun i _ => mul_nonneg (ht i) (Nat.cast_nonneg _))

/-- The exact one-arrival identity, with arbitrary dependence among colors. -/
theorem coloredLaplaceFactor_eq_linear_of_sum_le_one {s : ℕ}
    (t : Fin s → ℝ) (x : Fin s → ℕ) (hx : ∑ i, x i ≤ 1) :
    coloredLaplaceFactor t x = coloredLinearFactor t x := by
  classical
  by_cases hzero : ∀ i, x i = 0
  · simp [coloredLaplaceFactor, coloredLinearFactor, firstArrivalIndicator, hzero]
  · push Not at hzero
    obtain ⟨j, hj⟩ := hzero
    have hunique := Finset.sum_le_one_iff.mp hx
    have hjone : x j = 1 :=
      (hunique j j (Finset.mem_univ _) (Finset.mem_univ _) hj hj).2
    have hother : ∀ i, i ≠ j → x i = 0 := by
      intro i hij
      by_contra hxi
      exact hij (hunique i j (Finset.mem_univ _) (Finset.mem_univ _) hxi hj).1
    have hsum : ∑ i, t i * (x i : ℝ) = t j := by
      rw [Finset.sum_eq_single j]
      · simp [hjone]
      · intro i _ hij
        simp [hother i hij]
      · simp
    have hsumI : ∑ i, firstArrivalWeight (t i) * firstArrivalIndicator (x i) =
        firstArrivalWeight (t j) := by
      rw [Finset.sum_eq_single j]
      · simp [hjone, firstArrivalIndicator]
      · intro i _ hij
        simp [hother i hij, firstArrivalIndicator]
      · simp
    rw [coloredLaplaceFactor, coloredLinearFactor, hsum, hsumI]
    unfold firstArrivalWeight
    ring

theorem coloredLaplaceFactor_linear_error_bound {s : ℕ}
    (t : Fin s → ℝ) (ht : ∀ i, 0 ≤ t i) (x : Fin s → ℕ) :
    |coloredLaplaceFactor t x - coloredLinearFactor t x| ≤ (s : ℝ) + 1 := by
  have hψ := coloredLaplaceFactor_bounds t ht x
  have hterm : ∀ i, 0 ≤ firstArrivalWeight (t i) * firstArrivalIndicator (x i) ∧
      firstArrivalWeight (t i) * firstArrivalIndicator (x i) ≤ 1 := by
    intro i
    exact ⟨mul_nonneg (firstArrivalWeight_bounds (ht i)).1 (firstArrivalIndicator_bounds _).1,
      (mul_le_of_le_one_left (firstArrivalIndicator_bounds _).1
        (firstArrivalWeight_bounds (ht i)).2).trans (firstArrivalIndicator_bounds _).2⟩
  have hsum0 : 0 ≤ ∑ i, firstArrivalWeight (t i) * firstArrivalIndicator (x i) :=
    Finset.sum_nonneg fun i _ => (hterm i).1
  have hsum1 : (∑ i, firstArrivalWeight (t i) * firstArrivalIndicator (x i)) ≤ (s : ℝ) := by
    calc
      _ ≤ ∑ _i : Fin s, (1 : ℝ) := Finset.sum_le_sum fun i _ => (hterm i).2
      _ = s := by simp
  have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
  unfold coloredLinearFactor
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem coloredLaplaceFactor_linear_error_le_bad_indicator {s : ℕ}
    (t : Fin s → ℝ) (ht : ∀ i, 0 ≤ t i) (x : Fin s → ℕ) (y : ℕ)
    (hxy : ∑ i, x i ≤ y) :
    |coloredLaplaceFactor t x - coloredLinearFactor t x| ≤
      if 2 ≤ y then (s : ℝ) + 1 else 0 := by
  split_ifs with hy
  · exact coloredLaplaceFactor_linear_error_bound t ht x
  · have hx : ∑ i, x i ≤ 1 := hxy.trans (by omega)
    rw [coloredLaplaceFactor_eq_linear_of_sum_le_one t x hx]
    simp

section Probability
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem measurable_firstArrivalIndicator {x : Ω → ℕ} (hx : Measurable x) :
    Measurable (fun ω => firstArrivalIndicator (x ω)) :=
  (measurable_of_countable firstArrivalIndicator).comp hx

theorem measurable_coloredLaplaceFactor {s : ℕ} (t : Fin s → ℝ)
    {X : Fin s → Ω → ℕ} (hX : ∀ i, Measurable (X i)) :
    Measurable (fun ω => coloredLaplaceFactor t (fun i => X i ω)) := by
  unfold coloredLaplaceFactor
  apply Real.continuous_exp.measurable.comp
  apply Measurable.neg
  exact (Finset.univ).measurable_fun_sum fun i _ =>
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (hX i)).const_mul (t i)

theorem integrable_coloredLaplaceFactor {s : ℕ} (t : Fin s → ℝ)
    (ht : ∀ i, 0 ≤ t i) {X : Fin s → Ω → ℕ} (hX : ∀ i, Measurable (X i)) :
    Integrable (fun ω => coloredLaplaceFactor t (fun i => X i ω)) μ :=
  bounded_block_integrable (measurable_coloredLaplaceFactor t hX).stronglyMeasurable
    (fun ω => coloredLaplaceFactor_bounds t ht (fun i => X i ω))

omit [IsProbabilityMeasure μ] in
theorem integral_firstArrivalIndicator {x : Ω → ℕ} (hx : Measurable x) :
    (∫ ω, firstArrivalIndicator (x ω) ∂μ) = μ.real {ω | 1 ≤ x ω} := by
  have hset : MeasurableSet {ω | 1 ≤ x ω} := measurableSet_le measurable_const hx
  have heq : (fun ω => firstArrivalIndicator (x ω)) =
      {ω | 1 ≤ x ω}.indicator (fun _ => (1 : ℝ)) := by
    classical
    funext ω
    simp only [firstArrivalIndicator, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq, integral_indicator_const 1 hset]
  simp only [smul_eq_mul, mul_one]

theorem integrable_coloredLinearFactor {s : ℕ} (t : Fin s → ℝ)
    {X : Fin s → Ω → ℕ} (hX : ∀ i, Measurable (X i)) :
    Integrable (fun ω => coloredLinearFactor t (fun i => X i ω)) μ := by
  unfold coloredLinearFactor
  apply (integrable_const (1 : ℝ)).sub
  apply integrable_finsetSum Finset.univ
  intro i _
  apply Integrable.const_mul
  exact bounded_block_integrable (measurable_firstArrivalIndicator (hX i)).stronglyMeasurable
    (fun ω => firstArrivalIndicator_bounds _)

theorem integral_coloredLinearFactor {s : ℕ} (t : Fin s → ℝ)
    {X : Fin s → Ω → ℕ} (hX : ∀ i, Measurable (X i)) :
    (∫ ω, coloredLinearFactor t (fun i => X i ω) ∂μ) =
      1 - ∑ i, firstArrivalWeight (t i) * μ.real {ω | 1 ≤ X i ω} := by
  have hi : ∀ i, Integrable (fun ω => firstArrivalWeight (t i) *
      firstArrivalIndicator (X i ω)) μ := fun i =>
    (bounded_block_integrable (measurable_firstArrivalIndicator (hX i)).stronglyMeasurable
      (fun ω => firstArrivalIndicator_bounds _)).const_mul _
  unfold coloredLinearFactor
  rw [integral_sub (integrable_const (1 : ℝ)) (integrable_finsetSum Finset.univ (fun i _ => hi i)),
    integral_finsetSum Finset.univ (fun i _ => hi i)]
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul,
    integral_firstArrivalIndicator (hX _)]

/-- The nonlinear block error is paid only on two enclosing arrivals. -/
theorem integral_coloredLaplaceFactor_error_le {s : ℕ} (t : Fin s → ℝ)
    (ht : ∀ i, 0 ≤ t i) {X : Fin s → Ω → ℕ} {Y : Ω → ℕ}
    (hX : ∀ i, Measurable (X i)) (hY : Measurable Y)
    (hdom : ∀ ω, ∑ i, X i ω ≤ Y ω) :
    |(∫ ω, coloredLaplaceFactor t (fun i => X i ω) ∂μ) -
      (1 - ∑ i, firstArrivalWeight (t i) * μ.real {ω | 1 ≤ X i ω})| ≤
        ((s : ℝ) + 1) * μ.real {ω | 2 ≤ Y ω} := by
  have hset : MeasurableSet {ω | 2 ≤ Y ω} := measurableSet_le measurable_const hY
  have hψ := integrable_coloredLaplaceFactor t ht hX (μ := μ)
  have hL := integrable_coloredLinearFactor t hX (μ := μ)
  have hbad : Integrable ({ω | 2 ≤ Y ω}.indicator (fun _ => (s : ℝ) + 1)) μ :=
    (integrable_const _).indicator hset
  rw [← integral_coloredLinearFactor t hX, ← integral_sub hψ hL]
  calc
    _ ≤ ∫ ω, |coloredLaplaceFactor t (fun i => X i ω) -
        coloredLinearFactor t (fun i => X i ω)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, {ω | 2 ≤ Y ω}.indicator (fun _ => (s : ℝ) + 1) ω ∂μ := by
      apply integral_mono_ae (hψ.sub hL).abs hbad
      exact Eventually.of_forall fun ω => by
        change |coloredLaplaceFactor t (fun i => X i ω) -
          coloredLinearFactor t (fun i => X i ω)| ≤
          {ω | 2 ≤ Y ω}.indicator (fun _ => (s : ℝ) + 1) ω
        simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using
          coloredLaplaceFactor_linear_error_le_bad_indicator t ht (fun i => X i ω)
            (Y ω) (hdom ω)
    _ = ((s : ℝ) + 1) * μ.real {ω | 2 ≤ Y ω} := by
      rw [integral_indicator_const _ hset, smul_eq_mul, mul_comm]

/-- Arrival-probability approximation errors add without color independence. -/
theorem integral_coloredLaplaceFactor_error_le_of_arrival_approx {s : ℕ}
    (t : Fin s → ℝ) (ht : ∀ i, 0 ≤ t i) {X : Fin s → Ω → ℕ} {Y : Ω → ℕ}
    (hX : ∀ i, Measurable (X i)) (hY : Measurable Y)
    (hdom : ∀ ω, ∑ i, X i ω ≤ Y ω) (q : Fin s → ℝ) :
    |(∫ ω, coloredLaplaceFactor t (fun i => X i ω) ∂μ) -
      (1 - ∑ i, firstArrivalWeight (t i) * q i)| ≤
        ((s : ℝ) + 1) * μ.real {ω | 2 ≤ Y ω} +
          ∑ i, |μ.real {ω | 1 ≤ X i ω} - q i| := by
  have hbase := integral_coloredLaplaceFactor_error_le t ht hX hY hdom (μ := μ)
  have hlin : |(1 - ∑ i, firstArrivalWeight (t i) * μ.real {ω | 1 ≤ X i ω}) -
      (1 - ∑ i, firstArrivalWeight (t i) * q i)| ≤
        ∑ i, |μ.real {ω | 1 ≤ X i ω} - q i| := by
    have heq : (1 - ∑ i, firstArrivalWeight (t i) * μ.real {ω | 1 ≤ X i ω}) -
        (1 - ∑ i, firstArrivalWeight (t i) * q i) =
          -(∑ i, firstArrivalWeight (t i) * (μ.real {ω | 1 ≤ X i ω} - q i)) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      ring
    rw [heq, abs_neg]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    rw [abs_mul, abs_of_nonneg (firstArrivalWeight_bounds (ht i)).1]
    exact mul_le_of_le_one_left (abs_nonneg _) (firstArrivalWeight_bounds (ht i)).2
  exact (abs_sub_le _ _ _).trans (add_le_add hbase hlin)

end Probability
end FixedCouplingPoisson
