import FixedCouplingPoisson.IntervalStepApprox
import FixedCouplingPoisson.LaplaceTruncationBudget

/-! Deterministic compact-test versus interval-step Laplace error. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Set
open scoped Topology CompactlySupported BigOperators ENNReal

theorem realVagueMeasure_Ioc_ne_top (μ : RealVagueMeasure) (a b : ℝ) :
    (μ : Measure ℝ) (Ioc a b) ≠ ∞ := ne_of_lt
  ((measure_mono Ioc_subset_Icc_self).trans_lt isCompact_Icc.measure_lt_top)

/-- A uniform error on a common finite-mass support is controlled by its
actual mass, without an expected-mass estimate. -/
theorem abs_integral_sub_le_uniform_support {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (f g : α → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (A : Set α) (hA : MeasurableSet A) (hfin : μ A ≠ ∞) {η : ℝ} (hη : 0 ≤ η)
    (herror : ∀ x, |f x - g x| ≤ η) (hzero : ∀ x, x ∉ A → f x = 0 ∧ g x = 0) :
    |(∫ x, f x ∂μ) - (∫ x, g x ∂μ)| ≤ η * μ.real A := by
  have hAi : Integrable (A.indicator (fun _ => η)) μ :=
    (integrableOn_const hfin).integrable_indicator hA
  rw [← integral_sub hf hg]
  calc
    _ ≤ ∫ x, |f x - g x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, A.indicator (fun _ => η) x ∂μ := by
      apply integral_mono (hf.sub hg).abs hAi
      intro x
      change |f x - g x| ≤ A.indicator (fun _ => η) x
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx]
        exact herror x
      · rw [Set.indicator_of_notMem hx, (hzero x hx).1, (hzero x hx).2, sub_self, abs_zero]
    _ = _ := by rw [integral_indicator_const _ hA, smul_eq_mul, mul_comm]

/-- Genuine step tests on the symmetric grid are integrable for every
actual locally finite real measure. -/
theorem integrable_symmetricStep (f : C_c(ℝ, ℝ)) (R : ℝ) (m : ℕ)
    (μ : RealVagueMeasure) : Integrable (symmetricStep f R m) (μ : Measure ℝ) :=
  integrable_poissonStepDensity _ _ (fun _ => measurableSet_Ioc) _
    (fun _ => realVagueMeasure_Ioc_ne_top μ _ _)

theorem symmetricStep_nonneg (f : C_c(ℝ, ℝ)) (hf : 0 ≤ f)
    (R : ℝ) (m : ℕ) (y : ℝ) : 0 ≤ symmetricStep f R m y :=
  poissonStepDensity_nonneg _ _ (fun i => hf _) y

theorem symmetricStep_zero_outside (f : C_c(ℝ, ℝ)) {R : ℝ} {m : ℕ}
    (hR : 0 < R) (hm : 0 < m) {y : ℝ} (hy : y ∉ Ioc (-R) R) :
    symmetricStep f R m y = 0 := by
  have hx := (symmetricGrid_strictMono hR hm).strictMonoOn (Iic (2 * m))
  have hend := symmetricGrid_endpoints R hm
  apply poissonStepDensity_eq_zero_of_not_mem
  intro i hi
  apply hy
  have hleft := hx.monotoneOn (Nat.zero_le (2 * m)) i.isLt.le (Nat.zero_le _)
  have hright := hx.monotoneOn (by change i.val + 1 ≤ 2 * m; omega) (by change 2 * m ≤ 2 * m; exact le_rfl)
    (by change i.val + 1 ≤ 2 * m; omega)
  constructor
  · exact (by simpa only [hend.1] using hleft.trans_lt hi.1)
  · exact (by simpa only [hend.2.2] using hi.2.trans hright)

/-- The actual nonnegative C_c Laplace functional differs from its interval
step approximation by at most η times the enclosing-window mass. -/
theorem symmetricStep_laplace_error (μ : RealVagueMeasure) (f : C_c(ℝ, ℝ))
    (hf : 0 ≤ f) {R : ℝ} {m : ℕ} (hR : 0 < R) (hm : 0 < m)
    (hsupp : tsupport f ⊆ Ioo (-R) R) {η : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ y, |f y - symmetricStep f R m y| ≤ η) :
    |Real.exp (-RealVagueMeasure.testIntegral μ f) -
      Real.exp (-(∫ y, symmetricStep f R m y ∂(μ : Measure ℝ)))| ≤
      η * (μ : Measure ℝ).real (Ioc (-R) R) := by
  have hfnonneg : 0 ≤ RealVagueMeasure.testIntegral μ f :=
    RealVagueMeasure.testIntegral_nonneg μ f (fun y => hf y)
  have hgnonneg : 0 ≤ ∫ y, symmetricStep f R m y ∂(μ : Measure ℝ) :=
    integral_nonneg (symmetricStep_nonneg f hf R m)
  apply (abs_laplace_neg_sub_le hfnonneg hgnonneg).trans
  apply abs_integral_sub_le_uniform_support _ _ _ f.integrable
    (integrable_symmetricStep f R m μ) _ measurableSet_Ioc
    (realVagueMeasure_Ioc_ne_top μ _ _) hη happrox
  intro y hy
  refine ⟨?_, symmetricStep_zero_outside f hR hm hy⟩
  by_contra hne
  have hs := hsupp (subset_tsupport f (Function.mem_support.mpr hne))
  exact hy ⟨hs.1, hs.2.le⟩

end FixedCouplingPoisson
