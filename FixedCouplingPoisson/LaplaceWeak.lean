import FixedCouplingPoisson.CompactMomentWeak
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Probability.Distributions.Exponential
import Mathlib.MeasureTheory.Measure.Portmanteau

/-! Actual integer Laplace transforms are moments after the exponential
change of variables. The compact target is canonical Lebesgue measure on
`[0,1]`; its moments are computed here. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

/-- Canonical uniform probability on the actual compact unit interval. -/
def compactUniform : ProbabilityMeasure MomentInterval := ⟨volume, inferInstance⟩

instance compactUniform_nullSingletonClass : NullSingletonClass (compactUniform : Measure MomentInterval) := by
  change NullSingletonClass (volume : Measure MomentInterval)
  infer_instance

theorem compactMoment_compactUniform (m : ℕ) :
    compactMoment compactUniform m = 1 / ((m : ℝ) + 1) := by
  change (∫ x : MomentInterval, (x : ℝ) ^ m
    ∂Measure.comap Subtype.val (volume : Measure ℝ)) = _
  rw [integral_subtype_comap (μ := (volume : Measure ℝ)) measurableSet_Icc
    (fun x : ℝ => x ^ m), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    integral_pow]
  simp

/-- This globally defined change of variables agrees with `exp(-x)` for
nonnegative `x`. Clipping only supplies a total map into `[0,1]`. -/
def negativeExpInterval (x : ℝ) : MomentInterval :=
  ⟨Real.exp (-max x 0), Real.exp_nonneg _,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_right x 0))⟩

theorem continuous_negativeExpInterval : Continuous negativeExpInterval :=
  (((continuous_id.max continuous_const).neg).rexp).subtype_mk (fun x =>
    ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr (le_max_right x 0))⟩)

@[simp] theorem negativeExpInterval_coe_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    (negativeExpInterval x : ℝ) = Real.exp (-x) := by
  simp only [negativeExpInterval, max_eq_left hx]

section RandomVariables
variable {Ω : Type*} [MeasurableSpace Ω]

/-- The genuine push-forward law of the exponential change of variables. -/
def laplaceUnitLaw (P : ProbabilityMeasure Ω) (X : Ω → ℝ) (hX : Measurable X) :
    ProbabilityMeasure MomentInterval :=
  P.map ((continuous_negativeExpInterval.measurable.comp hX).aemeasurable)

theorem compactMoment_laplaceUnitLaw (P : ProbabilityMeasure Ω)
    (X : Ω → ℝ) (hX : Measurable X) (hX0 : ∀ ω, 0 ≤ X ω) (m : ℕ) :
    compactMoment (laplaceUnitLaw P X hX) m =
      ∫ ω, Real.exp (-(m : ℝ) * X ω) ∂(P : Measure Ω) := by
  have hpow : Continuous (fun x : MomentInterval => (x : ℝ) ^ m) :=
    continuous_subtype_val.pow m
  rw [compactMoment, laplaceUnitLaw, ProbabilityMeasure.toMeasure_map,
    integral_map (μ := (P : Measure Ω))
      ((continuous_negativeExpInterval.measurable.comp hX).aemeasurable)
      hpow.measurable.aestronglyMeasurable]
  apply integral_congr_ae
  exact ae_of_all _ fun ω => by
    change (negativeExpInterval (X ω) : ℝ) ^ m = Real.exp (-(m : ℝ) * X ω)
    rw [negativeExpInterval_coe_of_nonneg (hX0 ω), ← Real.exp_nat_mul]
    congr 1
    ring

/-- Integer Laplace convergence to `1/(m+1)` gives a genuine uniform
weak limit after the exponential change of variables. -/
theorem laplaceUnitLaw_tendsto_uniform {ι : Type*} {F : Filter ι}
    (P : ProbabilityMeasure Ω) (Xs : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (Xs i)) (hX0 : ∀ i ω, 0 ≤ Xs i ω)
    (hlaplace : ∀ m : ℕ,
      Tendsto (fun i => ∫ ω, Real.exp (-(m : ℝ) * Xs i ω) ∂(P : Measure Ω))
        F (𝓝 (1 / ((m : ℝ) + 1)))) :
    Tendsto (fun i => laplaceUnitLaw P (Xs i) (hX i)) F (𝓝 compactUniform) := by
  apply probabilityMeasure_tendsto_of_compactMoments
  intro m
  have hmoment (i : ι) := compactMoment_laplaceUnitLaw P (Xs i) (hX i) (hX0 i) m
  simpa only [hmoment, compactMoment_compactUniform] using hlaplace m

end RandomVariables

/-- Convergence on every closed lower ray gives actual weak convergence
of real probability measures. This supplies the final distribution bridge. -/
theorem probabilityMeasure_tendsto_of_Iic_real {ι : Type*} {F : Filter ι}
    [F.IsCountablyGenerated] (μs : ι → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hIic : ∀ x : ℝ, Tendsto (fun i => (μs i : Measure ℝ).real (Iic x)) F
      (𝓝 ((μ : Measure ℝ).real (Iic x)))) :
    Tendsto μs F (𝓝 μ) := by
  let S : Set (Set ℝ) := {s | ∃ a b : ℝ, a < b ∧ Ioc a b = s}
  have hS : IsPiSystem S := isPiSystem_Ioc id id
  have hformula (ν : ProbabilityMeasure ℝ) {a b : ℝ} (hab : a < b) :
      (ν : Measure ℝ).real (Ioc a b) =
        (ν : Measure ℝ).real (Iic b) - (ν : Measure ℝ).real (Iic a) := by
    have heq : Iic b \ Iic a = Ioc a b := by
      ext x
      simp only [Set.mem_sdiff, mem_Iic, mem_Ioc, not_le, and_comm]
    rw [← heq, measureReal_sdiff (Iic_subset_Iic.mpr hab.le) measurableSet_Iic]
  apply hS.tendsto_probabilityMeasure_of_tendsto_of_mem
  · rintro s ⟨a, b, hab, rfl⟩
    exact measurableSet_Ioc
  · intro u hu x hx
    obtain ⟨a, b, hxab, hsub⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hu.mem_nhds hx)
    refine ⟨Ioc a ((x + b) / 2), ⟨a, (x + b) / 2, by linarith [hxab.1, hxab.2], rfl⟩,
      Ioc_mem_nhds hxab.1 (by linarith [hxab.2]), ?_⟩
    intro y hy
    apply hsub
    exact ⟨hy.1, by linarith [hy.2, hxab.2]⟩
  · rintro s ⟨a, b, hab, rfl⟩
    have hIoc (ν : ProbabilityMeasure ℝ) :
        (ν : Measure ℝ).real (Ioc a b) =
          (ν : Measure ℝ).real (Iic b) - (ν : Measure ℝ).real (Iic a) := hformula ν hab
    apply NNReal.tendsto_coe.mp
    simpa only [← ProbabilityMeasure.measureReal_eq_coe_coeFn, hIoc] using
      (hIic b).sub (hIic a)

/-- The actual rate-one exponential probability measure from Mathlib. -/
def exponentialOne : ProbabilityMeasure ℝ :=
  ⟨expMeasure 1, isProbabilityMeasure_expMeasure (by norm_num)⟩

instance exponentialOne_nullSingletonClass : NullSingletonClass (exponentialOne : Measure ℝ) := by
  change NullSingletonClass (volume.withDensity (gammaPDF 1 1))
  infer_instance

theorem exponentialOne_Iic_real (x : ℝ) :
    (exponentialOne : Measure ℝ).real (Iic x) =
      if 0 ≤ x then 1 - Real.exp (-x) else 0 := by
  rw [← cdf_eq_real]
  change cdf (expMeasure 1) x = _
  simpa only [one_mul] using cdf_expMeasure_eq (by norm_num : 0 < (1 : ℝ)) x

/-- Nonnegative real random variables whose actual integer Laplace
transforms converge to `1/(m+1)` converge in law to the actual rate-one
exponential distribution. No distribution-identification premise is used. -/
theorem laws_tendsto_exponentialOne_of_integer_laplace
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} {F : Filter ι}
    [F.IsCountablyGenerated] (P : ProbabilityMeasure Ω) (Xs : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (Xs i)) (hX0 : ∀ i ω, 0 ≤ Xs i ω)
    (hlaplace : ∀ m : ℕ,
      Tendsto (fun i => ∫ ω, Real.exp (-(m : ℝ) * Xs i ω) ∂(P : Measure Ω))
        F (𝓝 (1 / ((m : ℝ) + 1)))) :
    Tendsto (fun i => P.map (hX i).aemeasurable) F (𝓝 exponentialOne) := by
  have hweak := laplaceUnitLaw_tendsto_uniform P Xs hX hX0 hlaplace
  apply probabilityMeasure_tendsto_of_Iic_real
  intro x
  by_cases hx : 0 ≤ x
  · let z : MomentInterval := ⟨Real.exp (-x), Real.exp_nonneg _,
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr hx)⟩
    have hfront : (compactUniform : Measure MomentInterval) (frontier (Ici z)) = 0 := by
      rw [frontier_Ici' (show (Iio z).Nonempty from
        ⟨0, show (0 : ℝ) < Real.exp (-x) from Real.exp_pos _⟩)]
      exact measure_singleton z
    have hmeasure := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      hweak hfront
    have hreal : Tendsto
        (fun i => (laplaceUnitLaw P (Xs i) (hX i) : Measure MomentInterval).real (Ici z))
        F (𝓝 ((compactUniform : Measure MomentInterval).real (Ici z))) := by
      simpa only [Measure.real, Function.comp_def] using
        (ENNReal.tendsto_toReal (measure_ne_top (compactUniform : Measure MomentInterval)
          (Ici z))).comp hmeasure
    have hcut (i : ι) :
        (P.map (hX i).aemeasurable : Measure ℝ).real (Iic x) =
          (laplaceUnitLaw P (Xs i) (hX i) : Measure MomentInterval).real (Ici z) := by
      unfold Measure.real
      rw [ProbabilityMeasure.map_apply' _ _ measurableSet_Iic, laplaceUnitLaw,
        ProbabilityMeasure.map_apply' _ _ measurableSet_Ici]
      apply congrArg ENNReal.toReal
      apply congrArg (fun s : Set Ω => (P : Measure Ω) s)
      ext ω
      change Xs i ω ≤ x ↔ Real.exp (-x) ≤ (negativeExpInterval (Xs i ω) : ℝ)
      rw [negativeExpInterval_coe_of_nonneg (hX0 i ω), Real.exp_le_exp]
      constructor <;> intro h <;> linarith
    have hUniform : (compactUniform : Measure MomentInterval).real (Ici z) =
        1 - Real.exp (-x) := by
      change ((volume : Measure MomentInterval) (Ici z)).toReal = _
      rw [unitInterval.volume_Ici, ENNReal.toReal_ofReal (sub_nonneg.mpr z.property.2)]
    have hExp : (exponentialOne : Measure ℝ).real (Iic x) = 1 - Real.exp (-x) := by
      simpa only [if_pos hx] using exponentialOne_Iic_real x
    simpa only [hcut, hUniform, hExp] using hreal
  · have hzero (i : ι) : (P.map (hX i).aemeasurable : Measure ℝ).real (Iic x) = 0 := by
      unfold Measure.real
      rw [ProbabilityMeasure.map_apply' _ _ measurableSet_Iic]
      have hpreimage : Xs i ⁻¹' Iic x = ∅ := by
        ext ω
        simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false]
        exact not_le_of_gt ((lt_of_not_ge hx).trans_le (hX0 i ω))
      rw [hpreimage, measure_empty, ENNReal.toReal_zero]
    have hExp : (exponentialOne : Measure ℝ).real (Iic x) = 0 := by
      simpa only [if_neg hx] using exponentialOne_Iic_real x
    simpa only [hzero, hExp] using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : ℝ)) F (𝓝 0))

/-- The zeroth transform is automatic for probability measures, so only
positive integer Laplace parameters need to be supplied. -/
theorem laws_tendsto_exponentialOne_of_positive_integer_laplace
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} {F : Filter ι}
    [F.IsCountablyGenerated] (P : ProbabilityMeasure Ω) (Xs : ι → Ω → ℝ)
    (hX : ∀ i, Measurable (Xs i)) (hX0 : ∀ i ω, 0 ≤ Xs i ω)
    (hlaplace : ∀ m : ℕ, 0 < m →
      Tendsto (fun i => ∫ ω, Real.exp (-(m : ℝ) * Xs i ω) ∂(P : Measure Ω))
        F (𝓝 (1 / ((m : ℝ) + 1)))) :
    Tendsto (fun i => P.map (hX i).aemeasurable) F (𝓝 exponentialOne) := by
  apply laws_tendsto_exponentialOne_of_integer_laplace P Xs hX hX0
  intro m
  by_cases hm : m = 0
  · subst m
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℝ)) F (𝓝 1))
  · exact hlaplace m (Nat.pos_of_ne_zero hm)

end FixedCouplingPoisson
