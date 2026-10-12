import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Tactic.Ring

/-!
# Weak convergence transfer across equality with high probability

All laws below are the actual pushforwards of a fixed probability measure.
The mismatch event controls every bounded continuous test integral, so
no coupling interface or extra tightness hypothesis is introduced.
-/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Filter Set
open scoped Topology BoundedContinuousFunction

section
variable {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [TopologicalSpace S] [OpensMeasurableSpace S] [MeasurableEq S]

omit [MeasurableEq S] in
/-- Integration against the genuine pushforward law. -/
theorem integral_probabilityMeasure_map (P : ProbabilityMeasure Ω)
    {X : Ω → S} (hX : Measurable X) (f : S →ᵇ ℝ) :
    (∫ z, f z ∂(P.map hX.aemeasurable : Measure S)) = ∫ ω, f (X ω) ∂P := by
  change (∫ z, f z ∂Measure.map X (P : Measure Ω)) = _
  exact integral_map hX.aemeasurable f.continuous.measurable.aestronglyMeasurable

/-- A mismatch probability bounds the difference of bounded test integrals. -/
theorem integral_boundedContinuous_comp_error_le (P : ProbabilityMeasure Ω)
    {X Y : Ω → S} (hX : Measurable X) (hY : Measurable Y) (f : S →ᵇ ℝ) :
    |(∫ ω, f (X ω) ∂P) - (∫ ω, f (Y ω) ∂P)| ≤
      (2 * ‖f‖) * (P : Measure Ω).real {ω | X ω ≠ Y ω} := by
  have hbad : MeasurableSet {ω | X ω ≠ Y ω} := (measurableSet_eq_fun hX hY).compl
  have hXi : Integrable (fun ω => f (X ω)) (P : Measure Ω) :=
    (f.integrable (Measure.map X (P : Measure Ω))).comp_measurable hX
  have hYi : Integrable (fun ω => f (Y ω)) (P : Measure Ω) :=
    (f.integrable (Measure.map Y (P : Measure Ω))).comp_measurable hY
  have hbi : Integrable ({ω | X ω ≠ Y ω}.indicator (fun _ => 2 * ‖f‖))
      (P : Measure Ω) := (integrable_const _).indicator hbad
  rw [← integral_sub hXi hYi]
  calc
    _ ≤ ∫ ω, |f (X ω) - f (Y ω)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, {ω | X ω ≠ Y ω}.indicator (fun _ => 2 * ‖f‖) ω ∂P := by
      apply integral_mono_ae (hXi.sub hYi).abs hbi
      filter_upwards with ω
      change |f (X ω) - f (Y ω)| ≤
        {ω | X ω ≠ Y ω}.indicator (fun _ => 2 * ‖f‖) ω
      by_cases hω : X ω = Y ω
      · simp [hω]
      · rw [Set.indicator_of_mem hω]
        calc
          |f (X ω) - f (Y ω)| ≤ |f (X ω)| + |f (Y ω)| := abs_sub _ _
          _ ≤ ‖f‖ + ‖f‖ := add_le_add
            (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (X ω))
            (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm (Y ω))
          _ = 2 * ‖f‖ := by ring
    _ = (2 * ‖f‖) * (P : Measure Ω).real {ω | X ω ≠ Y ω} := by
      rw [integral_indicator_const _ hbad, smul_eq_mul, mul_comm]

/-- If two measurable random variables disagree with probability tending to
zero, weak convergence of either genuine law transfers to the other. -/
theorem probabilityMeasure_map_tendsto_of_mismatch_probability_tendsto_zero
    {ι : Type*} {F : Filter ι} (P : ProbabilityMeasure Ω)
    {X Y : ι → Ω → S} (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {ν : ProbabilityMeasure S}
    (hbad : Tendsto (fun i => (P : Measure Ω).real {ω | X i ω ≠ Y i ω}) F (𝓝 0))
    (hYlim : Tendsto (fun i => P.map (hY i).aemeasurable) F (𝓝 ν)) :
    Tendsto (fun i => P.map (hX i).aemeasurable) F (𝓝 ν) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hYraw := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hYlim f
  have hYf : Tendsto (fun i => ∫ ω, f (Y i ω) ∂P) F
      (𝓝 (∫ z, f z ∂(ν : Measure S))) :=
    Filter.Tendsto.congr' (Eventually.of_forall fun i =>
      integral_probabilityMeasure_map P (hY i) f) hYraw
  have hdiff : Tendsto (fun i => (∫ ω, f (X i ω) ∂P) -
      (∫ ω, f (Y i ω) ∂P)) F (𝓝 0) := by
    apply squeeze_zero_norm (fun i => ?_)
      (by simpa only [mul_zero] using hbad.const_mul (2 * ‖f‖))
    simpa only [Real.norm_eq_abs] using
      integral_boundedContinuous_comp_error_le P (hX i) (hY i) f
  have hXf : Tendsto (fun i => ∫ ω, f (X i ω) ∂P) F
      (𝓝 (∫ z, f z ∂(ν : Measure S))) := by
    simpa only [zero_add, sub_add_cancel] using hdiff.add hYf
  exact Filter.Tendsto.congr' (Eventually.of_forall fun i =>
    (integral_probabilityMeasure_map P (hX i) f).symm) hXf

/-- The equivalent equality-probability formulation used after spectral
rounding succeeds with probability tending to one. -/
theorem probabilityMeasure_map_tendsto_of_eq_probability_tendsto_one
    {ι : Type*} {F : Filter ι} (P : ProbabilityMeasure Ω)
    {X Y : ι → Ω → S} (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {ν : ProbabilityMeasure S}
    (hgood : Tendsto (fun i => (P : Measure Ω).real {ω | X i ω = Y i ω}) F (𝓝 1))
    (hYlim : Tendsto (fun i => P.map (hY i).aemeasurable) F (𝓝 ν)) :
    Tendsto (fun i => P.map (hX i).aemeasurable) F (𝓝 ν) := by
  apply probabilityMeasure_map_tendsto_of_mismatch_probability_tendsto_zero P hX hY
    (hYlim := hYlim)
  have hcompl (i : ι) : (P : Measure Ω).real {ω | X i ω ≠ Y i ω} =
      1 - (P : Measure Ω).real {ω | X i ω = Y i ω} :=
    probReal_compl_eq_one_sub (measurableSet_eq_fun (hX i) (hY i))
  simpa only [hcompl, sub_self] using
    (tendsto_const_nhds (x := (1 : ℝ))).sub hgood

end
end FixedCouplingPoisson
