import FixedCouplingPoisson.LaplaceWeak

/-! Weak convergence evaluated at a moving observation threshold. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

theorem monotone_moving_argument_tendsto
    {ι : Type*} {F : Filter ι} (fs : ι → ℝ → ℝ) (g : ℝ → ℝ)
    (hmono : ∀ i, Monotone (fs i))
    (hpoint : ∀ y, Tendsto (fun i => fs i y) F (𝓝 (g y)))
    {x : ℝ} (hcont : ContinuousAt g x) {xs : ι → ℝ}
    (hxs : Tendsto xs F (𝓝 x)) :
    Tendsto (fun i => fs i (xs i)) F (𝓝 (g x)) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨r, hr, hrg⟩ := Metric.eventually_nhds_iff.mp
      (hcont.tendsto.eventually (Ioi_mem_nhds ha))
    let y : ℝ := x - r / 2
    have hy : y < x := by dsimp [y]; linarith
    have hdist : dist y x < r := by
      rw [Real.dist_eq, show y - x = -(r / 2) by dsimp [y]; ring,
        abs_neg, abs_of_pos (by positivity : 0 < r / 2)]
      linarith
    have hay : a < g y := hrg hdist
    filter_upwards [(hpoint y).eventually (Ioi_mem_nhds hay),
      hxs.eventually (Ioi_mem_nhds hy)] with i hi hix
    exact hi.trans_le (hmono i hix.le)
  · intro a ha
    obtain ⟨r, hr, hrg⟩ := Metric.eventually_nhds_iff.mp
      (hcont.tendsto.eventually (Iio_mem_nhds ha))
    let y : ℝ := x + r / 2
    have hy : x < y := by dsimp [y]; linarith
    have hdist : dist y x < r := by
      rw [Real.dist_eq, show y - x = r / 2 by dsimp [y]; ring,
        abs_of_pos (by positivity : 0 < r / 2)]
      linarith
    have hay : g y < a := hrg hdist
    filter_upwards [(hpoint y).eventually (Iio_mem_nhds hay),
      hxs.eventually (Iio_mem_nhds hy)] with i hi hix
    exact (hmono i hix.le).trans_lt hi

theorem cdf_tendsto_of_weak_null_singletons
    {ι : Type*} {F : Filter ι} {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (hweak : Tendsto μs F (𝓝 μ))
    (hμ : ∀ x, (μ : Measure ℝ) {x} = 0) (x : ℝ) :
    Tendsto (fun i => cdf (μs i : Measure ℝ) x) F
      (𝓝 (cdf (μ : Measure ℝ) x)) := by
  have hf : (μ : Measure ℝ) (frontier (Iic x)) = 0 := by
    rw [frontier_Iic]
    exact hμ x
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hweak hf
  have hr := (ENNReal.tendsto_toReal (measure_ne_top (μ : Measure ℝ) _)).comp ht
  simpa only [cdf_eq_real, Measure.real, Function.comp_def] using hr

theorem cdf_moving_threshold_tendsto_of_weak
    {ι : Type*} {F : Filter ι} {μs : ι → ProbabilityMeasure ℝ}
    {μ : ProbabilityMeasure ℝ} (hweak : Tendsto μs F (𝓝 μ))
    (hμ : ∀ x, (μ : Measure ℝ) {x} = 0)
    {x : ℝ} (hcont : ContinuousAt (cdf (μ : Measure ℝ)) x)
    {xs : ι → ℝ} (hxs : Tendsto xs F (𝓝 x)) :
    Tendsto (fun i => (μs i : Measure ℝ).real (Iic (xs i))) F
      (𝓝 ((μ : Measure ℝ).real (Iic x))) := by
  simpa only [cdf_eq_real] using monotone_moving_argument_tendsto
    (fun i => cdf (μs i : Measure ℝ)) (cdf (μ : Measure ℝ))
    (fun i => monotone_cdf _) (cdf_tendsto_of_weak_null_singletons hweak hμ)
    hcont hxs

end FixedCouplingPoisson
