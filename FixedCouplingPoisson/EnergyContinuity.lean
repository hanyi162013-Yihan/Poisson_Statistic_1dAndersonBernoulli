import FixedCouplingPoisson.LogMean
import Mathlib.Topology.Order.Compact

/-!
# Energy continuity of actual stationary probabilities and Euclidean means

These continuity properties follow from the actual action and bounded
potential law. They are not additional deep Furstenberg hypotheses.
Uniform Cesàro across energies remains a separate compactness argument.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter
open scoped Topology

theorem continuous_transfer_energy_fixed_potential (v : ℝ) :
    Continuous (fun E : ℝ => transfer E v) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j
  all_goals first | exact continuous_id.sub continuous_const | exact continuous_const

theorem continuous_forward_energy_fixed_potential (v : ℝ) :
    Continuous (fun z : ℝ × ProjectivePoint => transferProjective z.1 v z.2) := by
  apply projectivize_isQuotientMap.continuous_lift_prod_right
  have hv : Continuous (fun z : ℝ × NonzeroVector => (z.2 : Vector2)) :=
    continuous_subtype_val.comp continuous_snd
  have hmul := ((continuous_transfer_energy_fixed_potential v).comp continuous_fst).matrix_mulVec hv
  exact continuous_projectivize.comp (hmul.subtype_mk fun z =>
    sl2_mulVec_ne_zero (transfer z.1 v) (transfer_det _ _) z.2 z.2.2)

theorem continuous_transferLogCocycle_energy_fixed_potential (v : ℝ) :
    Continuous (fun z : ℝ × ProjectivePoint => transferLogCocycle z.1 v z.2) := by
  change Continuous (fun z : ℝ × ProjectivePoint =>
    Real.log (projectiveGrowth (transfer z.1 v) z.2))
  exact (continuous_projectiveGrowth (fun E : ℝ => transfer E v)
    (continuous_transfer_energy_fixed_potential v)).log
      (fun z => (projectiveGrowth_transfer_pos z.1 v z.2).ne')

theorem continuous_testIntegral : Continuous
    (fun z : C(ProjectivePoint, ℝ) × ProbabilityMeasure ProjectivePoint =>
      ∫ p, z.1 p ∂(z.2 : Measure ProjectivePoint)) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  have hnormc : Continuous
      (fun z : C(ProjectivePoint, ℝ) × ProbabilityMeasure ProjectivePoint => ‖z.1 - z₀.1‖) :=
    (continuous_fst.sub continuous_const).norm
  have hnorm : Tendsto
      (fun z : C(ProjectivePoint, ℝ) × ProbabilityMeasure ProjectivePoint => ‖z.1 - z₀.1‖)
      (𝓝 z₀) (𝓝 0) := by simpa only [sub_self, norm_zero] using hnormc.tendsto z₀
  have hd : Tendsto
      (fun z : C(ProjectivePoint, ℝ) × ProbabilityMeasure ProjectivePoint =>
        ∫ p, (z.1 - z₀.1) p ∂(z.2 : Measure ProjectivePoint)) (𝓝 z₀) (𝓝 0) := by
    apply squeeze_zero_norm (fun z => ?_) hnorm
    simpa only [Real.norm_eq_abs] using abs_integral_continuous_test_le (z.1 - z₀.1) z.2
  have hf := ((ProbabilityMeasure.continuous_integral_continuousMap z₀.1).comp
    (continuous_snd : Continuous (fun z : C(ProjectivePoint, ℝ) ×
      ProbabilityMeasure ProjectivePoint => z.2))).tendsto z₀
  have hsum := hd.add hf
  change Tendsto
    (fun z : C(ProjectivePoint, ℝ) × ProbabilityMeasure ProjectivePoint =>
      ∫ p, z.1 p ∂(z.2 : Measure ProjectivePoint))
    (𝓝 z₀) (𝓝 (∫ p, z₀.1 p ∂(z₀.2 : Measure ProjectivePoint)))
  convert hsum using 1
  · funext z
    rw [show (fun p => (z.1 - z₀.1) p) = (fun p => z.1 p - z₀.1 p) from rfl,
      integral_sub (integrable_continuous_test z.1 z.2) (integrable_continuous_test z₀.1 z.2)]
    simp only [Function.comp_def, sub_add_cancel]
  · simp

theorem continuous_forwardAverage_energy (law : PotentialLaw) (f : C(ProjectivePoint, ℝ)) :
    Continuous (fun z : ℝ × ProjectivePoint => forwardAverage law z.1 f z.2) := by
  apply continuous_of_dominated (bound := fun _ : ℝ => ‖f‖)
  · intro z
    exact (f.continuous.comp (continuous_forward_fixed_direction z.1 z.2)).measurable.aestronglyMeasurable
  · intro z
    exact Filter.Eventually.of_forall fun v => f.norm_coe_le_norm _
  · exact integrable_const ‖f‖
  · exact Filter.Eventually.of_forall fun v =>
      f.continuous.comp (continuous_forward_energy_fixed_potential v)

theorem continuous_forwardContinuousAverage_energy (law : PotentialLaw)
    (f : C(ProjectivePoint, ℝ)) : Continuous (fun E => forwardContinuousAverage law E f) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_forwardAverage_energy law f)

def energyTestDefect (law : PotentialLaw) (f : C(ProjectivePoint, ℝ))
    (z : ℝ × ProbabilityMeasure ProjectivePoint) : ℝ := forwardTestDefect law z.1 f z.2

theorem continuous_energyTestDefect (law : PotentialLaw) (f : C(ProjectivePoint, ℝ)) :
    Continuous (energyTestDefect law f) := by
  have havg := continuous_testIntegral.comp
    (((continuous_forwardContinuousAverage_energy law f).comp continuous_fst).prodMk continuous_snd)
  exact havg.sub ((ProbabilityMeasure.continuous_integral_continuousMap f).comp continuous_snd)

theorem mapClusterPt_prodMk_of_tendsto {ι X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {l : Filter ι}
    {f : ι → X} {g : ι → Y} {x : X} {y : Y}
    (hf : Tendsto f l (𝓝 x)) (hg : MapClusterPt y l g) :
    MapClusterPt (x, y) l (fun i => (f i, g i)) := by
  rw [((𝓝 x).basis_sets.prod_nhds (𝓝 y).basis_sets).mapClusterPt_iff_frequently]
  rintro ⟨s, t⟩ ⟨hs, ht⟩
  exact ((hg.frequently ht).and_eventually (hf.eventually hs)).mono fun _ h => ⟨h.2, h.1⟩

/-- The selected stationary probability varies continuously with energy.
This is derived from compactness, the actual Feller action, and the pointwise
qualitative uniqueness; no continuity field is added to the external input. -/
theorem continuous_selected_forwardMeasure (law : PotentialLaw) (input : Input law) :
    Continuous (fun E => (input.atEnergy E).forwardMeasure) := by
  apply continuous_iff_continuousAt.mpr
  intro E
  apply tendsto_nhds_of_unique_mapClusterPt
  intro μ hμ
  apply (input.atEnergy E).forward_unique μ
  apply forward_stationary_of_average_test law E μ
  intro f
  apply sub_eq_zero.mp
  have hpair := mapClusterPt_prodMk_of_tendsto (tendsto_id : Tendsto (fun a : ℝ => a)
    (𝓝 E) (𝓝 E)) hμ
  have hc := hpair.continuousAt_comp (continuous_energyTestDefect law f).continuousAt
  have hz : (fun a : ℝ => energyTestDefect law f (a, (input.atEnergy a).forwardMeasure)) =
      (fun _ => 0) := by
    funext a
    unfold energyTestDefect forwardTestDefect
    rw [← forwardDistribution_average_integral law a f (input.atEnergy a).forwardMeasure,
      (input.atEnergy a).forward_stationary, sub_self]
  have hd : Tendsto (fun a : ℝ => energyTestDefect law f
      (a, (input.atEnergy a).forwardMeasure)) (𝓝 E) (𝓝 0) := by
    rw [hz]
    exact tendsto_const_nhds
  exact eq_of_nhds_neBot (hc.clusterPt.mono hd)

theorem continuous_oneStepLogMean_energy (law : PotentialLaw) :
    Continuous (fun z : ℝ × ProjectivePoint => oneStepLogMean law z.1 z.2) := by
  obtain ⟨M, hM, hb⟩ := law.bounded
  change Continuous (fun z : ℝ × ProjectivePoint =>
    ∫ v, transferLogCocycle z.1 v z.2 ∂law.measure)
  apply continuous_iff_continuousAt.mpr
  intro z₀
  have hnear : ∀ᶠ z : ℝ × ProjectivePoint in 𝓝 z₀, |z.1 - z₀.1| < 1 := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      (continuous_fst.tendsto z₀).eventually (Metric.ball_mem_nhds z₀.1 zero_lt_one)
  apply continuousAt_of_dominated (bound := fun _ : ℝ => Real.log (|z₀.1| + M + 3))
  · exact Filter.Eventually.of_forall fun z =>
      ((continuous_transferLogCocycle z.1).comp
        (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable
  · apply hnear.mono
    intro z hz
    have hE : |z.1| ≤ |z₀.1| + 1 := by
      have ha := abs_add_le (z.1 - z₀.1) z₀.1
      have heq : z.1 - z₀.1 + z₀.1 = z.1 := by ring
      rw [heq] at ha
      linarith
    exact hb.mono fun v hv => by
      rw [Real.norm_eq_abs]
      exact (abs_transferLogCocycle_le z.1 v M hM hv z.2).trans
        (Real.log_le_log (by positivity) (by linarith))
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun v =>
      (continuous_transferLogCocycle_energy_fixed_potential v).continuousAt

theorem continuous_oneStepContinuousLogMean_energy (law : PotentialLaw) :
    Continuous (oneStepContinuousLogMean law) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_oneStepLogMean_energy law)

theorem continuous_selected_stationaryMean (law : PotentialLaw) (input : Input law) :
    Continuous (fun E => stationaryMean law E (input.atEnergy E).forwardMeasure) := by
  have h := continuous_testIntegral.comp
    ((continuous_oneStepContinuousLogMean_energy law).prodMk
      (continuous_selected_forwardMeasure law input))
  convert h using 1
  funext E
  exact stationaryMean_eq_integral_oneStep law E _

theorem exists_uniform_stationaryMean_lower_bound (law : PotentialLaw) (input : Input law)
    (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ m : ℝ, 0 < m ∧ ∀ E ∈ K, m ≤ stationaryMean law E (input.atEnergy E).forwardMeasure := by
  obtain ⟨E₀, hE₀, hmin⟩ := hK.exists_isMinOn hne
    (continuous_selected_stationaryMean law input).continuousOn
  exact ⟨stationaryMean law E₀ (input.atEnergy E₀).forwardMeasure,
    (input.atEnergy E₀).stationary_mean_pos, isMinOn_iff.mp hmin⟩

end FixedCouplingPoisson.Furstenberg
