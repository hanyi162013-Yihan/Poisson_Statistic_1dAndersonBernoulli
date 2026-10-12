import FixedCouplingPoisson.EnergyContinuity
import FixedCouplingPoisson.ProductCocycle
import Mathlib.Tactic.Choose

/-!
# Uniform Cesàro convergence on compact energy sets

Uniform convergence is derived from compactness and the actual jointly continuous Feller
averages. Selected stationary laws and their positive means come only from
the pointwise qualitative input; uniformity is not assumed.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter
open scoped Topology

theorem eventually_uniform_energy_integral_empiricalCesaro (law : PotentialLaw)
    (input : Input law) (K : Set ℝ) (hK : IsCompact K)
    (g : ℝ → C(ProjectivePoint, ℝ)) (hg : Continuous g)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ E ∈ K, ∀ ν : ProbabilityMeasure ProjectivePoint,
      |(∫ p, g E p ∂(empiricalCesaro law E ν n : Measure ProjectivePoint)) -
        ∫ p, g E p ∂((input.atEnergy E).forwardMeasure : Measure ProjectivePoint)| < ε := by
  classical
  by_contra h
  let bad (n : ℕ) : Prop := ∃ E : ℝ, E ∈ K ∧ ∃ ν : ProbabilityMeasure ProjectivePoint,
    ε ≤ |(∫ p, g E p ∂(empiricalCesaro law E ν n : Measure ProjectivePoint)) -
      ∫ p, g E p ∂((input.atEnergy E).forwardMeasure : Measure ProjectivePoint)|
  have hb : ∃ᶠ n in atTop, bad n := by
    change ¬ ∀ᶠ n in atTop, ¬ bad n
    simpa only [bad, not_exists, not_and, not_le] using h
  choose N hN hbad using frequently_atTop.mp hb
  choose E hEK ν hbadν using hbad
  have hNt : Tendsto N atTop atTop := tendsto_atTop_mono hN tendsto_id
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let states : ℕ → K × ProbabilityMeasure ProjectivePoint := fun n =>
    (⟨E n, hEK n⟩, empiricalCesaro law (E n) (ν n) (N n))
  obtain ⟨z₀, _, hc⟩ := (isCompact_univ : IsCompact
    (Set.univ : Set (K × ProbabilityMeasure ProjectivePoint))).exists_mapClusterPt
      (u := states) (f := atTop) (by simp)
  have hpairc : Continuous (fun z : K × ProbabilityMeasure ProjectivePoint =>
      ((z.1 : ℝ), z.2)) :=
    (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
  have hpair := hc.continuousAt_comp hpairc.continuousAt
  have hstat : ForwardStationary law (z₀.1 : ℝ) z₀.2 := by
    apply forward_stationary_of_average_test law (z₀.1 : ℝ) z₀.2
    intro f
    apply sub_eq_zero.mp
    have hd : Tendsto (fun n => energyTestDefect law f
        (E n, empiricalCesaro law (E n) (ν n) (N n))) atTop (𝓝 0) := by
      have hbound : ∀ n : ℕ, ‖energyTestDefect law f
          (E n, empiricalCesaro law (E n) (ν n) (N n))‖ ≤
          (2 * ‖f‖) / ((N n + 1 : ℕ) : ℝ) := by
        intro n
        simpa only [energyTestDefect, Real.norm_eq_abs] using
          abs_empiricalCesaro_test_defect_le law (E n) (ν n) (N n) f
      apply squeeze_zero_norm hbound
      have ht := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
          (2 * ‖f‖)).comp hNt
      simpa only [mul_zero, one_div, div_eq_mul_inv, one_mul, Nat.cast_add,
        Nat.cast_one, Function.comp_def] using ht
    have hdc := hpair.continuousAt_comp (continuous_energyTestDefect law f).continuousAt
    exact eq_of_nhds_neBot (hdc.clusterPt.mono hd)
  have hμeq := (input.atEnergy (z₀.1 : ℝ)).forward_unique z₀.2 hstat
  let error : K × ProbabilityMeasure ProjectivePoint → ℝ := fun z =>
    |(∫ p, g (z.1 : ℝ) p ∂(z.2 : Measure ProjectivePoint)) -
      ∫ p, g (z.1 : ℝ) p
        ∂((input.atEnergy (z.1 : ℝ)).forwardMeasure : Measure ProjectivePoint)|
  have henergy : Continuous (fun z : K × ProbabilityMeasure ProjectivePoint => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have herror : Continuous error :=
    ((continuous_testIntegral.comp ((hg.comp henergy).prodMk continuous_snd)).sub
      (continuous_testIntegral.comp ((hg.comp henergy).prodMk
        ((continuous_selected_forwardMeasure law input).comp henergy)))).abs
  have hcenter : error z₀ = 0 := by simp only [error, hμeq, sub_self, abs_zero]
  have hzero : MapClusterPt 0 atTop (fun n => error (states n)) := by
    simpa only [hcenter, Function.comp_def] using hc.continuousAt_comp herror.continuousAt
  have hsmall : ∃ᶠ n in atTop, error (states n) < ε := hzero.frequently (gt_mem_nhds hε)
  have hlarge : ∀ n, ε ≤ error (states n) := by
    intro n
    simpa only [error, states] using hbadν n
  exact hsmall (Eventually.of_forall fun n => not_lt.mpr (hlarge n))

theorem exists_uniform_positive_log_cesaro_on_compact (law : PotentialLaw)
    (input : Input law) (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ m : ℝ, 0 < m ∧ ∃ n : ℕ, ∀ E ∈ K, ∀ ν : ProbabilityMeasure ProjectivePoint,
      m / 2 ≤ ∫ p, oneStepLogMean law E p
        ∂(empiricalCesaro law E ν n : Measure ProjectivePoint) := by
  obtain ⟨m, hm, hmin⟩ := exists_uniform_stationaryMean_lower_bound law input K hK hne
  obtain ⟨n, hn⟩ := (eventually_uniform_energy_integral_empiricalCesaro law input K hK
    (oneStepContinuousLogMean law) (continuous_oneStepContinuousLogMean_energy law)
    (m / 2) (half_pos hm)).exists
  refine ⟨m, hm, n, fun E hE ν => ?_⟩
  have hi := (abs_lt.mp (hn E hE ν)).1
  change -(m / 2) < (∫ p, oneStepLogMean law E p
    ∂(empiricalCesaro law E ν n : Measure ProjectivePoint)) -
      ∫ p, oneStepLogMean law E p
        ∂((input.atEnergy E).forwardMeasure : Measure ProjectivePoint) at hi
  rw [← stationaryMean_eq_integral_oneStep law E (input.atEnergy E).forwardMeasure] at hi
  linarith [hmin E hE]

theorem exists_uniform_positive_product_log_mean_on_compact (law : PotentialLaw)
    (input : Input law) (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ m : ℝ, 0 < m ∧ ∃ N : ℕ, 0 < N ∧ ∀ E ∈ K, ∀ p : ProjectivePoint,
      (N : ℝ) * m / 2 ≤
        ∫ ω, projectiveLogGrowth (transferProduct E ω N) p ∂iidMeasure law := by
  obtain ⟨m, hm, n, hn⟩ := exists_uniform_positive_log_cesaro_on_compact law input K hK hne
  refine ⟨m, hm, n + 1, Nat.succ_pos n, fun E hE p => ?_⟩
  have hN : 0 < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hi := integral_empiricalCesaro law E (pointDistribution p) n
    (oneStepContinuousLogMean law E)
  have h : m / 2 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ *
      (∫ ω, projectiveLogGrowth (transferProduct E ω (n + 1)) p ∂iidMeasure law) := by
    rw [integral_projectiveLogGrowth_product]
    exact hi ▸ hn E hE (pointDistribution p)
  have hmul := mul_le_mul_of_nonneg_left h hN.le
  simpa only [mul_div_assoc, ← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] using hmul

end FixedCouplingPoisson.Furstenberg
