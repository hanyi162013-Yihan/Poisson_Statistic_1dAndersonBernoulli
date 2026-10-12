import FixedCouplingPoisson.NegativeMoment

/-! Positivity for all actual stationary probabilities yields a positive
finite iid block without assuming stationary uniqueness. This removes the
logical cycle in proving uniqueness from contraction. No Input is used.
This draft has not yet been compiled; checking is deferred by the user. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology

theorem continuous_stationaryMean_probability (law : PotentialLaw) (E : ℝ) :
    Continuous (stationaryMean law E) := by
  have heq : stationaryMean law E =
      (fun ν : ProbabilityMeasure ProjectivePoint =>
        ∫ p, (oneStepContinuousLogMean law E) p ∂(ν : Measure ProjectivePoint)) := by
    funext ν
    exact stationaryMean_eq_integral_oneStep law E ν
  rw [heq]
  exact ProbabilityMeasure.continuous_integral_continuousMap (oneStepContinuousLogMean law E)

theorem exists_uniform_positive_log_cesaro_of_all_stationary_positive
    (law : PotentialLaw) (E : ℝ)
    (hpos : ∀ ν : ProbabilityMeasure ProjectivePoint,
      ForwardStationary law E ν → 0 < stationaryMean law E ν) :
    ∃ n : ℕ, ∃ c : ℝ, 0 < c ∧ ∀ η : ProbabilityMeasure ProjectivePoint,
      c ≤ stationaryMean law E (empiricalCesaro law E η n) := by
  classical
  by_contra h
  let c : ℕ → ℝ := fun n => (((n + 1 : ℕ) : ℝ))⁻¹
  have hcpos (n : ℕ) : 0 < c n :=
    inv_pos.mpr (Nat.cast_pos.mpr (Nat.succ_pos n))
  have hbad : ∀ n : ℕ, ∃ η : ProbabilityMeasure ProjectivePoint,
      stationaryMean law E (empiricalCesaro law E η n) < c n := by
    intro n
    have hn : ¬ ∀ η : ProbabilityMeasure ProjectivePoint,
        c n ≤ stationaryMean law E (empiricalCesaro law E η n) := by
      intro hn
      exact h ⟨n, c n, hcpos n, hn⟩
    simpa only [not_forall, not_le] using hn
  choose η hη using hbad
  let μ : ℕ → ProbabilityMeasure ProjectivePoint := fun n => empiricalCesaro law E (η n) n
  obtain ⟨ν, _, hν⟩ := (isCompact_univ :
    IsCompact (univ : Set (ProbabilityMeasure ProjectivePoint))).exists_mapClusterPt
      (show Filter.map μ atTop ≤ 𝓟 (univ : Set (ProbabilityMeasure ProjectivePoint)) from by simp)
  have hstat : ForwardStationary law E ν :=
    forward_stationary_of_cluster_vanishing_defect law E μ ν hν
      (empiricalCesaro_test_defect_tendsto law E η)
  have hp : 0 < stationaryMean law E ν := hpos ν hstat
  have hmean := hν.continuousAt_comp
    (continuous_stationaryMean_probability law E).continuousAt
  have hfrequent : ∃ᶠ n in atTop,
      stationaryMean law E ν / 2 < stationaryMean law E (μ n) :=
    hmean.frequently (Ioi_mem_nhds (half_lt_self hp))
  have hc : Tendsto c atTop (𝓝 0) := by
    simpa only [c, one_div, Nat.cast_add, Nat.cast_one] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hsmall : ∀ᶠ n in atTop, c n < stationaryMean law E ν / 2 :=
    hc.eventually (gt_mem_nhds (half_pos hp))
  apply hfrequent
  exact hsmall.mono fun n hn => not_lt.mpr ((hη n).le.trans hn.le)

theorem exists_uniform_positive_product_log_mean_of_all_stationary_positive
    (law : PotentialLaw) (E : ℝ)
    (hpos : ∀ ν : ProbabilityMeasure ProjectivePoint,
      ForwardStationary law E ν → 0 < stationaryMean law E ν) :
    ∃ N : ℕ, ∃ c : ℝ, 0 < N ∧ 0 < c ∧ ∀ p : ProjectivePoint,
      (N : ℝ) * c ≤
        ∫ ω, projectiveLogGrowth (transferProduct E ω N) p ∂iidMeasure law := by
  obtain ⟨n, c, hc, hn⟩ :=
    exists_uniform_positive_log_cesaro_of_all_stationary_positive law E hpos
  refine ⟨n + 1, c, Nat.succ_pos n, hc, fun p => ?_⟩
  have hN : 0 < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
  have hi : stationaryMean law E (empiricalCesaro law E (pointDistribution p) n) =
      ((n + 1 : ℕ) : ℝ)⁻¹ *
        (∫ ω, projectiveLogGrowth (transferProduct E ω (n + 1)) p ∂iidMeasure law) := by
    rw [stationaryMean_eq_integral_oneStep, integral_projectiveLogGrowth_product]
    exact integral_empiricalCesaro law E (pointDistribution p) n (oneStepContinuousLogMean law E)
  have hp := hn (pointDistribution p)
  rw [hi] at hp
  have hmul := mul_le_mul_of_nonneg_left hp hN.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] using hmul

theorem exists_uniform_product_negative_log_moment_of_all_stationary_positive
    (law : PotentialLaw) (E : ℝ)
    (hpos : ∀ ν : ProbabilityMeasure ProjectivePoint,
      ForwardStationary law E ν → 0 < stationaryMean law E ν) :
    ∃ N : ℕ, 0 < N ∧ ∃ s q : ℝ, 0 < s ∧ s ≤ 1 ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ p r : ProjectivePoint,
        (∫ ω, Real.exp (-s *
          (projectiveLogGrowth (transferProduct E ω N) p +
            projectiveLogGrowth (transferProduct E ω N) r)) ∂iidMeasure law) ≤ q := by
  obtain ⟨N, c, hN, hc, hmean⟩ :=
    exists_uniform_positive_product_log_mean_of_all_stationary_positive law E hpos
  obtain ⟨K, hK, hb⟩ := ae_uniform_product_log_bound law E N
  let X : (ProjectivePoint × ProjectivePoint) → PotentialSpace → ℝ := fun z ω =>
    projectiveLogGrowth (transferProduct E ω N) z.1 +
      projectiveLogGrowth (transferProduct E ω N) z.2
  have hXm : ∀ z, Measurable (X z) := fun z =>
    (measurable_projectiveLogGrowth_product E z.1 N).add
      (measurable_projectiveLogGrowth_product E z.2 N)
  have hXb : ∀ z, ∀ᵐ ω ∂iidMeasure law, |X z ω| ≤ 2 * K := by
    intro z
    exact hb.mono fun ω hω => (abs_add_le _ _).trans (by linarith [hω z.1, hω z.2])
  have hm : 0 < 2 * (N : ℝ) * c :=
    mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr hN)) hc
  have hXm' : ∀ z, 2 * (N : ℝ) * c ≤ ∫ ω, X z ω ∂iidMeasure law := by
    intro z
    rw [show X z = (fun ω => projectiveLogGrowth (transferProduct E ω N) z.1 +
      projectiveLogGrowth (transferProduct E ω N) z.2) from rfl,
      integral_add (integrable_projectiveLogGrowth_product law E z.1 N)
        (integrable_projectiveLogGrowth_product law E z.2 N)]
    linarith [hmean z.1, hmean z.2]
  obtain ⟨s, q, hs, hs1, hq0, hq1, hq⟩ := exists_uniform_negative_moment
    (iidMeasure law) X hXm (2 * K) (2 * (N : ℝ) * c)
    (mul_nonneg (by norm_num) hK) hm hXb hXm'
  exact ⟨N, hN, s, q, hs, hs1, hq0, hq1, fun p r => hq (p, r)⟩

end FixedCouplingPoisson.Furstenberg
