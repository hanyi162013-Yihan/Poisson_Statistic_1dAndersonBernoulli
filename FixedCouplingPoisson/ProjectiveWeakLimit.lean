import FixedCouplingPoisson.ProductCocycle
import FixedCouplingPoisson.PhaseWeakTools
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Continuous test control for the actual projective Markov iterates

The deterministic and integration bridge converts an actual uniform pair
moment estimate to convergence of ordinary Markov iterates. The separate
actual iid multiblock theorem supplies that moment estimate without adding
a quantitative convergence field to qualitative input.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Matrix Filter
open scoped Topology

/-- The continuous dual Markov iterate, retaining its actual one-site average. -/
def forwardTestOrbit (law : PotentialLaw) (E : ℝ) (f : C(ProjectivePoint, ℝ)) :
    ℕ → C(ProjectivePoint, ℝ)
  | 0 => f
  | n + 1 => forwardTestOrbit law E (forwardContinuousAverage law E f) n

theorem probabilityOrbit_integral_testOrbit (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (n : ℕ) (f : C(ProjectivePoint, ℝ)) :
    (∫ p, f p ∂(probabilityOrbit law E ν n : Measure ProjectivePoint)) =
      ∫ p, forwardTestOrbit law E f n p ∂(ν : Measure ProjectivePoint) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [probabilityOrbit_succ, forwardDistribution_average_integral]
    exact ih (forwardContinuousAverage law E f)

theorem projectiveProcess_integral_testOrbit (law : PotentialLaw) (E : ℝ)
    (p : ProjectivePoint) (n : ℕ) (f : C(ProjectivePoint, ℝ)) :
    (∫ ω, f (projectiveProcess E p n ω) ∂iidMeasure law) =
      forwardTestOrbit law E f n p := by
  calc
    _ = ∫ r, f r ∂(projectiveProcessDistribution law E p n : Measure ProjectivePoint) := by
      change _ = ∫ r, f r ∂(iidMeasure law).map (projectiveProcess E p n)
      exact (integral_map (projectiveProcess_measurable E p n).aemeasurable
        f.continuous.measurable.aestronglyMeasurable).symm
    _ = ∫ r, f r ∂(probabilityOrbit law E (pointDistribution p) n : Measure ProjectivePoint) := by
      rw [projectiveProcessDistribution_eq_orbit]
    _ = ∫ r, forwardTestOrbit law E f n r ∂(pointDistribution p : Measure ProjectivePoint) :=
      probabilityOrbit_integral_testOrbit law E (pointDistribution p) n f
    _ = forwardTestOrbit law E f n p := by
      change (∫ r, forwardTestOrbit law E f n r ∂Measure.dirac p) = _
      exact integral_dirac _ p

theorem probabilityOrbit_stationary (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : ForwardStationary law E ν) (n : ℕ) :
    probabilityOrbit law E ν n = ν := by
  induction n with
  | zero => rfl
  | succ n ih => rw [probabilityOrbit_succ, ih]; exact hν

theorem forwardTestOrbit_stationary_integral (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : ForwardStationary law E ν)
    (n : ℕ) (f : C(ProjectivePoint, ℝ)) :
    (∫ p, forwardTestOrbit law E f n p ∂(ν : Measure ProjectivePoint)) =
      ∫ p, f p ∂(ν : Measure ProjectivePoint) := by
  rw [← probabilityOrbit_integral_testOrbit, probabilityOrbit_stationary law E ν hν]

theorem integrable_projective_test_process (law : PotentialLaw) (E : ℝ)
    (p : ProjectivePoint) (n : ℕ) (f : C(ProjectivePoint, ℝ)) :
    Integrable (fun ω => f (projectiveProcess E p n ω)) (iidMeasure law) := by
  apply (integrable_const ‖f‖).mono'
    (f.continuous.measurable.comp (projectiveProcess_measurable E p n)).aestronglyMeasurable
  exact Eventually.of_forall fun ω => f.norm_coe_le_norm _

/-- Joint distance measurability is factored before substituting recursive products. -/
theorem measurable_projectiveDistance_comp {Ω : Type*} [MeasurableSpace Ω]
    {f g : Ω → ProjectivePoint} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun ω => projectiveDistance (f ω) (g ω)) := by
  have hd : Measurable (fun z : ProjectivePoint × ProjectivePoint =>
      projectiveDistance z.1 z.2) := continuous_projectiveDistance_joint.measurable
  have hp : Measurable (fun ω => (f ω, g ω)) := hf.prodMk hg
  exact hd.comp hp

theorem integrable_pair_projective_moment (law : PotentialLaw) (E : ℝ)
    (p r : ProjectivePoint) (n : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    Integrable (fun ω => projectiveDistance (projectiveProcess E p n ω)
      (projectiveProcess E r n ω) ^ s) (iidMeasure law) := by
  have hm : Measurable (fun ω => projectiveDistance (projectiveProcess E p n ω)
      (projectiveProcess E r n ω)) :=
    measurable_projectiveDistance_comp (f := projectiveProcess E p n)
      (g := projectiveProcess E r n) (projectiveProcess_measurable E p n)
      (projectiveProcess_measurable E r n)
  apply (integrable_const (1 : ℝ)).mono'
    ((Real.continuous_rpow_const hs).measurable.comp hm).aestronglyMeasurable
  exact Eventually.of_forall fun ω => by
    have hD : 0 ≤ projectiveDistance (projectiveProcess E p n ω) (projectiveProcess E r n ω) := by
      by_cases heq : projectiveProcess E p n ω = projectiveProcess E r n ω
      · exact ((projectiveDistance_eq_zero_iff _ _).mpr heq).symm.le
      · exact ((projectiveDistance_pos_iff _ _).mpr heq).le
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hD s)]
    simpa only [Real.one_rpow] using Real.rpow_le_rpow hD (projectiveDistance_le_one _ _) hs

/-- A deterministic test modulus controls actual product-test means. -/
theorem testOrbit_pair_moment_control_of_pointwise (law : PotentialLaw) (E : ℝ)
    (f : C(ProjectivePoint, ℝ)) (ε C s : ℝ) (hs : 0 ≤ s)
    (hpoint : ∀ p r, |f p - f r| ≤ ε + C * projectiveDistance p r ^ s)
    (n : ℕ) (p r : ProjectivePoint) :
      |forwardTestOrbit law E f n p - forwardTestOrbit law E f n r| ≤ ε + C *
        (∫ ω, projectiveDistance (projectiveProcess E p n ω)
          (projectiveProcess E r n ω) ^ s ∂iidMeasure law) := by
  have hp := integrable_projective_test_process law E p n f
  have hr := integrable_projective_test_process law E r n f
  have hi := integrable_pair_projective_moment law E p r n s hs
  calc
    _ = |∫ ω, (f (projectiveProcess E p n ω) - f (projectiveProcess E r n ω))
        ∂iidMeasure law| := by
      rw [integral_sub hp hr, projectiveProcess_integral_testOrbit,
        projectiveProcess_integral_testOrbit]
    _ ≤ ∫ ω, |f (projectiveProcess E p n ω) - f (projectiveProcess E r n ω)|
        ∂iidMeasure law := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (ε + C * projectiveDistance (projectiveProcess E p n ω)
        (projectiveProcess E r n ω) ^ s) ∂iidMeasure law :=
      integral_mono (hp.sub hr).abs ((integrable_const ε).add (hi.const_mul C))
        (fun ω => hpoint _ _)
    _ = ε + C * (∫ ω, projectiveDistance (projectiveProcess E p n ω)
        (projectiveProcess E r n ω) ^ s ∂iidMeasure law) := by
      rw [integral_add (integrable_const ε) (hi.const_mul C), integral_const_mul]
      simp

/-- The actual pair moment controls the difference of actual product-test means. -/
theorem exists_testOrbit_pair_moment_control (law : PotentialLaw) (E : ℝ)
    (f : C(ProjectivePoint, ℝ)) (ε : ℝ) (hε : 0 < ε) (s : ℝ) (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n p r,
      |forwardTestOrbit law E f n p - forwardTestOrbit law E f n r| ≤ ε + C *
        (∫ ω, projectiveDistance (projectiveProcess E p n ω)
          (projectiveProcess E r n ω) ^ s ∂iidMeasure law) := by
  obtain ⟨C, hC, hpoint⟩ := continuous_test_projective_moment_bound f ε hε s hs
  exact ⟨C, hC, testOrbit_pair_moment_control_of_pointwise law E f ε C s hs hpoint⟩

/-- The same test modulus works at every energy. -/
theorem exists_uniform_testOrbit_pair_moment_control (law : PotentialLaw)
    (f : C(ProjectivePoint, ℝ)) (ε : ℝ) (hε : 0 < ε) (s : ℝ) (hs : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E n p r,
      |forwardTestOrbit law E f n p - forwardTestOrbit law E f n r| ≤ ε + C *
        (∫ ω, projectiveDistance (projectiveProcess E p n ω)
          (projectiveProcess E r n ω) ^ s ∂iidMeasure law) := by
  obtain ⟨C, hC, hpoint⟩ := continuous_test_projective_moment_bound f ε hε s hs
  exact ⟨C, hC, fun E => testOrbit_pair_moment_control_of_pointwise law E f ε C s hs hpoint⟩

/-- Uniform control of pair test means controls distance from any actual stationary mean. -/
theorem testOrbit_stationary_error_of_pair_bound (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : ForwardStationary law E ν)
    (n : ℕ) (f : C(ProjectivePoint, ℝ)) (b : ℝ)
    (hb : ∀ p r, |forwardTestOrbit law E f n p - forwardTestOrbit law E f n r| ≤ b)
    (p : ProjectivePoint) :
    |forwardTestOrbit law E f n p - ∫ r, f r ∂(ν : Measure ProjectivePoint)| ≤ b := by
  rw [← forwardTestOrbit_stationary_integral law E ν hν n f]
  have hi : Integrable (fun r => forwardTestOrbit law E f n r) (ν : Measure ProjectivePoint) :=
    integrable_continuous_test (forwardTestOrbit law E f n) ν
  have hconst : Integrable (fun _ : ProjectivePoint => forwardTestOrbit law E f n p)
      (ν : Measure ProjectivePoint) := integrable_const _
  have heq : forwardTestOrbit law E f n p -
      (∫ r, forwardTestOrbit law E f n r ∂(ν : Measure ProjectivePoint)) =
      ∫ r, (forwardTestOrbit law E f n p - forwardTestOrbit law E f n r)
        ∂(ν : Measure ProjectivePoint) := by
    rw [integral_sub hconst hi]
    simp
  rw [heq]
  have h := norm_integral_le_of_norm_le_const (μ := (ν : Measure ProjectivePoint))
    (f := fun r => forwardTestOrbit law E f n p - forwardTestOrbit law E f n r) (C := b)
    (Eventually.of_forall fun r => by
      simpa only [Real.norm_eq_abs] using hb p r)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

/-- Uniform pair test control also controls every initial probability measure. -/
theorem probabilityOrbit_test_error_of_pair_bound (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : ForwardStationary law E ν)
    (η : ProbabilityMeasure ProjectivePoint) (n : ℕ) (f : C(ProjectivePoint, ℝ)) (b : ℝ)
    (hb : ∀ p r, |forwardTestOrbit law E f n p - forwardTestOrbit law E f n r| ≤ b) :
    |(∫ p, f p ∂(probabilityOrbit law E η n : Measure ProjectivePoint)) -
      ∫ p, f p ∂(ν : Measure ProjectivePoint)| ≤ b := by
  rw [probabilityOrbit_integral_testOrbit]
  have hi := integrable_continuous_test (forwardTestOrbit law E f n) η
  have hc : Integrable (fun _ : ProjectivePoint => ∫ p, f p ∂(ν : Measure ProjectivePoint))
      (η : Measure ProjectivePoint) := integrable_const _
  have heq : (∫ p, forwardTestOrbit law E f n p ∂(η : Measure ProjectivePoint)) -
      (∫ p, f p ∂(ν : Measure ProjectivePoint)) =
      ∫ p, (forwardTestOrbit law E f n p - ∫ r, f r ∂(ν : Measure ProjectivePoint))
        ∂(η : Measure ProjectivePoint) := by
    rw [integral_sub hi hc]
    simp
  rw [heq]
  have h := norm_integral_le_of_norm_le_const (μ := (η : Measure ProjectivePoint))
    (f := fun p => forwardTestOrbit law E f n p - ∫ r, f r ∂(ν : Measure ProjectivePoint))
    (C := b) (Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using
        testOrbit_stationary_error_of_pair_bound law E ν hν n f b hb p)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

/-- An actual uniform pair-moment estimate implies convergence of complete
Markov iterates, even when the initial distribution changes with time. -/
theorem probabilityOrbit_tendsto_varying_initial_of_uniform_pair_moment
    (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : ForwardStationary law E ν)
    (s : ℝ) (hs : 0 ≤ s) (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (hm : ∀ n p r, (∫ ω, projectiveDistance (projectiveProcess E p n ω)
      (projectiveProcess E r n ω) ^ s ∂iidMeasure law) ≤ a n)
    (η : ℕ → ProbabilityMeasure ProjectivePoint) :
    Tendsto (fun n => probabilityOrbit law E (η n) n) atTop (𝓝 ν) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  let g : C(ProjectivePoint, ℝ) := f.toContinuousMap
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨C, hC, hcontrol⟩ := exists_testOrbit_pair_moment_control law E g (ε / 2)
    (half_pos hε) s hs
  have hc : Tendsto (fun n => C * a n) atTop (𝓝 0) := by simpa only [mul_zero] using ha.const_mul C
  have hsmall : ∀ᶠ n in atTop, C * a n < ε / 2 := hc.eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [hsmall] with n hn
  rw [Real.dist_eq]
  have hpair : ∀ r t, |forwardTestOrbit law E g n r - forwardTestOrbit law E g n t| ≤
      ε / 2 + C * a n := by
    intro r t
    exact (hcontrol n r t).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hm n r t) hC))
  have hvalue : |(∫ r, f r ∂(probabilityOrbit law E (η n) n :
      Measure ProjectivePoint)) - ∫ r, f r ∂(ν : Measure ProjectivePoint)| ≤ ε / 2 + C * a n := by
    change |(∫ r, g r ∂(probabilityOrbit law E (η n) n :
      Measure ProjectivePoint)) - ∫ r, g r ∂(ν : Measure ProjectivePoint)| ≤ _
    exact probabilityOrbit_test_error_of_pair_bound law E ν hν (η n) n g _ hpair
  exact lt_of_le_of_lt hvalue (by linarith)

theorem probabilityOrbit_tendsto_of_uniform_pair_moment (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : ForwardStationary law E ν)
    (s : ℝ) (hs : 0 ≤ s) (a : ℕ → ℝ) (ha : Tendsto a atTop (𝓝 0))
    (hm : ∀ n p r, (∫ ω, projectiveDistance (projectiveProcess E p n ω)
      (projectiveProcess E r n ω) ^ s ∂iidMeasure law) ≤ a n)
    (p : ProjectivePoint) :
    Tendsto (probabilityOrbit law E (pointDistribution p)) atTop (𝓝 ν) :=
  probabilityOrbit_tendsto_varying_initial_of_uniform_pair_moment law E ν hν s hs a ha hm
    (fun _ => pointDistribution p)

end FixedCouplingPoisson.Furstenberg
