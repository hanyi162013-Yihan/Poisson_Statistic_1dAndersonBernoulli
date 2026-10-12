import FixedCouplingPoisson.MultiBlockContraction
import FixedCouplingPoisson.ProjectiveWeakLimit
import FixedCouplingPoisson.PhaseDistribution

/-!
# Full weak convergence of the actual canonical phase laws

The qualitative input is used only for the actual stationary measure and the
positive Euclidean logarithmic mean. Actual iid multiblock contraction supplies
the moment estimate; compact test control then gives complete weak convergence.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter
open scoped Topology
local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- Full Markov iterates converge, uniformly enough to allow changing initial laws. -/
theorem probabilityOrbit_tendsto_forwardMeasure (law : PotentialLaw) (E : ℝ)
    (data : QualitativeData law E) (η : ℕ → ProbabilityMeasure ProjectivePoint) :
    Tendsto (fun n => probabilityOrbit law E (η n) n) atTop (𝓝 data.forwardMeasure) := by
  obtain ⟨N, hN, s, q, hs, _hs1, hq0, hq1, hbound⟩ :=
    exists_projective_product_moment_geometric_bound law E data
  have ha : Tendsto (fun n : ℕ => q ^ (n / N)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp
      (Nat.tendsto_div_const_atTop hN.ne')
  apply probabilityOrbit_tendsto_varying_initial_of_uniform_pair_moment law E
    data.forwardMeasure data.forward_stationary s hs.le (fun n => q ^ (n / N)) ha
    (fun n p r => ?_) η
  exact hbound n p r

/-- This is the law of the actual iid product at every time, not a Cesàro average. -/
theorem projectiveProcessDistribution_tendsto_forwardMeasure (law : PotentialLaw) (E : ℝ)
    (data : QualitativeData law E) (p : ProjectivePoint) :
    Tendsto (projectiveProcessDistribution law E p) atTop (𝓝 data.forwardMeasure) := by
  have heq : projectiveProcessDistribution law E p =
      (fun n => probabilityOrbit law E (pointDistribution p) n) := by
    funext n
    exact projectiveProcessDistribution_eq_orbit law E p n
  rw [heq]
  exact probabilityOrbit_tendsto_forwardMeasure law E data (fun _ => pointDistribution p)

/-- The actual phase process modulo π converges to the actual forward stationary law. -/
theorem phaseProcessDistribution_tendsto_forwardMeasure (law : PotentialLaw) (E θ : ℝ)
    (data : QualitativeData law E) :
    Tendsto (phaseProcessDistribution law E θ) atTop
      (𝓝 (pullbackPhaseDistribution data.forwardMeasure)) :=
  phaseProcessDistribution_tendsto_of_projective law E θ data.forwardMeasure
    (projectiveProcessDistribution_tendsto_forwardMeasure law E data (phaseProjective θ))

/-- The limiting law of the actual phase process has no atoms. -/
theorem phaseProcessDistribution_has_nonatomic_weak_limit (law : PotentialLaw) (E θ : ℝ)
    (data : QualitativeData law E) :
    ∃ ν : ProbabilityMeasure (AddCircle Real.pi),
      Tendsto (phaseProcessDistribution law E θ) atTop (𝓝 ν) ∧
      ∀ x, (ν : Measure (AddCircle Real.pi)) {x} = 0 := by
  refine ⟨pullbackPhaseDistribution data.forwardMeasure,
    phaseProcessDistribution_tendsto_forwardMeasure law E θ data, ?_⟩
  exact pullbackPhaseDistribution_null_singletons data.forwardMeasure data.forward_null_singletons

/-- Compact-energy contraction gives uniform convergence for each continuous
test, uniformly over all starting distributions. -/
theorem probabilityOrbit_test_tendsto_uniform_on_compact (law : PotentialLaw)
    (input : Input law) (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty)
    (f : C(ProjectivePoint, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ E ∈ K, ∀ η : ProbabilityMeasure ProjectivePoint,
      |(∫ p, f p ∂(probabilityOrbit law E η n : Measure ProjectivePoint)) -
        ∫ p, f p ∂((input.atEnergy E).forwardMeasure : Measure ProjectivePoint)| < ε := by
  obtain ⟨s, hs, _hs1, hdecay⟩ :=
    exists_projective_product_moment_uniform_decay_on_compact law input K hK hne
  obtain ⟨C, hC, hcontrol⟩ := exists_uniform_testOrbit_pair_moment_control law f
    (ε / 2) (half_pos hε) s hs.le
  let δ := ε / (2 * (C + 1))
  have hden : 0 < 2 * (C + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  have hmul : δ * (2 * (C + 1)) = ε := div_mul_cancel₀ ε hden.ne'
  have hCδ : C * δ < ε / 2 := by nlinarith
  filter_upwards [hdecay δ hδ] with n hn
  intro E hE η
  have hpair : ∀ p r, |forwardTestOrbit law E f n p - forwardTestOrbit law E f n r| ≤
      ε / 2 + C * δ := by
    intro p r
    exact (hcontrol E n p r).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left (hn E hE p r).le hC))
  have hbound := probabilityOrbit_test_error_of_pair_bound law E
    (input.atEnergy E).forwardMeasure (input.atEnergy E).forward_stationary η n f _ hpair
  exact hbound.trans_lt (by linarith)

end FixedCouplingPoisson.Furstenberg
