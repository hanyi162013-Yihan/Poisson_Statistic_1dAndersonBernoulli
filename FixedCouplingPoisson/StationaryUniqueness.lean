import FixedCouplingPoisson.StationaryPositiveBlock
import FixedCouplingPoisson.MultiBlockContraction
import FixedCouplingPoisson.ProjectiveWeakLimit

/-!
# Stationary uniqueness from positivity for all stationary probabilities

The input here is the mathematical positivity statement for every actual
forward-stationary probability. The proof uses the actual iid negative
moment block, actual deterministic-time iid restart, and synchronous
projective coupling already formalized in the project.

Neither `Input` nor `QualitativeData` is used. In particular, uniqueness is
not obtained by assuming the existing qualitative interface whose fields
include uniqueness. No new all-time convergence interface is introduced.

This source is an uncompiled draft while checking is deferred by the user.
-/

noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter
open scoped Topology

/-- The actual same-energy iid contraction block follows from positivity
for all stationary probabilities, with no uniqueness premise. -/
theorem exists_projective_block_contraction_of_all_stationary_positive
    (law : PotentialLaw) (E : ℝ)
    (hpos : ∀ ν : ProbabilityMeasure ProjectivePoint,
      ForwardStationary law E ν → 0 < stationaryMean law E ν) :
    ∃ N : ℕ, 0 < N ∧ ∃ s q : ℝ, 0 < s ∧ s ≤ 1 ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ p r : ProjectivePoint,
        pairDistanceMoment law E s p r N ≤ q * (projectiveDistance p r) ^ s := by
  obtain ⟨N, hN, s, q, hs, hs1, hq0, hq1, hq⟩ :=
    exists_uniform_product_negative_log_moment_of_all_stationary_positive law E hpos
  refine ⟨N, hN, s, q, hs, hs1, hq0, hq1, fun p r => ?_⟩
  have heq : (fun ω => (projectiveDistance (projectiveProcess E p N ω)
      (projectiveProcess E r N ω)) ^ s) =
      (fun ω => (projectiveDistance p r) ^ s * Real.exp (-s *
        (projectiveLogGrowth (transferProduct E ω N) p +
          projectiveLogGrowth (transferProduct E ω N) r))) :=
    funext fun ω => projectiveDistance_product_rpow_identity E ω N p r s
  unfold pairDistanceMoment
  rw [heq, integral_const_mul]
  calc
    _ ≤ (projectiveDistance p r) ^ s * q :=
      mul_le_mul_of_nonneg_left (hq p r)
        (Real.rpow_nonneg (projectiveDistance_nonneg p r) s)
    _ = _ := mul_comm _ _

/-- Any two actual stationary probabilities coincide if all actual
stationary probabilities have positive logarithmic mean. The same iid
potential sequence couples their projective trajectories. -/
theorem forwardStationary_unique_of_all_stationary_positive
    (law : PotentialLaw) (E : ℝ)
    (hpos : ∀ ξ : ProbabilityMeasure ProjectivePoint,
      ForwardStationary law E ξ → 0 < stationaryMean law E ξ)
    (ν η : ProbabilityMeasure ProjectivePoint)
    (hν : ForwardStationary law E ν) (hη : ForwardStationary law E η) : ν = η := by
  obtain ⟨N, hN, s, q, hs, _, hq0, hq1, hblock⟩ :=
    exists_projective_block_contraction_of_all_stationary_positive law E hpos
  have hdecay : Tendsto (fun n : ℕ => q ^ (n / N)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp
      (Nat.tendsto_div_const_atTop hN.ne')
  have hmoment : ∀ n p r,
      (∫ ω, projectiveDistance (projectiveProcess E p n ω)
        (projectiveProcess E r n ω) ^ s ∂iidMeasure law) ≤ q ^ (n / N) := by
    intro n p r
    exact pairDistanceMoment_geometric_bound law E s q N hs.le hq0 hblock p r n
  have ht := probabilityOrbit_tendsto_varying_initial_of_uniform_pair_moment
    law E ν hν s hs.le (fun n : ℕ => q ^ (n / N)) hdecay hmoment
    (fun _ => η)
  have heq : (fun n : ℕ => probabilityOrbit law E η n) = (fun _ : ℕ => η) := by
    funext n
    exact probabilityOrbit_stationary law E η hη n
  change Tendsto (fun n : ℕ => probabilityOrbit law E η n) atTop (𝓝 ν) at ht
  rw [heq] at ht
  exact (tendsto_nhds_unique tendsto_const_nhds ht).symm

end FixedCouplingPoisson.Furstenberg
