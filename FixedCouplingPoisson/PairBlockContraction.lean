import FixedCouplingPoisson.ForcedBlockContraction
import FixedCouplingPoisson.PairProcess
import FixedCouplingPoisson.PhaseDistribution

/-!
# Actual pair-kernel contraction and bounded stopped occupation

The operator here is the already defined common-potential pair kernel.
Its powers are identified with the actual iid projective pair process,
using the actual canonical phase process and its checked projective bridge.
The fixed-block estimate is then supplied by the proved matrix-product
contraction, rather than made into an additional external hypothesis.
Only bounded stopping times are treated here; the unbounded limit is separate.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter
open scoped Topology

theorem pairKernel_pow_pairDistancePower_eq_integral (law : PotentialLaw)
    (E E' s : ℝ) (hs : 0 ≤ s) (n : ℕ) (p r : ProjectivePoint) :
    (pairKernel law E E' ^ n) (pairDistancePower s hs) (p, r) =
      ∫ ω, (projectiveDistance (projectiveProcess E p n ω)
        (projectiveProcess E' r n ω)) ^ s ∂iidMeasure law := by
  obtain ⟨θ, rfl⟩ := phaseProjective_surjective p
  obtain ⟨φ, rfl⟩ := phaseProjective_surjective r
  rw [← integral_phasePairProcess_test law E E' θ φ (pairDistancePower s hs) n]
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    change (projectiveDistance
      (phaseProjective (canonicalPhaseProcess E θ n ω))
      (phaseProjective (canonicalPhaseProcess E' φ n ω))) ^ s = _
    rw [phaseProjective_canonicalPhaseProcess, phaseProjective_canonicalPhaseProcess]

theorem pairBlockForcing_tendsto_zero (C s : ℝ) (hs : 0 < s) :
    Tendsto (fun δ : ℝ => C * |δ| ^ s) (𝓝 0) (𝓝 0) := by
  have h : Continuous (fun δ : ℝ => C * |δ| ^ s) :=
    continuous_const.mul ((Real.continuous_rpow_const hs.le).comp continuous_abs)
  simpa only [abs_zero, Real.zero_rpow hs.ne', mul_zero] using h.tendsto 0

/-- The true common-potential Markov kernel satisfies the forced fixed-block
bound, uniformly in the reference energy on a compact set. -/
theorem exists_uniform_pairKernel_block_contraction (law : PotentialLaw)
    (input : Input law) (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ N : ℕ, 0 < N ∧ ∃ s q C : ℝ,
      ∃ hs : 0 < s, s ≤ 1 ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧
      ∀ E ∈ K, ∀ E' : ℝ, ∀ z : ProjectivePair,
        (pairKernel law E E' ^ N) (pairDistancePower s hs.le) z ≤
          q * pairDistancePower s hs.le z + C * |E - E'| ^ s := by
  obtain ⟨N, hN, s, q, C, hs, hs1, hq0, hq1, hC, hblock⟩ :=
    exists_uniform_forced_projective_block_contraction law input K hK hne
  refine ⟨N, hN, s, q, C, hs, hs1, hq0, hq1, hC, fun E hE E' z => ?_⟩
  rcases z with ⟨p, r⟩
  rw [pairKernel_pow_pairDistancePower_eq_integral]
  exact hblock E hE E' p r

/-- A bounded stopping-time occupation estimate for the actual two-energy
canonical phase process. The only qualitative input is `Input law`.
All contraction and conditional-drift premises have been discharged. -/
theorem exists_uniform_phasePairProcess_bounded_occupation (law : PotentialLaw)
    (input : Input law) (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ N : ℕ, 0 < N ∧ ∃ s q C : ℝ,
      0 < s ∧ s ≤ 1 ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧
      ∀ E ∈ K, ∀ E' θ φ : ℝ,
      ∀ τ : PotentialSpace → ℕ, Measurable τ →
      ∀ T : ℕ, (∀ ω, τ ω ≤ T) →
      (∀ j, MeasurableSet[pastMeasurableSpace j] {ω | j < τ ω}) →
        (1 - q) * (∫ ω, ∑ j ∈ Finset.range (τ ω),
          (projectiveDistance
            (phaseProjective (canonicalPhaseProcess E θ j ω))
            (phaseProjective (canonicalPhaseProcess E' φ j ω))) ^ s
          ∂iidMeasure law) ≤
            (N : ℝ) + C * |E - E'| ^ s * (∫ ω, (τ ω : ℝ) ∂iidMeasure law) := by
  obtain ⟨N, hN, s, q, C, hs, hs1, hq0, hq1, hC, hblock⟩ :=
    exists_uniform_pairKernel_block_contraction law input K hK hne
  refine ⟨N, hN, s, q, C, hs, hs1, hq0, hq1, hC, ?_⟩
  intro E hE E' θ φ τ hτm T hτ hA
  simpa only [pairDistancePower, ContinuousMap.coe_mk, phasePairProcess] using
    phasePairProcess_bounded_occupation law E E' θ φ (pairDistancePower s hs.le)
      (pairDistancePower_nonneg s hs.le) (pairDistancePower_le_one s hs.le)
      N q (C * |E - E'| ^ s) (hblock E hE E') τ hτm T hτ hA

end FixedCouplingPoisson.Furstenberg
