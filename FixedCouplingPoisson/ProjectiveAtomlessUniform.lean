import FixedCouplingPoisson.ProjectivePinningTools
import FixedCouplingPoisson.ProjectiveMetric
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Uniform small projective neighborhoods for an actual atomless
probability. No Furstenberg input or stationary uniqueness is used.
Draft: actual compilation is deferred. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology

theorem continuous_projectiveAnchorKernel_integral_anchor
    (ν : ProbabilityMeasure ProjectivePoint) (m : ℕ) :
    Continuous (fun β : ProjectivePoint =>
      ∫ p, projectiveAnchorKernel β m p ∂(ν : Measure ProjectivePoint)) := by
  apply continuous_of_dominated (bound := fun _ : ProjectivePoint => (1 : ℝ))
  · intro β
    exact (projectiveAnchorKernel β m).continuous.measurable.aestronglyMeasurable
  · intro β
    exact Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (projectiveAnchorKernel_nonneg β p m)]
      exact projectiveAnchorKernel_le_one β p m
  · exact integrable_const 1
  · apply Eventually.of_forall
    intro p
    change Continuous (fun β : ProjectivePoint => (1 - projectiveDistance p β) ^ m)
    have hpair : Continuous (fun β : ProjectivePoint => (p, β)) :=
      continuous_const.prodMk continuous_id
    have hd : Continuous (fun β : ProjectivePoint => projectiveDistance p β) :=
      continuous_projectiveDistance_joint.comp hpair
    exact (continuous_const.sub hd).pow m

/-- Dini's theorem makes the continuous singleton approximants vanish
uniformly over every anchor, for a single atomless probability. -/
theorem projectiveAnchorKernel_integral_tendsto_uniform_anchor
    (ν : ProbabilityMeasure ProjectivePoint)
    (hν : ∀ β, (ν : Measure ProjectivePoint) {β} = 0) :
    TendstoUniformlyOn
      (fun m β => ∫ p, projectiveAnchorKernel β m p ∂(ν : Measure ProjectivePoint))
      (fun _ => 0) atTop univ := by
  apply Antitone.tendstoUniformlyOn_of_forall_tendsto isCompact_univ
  · intro m
    exact (continuous_projectiveAnchorKernel_integral_anchor ν m).continuousOn
  · intro β hβ m n hmn
    exact integral_mono (integrable_continuous_test (projectiveAnchorKernel β n) ν)
      (integrable_continuous_test (projectiveAnchorKernel β m) ν)
      (fun p => projectiveAnchorKernel_antitone β p hmn)
  · exact continuousOn_const
  · intro β hβ
    exact projectiveAnchorKernel_integral_tendsto_zero ν β (hν β)

/-- A uniform distance radius works for the fixed power at every anchor.
The scalar function (1-d)^m is continuous at d=0 with value one. -/
theorem projectiveAnchorKernel_half_near_uniform (m : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ β p : ProjectivePoint,
      projectiveDistance p β ≤ δ → (1 : ℝ) / 2 ≤ projectiveAnchorKernel β m p := by
  have hc : ContinuousAt (fun d : ℝ => (1 - d) ^ m) 0 := by fun_prop
  obtain ⟨r, hr, hmod⟩ := Metric.continuousAt_iff.mp hc (1 / 2) (by norm_num)
  refine ⟨r / 2, half_pos hr, fun β p hp => ?_⟩
  have hd : 0 ≤ projectiveDistance p β := by
    by_cases heq : p = β
    · exact ((projectiveDistance_eq_zero_iff p β).mpr heq).symm.le
    · exact ((projectiveDistance_pos_iff p β).mpr heq).le
  have hdist : dist (projectiveDistance p β) 0 < r := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hd]
    linarith
  have h := hmod hdist
  change dist ((1 - projectiveDistance p β) ^ m) ((1 - (0 : ℝ)) ^ m) < 1 / 2 at h
  rw [Real.dist_eq, sub_zero, one_pow] at h
  change 1 / 2 ≤ (1 - projectiveDistance p β) ^ m
  linarith [(abs_lt.mp h).1]

/-- Atomlessness on the compact projective line controls all moving
singular directions simultaneously. -/
theorem exists_uniform_projective_atomless_radius
    (ν : ProbabilityMeasure ProjectivePoint)
    (hν : ∀ β, (ν : Measure ProjectivePoint) {β} = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ β : ProjectivePoint,
      (ν : Measure ProjectivePoint) {p | projectiveDistance p β ≤ δ} <
        ENNReal.ofReal ε := by
  have hu := projectiveAnchorKernel_integral_tendsto_uniform_anchor ν hν
  obtain ⟨m, hm⟩ := (Metric.tendstoUniformlyOn_iff.mp hu (ε / 4) (by positivity)).exists
  obtain ⟨δ, hδ, hnear⟩ := projectiveAnchorKernel_half_near_uniform m
  refine ⟨δ, hδ, fun β => ?_⟩
  have hi := (integrable_continuous_test (projectiveAnchorKernel β m) ν).const_mul 2
  have hbound := hi.measure_le_integral
    (Eventually.of_forall fun p => mul_nonneg (by norm_num) (projectiveAnchorKernel_nonneg β p m))
    (s := {p | projectiveDistance p β ≤ δ}) (fun p hp => by
      linarith [hnear β p hp])
  rw [integral_const_mul] at hbound
  have hsmall := hm β (mem_univ β)
  rw [dist_comm, Real.dist_eq, sub_zero] at hsmall
  exact hbound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (by
    linarith [(abs_lt.mp hsmall).2]))

end FixedCouplingPoisson.Furstenberg
