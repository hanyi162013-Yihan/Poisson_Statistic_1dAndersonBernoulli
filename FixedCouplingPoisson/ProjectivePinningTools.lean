import FixedCouplingPoisson.ProjectiveCesaro
import FixedCouplingPoisson.PhaseWeakTools
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.UniformSpace.Dini

/-!
# Continuous anchor kernels and weak-law pinning

The kernels use the actual Euclidean projective determinant distance. Their
integrals vanish from absence of the anchor atom, uniformly on compact
continuous families. Weak convergence then bounds the actual probabilities
of closed anchor neighborhoods; no finite-time atomlessness is assumed.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter
open scoped Topology

private theorem distance_nonneg (p q : ProjectivePoint) : 0 ≤ projectiveDistance p q := by
  by_cases heq : p = q
  · exact ((projectiveDistance_eq_zero_iff p q).mpr heq).symm.le
  · exact ((projectiveDistance_pos_iff p q).mpr heq).le

/-- Continuous tests decreasing to the singleton indicator of the actual anchor. -/
def projectiveAnchorKernel (β : ProjectivePoint) (m : ℕ) : C(ProjectivePoint, ℝ) :=
  ⟨fun p => (1 - projectiveDistance p β) ^ m,
    (continuous_const.sub (continuous_projectiveDistance_right β)).pow m⟩

theorem projectiveAnchorKernel_nonneg (β p : ProjectivePoint) (m : ℕ) :
    0 ≤ projectiveAnchorKernel β m p :=
  pow_nonneg (sub_nonneg.mpr (projectiveDistance_le_one p β)) m

theorem projectiveAnchorKernel_le_one (β p : ProjectivePoint) (m : ℕ) :
    projectiveAnchorKernel β m p ≤ 1 := by
  exact pow_le_one₀ (sub_nonneg.mpr (projectiveDistance_le_one p β))
    (sub_le_self _ (distance_nonneg p β))

@[simp] theorem projectiveAnchorKernel_self (β : ProjectivePoint) (m : ℕ) :
    projectiveAnchorKernel β m β = 1 := by
  change (1 - projectiveDistance β β) ^ m = 1
  rw [(projectiveDistance_eq_zero_iff β β).mpr rfl]
  simp

theorem projectiveAnchorKernel_antitone (β p : ProjectivePoint) :
    Antitone (fun m => projectiveAnchorKernel β m p) :=
  pow_right_anti₀ (sub_nonneg.mpr (projectiveDistance_le_one p β))
    (sub_le_self _ (distance_nonneg p β))

/-- At every non-anchor direction the kernel converges to zero. -/
theorem projectiveAnchorKernel_tendsto_zero (β p : ProjectivePoint) (hp : p ≠ β) :
    Tendsto (fun m => projectiveAnchorKernel β m p) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one
    (sub_nonneg.mpr (projectiveDistance_le_one p β))
    (by linarith [(projectiveDistance_pos_iff p β).mpr hp])

/-- Absence of just the anchor atom suffices for the integral limit. -/
theorem projectiveAnchorKernel_integral_tendsto_zero (ν : ProbabilityMeasure ProjectivePoint)
    (β : ProjectivePoint) (hβ : (ν : Measure ProjectivePoint) {β} = 0) :
    Tendsto (fun m => ∫ p, projectiveAnchorKernel β m p ∂(ν : Measure ProjectivePoint))
      atTop (𝓝 0) := by
  have hne : ∀ᵐ p ∂(ν : Measure ProjectivePoint), p ≠ β := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_eq_eq_singleton] using hβ
  have h := tendsto_integral_of_dominated_convergence (μ := (ν : Measure ProjectivePoint))
    (fun _ => (1 : ℝ))
    (fun m => (projectiveAnchorKernel β m).continuous.measurable.aestronglyMeasurable)
    (integrable_const 1)
    (fun m => Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (projectiveAnchorKernel_nonneg β p m)]
      exact projectiveAnchorKernel_le_one β p m)
    (hne.mono fun p hp => projectiveAnchorKernel_tendsto_zero β p hp)
  simpa only [integral_zero] using h

/-- Compactness and weak continuity make the stationary anchor kernels vanish uniformly. -/
theorem projectiveAnchorKernel_integral_tendsto_uniformOn
    (ν : ℝ → ProbabilityMeasure ProjectivePoint) (K : Set ℝ) (hK : IsCompact K)
    (hν : ContinuousOn ν K) (β : ProjectivePoint)
    (hβ : ∀ E ∈ K, (ν E : Measure ProjectivePoint) {β} = 0) :
    TendstoUniformlyOn
      (fun m E => ∫ p, projectiveAnchorKernel β m p ∂(ν E : Measure ProjectivePoint))
      (fun _ => 0) atTop K := by
  apply Antitone.tendstoUniformlyOn_of_forall_tendsto hK
  · intro m
    exact (ProbabilityMeasure.continuous_integral_continuousMap
      (projectiveAnchorKernel β m)).comp_continuousOn hν
  · intro E hE m n hmn
    exact integral_mono (integrable_continuous_test (projectiveAnchorKernel β n) (ν E))
      (integrable_continuous_test (projectiveAnchorKernel β m) (ν E))
      (fun p => projectiveAnchorKernel_antitone β p hmn)
  · exact continuousOn_const
  · intro E hE
    exact projectiveAnchorKernel_integral_tendsto_zero (ν E) β (hβ E hE)

/-- A fixed continuous anchor test is at least one half on a genuine closed neighborhood. -/
theorem projectiveAnchorKernel_half_near (β : ProjectivePoint) (m : ℕ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p,
      projectiveDistance p β ≤ δ → (1 : ℝ) / 2 ≤ projectiveAnchorKernel β m p := by
  obtain ⟨r, hr, hmod⟩ := continuous_test_projective_modulus
    (projectiveAnchorKernel β m) (1 / 2) (by norm_num)
  refine ⟨r / 2, half_pos hr, fun p hp => ?_⟩
  have hnear := hmod p β (show projectiveDistance p β < r by linarith)
  rw [projectiveAnchorKernel_self] at hnear
  have h := (abs_lt.mp hnear).1
  linarith

/-- Weak convergence to an atom-free anchor gives small closed-neighborhood probabilities. -/
theorem exists_anchor_pinning_of_tendsto (μ : ℕ → ProbabilityMeasure ProjectivePoint)
    (ν : ProbabilityMeasure ProjectivePoint) (hμ : Tendsto μ atTop (𝓝 ν))
    (β : ProjectivePoint) (hβ : (ν : Measure ProjectivePoint) {β} = 0)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      (μ n : Measure ProjectivePoint) {p | projectiveDistance p β ≤ δ} < ENNReal.ofReal ε := by
  have hkernel := projectiveAnchorKernel_integral_tendsto_zero ν β hβ
  obtain ⟨m, hm⟩ := (hkernel.eventually (gt_mem_nhds (show 0 < ε / 4 by positivity))).exists
  obtain ⟨δ, hδ, hnear⟩ := projectiveAnchorKernel_half_near β m
  have ht := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ
    ((ContinuousMap.equivBoundedOfCompact ProjectivePoint ℝ) (projectiveAnchorKernel β m))
  have hevent : ∀ᶠ n in atTop,
      (∫ p, projectiveAnchorKernel β m p ∂(μ n : Measure ProjectivePoint)) < ε / 2 :=
    ht.eventually (gt_mem_nhds (show
      (∫ p, projectiveAnchorKernel β m p ∂(ν : Measure ProjectivePoint)) < ε / 2 by linarith))
  refine ⟨δ, hδ, hevent.mono fun n hn => ?_⟩
  have hi := (integrable_continuous_test (projectiveAnchorKernel β m) (μ n)).const_mul 2
  have hbound := hi.measure_le_integral
    (Eventually.of_forall fun p => mul_nonneg (by norm_num) (projectiveAnchorKernel_nonneg β p m))
    (s := {p | projectiveDistance p β ≤ δ}) (fun p hp => by
      linarith [hnear p hp])
  rw [integral_const_mul] at hbound
  exact hbound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith))

end FixedCouplingPoisson.Furstenberg
