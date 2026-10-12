import FixedCouplingPoisson.ProjectiveSL2Proper
import Mathlib.MeasureTheory.Measure.Support

/-! Stationarity makes the actual averaged log norm harmonic with constant
drift. At zero drift its compact minimizer set is invariant under every
transfer from the support. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set
open scoped Topology

theorem integrable_sl2_right_transfer_logGrowth (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (A : RealSL2) :
    Integrable (fun z : ℝ × ProjectivePoint =>
      projectiveLogGrowth (A * schrodingerTransferSL2 E z.1 : RealSL2) z.2)
      (inputDistribution law ν : Measure (ℝ × ProjectivePoint)) := by
  have hi := (integrable_forward_product_test law E (sl2LogContinuousMap A) ν).add
    (integrable_transferLogCocycle law E ν)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro z
  change projectiveLogGrowth A (transferProjective E z.1 z.2) + transferLogCocycle E z.1 z.2 =
    projectiveLogGrowth (A * schrodingerTransferSL2 E z.1 : RealSL2) z.2
  exact (projectiveLogGrowth_sl2_mul_transfer A E z.1 z.2).symm

theorem integrable_stationarySL2Mean_right_transfer (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (A : RealSL2) :
    Integrable (fun v => stationarySL2Mean ν (A * schrodingerTransferSL2 E v)) law.measure := by
  have hi := integrable_sl2_right_transfer_logGrowth law E ν A
  change Integrable _ (law.measure.prod (ν : Measure ProjectivePoint)) at hi
  exact hi.integral_prod_left

/-- The matrix is multiplied on the right by the next transfer. This is
the orientation for which source stationarity gives constant drift. -/
theorem stationarySL2Mean_right_transfer_integral (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : ForwardStationary law E ν) (A : RealSL2) :
    (∫ v, stationarySL2Mean ν (A * schrodingerTransferSL2 E v) ∂law.measure) =
      stationarySL2Mean ν A + stationaryMean law E ν := by
  have hi := integrable_sl2_right_transfer_logGrowth law E ν A
  have hA := integrable_forward_product_test law E (sl2LogContinuousMap A) ν
  have hT := integrable_transferLogCocycle law E ν
  calc
    _ = ∫ z : ℝ × ProjectivePoint,
        projectiveLogGrowth (A * schrodingerTransferSL2 E z.1 : RealSL2) z.2
        ∂(inputDistribution law ν : Measure (ℝ × ProjectivePoint)) :=
      (integral_prod _ hi).symm
    _ = (∫ z, projectiveLogGrowth A (forwardStep E z)
        ∂(inputDistribution law ν : Measure (ℝ × ProjectivePoint))) +
        stationaryMean law E ν := by
      simp_rw [projectiveLogGrowth_sl2_mul_transfer]
      exact integral_add hA hT
    _ = stationarySL2Mean ν A + stationaryMean law E ν := by
      have hstationary := forward_stationary_integral law E ν hν
        (sl2LogContinuousMap A) (sl2LogContinuousMap A).continuous.measurable
      change stationarySL2Mean ν A =
        (∫ z, projectiveLogGrowth A (forwardStep E z)
          ∂(inputDistribution law ν : Measure (ℝ × ProjectivePoint))) at hstationary
      exact congrArg (fun x : ℝ => x + stationaryMean law E ν) hstationary.symm

theorem stationaryMean_nonneg_of_sl2_minimizer (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : ForwardStationary law E ν)
    (A : RealSL2) (hmin : ∀ B : RealSL2, stationarySL2Mean ν A ≤ stationarySL2Mean ν B) :
    0 ≤ stationaryMean law E ν := by
  have h := integral_mono (integrable_const (stationarySL2Mean ν A))
    (integrable_stationarySL2Mean_right_transfer law E ν A)
    (fun v => hmin (A * schrodingerTransferSL2 E v))
  rw [integral_const, probReal_univ, one_smul,
    stationarySL2Mean_right_transfer_integral law E ν hν A] at h
  linarith

theorem sl2_minimizer_right_transfer_of_zero_mean (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : ForwardStationary law E ν)
    (hzero : stationaryMean law E ν = 0) (A : RealSL2)
    (hmin : ∀ B : RealSL2, stationarySL2Mean ν A ≤ stationarySL2Mean ν B)
    (v : ℝ) (hv : v ∈ law.measure.support) :
    stationarySL2Mean ν (A * schrodingerTransferSL2 E v) = stationarySL2Mean ν A := by
  have hi := (integrable_stationarySL2Mean_right_transfer law E ν A).sub
    (integrable_const (stationarySL2Mean ν A))
  have hint : (∫ w, stationarySL2Mean ν (A * schrodingerTransferSL2 E w) -
      stationarySL2Mean ν A ∂law.measure) = 0 := by
    rw [integral_sub (integrable_stationarySL2Mean_right_transfer law E ν A)
      (integrable_const _), stationarySL2Mean_right_transfer_integral law E ν hν A,
      integral_const, probReal_univ, one_smul, hzero]
    ring
  have hae0 := (integral_eq_zero_iff_of_nonneg
    (fun w => sub_nonneg.mpr (hmin (A * schrodingerTransferSL2 E w))) hi).mp hint
  have hae : {w : ℝ | stationarySL2Mean ν (A * schrodingerTransferSL2 E w) =
      stationarySL2Mean ν A} ∈ ae law.measure := by
    filter_upwards [hae0] with w hw
    exact sub_eq_zero.mp hw
  have hmat : Continuous (fun w : ℝ => A * schrodingerTransferSL2 E w) :=
    continuous_const.mul (continuous_schrodingerTransferSL2_fixed E)
  have hclosed : IsClosed {w : ℝ | stationarySL2Mean ν (A * schrodingerTransferSL2 E w) =
      stationarySL2Mean ν A} :=
    isClosed_eq ((continuous_stationarySL2Mean ν).comp hmat) continuous_const
  have hmem := law.measure.support_subset_of_isClosed hclosed hae hv
  change stationarySL2Mean ν (A * schrodingerTransferSL2 E v) = stationarySL2Mean ν A at hmem
  exact hmem

end FixedCouplingPoisson.Furstenberg
