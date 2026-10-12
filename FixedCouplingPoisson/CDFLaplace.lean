import FixedCouplingPoisson.CDFThreshold
import FixedCouplingPoisson.GeometricStopping


/-! Factored proof group: CDFLaplace. -/

/-! Unchecked work draft. The geometric affine identity is instantiated
at the actual first-crossing truncation, with the actual IDS conditional
drift. No model conclusion is supplied by an additional input interface. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory Topology BigOperators

def cdfGeometricDiscount (law : PotentialLaw) (E δ q : ℝ) : ℝ :=
  (1 + q * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)))⁻¹

theorem cdfGeometricDiscount_bounds (law : PotentialLaw) (E δ q : ℝ)
    (hq : 0 ≤ q) (hp : 0 ≤ idsCandidate law (E + δ) - idsCandidate law E) :
    0 ≤ cdfGeometricDiscount law E δ q ∧ cdfGeometricDiscount law E δ q ≤ 1 :=
  Occupation.geometric_discount_bounds hq (mul_nonneg Real.pi_pos.le hp)

/-- The exact affine identity at every actual finite truncation of the
first crossing. It retains the correct initial coordinate for every pair
of starting phases, rather than imposing a zero initial CDF gap. -/
theorem cdfGapProcess_geometric_bounded_stopped_identity (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ q : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (hq : 0 ≤ q) (hp : 0 ≤ idsCandidate law (E + δ) - idsCandidate law E) (N : ℕ) :
    (∫ ω, (cdfGeometricDiscount law E δ q) ^ crossingTruncIndex E δ θ φ N ω *
        (1 + q * cdfGapProcess ν ν' E δ θ φ (crossingTruncIndex E δ θ φ N ω) ω)
        ∂iidMeasure law) -
      (1 + q * (stationaryCDFLift ν θ - stationaryCDFLift ν' φ)) =
      -(q ^ 2 * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))) *
        (∫ ω, ∑ j ∈ Finset.range (crossingTruncIndex E δ θ φ N ω),
          (cdfGeometricDiscount law E δ q) ^ (j + 1) *
            cdfGapProcess ν ν' E δ θ φ j ω ∂iidMeasure law) := by
  have hρ := cdfGeometricDiscount_bounds law E δ q hq hp
  have hrel : cdfGeometricDiscount law E δ q *
      (1 + q * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))) = 1 :=
    Occupation.geometric_discount_relation hq (mul_nonneg Real.pi_pos.le hp)
  have h := Occupation.bounded_stopped_geometric_affine_identity
    pastMeasurableSpace pastMeasurableSpace_le
    (crossingTruncIndex E δ θ φ N) (measurable_crossingTruncIndex E δ θ φ N) N
    (crossingTruncIndex_le E δ θ φ N) (crossingTruncIndex_event_measurable E δ θ φ N)
    (cdfGapProcess ν ν' E δ θ φ) (integrable_cdfGapProcess law ν ν' E δ θ φ)
    (integrable_cdfGapProcess_truncated law ν ν' E δ θ φ hδ hinit hsmall N)
    (cdfGeometricDiscount law E δ q) q
    (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) hρ.1 hρ.2 hrel
    (fun j _ => cdfGapProcess_condExp_IDS law ν ν' E δ θ φ hν hν' j)
  have hzero : (fun ω => 1 + q * cdfGapProcess ν ν' E δ θ φ 0 ω) =
      (fun _ω : PotentialSpace => 1 + q * (stationaryCDFLift ν θ - stationaryCDFLift ν' φ)) := by
    funext ω
    rw [cdfGapProcess_zero]
  rw [hzero] at h
  simpa only [integral_const, probReal_univ, one_smul] using h

end FixedCouplingPoisson.Furstenberg

/-! Factored proof group: CDFLaplaceLimit. -/

/-! Unchecked work draft. The geometric stopped identity has an
unbounded-time limit because the actual crossing time has already been
proved finite and integrable. The coordinate is killed after crossing
solely to give a global dominator for signed occupation sums. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators

def cdfKilledCoordinateProcess (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) : ℝ :=
  if (n : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω then
    cdfGapProcess ν ν' E δ θ φ n ω else 0

theorem measurable_cdfKilledCoordinateProcess
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ) (n : ℕ) :
    Measurable (cdfKilledCoordinateProcess ν ν' E δ θ φ n) :=
  (measurable_cdfGapProcess ν ν' E δ θ φ n).ite
    (pastMeasurableSpace_le n _
      ((canonicalCrossingTime_isStoppingTime E δ θ φ).measurableSet_gt n))
    measurable_const

theorem norm_cdfKilledCoordinateProcess_le
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (n : ℕ) (ω : PotentialSpace) :
    ‖cdfKilledCoordinateProcess ν ν' E δ θ φ n ω‖ ≤ 3 * Real.pi + δ := by
  unfold cdfKilledCoordinateProcess
  split_ifs with hn
  · exact norm_cdfGapProcess_le_of_time_le_crossing
      ν ν' E δ θ φ hδ hinit hsmall n ω hn.le
  · simpa only [norm_zero] using
      (show (0 : ℝ) ≤ 3 * Real.pi + δ by positivity)

theorem canonicalCrossingTime_untopD_le (E δ θ φ : ℝ) (ω : PotentialSpace) :
    (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : WithTop ℕ) ≤
      canonicalCrossingTime E δ θ φ ω := by
  cases hT : canonicalCrossingTime E δ θ φ ω with
  | top => simp only [hT, le_top]
  | coe n => simp only [hT, Nat.cast_withTop, WithTop.untopD_coe, le_refl]

theorem cdfDiscountedKilledCoordinate_sum_eq
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ ρ : ℝ)
    (n : ℕ) (ω : PotentialSpace)
    (hn : (n : WithTop ℕ) ≤ canonicalCrossingTime E δ θ φ ω) :
    Occupation.sumBefore (fun j η =>
      ρ ^ (j + 1) * cdfKilledCoordinateProcess ν ν' E δ θ φ j η) n ω =
        ∑ j ∈ Finset.range n, ρ ^ (j + 1) * cdfGapProcess ν ν' E δ θ φ j ω := by
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : (j : WithTop ℕ) < (n : WithTop ℕ) := by
    exact_mod_cast Finset.mem_range.mp hj
  have hbefore : (j : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω :=
    lt_of_lt_of_le hjn hn
  simp only [cdfKilledCoordinateProcess, if_pos hbefore]

theorem norm_cdfDiscountedKilledCoordinate_le
    (law : PotentialLaw) (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ q : ℝ) (hδ : 0 ≤ δ) (hinit : φ ≤ θ)
    (hsmall : θ - φ ≤ Real.pi) (hq : 0 ≤ q)
    (hp : 0 ≤ idsCandidate law (E + δ) - idsCandidate law E)
    (n : ℕ) (ω : PotentialSpace) :
    ‖(cdfGeometricDiscount law E δ q) ^ (n + 1) *
      cdfKilledCoordinateProcess ν ν' E δ θ φ n ω‖ ≤ 3 * Real.pi + δ := by
  have hρ := cdfGeometricDiscount_bounds law E δ q hq hp
  have hpow : ‖(cdfGeometricDiscount law E δ q) ^ (n + 1)‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hρ.1 _)]
    exact pow_le_one₀ hρ.1 hρ.2
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans
    (by simpa only [one_mul] using
      norm_cdfKilledCoordinateProcess_le ν ν' E δ θ φ hδ hinit hsmall n ω)

theorem norm_cdfGeometricAffine_truncated_le
    (law : PotentialLaw) (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ q : ℝ) (hδ : 0 ≤ δ) (hinit : φ ≤ θ)
    (hsmall : θ - φ ≤ Real.pi) (hq : 0 ≤ q)
    (hp : 0 ≤ idsCandidate law (E + δ) - idsCandidate law E)
    (N : ℕ) (ω : PotentialSpace) :
    ‖(cdfGeometricDiscount law E δ q) ^ crossingTruncIndex E δ θ φ N ω *
      (1 + q * cdfGapProcess ν ν' E δ θ φ (crossingTruncIndex E δ θ φ N ω) ω)‖ ≤
        1 + q * (3 * Real.pi + δ) := by
  have hρ := cdfGeometricDiscount_bounds law E δ q hq hp
  have hpow : ‖(cdfGeometricDiscount law E δ q) ^ crossingTruncIndex E δ θ φ N ω‖ ≤
      (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hρ.1 _)]
    exact pow_le_one₀ hρ.1 hρ.2
  have hinner :
      ‖1 + q * cdfGapProcess ν ν' E δ θ φ (crossingTruncIndex E δ θ φ N ω) ω‖ ≤
        1 + q * (3 * Real.pi + δ) := by
    calc
      _ ≤ 1 + ‖q * cdfGapProcess ν ν' E δ θ φ (crossingTruncIndex E δ θ φ N ω) ω‖ :=
        by simpa only [norm_one] using norm_add_le (1 : ℝ) _
      _ = 1 + q * ‖cdfGapProcess ν ν' E δ θ φ (crossingTruncIndex E δ θ φ N ω) ω‖ :=
        by rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hq]
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (norm_cdfGapProcess_truncated_le ν ν' E δ θ φ hδ hinit hsmall N ω) hq)
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans
    (by simpa only [one_mul] using hinner)

/-- Actual positive IDS increment supplies finite mean before the
dominated-convergence argument. The right side is a signed occupation,
so no unjustified positivity of the two-energy CDF coordinate is used. -/
theorem cdfGapProcess_geometric_stopped_identity (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ q : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (hq : 0 ≤ q) (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E) :
    (∫ ω, (cdfGeometricDiscount law E δ q) ^
        (canonicalCrossingTime E δ θ φ ω).untopD 0 *
      (1 + q * cdfGapProcess ν ν' E δ θ φ
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω) ∂iidMeasure law) -
      (1 + q * (stationaryCDFLift ν θ - stationaryCDFLift ν' φ)) =
      -(q ^ 2 * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))) *
        (∫ ω, Occupation.sumBefore (fun j η =>
          (cdfGeometricDiscount law E δ q) ^ (j + 1) *
            cdfKilledCoordinateProcess ν ν' E δ θ φ j η)
          ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) := by
  obtain ⟨hfinite, hiT, _⟩ := canonicalCrossingTime_finite_mean_IDS
    law ν ν' E δ θ φ hν hν' hδ hinit hsmall hp
  let ρ := cdfGeometricDiscount law E δ q
  let V := Occupation.geometricAffineProcess ρ q (cdfGapProcess ν ν' E δ θ φ)
  let f : ℕ → PotentialSpace → ℝ := fun j ω =>
    ρ ^ (j + 1) * cdfKilledCoordinateProcess ν ν' E δ θ φ j ω
  have hf : ∀ j, Measurable (f j) := fun j => measurable_const.mul
    (measurable_cdfKilledCoordinateProcess ν ν' E δ θ φ j)
  have hmeas : ∀ N : ℕ, AEStronglyMeasurable
      (fun ω => V ((min (canonicalCrossingTime E δ θ φ ω)
        (WithTop.some N : WithTop ℕ)).untopD 0) ω) (iidMeasure law) := by
    intro N
    have hweight : Measurable (fun ω => ρ ^ crossingTruncIndex E δ θ φ N ω) :=
      (measurable_of_countable (fun n : ℕ => ρ ^ n)).comp
        (measurable_crossingTruncIndex E δ θ φ N)
    have hm : Measurable (fun ω => ρ ^ crossingTruncIndex E δ θ φ N ω *
        (1 + q * cdfGapProcess ν ν' E δ θ φ (crossingTruncIndex E δ θ φ N ω) ω)) :=
      hweight.mul (measurable_const.add (measurable_const.mul
        (measurable_cdfGapProcess_truncated ν ν' E δ θ φ N)))
    exact hm.aestronglyMeasurable
  have hbound : ∀ N : ℕ, ∀ᵐ ω ∂iidMeasure law,
      ‖V ((min (canonicalCrossingTime E δ θ φ ω)
        (WithTop.some N : WithTop ℕ)).untopD 0) ω‖ ≤ 1 + q * (3 * Real.pi + δ) :=
    fun N => ae_of_all _ (norm_cdfGeometricAffine_truncated_le
      law ν ν' E δ θ φ q hδ hinit hsmall hq hp.le N)
  have hleft := (Occupation.integral_stopped_truncation_tendsto hfinite V hmeas hbound).sub_const
    (1 + q * (stationaryCDFLift ν θ - stationaryCDFLift ν' φ))
  have hright := (Occupation.stoppedSum_signed_integral_tendsto f hf
    (canonicalCrossingTime_measurable E δ θ φ) hfinite hiT
    (show (0 : ℝ) ≤ 3 * Real.pi + δ by positivity)
    (norm_cdfDiscountedKilledCoordinate_le law ν ν' E δ θ φ q hδ hinit hsmall hq hp.le)).const_mul
      (-(q ^ 2 * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))))
  apply tendsto_nhds_unique hleft
  apply hright.congr
  intro N
  have h := cdfGapProcess_geometric_bounded_stopped_identity
    law ν ν' E δ θ φ q hν hν' hδ hinit hsmall hq hp.le N
  have hsum : (fun ω => Occupation.sumBefore f (crossingTruncIndex E δ θ φ N ω) ω) =
      (fun ω => ∑ j ∈ Finset.range (crossingTruncIndex E δ θ φ N ω),
        ρ ^ (j + 1) * cdfGapProcess ν ν' E δ θ φ j ω) := by
    funext ω
    apply cdfDiscountedKilledCoordinate_sum_eq
    rw [crossingTruncIndex_coe]
    exact min_le_left _ _
  change -(q ^ 2 * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))) *
      (∫ ω, Occupation.sumBefore f (crossingTruncIndex E δ θ φ N ω) ω ∂iidMeasure law) =
      (∫ ω, V (crossingTruncIndex E δ θ φ N ω) ω ∂iidMeasure law) -
        (1 + q * (stationaryCDFLift ν θ - stationaryCDFLift ν' φ))
  rw [hsum]
  exact h.symm

end FixedCouplingPoisson.Furstenberg

/-! Factored proof group: CDFExitLaplace. -/

/-! Unchecked work draft. A finite error budget for the exit Laplace
transform. Endpoint and killed-occupation estimates remain explicit in
this lemma and must be supplied by the actual compact CDF and contraction
proofs; no new external model interface is introduced. -/
noncomputable section
namespace FixedCouplingPoisson.Occupation
open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem integrable_geometricWeight {τ : Ω → ℕ} (hτ : Measurable τ)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    Integrable (fun ω => ρ ^ τ ω) μ := by
  apply (integrable_const (μ := μ) (1 : ℝ)).mono'
    ((measurable_of_countable (fun n : ℕ => ρ ^ n)).comp hτ).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    simp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hρ0 _)]
    exact pow_le_one₀ hρ0 hρ1

theorem geometric_affine_exit_error {τ : Ω → ℕ} (hτ : Measurable τ)
    {U : Ω → ℝ} (hiU : Integrable U μ)
    {ρ q c w₀ e D K : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hq : 0 ≤ q) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hExit : ∀ᵐ ω ∂μ, |U ω - Real.pi| ≤ e)
    (hD : |D| ≤ K)
    (hid : (∫ ω, ρ ^ τ ω * (1 + q * U ω) ∂μ) - (1 + q * w₀) =
      -(q ^ 2 * c) * D) :
    |(1 + q * Real.pi) * (∫ ω, ρ ^ τ ω ∂μ) - (1 + q * w₀)| ≤
      q * e + q ^ 2 * c * K := by
  have hweight : Measurable (fun ω => ρ ^ τ ω) :=
    (measurable_of_countable (fun n : ℕ => ρ ^ n)).comp hτ
  have hweightNorm : ∀ᵐ ω ∂μ, ‖ρ ^ τ ω‖ ≤ (1 : ℝ) := ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hρ0 _)]
    exact pow_le_one₀ hρ0 hρ1
  have hiR := integrable_geometricWeight (μ := μ) hτ hρ0 hρ1
  have hiA : Integrable (fun ω => ρ ^ τ ω * (1 + q * U ω)) μ :=
    ((integrable_const (μ := μ) (1 : ℝ)).add (hiU.const_mul q)).bdd_mul
      hweight.aestronglyMeasurable hweightNorm
  have hiDifference := (hiR.const_mul (1 + q * Real.pi)).sub hiA
  have hterminal :
      |(1 + q * Real.pi) * (∫ ω, ρ ^ τ ω ∂μ) -
        (∫ ω, ρ ^ τ ω * (1 + q * U ω) ∂μ)| ≤ q * e := by
    rw [← integral_const_mul, ← integral_sub (hiR.const_mul (1 + q * Real.pi)) hiA]
    calc
      _ ≤ ∫ ω, ‖(1 + q * Real.pi) * ρ ^ τ ω -
          ρ ^ τ ω * (1 + q * U ω)‖ ∂μ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun ω => (1 + q * Real.pi) * ρ ^ τ ω - ρ ^ τ ω * (1 + q * U ω))
      _ ≤ ∫ _ω : Ω, q * e ∂μ :=
        integral_mono_ae hiDifference.norm (integrable_const (μ := μ) (q * e)) (by
          filter_upwards [hExit] with ω hω
          have hpoint : (1 + q * Real.pi) * ρ ^ τ ω - ρ ^ τ ω * (1 + q * U ω) =
              q * ρ ^ τ ω * (Real.pi - U ω) := by ring
          rw [Real.norm_eq_abs, hpoint, abs_mul, abs_mul,
            abs_of_nonneg hq, abs_of_nonneg (pow_nonneg hρ0 _), abs_sub_comm]
          calc
            _ ≤ q * 1 * e := mul_le_mul
              (mul_le_mul_of_nonneg_left (pow_le_one₀ hρ0 hρ1) hq) hω
              (abs_nonneg _) (by simpa only [mul_one] using hq)
            _ = q * e := by ring)
      _ = q * e := by simp
  have hoccupation :
      |(∫ ω, ρ ^ τ ω * (1 + q * U ω) ∂μ) - (1 + q * w₀)| ≤ q ^ 2 * c * K := by
    rw [hid, abs_mul, abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg q) hc)]
    exact mul_le_mul_of_nonneg_left hD (mul_nonneg (sq_nonneg q) hc)
  calc
    _ = |((1 + q * Real.pi) * (∫ ω, ρ ^ τ ω ∂μ) -
          (∫ ω, ρ ^ τ ω * (1 + q * U ω) ∂μ)) +
        ((∫ ω, ρ ^ τ ω * (1 + q * U ω) ∂μ) - (1 + q * w₀))| := by congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ q * e + q ^ 2 * c * K := add_le_add hterminal hoccupation

theorem geometric_exit_laplace_profile_error {R w₀ q e A : ℝ} (hq : 0 ≤ q)
    (h : |(1 + q * Real.pi) * R - (1 + q * w₀)| ≤ q * e + A) :
    |R - (1 + q * w₀) / (1 + q * Real.pi)| ≤
      (q * e + A) / (1 + q * Real.pi) := by
  have hden : 0 < 1 + q * Real.pi := by positivity
  have heq : R - (1 + q * w₀) / (1 + q * Real.pi) =
      ((1 + q * Real.pi) * R - (1 + q * w₀)) / (1 + q * Real.pi) := by
    field_simp [hden.ne']
    <;> ring
  rw [heq, abs_div, abs_of_nonneg hden.le]
  exact div_le_div_of_nonneg_right h hden.le

end FixedCouplingPoisson.Occupation

namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem norm_sum_cdfDiscountedKilledCoordinate_le
    (law : PotentialLaw) (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ q : ℝ) (hq : 0 ≤ q)
    (hp : 0 ≤ idsCandidate law (E + δ) - idsCandidate law E)
    (n : ℕ) (ω : PotentialSpace) :
    ‖Occupation.sumBefore (fun j η => (cdfGeometricDiscount law E δ q) ^ (j + 1) *
        cdfKilledCoordinateProcess ν ν' E δ θ φ j η) n ω‖ ≤
      Occupation.sumBefore (fun j η => ‖cdfKilledCoordinateProcess ν ν' E δ θ φ j η‖) n ω := by
  have hρ := cdfGeometricDiscount_bounds law E δ q hq hp
  calc
    _ ≤ ∑ j ∈ Finset.range n, ‖(cdfGeometricDiscount law E δ q) ^ (j + 1) *
        cdfKilledCoordinateProcess ν ν' E δ θ φ j ω‖ := norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun j _ => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hρ.1 _)]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (pow_le_one₀ hρ.1 hρ.2) (norm_nonneg (cdfKilledCoordinateProcess ν ν' E δ θ φ j ω)))

theorem cdfDiscountedKilledCoordinate_integral_abs_le
    (law : PotentialLaw) (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ q : ℝ) (hν : InverseStationary law E ν)
    (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi) (hq : 0 ≤ q)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E) :
    |∫ ω, Occupation.sumBefore (fun j η => (cdfGeometricDiscount law E δ q) ^ (j + 1) *
        cdfKilledCoordinateProcess ν ν' E δ θ φ j η)
      ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law| ≤
      ∫ ω, Occupation.sumBefore (fun j η => ‖cdfKilledCoordinateProcess ν ν' E δ θ φ j η‖)
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law := by
  obtain ⟨_, hiT, _⟩ := canonicalCrossingTime_finite_mean_IDS
    law ν ν' E δ θ φ hν hν' hδ hinit hsmall hp
  let f : ℕ → PotentialSpace → ℝ := fun j ω =>
    (cdfGeometricDiscount law E δ q) ^ (j + 1) * cdfKilledCoordinateProcess ν ν' E δ θ φ j ω
  have hif := Occupation.integrable_signed_stoppedSum f
    (fun j => measurable_const.mul (measurable_cdfKilledCoordinateProcess ν ν' E δ θ φ j))
    (canonicalCrossingTime_measurable E δ θ φ) hiT
    (norm_cdfDiscountedKilledCoordinate_le law ν ν' E δ θ φ q hδ hinit hsmall hq hp.le)
  have hiAbs := Occupation.integrable_stoppedSum
    (fun j ω => ‖cdfKilledCoordinateProcess ν ν' E δ θ φ j ω‖)
    (fun j => (measurable_cdfKilledCoordinateProcess ν ν' E δ θ φ j).norm)
    (canonicalCrossingTime_measurable E δ θ φ) hiT
    (fun j ω => norm_nonneg _) (norm_cdfKilledCoordinateProcess_le ν ν' E δ θ φ hδ hinit hsmall)
  calc
    _ ≤ ∫ ω, ‖Occupation.sumBefore f ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω‖
        ∂iidMeasure law := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun ω => Occupation.sumBefore f ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω)
    _ ≤ _ := integral_mono_ae hif.norm hiAbs (ae_of_all _ fun ω =>
      norm_sum_cdfDiscountedKilledCoordinate_le law ν ν' E δ θ φ q hq hp.le _ ω)

theorem cdfGapProcess_geometric_exit_error_le
    (law : PotentialLaw) (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ q e : ℝ) (hν : InverseStationary law E ν)
    (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (hq : 0 ≤ q) (he : 0 ≤ e)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E)
    (hExit : ∀ᵐ ω ∂iidMeasure law,
      |cdfGapProcess ν ν' E δ θ φ ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω - Real.pi| ≤ e) :
    |(1 + q * Real.pi) * (∫ ω, (cdfGeometricDiscount law E δ q) ^
        (canonicalCrossingTime E δ θ φ ω).untopD 0 ∂iidMeasure law) -
      (1 + q * (stationaryCDFLift ν θ - stationaryCDFLift ν' φ))| ≤
      q * e + q ^ 2 * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
        (∫ ω, Occupation.sumBefore (fun j η => ‖cdfKilledCoordinateProcess ν ν' E δ θ φ j η‖)
          ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) := by
  obtain ⟨hfinite, _, _⟩ := canonicalCrossingTime_finite_mean_IDS
    law ν ν' E δ θ φ hν hν' hδ hinit hsmall hp
  have hρ := cdfGeometricDiscount_bounds law E δ q hq hp.le
  exact Occupation.geometric_affine_exit_error
    ((WithTop.measurable_untopD 0).comp (canonicalCrossingTime_measurable E δ θ φ))
    (integrable_cdfGapProcess_atCrossing law ν ν' E δ θ φ hδ hinit hsmall hfinite)
    hρ.1 hρ.2 hq (mul_nonneg Real.pi_pos.le hp.le) he hExit
    (cdfDiscountedKilledCoordinate_integral_abs_le law ν ν' E δ θ φ q
      hν hν' hδ hinit hsmall hq hp)
    (cdfGapProcess_geometric_stopped_identity law ν ν' E δ θ φ q
      hν hν' hδ hinit hsmall hq hp)

/-- Conversion to the ordinary Laplace transform uses only the already
proved first moment. In particular it does not ask for a second moment
of the crossing time or an energy-error/IDS-increment ratio. -/
theorem cdfGapProcess_exit_laplace_profile_error_le
    (law : PotentialLaw) (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ q e : ℝ) (hν : InverseStationary law E ν)
    (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (hq : 0 ≤ q) (he : 0 ≤ e)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E)
    (hExit : ∀ᵐ ω ∂iidMeasure law,
      |cdfGapProcess ν ν' E δ θ φ ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω - Real.pi| ≤ e) :
    |(∫ ω, Real.exp (-(q * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))) *
        (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ)) ∂iidMeasure law) -
      (1 + q * (stationaryCDFLift ν θ - stationaryCDFLift ν' φ)) / (1 + q * Real.pi)| ≤
      (q * e + q ^ 2 * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
        (∫ ω, Occupation.sumBefore (fun j η => ‖cdfKilledCoordinateProcess ν ν' E δ θ φ j η‖)
          ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law)) /
          (1 + q * Real.pi) +
      (q - Real.log (1 + q * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))) /
          (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))) *
        ((Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
          (∫ ω, (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law)) := by
  obtain ⟨_, hiT, _⟩ := canonicalCrossingTime_finite_mean_IDS
    law ν ν' E δ θ φ hν hν' hδ hinit hsmall hp
  have hprofile := Occupation.geometric_exit_laplace_profile_error hq
    (cdfGapProcess_geometric_exit_error_le law ν ν' E δ θ φ q e
      hν hν' hδ hinit hsmall hq he hp hExit)
  have hconversion := Occupation.geometric_laplace_conversion
    ((WithTop.measurable_untopD 0).comp (canonicalCrossingTime_measurable E δ θ φ))
    hiT hq (mul_pos Real.pi_pos hp)
  simp only [Function.comp_apply] at hconversion
  have hexp : (fun ω => Real.exp
      (-q * ((Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
        (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ)))) =
      (fun ω => Real.exp (-(q * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))) *
        (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ))) := by
    funext ω
    congr 1
    ring
  rw [hexp] at hconversion
  rw [abs_sub_comm] at hconversion
  calc
    _ ≤ |(∫ ω, Real.exp (-(q * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))) *
          (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ)) ∂iidMeasure law) -
        (∫ ω, (cdfGeometricDiscount law E δ q) ^
          (canonicalCrossingTime E δ θ φ ω).untopD 0 ∂iidMeasure law)| +
        |(∫ ω, (cdfGeometricDiscount law E δ q) ^
          (canonicalCrossingTime E δ θ φ ω).untopD 0 ∂iidMeasure law) -
          (1 + q * (stationaryCDFLift ν θ - stationaryCDFLift ν' φ)) / (1 + q * Real.pi)| :=
      abs_sub_le _ _ _
    _ ≤ _ := add_le_add hconversion hprofile
    _ = _ := add_comm _ _

end FixedCouplingPoisson.Furstenberg
