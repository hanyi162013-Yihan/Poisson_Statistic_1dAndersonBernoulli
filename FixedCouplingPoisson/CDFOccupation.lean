import FixedCouplingPoisson.CDFThreshold
import FixedCouplingPoisson.CDFMean
import FixedCouplingPoisson.PairProcess
import FixedCouplingPoisson.UpperLayerStoppedMean
import FixedCouplingPoisson.IDSContinuity
import FixedCouplingPoisson.PairBlockContraction


/-! Factored proof group: UniformIDS. -/

/-! Unchecked work draft. The actual IDS is uniformly continuous on
compact energy sets. Its small increments control the geometric discount
and the scaled fixed-block boundary term; no derivative or lower power
bound for the IDS increment is needed. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open Set

theorem idsCandidate_increment_uniform (law : PotentialLaw)
    {K : Set ℝ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      0 ≤ idsCandidate law (E + δ) - idsCandidate law E ∧
        idsCandidate law (E + δ) - idsCandidate law E < ε := by
  obtain ⟨d, hd, hb⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous (continuous_idsCandidate law).continuousOn) ε hε
  refine ⟨d, hd, ?_⟩
  intro E hE δ hδ hE' hδd
  have hp : 0 ≤ idsCandidate law (E + δ) - idsCandidate law E :=
    sub_nonneg.mpr ((monotone_idsCandidate law) (le_add_of_nonneg_right hδ))
  have hdist : dist E (E + δ) < d := by
    rw [Real.dist_eq]
    have heq : E - (E + δ) = -δ := by ring
    simpa only [heq, abs_neg, abs_of_nonneg hδ] using hδd
  have h := hb E hE (E + δ) hE' hdist
  rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg hp] at h
  exact ⟨hp, h⟩

theorem scaled_idsCandidate_increment_uniform (law : PotentialLaw)
    {K : Set ℝ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      0 ≤ Real.pi * (idsCandidate law (E + δ) - idsCandidate law E) ∧
        Real.pi * (idsCandidate law (E + δ) - idsCandidate law E) < ε := by
  obtain ⟨d, hd, hb⟩ := idsCandidate_increment_uniform law hK
    (div_pos hε Real.pi_pos)
  refine ⟨d, hd, ?_⟩
  intro E hE δ hδ hE' hδd
  have hp := hb E hE δ hδ hE' hδd
  refine ⟨mul_nonneg Real.pi_pos.le hp.1, ?_⟩
  calc
    _ < Real.pi * (ε / Real.pi) := mul_lt_mul_of_pos_left hp.2 Real.pi_pos
    _ = ε := by field_simp [Real.pi_ne_zero]

end FixedCouplingPoisson.Furstenberg

/-! Factored proof group: CDFOccupation. -/

/-! Unchecked work draft. Removing the actual first-crossing truncation
from the proved pair budget, and the deterministic three-region estimate.
The matrix block inequality remains explicit until its actual proof is
instantiated; it is not an additional external input to the manuscript. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators

theorem sin_lower_on_middle {h D : ℝ} (hh0 : 0 ≤ h) (hh : h ≤ Real.pi / 2)
    (hlo : h ≤ D) (hhi : D ≤ Real.pi - h) : Real.sin h ≤ |Real.sin D| := by
  have hD0 : 0 ≤ D := hh0.trans hlo
  have hDpi : D ≤ Real.pi := by linarith
  rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hD0 hDpi)]
  by_cases hmid : D ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) hmid hlo
  · have hreflect : Real.pi - D ≤ Real.pi / 2 := by linarith
    have h := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi / 2) ≤ h by linarith [Real.pi_pos]) hreflect
      (show h ≤ Real.pi - D by linarith)
    simpa only [Real.sin_pi_sub] using h

/-- The bound distinguishes the two oriented ends while the projective
observable only sees distance to an integer multiple of pi. -/
theorem oriented_three_region_bound {h D B ε s : ℝ}
    (hh0 : 0 < h) (hh : h ≤ Real.pi / 2) (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (hB : B ≤ Real.pi) (hsmall : D ≤ h → B ≤ ε) :
    B ≤ ε + (Real.pi / (Real.sin h) ^ s) * |Real.sin D| ^ s +
      Real.pi * (if Real.pi - h ≤ D then (1 : ℝ) else 0) := by
  have hsin : 0 < Real.sin h := Real.sin_pos_of_pos_of_lt_pi hh0
    (by linarith [Real.pi_pos])
  have hpow : 0 < (Real.sin h) ^ s := Real.rpow_pos_of_pos hsin s
  have hC : 0 ≤ Real.pi / (Real.sin h) ^ s :=
    div_nonneg Real.pi_pos.le hpow.le
  have hterm : 0 ≤ (Real.pi / (Real.sin h) ^ s) * |Real.sin D| ^ s :=
    mul_nonneg hC (Real.rpow_nonneg (abs_nonneg _) _)
  by_cases hlo : D ≤ h
  · have hu : 0 ≤ Real.pi * (if Real.pi - h ≤ D then (1 : ℝ) else 0) := by
      split_ifs <;> positivity
    linarith [hsmall hlo]
  · by_cases hup : Real.pi - h ≤ D
    · simp only [if_pos hup, mul_one]
      linarith
    · have hp : (Real.sin h) ^ s ≤ |Real.sin D| ^ s :=
        Real.rpow_le_rpow hsin.le
          (sin_lower_on_middle hh0.le hh (le_of_lt (lt_of_not_ge hlo))
            (le_of_lt (lt_of_not_ge hup))) hs
      have hm : Real.pi ≤ (Real.pi / (Real.sin h) ^ s) * |Real.sin D| ^ s := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hpow]
        exact mul_le_mul_of_nonneg_left hp Real.pi_pos.le
      simp only [if_neg hup, mul_zero, add_zero]
      linarith

theorem pairDistancePower_phasePairProcess (s : ℝ) (hs : 0 ≤ s)
    (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) :
    pairDistancePower s hs (phasePairProcess E (E + δ) θ φ n ω) =
      |Real.sin (canonicalGapProcess E δ θ φ n ω)| ^ s := by
  change projectiveDistance
    (phaseProjective (canonicalPhaseProcess E θ n ω))
    (phaseProjective (canonicalPhaseProcess (E + δ) φ n ω)) ^ s = _
  rw [projectiveDistance_phaseProjective]
  have heq : canonicalPhaseProcess (E + δ) φ n ω - canonicalPhaseProcess E θ n ω =
      -canonicalGapProcess E δ θ φ n ω := by
    dsimp [canonicalGapProcess]
    ring
  rw [heq, Real.sin_neg, abs_neg]

theorem measurable_cdfSameEnergyGapProcess (ν : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (n : ℕ) : Measurable (cdfSameEnergyGapProcess ν E δ θ φ n) :=
  ((stationaryCDFLift_monotone ν).measurable.comp
    (canonicalPhaseProcess_measurable E θ n)).sub
      ((stationaryCDFLift_monotone ν).measurable.comp
        (canonicalPhaseProcess_measurable (E + δ) φ n))

/-- Zero extension beyond the first crossing makes all pointwise bounds
global without asserting that the unstopped oriented gap is bounded. -/
def cdfKilledGapProcess (ν : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) : ℝ :=
  if (n : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω then
    cdfSameEnergyGapProcess ν E δ θ φ n ω else 0

theorem measurable_cdfKilledGapProcess (ν : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (n : ℕ) : Measurable (cdfKilledGapProcess ν E δ θ φ n) :=
  (measurable_cdfSameEnergyGapProcess ν E δ θ φ n).ite
    (pastMeasurableSpace_le n _
      ((canonicalCrossingTime_isStoppingTime E δ θ φ).measurableSet_gt n))
    measurable_const

theorem cdfKilledGapProcess_bounds (ν : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (n : ℕ) (ω : PotentialSpace) :
    0 ≤ cdfKilledGapProcess ν E δ θ φ n ω ∧
      cdfKilledGapProcess ν E δ θ φ n ω ≤ Real.pi := by
  unfold cdfKilledGapProcess
  split_ifs with hn
  · exact cdfSameEnergyGapProcess_before_bounds ν E δ θ φ hδ hinit n ω hn
  · exact ⟨le_rfl, Real.pi_pos.le⟩

theorem cdfKilledGapProcess_sum_eq (ν : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (ω : PotentialSpace) :
    Occupation.sumBefore (cdfKilledGapProcess ν E δ θ φ)
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω =
      Occupation.sumBefore (cdfSameEnergyGapProcess ν E δ θ φ)
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω := by
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt : (j : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω := by
    cases hT : canonicalCrossingTime E δ θ φ ω with
    | top => simp only [hT, WithTop.untopD_top, Finset.mem_range, Nat.not_lt_zero] at hj
    | coe n =>
      simpa only [hT, Nat.cast_withTop, WithTop.untopD_coe, Finset.mem_range, WithTop.coe_lt_coe] using hj
  exact if_pos hjlt

theorem integrable_cdfKilledGap_sum (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E) :
    Integrable (fun ω => Occupation.sumBefore (cdfKilledGapProcess ν E δ θ φ)
      ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω) (iidMeasure law) := by
  obtain ⟨_, hiT, _⟩ := canonicalCrossingTime_finite_mean_IDS law ν ν'
    E δ θ φ hν hν' hδ hinit hsmall hp
  exact Occupation.integrable_stoppedSum (cdfKilledGapProcess ν E δ θ φ)
    (measurable_cdfKilledGapProcess ν E δ θ φ)
    (canonicalCrossingTime_measurable E δ θ φ) hiT
    (fun n ω => (cdfKilledGapProcess_bounds ν E δ θ φ hδ hinit n ω).1)
    (fun n ω => (cdfKilledGapProcess_bounds ν E δ θ φ hδ hinit n ω).2)

/-- All hypotheses in this deterministic ledger will be supplied by the
proved compact CDF moduli. The upper observable counts every later visit. -/
theorem cdfKilledGapProcess_three_region_bound
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ h ε s a : ℝ)
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hh0 : 0 < h) (hh : h ≤ Real.pi / 2)
    (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (hphase : ∀ α β : ℝ, β ≤ α → α - β ≤ h → cdfSameEnergyGap ν α β ≤ ε)
    (hupper : ∀ n ω, Real.pi - h ≤ canonicalGapProcess E δ θ φ n ω →
      Real.pi - a ≤ cdfGapProcess ν ν' E δ θ φ n ω)
    (n : ℕ) (ω : PotentialSpace) :
    cdfKilledGapProcess ν E δ θ φ n ω ≤
      ε + (Real.pi / (Real.sin h) ^ s) *
        pairDistancePower s hs (phasePairProcess E (E + δ) θ φ n ω) +
      Real.pi * cdfUpperVisit ν ν' E δ θ φ a n ω := by
  have hsin : 0 < Real.sin h := Real.sin_pos_of_pos_of_lt_pi hh0
    (by linarith [Real.pi_pos])
  have hC : 0 ≤ Real.pi / (Real.sin h) ^ s :=
    div_nonneg Real.pi_pos.le (Real.rpow_pos_of_pos hsin s).le
  by_cases hbefore : (n : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω
  · have hB := cdfSameEnergyGapProcess_before_bounds ν E δ θ φ hδ hinit n ω hbefore
    have hraw0 := canonicalGapProcess_nonneg E δ θ φ hδ hinit n ω
    have hbound := oriented_three_region_bound hh0 hh hs hε hB.2 (fun hlo =>
      hphase _ _ (sub_nonneg.mp hraw0) hlo)
    have hindicator : (if Real.pi - h ≤ canonicalGapProcess E δ θ φ n ω then
        (1 : ℝ) else 0) ≤ cdfUpperVisit ν ν' E δ θ φ a n ω := by
      split_ifs with hup
      · simp only [cdfUpperVisit, if_pos (hupper n ω hup), le_refl]
      · exact cdfUpperVisit_nonneg ν ν' E δ θ φ a n ω
    simp only [cdfKilledGapProcess, if_pos hbefore]
    rw [pairDistancePower_phasePairProcess]
    exact hbound.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hindicator Real.pi_pos.le))
  · simp only [cdfKilledGapProcess, if_neg hbefore]
    exact add_nonneg (add_nonneg hε
      (mul_nonneg hC (pairDistancePower_nonneg s hs _)))
      (mul_nonneg Real.pi_pos.le (cdfUpperVisit_nonneg ν ν' E δ θ φ a n ω))

/-- The actual compact CDF moduli supply every local hypothesis of the
three-region bound, uniformly over both initial phases and all paths. -/
theorem cdfKilledGapProcess_three_region_uniform
    (ν : ℝ → ProbabilityMeasure ProjectivePoint) (hweak : Continuous ν)
    (hatom : ∀ E p, (ν E : Measure ProjectivePoint) {p} = 0)
    {K : Set ℝ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    (s : ℝ) (hs : 0 ≤ s) :
    ∃ h > 0, h ≤ Real.pi / 2 ∧ ∃ d > 0,
      ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → ∀ n ω,
        cdfKilledGapProcess (ν E) E δ θ φ n ω ≤
          ε + (Real.pi / (Real.sin h) ^ s) *
            pairDistancePower s hs (phasePairProcess E (E + δ) θ φ n ω) +
          Real.pi * cdfUpperVisit (ν E) (ν (E + δ)) E δ θ φ ε n ω := by
  obtain ⟨d0, hd0, hsmall⟩ := cdfSameEnergyGap_small_uniform ν hweak hatom hK hε
  obtain ⟨d1, hd1, hupper⟩ := stationaryCDFLift_raw_upper_lower_uniform ν hweak hatom hK hε
  let h := min (d0 / 2) (min (d1 / 2) (Real.pi / 4))
  have hh0 : 0 < h := lt_min (half_pos hd0)
    (lt_min (half_pos hd1) (by positivity))
  have hh0d : h < d0 := (min_le_left _ _).trans_lt (by linarith)
  have hh1d : h < d1 := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt
    (by linarith)
  have hhpi : h ≤ Real.pi / 2 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (by linarith [Real.pi_pos])
  refine ⟨h, hh0, hhpi, d1, hd1, ?_⟩
  intro E hE δ hδ hE' hδd θ φ hinit n ω
  apply cdfKilledGapProcess_three_region_bound (ν E) (ν (E + δ))
    E δ θ φ h ε s ε hδ hinit hh0 hhpi hs hε.le
  · intro α β horder hgap
    exact (hsmall E hE α β horder (hgap.trans_lt hh0d)).2.le
  · intro j η hgap
    have hl := hupper E hE δ hδ hE' hδd h hh0.le hh1d
      (canonicalPhaseProcess E θ j η) (canonicalPhaseProcess (E + δ) φ j η) hgap
    exact hl

/-- The original crossing's integrability was derived from its actual IDS
drift before this limit is taken. The only remaining hypothesis here is
the separately displayed block inequality for the actual pair operator. -/
theorem phasePairProcess_crossing_occupation (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E)
    (f : C(ProjectivePair, ℝ)) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (L : ℕ) (q ε : ℝ)
    (hblock : ∀ z, (pairKernel law E (E + δ) ^ L) f z ≤ q * f z + ε) :
    (1 - q) * (∫ ω, Occupation.sumBefore
      (fun j ω => f (phasePairProcess E (E + δ) θ φ j ω))
      ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) ≤
      (L : ℝ) + ε * (∫ ω, (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ)
        ∂iidMeasure law) := by
  let T := canonicalCrossingTime E δ θ φ
  let F := fun j ω => f (phasePairProcess E (E + δ) θ φ j ω)
  have hTm : Measurable T := canonicalCrossingTime_measurable E δ θ φ
  have hTs : IsStoppingTime potentialFiltration T :=
    canonicalCrossingTime_isStoppingTime E δ θ φ
  obtain ⟨hfinite, hiT, _⟩ := canonicalCrossingTime_finite_mean_IDS law ν ν'
    E δ θ φ hν hν' hδ hinit hsmall hp
  have hFm : ∀ j, Measurable (F j) := fun j =>
    f.continuous.measurable.comp (phasePairProcess_measurable E (E + δ) θ φ j)
  have hF0 : ∀ j ω, 0 ≤ F j ω := fun j ω => hf0 _
  have hF1 : ∀ j ω, F j ω ≤ 1 := fun j ω => hf1 _
  have hleft := (Occupation.stoppedSum_integral_tendsto F hFm hTm hfinite hiT
    (by norm_num : (0 : ℝ) ≤ 1) hF0 hF1).const_mul (1 - q)
  have hright := ((Occupation.truncatedTime_integral_tendsto hTm hfinite hiT).const_mul ε).const_add
    (L : ℝ)
  apply le_of_tendsto_of_tendsto hleft hright
  apply Eventually.of_forall
  intro N
  exact phasePairProcess_bounded_occupation law E (E + δ) θ φ f hf0 hf1 L q ε hblock
    (Occupation.stoppingTruncIndex T N) (Occupation.measurable_stoppingTruncIndex hTm N) N
    (Occupation.stoppingTruncIndex_le T N)
    (Occupation.stoppingTruncIndex_event_measurable hTs N)

/-- Scaling is performed before using the mean bound. In particular no
ratio of the physical-energy perturbation to the IDS mass is introduced. -/
theorem phasePairProcess_scaled_crossing_occupation (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E)
    (f : C(ProjectivePair, ℝ)) (hf0 : 0 ≤ f) (hf1 : f ≤ 1)
    (L : ℕ) (q ε M : ℝ) (hε : 0 ≤ ε)
    (hmean : (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) ≤ M)
    (hblock : ∀ z, (pairKernel law E (E + δ) ^ L) f z ≤ q * f z + ε) :
    (1 - q) * ((Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, Occupation.sumBefore
        (fun j ω => f (phasePairProcess E (E + δ) θ φ j ω))
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law)) ≤
      (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) * (L : ℝ) + ε * M := by
  let c := Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)
  have h := mul_le_mul_of_nonneg_left
    (phasePairProcess_crossing_occupation law ν ν' E δ θ φ hν hν' hδ hinit hsmall hp
      f hf0 hf1 L q ε hblock) (mul_pos Real.pi_pos hp).le
  calc
    _ = c * ((1 - q) * (∫ ω, Occupation.sumBefore
        (fun j ω => f (phasePairProcess E (E + δ) θ φ j ω))
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law)) := by ring
    _ ≤ c * ((L : ℝ) + ε * (∫ ω,
        (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law)) := h
    _ = c * (L : ℝ) + ε * (c * (∫ ω,
        (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law)) := by ring
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hmean hε)

/-- The three parts are estimated on the IDS scale before the waiting
time bound is used. The perturbation enters as `η * M`, without dividing
by the IDS increment. The displayed block inequality is discharged by
the separate actual matrix-contraction proof. -/
theorem cdfKilledGapProcess_scaled_occupation_le_of_pointwise (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ ε s a b A : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E)
    (hs : 0 ≤ s) (hε : 0 ≤ ε) (hA : 0 ≤ A)
    (hpoint : ∀ n ω, cdfKilledGapProcess ν E δ θ φ n ω ≤
      ε + A * pairDistancePower s hs (phasePairProcess E (E + δ) θ φ n ω) +
        Real.pi * cdfUpperVisit ν ν' E δ θ φ a n ω)
    (hexitLower : ∀ ω (n : ℕ), canonicalCrossingTime E δ θ φ ω = n →
      Real.pi - a ≤ cdfGapProcess ν ν' E δ θ φ n ω)
    (hexitUpper : ∀ ω (n : ℕ), canonicalCrossingTime E δ θ φ ω = n →
      cdfGapProcess ν ν' E δ θ φ n ω ≤ Real.pi + b)
    (L : ℕ) (q η M : ℝ) (hq : q < 1) (hη : 0 ≤ η)
    (hmean : (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) ≤ M)
    (hblock : ∀ z, (pairKernel law E (E + δ) ^ L) (pairDistancePower s hs) z ≤
      q * pairDistancePower s hs z + η) :
    (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, Occupation.sumBefore (cdfKilledGapProcess ν E δ θ φ)
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) ≤
      ε * M + A *
        (((Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) * (L : ℝ) +
          η * M) / (1 - q)) + Real.pi * (a + b) := by
  let T := canonicalCrossingTime E δ θ φ
  let c := Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)
  let C := A
  let B := cdfKilledGapProcess ν E δ θ φ
  let F := fun j ω => pairDistancePower s hs (phasePairProcess E (E + δ) θ φ j ω)
  let U := cdfUpperVisit ν ν' E δ θ φ a
  have hc : 0 ≤ c := (mul_pos Real.pi_pos hp).le
  have hC : 0 ≤ C := hA
  have hTm : Measurable T := canonicalCrossingTime_measurable E δ θ φ
  obtain ⟨_, hiT, _⟩ := canonicalCrossingTime_finite_mean_IDS law ν ν'
    E δ θ φ hν hν' hδ hinit hsmall hp
  have hiB : Integrable (fun ω => Occupation.sumBefore B ((T ω).untopD 0) ω)
      (iidMeasure law) :=
    integrable_cdfKilledGap_sum law ν ν' E δ θ φ hν hν' hδ hinit hsmall hp
  have hFm : ∀ j, Measurable (F j) := fun j =>
    (pairDistancePower s hs).continuous.measurable.comp
      (phasePairProcess_measurable E (E + δ) θ φ j)
  have hiF : Integrable (fun ω => Occupation.sumBefore F ((T ω).untopD 0) ω)
      (iidMeasure law) :=
    Occupation.integrable_stoppedSum F hFm hTm hiT
      (fun j ω => pairDistancePower_nonneg s hs _)
      (fun j ω => pairDistancePower_le_one s hs _)
  have hiU : Integrable (fun ω => Occupation.sumBefore U ((T ω).untopD 0) ω)
      (iidMeasure law) :=
    Occupation.integrable_stoppedSum U (measurable_cdfUpperVisit ν ν' E δ θ φ a)
      hTm hiT (cdfUpperVisit_nonneg ν ν' E δ θ φ a)
      (cdfUpperVisit_le_one ν ν' E δ θ φ a)
  have hsum : ∀ ω, Occupation.sumBefore B ((T ω).untopD 0) ω ≤
      ε * (((T ω).untopD 0 : ℕ) : ℝ) +
        C * Occupation.sumBefore F ((T ω).untopD 0) ω +
        Real.pi * Occupation.sumBefore U ((T ω).untopD 0) ω := fun ω =>
    Occupation.sumBefore_le_affine B F U ε C Real.pi hpoint ((T ω).untopD 0) ω
  have hInt : (∫ ω, Occupation.sumBefore B ((T ω).untopD 0) ω ∂iidMeasure law) ≤
      ε * (∫ ω, (((T ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) +
        C * (∫ ω, Occupation.sumBefore F ((T ω).untopD 0) ω ∂iidMeasure law) +
        Real.pi * (∫ ω, Occupation.sumBefore U ((T ω).untopD 0) ω ∂iidMeasure law) := by
    calc
      _ ≤ ∫ ω, ε * (((T ω).untopD 0 : ℕ) : ℝ) +
          C * Occupation.sumBefore F ((T ω).untopD 0) ω +
          Real.pi * Occupation.sumBefore U ((T ω).untopD 0) ω ∂iidMeasure law :=
        integral_mono_ae hiB
          (((hiT.const_mul ε).add (hiF.const_mul C)).add (hiU.const_mul Real.pi))
          (ae_of_all _ hsum)
      _ = (∫ ω, ε * (((T ω).untopD 0 : ℕ) : ℝ) +
          C * Occupation.sumBefore F ((T ω).untopD 0) ω ∂iidMeasure law) +
          (∫ ω, Real.pi * Occupation.sumBefore U ((T ω).untopD 0) ω ∂iidMeasure law) := by
        simpa only [Pi.add_apply] using
          integral_add ((hiT.const_mul ε).add (hiF.const_mul C)) (hiU.const_mul Real.pi)
      _ = _ := by
        rw [integral_add (hiT.const_mul ε) (hiF.const_mul C)]
        simp only [integral_const_mul, T]
  have hpair := phasePairProcess_scaled_crossing_occupation law ν ν'
    E δ θ φ hν hν' hδ hinit hsmall hp (pairDistancePower s hs)
    (pairDistancePower_nonneg s hs) (pairDistancePower_le_one s hs)
    L q η M hη hmean hblock
  have hpair' : c * (∫ ω, Occupation.sumBefore F ((T ω).untopD 0) ω ∂iidMeasure law) ≤
      (c * (L : ℝ) + η * M) / (1 - q) := by
    change (1 - q) * (c * (∫ ω,
      Occupation.sumBefore F ((T ω).untopD 0) ω ∂iidMeasure law)) ≤ c * (L : ℝ) + η * M at hpair
    apply (le_div_iff₀ (sub_pos.mpr hq)).mpr
    simpa only [mul_comm] using hpair
  have hupperBudget : c * (∫ ω,
      Occupation.sumBefore U ((T ω).untopD 0) ω ∂iidMeasure law) ≤ a + b :=
    cdfUpperVisit_occupation_IDS_le law ν ν' E δ θ φ a b hν hν'
      hδ hinit hsmall hp hexitLower hexitUpper
  calc
    _ ≤ c * (ε * (∫ ω, (((T ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) +
        C * (∫ ω, Occupation.sumBefore F ((T ω).untopD 0) ω ∂iidMeasure law) +
        Real.pi * (∫ ω, Occupation.sumBefore U ((T ω).untopD 0) ω ∂iidMeasure law)) :=
      mul_le_mul_of_nonneg_left hInt hc
    _ = ε * (c * (∫ ω, (((T ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law)) +
        C * (c * (∫ ω, Occupation.sumBefore F ((T ω).untopD 0) ω ∂iidMeasure law)) +
        Real.pi * (c * (∫ ω, Occupation.sumBefore U ((T ω).untopD 0) ω ∂iidMeasure law)) := by ring
    _ ≤ ε * M + C * ((c * (L : ℝ) + η * M) / (1 - q)) + Real.pi * (a + b) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hmean hε)
        (mul_le_mul_of_nonneg_left hpair' hC))
        (mul_le_mul_of_nonneg_left hupperBudget Real.pi_pos.le)

/-- The three parts are estimated on the IDS scale before the waiting
time bound is used. The perturbation enters as `η * M`, without dividing
by the IDS increment. The displayed block inequality is discharged by
the separate actual matrix-contraction proof. -/
theorem cdfKilledGapProcess_scaled_occupation_le (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ h ε s a b : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E)
    (hh0 : 0 < h) (hh : h ≤ Real.pi / 2) (hs : 0 ≤ s) (hε : 0 ≤ ε)
    (hphase : ∀ α β : ℝ, β ≤ α → α - β ≤ h → cdfSameEnergyGap ν α β ≤ ε)
    (hupper : ∀ n ω, Real.pi - h ≤ canonicalGapProcess E δ θ φ n ω →
      Real.pi - a ≤ cdfGapProcess ν ν' E δ θ φ n ω)
    (hexitLower : ∀ ω (n : ℕ), canonicalCrossingTime E δ θ φ ω = n →
      Real.pi - a ≤ cdfGapProcess ν ν' E δ θ φ n ω)
    (hexitUpper : ∀ ω (n : ℕ), canonicalCrossingTime E δ θ φ ω = n →
      cdfGapProcess ν ν' E δ θ φ n ω ≤ Real.pi + b)
    (L : ℕ) (q η M : ℝ) (hq : q < 1) (hη : 0 ≤ η)
    (hmean : (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) ≤ M)
    (hblock : ∀ z, (pairKernel law E (E + δ) ^ L) (pairDistancePower s hs) z ≤
      q * pairDistancePower s hs z + η) :
    (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, Occupation.sumBefore (cdfKilledGapProcess ν E δ θ φ)
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) ≤
      ε * M + (Real.pi / (Real.sin h) ^ s) *
        (((Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) * (L : ℝ) +
          η * M) / (1 - q)) + Real.pi * (a + b) := by
  have hsin : 0 < Real.sin h := Real.sin_pos_of_pos_of_lt_pi hh0
    (by linarith [Real.pi_pos])
  exact cdfKilledGapProcess_scaled_occupation_le_of_pointwise law ν ν'
    E δ θ φ ε s a b (Real.pi / (Real.sin h) ^ s)
    hν hν' hδ hinit hsmall hp hs hε
    (div_nonneg Real.pi_pos.le (Real.rpow_pos_of_pos hsin s).le)
    (cdfKilledGapProcess_three_region_bound ν ν' E δ θ φ h ε s a
      hδ hinit hh0 hh hs hε hphase hupper)
    hexitLower hexitUpper L q η M hq hη hmean hblock

/-- Absolute exact-drift occupation, extended by zero after exit. -/
def cdfKilledNormProcess (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) : ℝ :=
  if (n : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω then
    |cdfGapProcess ν ν' E δ θ φ n ω| else 0

theorem measurable_cdfKilledNormProcess (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (n : ℕ) : Measurable (cdfKilledNormProcess ν ν' E δ θ φ n) :=
  by
    have hm : Measurable (fun ω => |cdfGapProcess ν ν' E δ θ φ n ω|) := by
      simpa only [Real.norm_eq_abs] using
        (measurable_cdfGapProcess ν ν' E δ θ φ n).norm
    exact hm.ite
      (pastMeasurableSpace_le n _
        ((canonicalCrossingTime_isStoppingTime E δ θ φ).measurableSet_gt n))
      measurable_const

theorem cdfKilledNormProcess_nonneg (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) :
    0 ≤ cdfKilledNormProcess ν ν' E δ θ φ n ω := by
  unfold cdfKilledNormProcess
  split_ifs
  · exact abs_nonneg _
  · exact le_rfl

theorem cdfKilledNormProcess_le_gap_add (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ η : ℝ) (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hη : 0 ≤ η)
    (henergy : ∀ n ω, |cdfGapProcess ν ν' E δ θ φ n ω -
      cdfSameEnergyGapProcess ν E δ θ φ n ω| ≤ η) (n : ℕ) (ω : PotentialSpace) :
    cdfKilledNormProcess ν ν' E δ θ φ n ω ≤ cdfKilledGapProcess ν E δ θ φ n ω + η := by
  unfold cdfKilledNormProcess cdfKilledGapProcess
  split_ifs with hn
  · have hB := (cdfSameEnergyGapProcess_before_bounds ν E δ θ φ hδ hinit n ω hn).1
    have hb := abs_add_le
      (cdfGapProcess ν ν' E δ θ φ n ω - cdfSameEnergyGapProcess ν E δ θ φ n ω)
      (cdfSameEnergyGapProcess ν E δ θ φ n ω)
    rw [sub_add_cancel, abs_of_nonneg hB] at hb
    linarith [henergy n ω]
  · exact le_add_of_nonneg_right hη

/-- The energy error is accumulated only as `η * (c E T)` on the
IDS scale. No comparison between `η` and the IDS increment is assumed. -/
theorem cdfKilledNormProcess_scaled_occupation_le (law : PotentialLaw)
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ η M K : ℝ)
    (hν : InverseStationary law E ν) (hν' : InverseStationary law (E + δ) ν')
    (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (hsmall : θ - φ ≤ Real.pi) (hη : 0 ≤ η)
    (hp : 0 < idsCandidate law (E + δ) - idsCandidate law E)
    (henergy : ∀ n ω, |cdfGapProcess ν ν' E δ θ φ n ω -
      cdfSameEnergyGapProcess ν E δ θ φ n ω| ≤ η)
    (hmean : (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) ≤ M)
    (hgap : (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, Occupation.sumBefore (cdfKilledGapProcess ν E δ θ φ)
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) ≤ K) :
    (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      (∫ ω, Occupation.sumBefore (cdfKilledNormProcess ν ν' E δ θ φ)
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) ≤ K + η * M := by
  let T := canonicalCrossingTime E δ θ φ
  let c := Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)
  let B := cdfKilledGapProcess ν E δ θ φ
  let A := cdfKilledNormProcess ν ν' E δ θ φ
  have hc : 0 ≤ c := (mul_pos Real.pi_pos hp).le
  have hTm : Measurable T := canonicalCrossingTime_measurable E δ θ φ
  obtain ⟨_, hiT, _⟩ := canonicalCrossingTime_finite_mean_IDS law ν ν'
    E δ θ φ hν hν' hδ hinit hsmall hp
  have hpoint : ∀ n ω, A n ω ≤ B n ω + η :=
    cdfKilledNormProcess_le_gap_add ν ν' E δ θ φ η hδ hinit hη henergy
  have hiB : Integrable (fun ω => Occupation.sumBefore B ((T ω).untopD 0) ω)
      (iidMeasure law) :=
    integrable_cdfKilledGap_sum law ν ν' E δ θ φ hν hν' hδ hinit hsmall hp
  have hiA : Integrable (fun ω => Occupation.sumBefore A ((T ω).untopD 0) ω)
      (iidMeasure law) :=
    Occupation.integrable_stoppedSum A (measurable_cdfKilledNormProcess ν ν' E δ θ φ)
      hTm hiT (cdfKilledNormProcess_nonneg ν ν' E δ θ φ)
      (fun n ω => (hpoint n ω).trans (add_le_add
        (cdfKilledGapProcess_bounds ν E δ θ φ hδ hinit n ω).2 le_rfl))
  have hsum : ∀ ω, Occupation.sumBefore A ((T ω).untopD 0) ω ≤
      Occupation.sumBefore B ((T ω).untopD 0) ω + η * (((T ω).untopD 0 : ℕ) : ℝ) := by
    intro ω
    have h := Occupation.sumBefore_le_affine A B (fun _ _ => 0) η 1 0
      (fun n ω => by simpa only [one_mul, zero_mul, add_zero, zero_add, add_comm] using hpoint n ω)
      ((T ω).untopD 0) ω
    simpa only [one_mul, zero_mul, add_zero, zero_add, add_comm] using h
  have hInt : (∫ ω, Occupation.sumBefore A ((T ω).untopD 0) ω ∂iidMeasure law) ≤
      (∫ ω, Occupation.sumBefore B ((T ω).untopD 0) ω ∂iidMeasure law) +
        η * (∫ ω, (((T ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) := by
    calc
      _ ≤ ∫ ω, Occupation.sumBefore B ((T ω).untopD 0) ω +
          η * (((T ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law :=
        integral_mono_ae hiA (hiB.add (hiT.const_mul η)) (ae_of_all _ hsum)
      _ = _ := by rw [integral_add hiB (hiT.const_mul η), integral_const_mul]
  calc
    _ ≤ c * ((∫ ω, Occupation.sumBefore B ((T ω).untopD 0) ω ∂iidMeasure law) +
        η * (∫ ω, (((T ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law)) :=
      mul_le_mul_of_nonneg_left hInt hc
    _ = c * (∫ ω, Occupation.sumBefore B ((T ω).untopD 0) ω ∂iidMeasure law) +
        η * (c * (∫ ω, (((T ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law)) := by ring
    _ ≤ K + η * M := add_le_add hgap (mul_le_mul_of_nonneg_left hmean hη)

end FixedCouplingPoisson.Furstenberg

/-! Factored proof group: CDFOccupationUniform. -/

/-! Unchecked work draft. The actual compact block contraction discharges
the last operator premise in the killed occupation estimate. All errors
are put on the IDS scale before the first-moment bound is used. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set Filter
open scoped Topology

/-- The absolute exact-drift coordinate has vanishing IDS-scaled total
occupation, uniformly over compact energies and every initial gap below pi.
The only qualitative external parameter is the declared Furstenberg input. -/
theorem inverseCDFKilledNorm_occupation_uniform (law : PotentialLaw)
    (input : Input law) {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < Real.pi →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
          (∫ ω, Occupation.sumBefore
            (cdfKilledNormProcess (input.atEnergy E).inverseMeasure
              (input.atEnergy (E + δ)).inverseMeasure E δ θ φ)
            ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) ≤ ε := by
  by_cases hne : K.Nonempty
  · obtain ⟨N, hN, s, q, C, hs, hs1, hq0, hq1, hC, hblock⟩ :=
      exists_uniform_pairKernel_block_contraction law input K hK hne
    let ν : ℝ → ProbabilityMeasure ProjectivePoint :=
      fun E => (input.atEnergy E).inverseMeasure
    have hweak : Continuous ν := continuous_selected_inverseMeasure law input
    have hatom : ∀ E p, (ν E : Measure ProjectivePoint) {p} = 0 :=
      fun E => (input.atEnergy E).inverse_null_singletons
    have hstat : ∀ E, InverseStationary law E (ν E) :=
      fun E => (input.atEnergy E).inverse_stationary
    let M : ℝ := 5 * Real.pi + 1
    have hM : 0 < M := by dsimp [M]; positivity
    let r : ℝ := ε / (8 * (M + Real.pi + 1))
    have hr : 0 < r := by dsimp [r]; positivity
    obtain ⟨h, hh0, hhpi, d0, hd0, hthree⟩ :=
      cdfKilledGapProcess_three_region_uniform ν hweak hatom hK hr s hs.le
    obtain ⟨d1, hd1, hexit⟩ := cdfGapProcess_exit_uniform ν hweak hatom hK hr
    obtain ⟨d2, hd2, henergy⟩ := cdfGapProcess_energy_error_uniform ν hweak hatom hK hr
    let A : ℝ := Real.pi / (Real.sin h) ^ s
    have hsin : 0 < Real.sin h := Real.sin_pos_of_pos_of_lt_pi hh0
      (by linarith [Real.pi_pos])
    have hA : 0 < A := div_pos Real.pi_pos (Real.rpow_pos_of_pos hsin s)
    let b : ℝ := ε * (1 - q) / (4 * A)
    have hqgap : 0 < 1 - q := sub_pos.mpr hq1
    have hb : 0 < b := by dsimp [b]; positivity
    have hN1 : 0 < (N : ℝ) + 1 := by positivity
    obtain ⟨d3, hd3, hmass⟩ := scaled_idsCandidate_increment_uniform law hK
      (div_pos hb hN1)
    obtain ⟨d4, hd4, hforce⟩ := Metric.tendsto_nhds_nhds.mp
      (pairBlockForcing_tendsto_zero C s hs) (b / M) (div_pos hb hM)
    let d : ℝ := min 1 (min d0 (min d1 (min d2 (min d3 d4))))
    have hd : 0 < d := lt_min zero_lt_one
      (lt_min hd0 (lt_min hd1 (lt_min hd2 (lt_min hd3 hd4))))
    refine ⟨d, hd, ?_⟩
    intro E hE δ hδ hE' hδd θ φ hinit hsmall hp
    have hδ1 : δ < 1 := hδd.trans_le (min_le_left _ _)
    have htail : δ < min d0 (min d1 (min d2 (min d3 d4))) :=
      hδd.trans_le (min_le_right _ _)
    have hδ0 : δ < d0 := htail.trans_le (min_le_left _ _)
    have htail1 : δ < min d1 (min d2 (min d3 d4)) :=
      htail.trans_le (min_le_right _ _)
    have hδd1 : δ < d1 := htail1.trans_le (min_le_left _ _)
    have htail2 : δ < min d2 (min d3 d4) := htail1.trans_le (min_le_right _ _)
    have hδd2 : δ < d2 := htail2.trans_le (min_le_left _ _)
    have htail3 : δ < min d3 d4 := htail2.trans_le (min_le_right _ _)
    have hδd3 : δ < d3 := htail3.trans_le (min_le_left _ _)
    have hδd4 : δ < d4 := htail3.trans_le (min_le_right _ _)
    let c : ℝ := Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)
    let η : ℝ := C * |δ| ^ s
    have hc : 0 ≤ c := (mul_pos Real.pi_pos hp).le
    have hη : 0 ≤ η := mul_nonneg hC (Real.rpow_nonneg (abs_nonneg δ) s)
    have hmean : c * (∫ ω,
        (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) ≤ M :=
      (canonicalCrossingTime_scaled_mean_le law (ν E) (ν (E + δ)) E δ θ φ
        (hstat E) (hstat (E + δ)) hδ hinit hsmall.le hp).trans
        (add_le_add le_rfl hδ1.le)
    have hcn : c * (N : ℝ) ≤ b := by
      have hcsmall := (hmass E hE δ hδ hE' hδd3).2
      have hcb : c * ((N : ℝ) + 1) < b := (lt_div_iff₀ hN1).mp hcsmall
      exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hc).trans hcb.le
    have hηM : η * M ≤ b := by
      have hdist : dist δ (0 : ℝ) < d4 := by
        simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hδ] using hδd4
      have hηsmall : η < b / M := by
        have hf := hforce hdist
        have hηdist : dist η (0 : ℝ) = η := by
          rw [Real.dist_eq, sub_zero, abs_of_nonneg hη]
        rw [hηdist] at hf
        exact hf
      exact ((lt_div_iff₀ hM).mp hηsmall).le
    have hpairBudget : A * ((c * (N : ℝ) + η * M) / (1 - q)) ≤ ε / 2 := by
      rw [← mul_div_assoc, div_le_iff₀ hqgap]
      calc
        _ ≤ A * (b + b) := mul_le_mul_of_nonneg_left (add_le_add hcn hηM) hA.le
        _ = ε / 2 * (1 - q) := by
          dsimp [b]
          field_simp [hA.ne']
          <;> ring
    have hblock' : ∀ z, (pairKernel law E (E + δ) ^ N) (pairDistancePower s hs.le) z ≤
        q * pairDistancePower s hs.le z + η := by
      intro z
      have heq : E - (E + δ) = -δ := by ring
      simpa only [heq, abs_neg] using hblock E hE (E + δ) z
    have hexitLower : ∀ ω (n : ℕ), canonicalCrossingTime E δ θ φ ω = n →
        Real.pi - r ≤ cdfGapProcess (ν E) (ν (E + δ)) E δ θ φ n ω := by
      intro ω n hn
      exact (by linarith [(abs_lt.mp (hexit E hE δ hδ hE' hδd1 θ φ hsmall ω n hn)).1])
    have hexitUpper : ∀ ω (n : ℕ), canonicalCrossingTime E δ θ φ ω = n →
        cdfGapProcess (ν E) (ν (E + δ)) E δ θ φ n ω ≤ Real.pi + r := by
      intro ω n hn
      exact (by linarith [(abs_lt.mp (hexit E hE δ hδ hE' hδd1 θ φ hsmall ω n hn)).2])
    let B : ℝ := r * M + A * ((c * (N : ℝ) + η * M) / (1 - q)) + Real.pi * (r + r)
    have hgap : c * (∫ ω, Occupation.sumBefore (cdfKilledGapProcess (ν E) E δ θ φ)
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) ≤ B :=
      cdfKilledGapProcess_scaled_occupation_le_of_pointwise law (ν E) (ν (E + δ))
        E δ θ φ r s r r A (hstat E) (hstat (E + δ)) hδ hinit hsmall.le hp hs.le hr.le hA.le
        (hthree E hE δ hδ hE' hδ0 θ φ hinit) hexitLower hexitUpper
        N q η M hq1 hη hmean hblock'
    have hnorm := cdfKilledNormProcess_scaled_occupation_le law (ν E) (ν (E + δ))
      E δ θ φ r M B (hstat E) (hstat (E + δ)) hδ hinit hsmall.le hr.le hp
      (fun n ω => (henergy E hE δ hδ hE' hδd2 θ φ n ω).le) hmean hgap
    apply hnorm.trans
    change r * M + A * ((c * (N : ℝ) + η * M) / (1 - q)) + Real.pi * (r + r) + r * M ≤ ε
    have hrbudget : 2 * r * (M + Real.pi) ≤ ε / 4 := by
      have hden : 0 < M + Real.pi + 1 := by positivity
      have heq : 2 * r * (M + Real.pi + 1) = ε / 4 := by
        dsimp [r]
        field_simp [hden.ne']
        <;> ring
      calc
        _ ≤ 2 * r * (M + Real.pi + 1) :=
          mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)
        _ = ε / 4 := heq
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro E hE
    exact (hne ⟨E, hE⟩).elim

end FixedCouplingPoisson.Furstenberg
