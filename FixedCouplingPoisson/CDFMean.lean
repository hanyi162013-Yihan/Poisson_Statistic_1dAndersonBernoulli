import FixedCouplingPoisson.CDFDynamics
import FixedCouplingPoisson.CDFUniform


/-! Factored proof group: CDFBounds. -/

/-! Unchecked work draft. Actual same-energy CDF gaps lie in [0,pi]
before exit. Compact-energy regularity controls the difference from the
exact-drift two-energy coordinate, uniformly over all lifted phases. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set

def cdfSameEnergyGap (ν : ProbabilityMeasure ProjectivePoint) (θ φ : ℝ) : ℝ :=
  stationaryCDFLift ν θ - stationaryCDFLift ν φ

theorem cdfSameEnergyGap_nonneg (ν : ProbabilityMeasure ProjectivePoint)
    {θ φ : ℝ} (hinit : φ ≤ θ) : 0 ≤ cdfSameEnergyGap ν θ φ :=
  sub_nonneg.mpr (stationaryCDFLift_monotone ν hinit)

theorem cdfSameEnergyGap_le_pi (ν : ProbabilityMeasure ProjectivePoint)
    {θ φ : ℝ} (hsmall : θ - φ ≤ Real.pi) : cdfSameEnergyGap ν θ φ ≤ Real.pi := by
  have hθφ : θ ≤ φ + Real.pi := by linarith
  have h := stationaryCDFLift_monotone ν hθφ
  have hp := stationaryCDFLift_add_int ν φ 1
  simp only [Int.cast_one, one_mul] at hp
  rw [hp] at h
  dsimp [cdfSameEnergyGap]
  linarith

def cdfSameEnergyGapProcess (ν : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (n : ℕ) (ω : PotentialSpace) : ℝ :=
  cdfSameEnergyGap ν (canonicalPhaseProcess E θ n ω)
    (canonicalPhaseProcess (E + δ) φ n ω)

theorem cdfSameEnergyGapProcess_before_bounds (ν : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (hδ : 0 ≤ δ) (hinit : φ ≤ θ) (n : ℕ) (ω : PotentialSpace)
    (hbefore : (n : WithTop ℕ) < canonicalCrossingTime E δ θ φ ω) :
    0 ≤ cdfSameEnergyGapProcess ν E δ θ φ n ω ∧
      cdfSameEnergyGapProcess ν E δ θ φ n ω ≤ Real.pi := by
  have hlo := canonicalGapProcess_nonneg E δ θ φ hδ hinit n ω
  have hhi := canonicalCrossingTime_before E δ θ φ n ω hbefore
  exact ⟨cdfSameEnergyGap_nonneg ν (sub_nonneg.mp hlo),
    cdfSameEnergyGap_le_pi ν hhi.le⟩

theorem cdfGapProcess_sub_sameEnergy (ν ν' : ProbabilityMeasure ProjectivePoint)
    (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) :
    cdfGapProcess ν ν' E δ θ φ n ω - cdfSameEnergyGapProcess ν E δ θ φ n ω =
      stationaryCDFLift ν (canonicalPhaseProcess (E + δ) φ n ω) -
        stationaryCDFLift ν' (canonicalPhaseProcess (E + δ) φ n ω) := by
  dsimp [cdfGapProcess, cdfProcess, cdfSameEnergyGapProcess, cdfSameEnergyGap]
  ring

variable (ν : ℝ → ProbabilityMeasure ProjectivePoint) (hweak : Continuous ν)
  (hatom : ∀ E p, (ν E : Measure ProjectivePoint) {p} = 0)

include hweak hatom in
/-- The exact-drift coordinate and the nonnegative same-energy gap
are uniformly close at every time and every path, before or after exit. -/
theorem cdfGapProcess_energy_error_uniform {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, ∀ n ω,
        |cdfGapProcess (ν E) (ν (E + δ)) E δ θ φ n ω -
          cdfSameEnergyGapProcess (ν E) E δ θ φ n ω| < ε := by
  obtain ⟨d, hd, he⟩ := stationaryCDFLift_energy_uniform ν hweak hatom hK hε
  refine ⟨d, hd, ?_⟩
  intro E hE δ hδ hE' hδd θ φ n ω
  rw [cdfGapProcess_sub_sameEnergy]
  have hEE' : |E - (E + δ)| < d := by
    have heq : E - (E + δ) = -δ := by ring
    simpa only [heq, abs_neg, abs_of_nonneg hδ] using hδd
  exact he E hE (E + δ) hE' hEE' _

include hweak hatom in
/-- Small oriented gaps have small same-energy CDF gaps, uniformly
over the common phase and a compact set of energies. -/
theorem cdfSameEnergyGap_small_uniform {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ θ φ : ℝ, φ ≤ θ → θ - φ < d →
      0 ≤ cdfSameEnergyGap (ν E) θ φ ∧ cdfSameEnergyGap (ν E) θ φ < ε := by
  obtain ⟨d, hd, hb⟩ := stationaryCDFLift_phase_uniform ν hweak hatom hK hε
  refine ⟨d, hd, ?_⟩
  intro E hE θ φ hinit hsmall
  have hn := cdfSameEnergyGap_nonneg (ν E) hinit
  refine ⟨hn, ?_⟩
  have hclose : |θ - φ| < d := by
    rwa [abs_of_nonneg (sub_nonneg.mpr hinit)]
  have h := hb E hE θ φ hclose
  change |cdfSameEnergyGap (ν E) θ φ| < ε at h
  simpa only [abs_of_nonneg hn] using h

/-- The model's compact-energy coordinate error follows from the
authorized Furstenberg data, with no extra regularity field. -/
theorem inverseCDFGap_energy_error_uniform (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, ∀ n ω,
        |cdfGapProcess (input.atEnergy E).inverseMeasure
            (input.atEnergy (E + δ)).inverseMeasure E δ θ φ n ω -
          cdfSameEnergyGapProcess (input.atEnergy E).inverseMeasure E δ θ φ n ω| < ε :=
  cdfGapProcess_energy_error_uniform (fun E => (input.atEnergy E).inverseMeasure)
    (continuous_selected_inverseMeasure law input)
    (fun E => (input.atEnergy E).inverse_null_singletons) hK hε

end FixedCouplingPoisson.Furstenberg

/-! Factored proof group: CDFExitBounds. -/

/-! Unchecked work draft. Uniform regularity of the actual inverse
stationary CDF converts the deterministic angular overshoot to a CDF exit
coordinate close to pi. No inverse CDF or full-support hypothesis is used. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set

variable (ν : ℝ → ProbabilityMeasure ProjectivePoint) (hweak : Continuous ν)
  (hν : ∀ E p, (ν E : Measure ProjectivePoint) {p} = 0)

include hweak hν in
theorem stationaryCDFLift_exit_uniform {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ E' ∈ K, ∀ δ ≥ 0, |E - E'| < d → δ < d →
      ∀ θ φ : ℝ, Real.pi ≤ θ - φ → θ - φ ≤ Real.pi + δ →
        |stationaryCDFLift (ν E) θ - stationaryCDFLift (ν E') φ - Real.pi| < ε := by
  obtain ⟨d, hd, hb⟩ := stationaryCDFLift_period_gap_uniform ν hweak hν hK hε
  refine ⟨d, hd, ?_⟩
  intro E hE E' hE' δ hδ hEE' hδd θ φ hlo hhi
  have hr : |θ - φ - (1 : ℤ) * Real.pi| < d := by
    simp only [Int.cast_one, one_mul]
    rw [abs_of_nonneg (by linarith)]
    exact (show θ - φ - Real.pi ≤ δ by linarith).trans_lt hδd
  simpa only [Int.cast_one, one_mul] using hb E hE E' hE' hEE' θ φ 1 hr

theorem canonicalCrossingTime_ne_zero (E δ θ φ : ℝ) (hsmall : θ - φ < Real.pi)
    (ω : PotentialSpace) : canonicalCrossingTime E δ θ φ ω ≠ 0 := by
  intro hzero
  have h := canonicalCrossingTime_hits E δ θ φ 0 ω hzero
  simpa only [canonicalGapProcess_zero] using not_le_of_gt hsmall h

theorem canonicalCrossingTime_exit_bounds (E δ θ φ : ℝ) (hδ : 0 ≤ δ)
    (hsmall : θ - φ < Real.pi) (ω : PotentialSpace) (n : ℕ)
    (hn : canonicalCrossingTime E δ θ φ ω = n) :
    Real.pi ≤ canonicalGapProcess E δ θ φ n ω ∧
      canonicalGapProcess E δ θ φ n ω ≤ Real.pi + δ := by
  have hn0 : n ≠ 0 := by
    intro hn0
    exact canonicalCrossingTime_ne_zero E δ θ φ hsmall ω (by simpa only [hn0, WithTop.coe_zero, Nat.cast_zero] using hn)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  exact canonicalCrossingTime_overshoot E δ θ φ hδ m ω hn

include hweak hν in
/-- Every finite first crossing has CDF exit coordinate uniformly close
to pi as the two energies merge in a compact set. -/
theorem cdfGapProcess_exit_uniform {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, θ - φ < Real.pi → ∀ ω (n : ℕ),
        canonicalCrossingTime E δ θ φ ω = n →
          |cdfGapProcess (ν E) (ν (E + δ)) E δ θ φ n ω - Real.pi| < ε := by
  obtain ⟨d, hd, hbound⟩ := stationaryCDFLift_exit_uniform ν hweak hν hK hε
  refine ⟨d, hd, ?_⟩
  intro E hE δ hδ hE' hδd θ φ hsmall ω n hn
  have hb := canonicalCrossingTime_exit_bounds E δ θ φ hδ hsmall ω n hn
  have hEE' : |E - (E + δ)| < d := by
    have heq : E - (E + δ) = -δ := by ring
    simpa only [heq, abs_neg, abs_of_nonneg hδ] using hδd
  exact hbound E hE (E + δ) hE' δ hδ hEE' hδd
    (canonicalPhaseProcess E θ n ω) (canonicalPhaseProcess (E + δ) φ n ω) hb.1 hb.2

/-- Specialization to the actual family in the explicitly supplied
Furstenberg input. Its regularity is proved, not added as an input field. -/
theorem inverseCDFGap_exit_uniform (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, θ - φ < Real.pi → ∀ ω (n : ℕ),
        canonicalCrossingTime E δ θ φ ω = n →
          |cdfGapProcess (input.atEnergy E).inverseMeasure
              (input.atEnergy (E + δ)).inverseMeasure E δ θ φ n ω - Real.pi| < ε :=
  cdfGapProcess_exit_uniform (fun E => (input.atEnergy E).inverseMeasure)
    (continuous_selected_inverseMeasure law input)
    (fun E => (input.atEnergy E).inverse_null_singletons) hK hε

end FixedCouplingPoisson.Furstenberg

/-! Factored proof group: CDFMean. -/

/-! Unchecked work draft. The actual stopped IDS identity and actual
uniform exit coordinate give the mean waiting estimate. Regularity is
derived for the inverse stationary family, with no inverse-CDF assumption. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set

def canonicalCrossingMean (law : PotentialLaw) (E δ θ φ : ℝ) : ℝ :=
  ∫ ω, (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law

theorem canonicalCrossingMean_nonneg (law : PotentialLaw) (E δ θ φ : ℝ) :
    0 ≤ canonicalCrossingMean law E δ θ φ :=
  integral_nonneg (fun _ => Nat.cast_nonneg _)

variable (law : PotentialLaw) (ν : ℝ → ProbabilityMeasure ProjectivePoint)
  (hweak : Continuous ν) (hatom : ∀ E p, (ν E : Measure ProjectivePoint) {p} = 0)
  (hstat : ∀ E, InverseStationary law E (ν E))

include hweak hatom hstat in
/-- The scaled mean is identified uniformly even for arbitrary initial
gaps below the first crossing level. -/
theorem canonicalCrossingMean_exit_error_uniform {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < Real.pi →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        |(Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
            canonicalCrossingMean law E δ θ φ -
          (Real.pi - (stationaryCDFLift (ν E) θ - stationaryCDFLift (ν (E + δ)) φ))| ≤ ε := by
  obtain ⟨d, hd, hexit⟩ := cdfGapProcess_exit_uniform ν hweak hatom hK hε
  refine ⟨d, hd, ?_⟩
  intro E hE δ hδ hE' hδd θ φ hinit hsmall hp
  obtain ⟨hfinite, _, hid⟩ := canonicalCrossingTime_finite_mean_IDS law
    (ν E) (ν (E + δ)) E δ θ φ (hstat E) (hstat (E + δ)) hδ hinit hsmall.le hp
  have hi := integrable_cdfGapProcess_atCrossing law (ν E) (ν (E + δ))
    E δ θ φ hδ hinit hsmall.le hfinite
  have hb : ∀ᵐ ω ∂iidMeasure law,
      ‖cdfGapProcess (ν E) (ν (E + δ)) E δ θ φ
        ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω - Real.pi‖ ≤ ε := by
    filter_upwards [hfinite] with ω hω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
    have he := hexit E hE δ hδ hE' hδd θ φ hsmall ω n hn.symm
    simpa only [← hn, WithTop.untopD_coe, Real.norm_eq_abs] using he.le
  have hierror := norm_integral_le_of_norm_le_const hb
  have herr : |(∫ ω, cdfGapProcess (ν E) (ν (E + δ)) E δ θ φ
      ((canonicalCrossingTime E δ θ φ ω).untopD 0) ω ∂iidMeasure law) - Real.pi| ≤ ε := by
    rw [integral_sub hi (integrable_const _)] at hierror
    simpa only [integral_const, probReal_univ, one_smul, mul_one,
      Real.norm_eq_abs] using hierror
  change |(Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
    (∫ ω, (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law) - _| ≤ ε
  rw [hid]
  convert herr using 1 <;> congr 1 <;> ring

include hweak hatom hstat in
/-- The manuscript's mean profile uses the same-energy initial gap.
The additional error is just the uniform change of the stationary CDF
with energy; no comparison between physical gap and IDS mass is used. -/
theorem canonicalCrossingMean_profile_uniform {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < Real.pi →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        |(Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
            canonicalCrossingMean law E δ θ φ -
          (Real.pi - cdfSameEnergyGap (ν E) θ φ)| ≤ ε := by
  obtain ⟨d0, hd0, hmean⟩ := canonicalCrossingMean_exit_error_uniform
    law ν hweak hatom hstat hK (half_pos hε)
  obtain ⟨d1, hd1, henergy⟩ := stationaryCDFLift_energy_uniform ν hweak hatom hK (half_pos hε)
  refine ⟨min d0 d1, lt_min hd0 hd1, ?_⟩
  intro E hE δ hδ hE' hδd θ φ hinit hsmall hp
  have hm := hmean E hE δ hδ hE' (hδd.trans_le (min_le_left _ _))
    θ φ hinit hsmall hp
  have hEE' : |E - (E + δ)| < d1 := by
    have heq : E - (E + δ) = -δ := by ring
    simpa only [heq, abs_neg, abs_of_nonneg hδ] using
      hδd.trans_le (min_le_right _ _)
  have he := henergy E hE (E + δ) hE' hEE' φ
  calc
    _ = |((Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
        canonicalCrossingMean law E δ θ φ -
        (Real.pi - (stationaryCDFLift (ν E) θ - stationaryCDFLift (ν (E + δ)) φ))) -
        (stationaryCDFLift (ν E) φ - stationaryCDFLift (ν (E + δ)) φ)| := by
          dsimp [cdfSameEnergyGap]
          congr 1
          ring
    _ ≤ _ := abs_sub_le_sum_abs _ _
    _ ≤ ε / 2 + ε / 2 := add_le_add hm he.le
    _ = ε := by ring

include hweak hatom hstat in
/-- Small angular restart gaps have mean asymptotic to the reciprocal
of the actual IDS increment, uniformly over compact energies. -/
theorem canonicalCrossingMean_small_gap_uniform {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < min d Real.pi →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        |(idsCandidate law (E + δ) - idsCandidate law E) *
            canonicalCrossingMean law E δ θ φ - 1| ≤ ε := by
  have hπ : 0 < Real.pi * ε / 2 := half_pos (mul_pos Real.pi_pos hε)
  obtain ⟨d0, hd0, hmean⟩ := canonicalCrossingMean_exit_error_uniform
    law ν hweak hatom hstat hK hπ
  obtain ⟨d1, hd1, hgap⟩ := stationaryCDFLift_initial_gap_uniform
    ν hweak hatom hK hπ
  refine ⟨min d0 d1, lt_min hd0 hd1, ?_⟩
  intro E hE δ hδ hE' hδd θ φ hinit hsmall hp
  have hθφ : θ - φ < min d0 d1 := hsmall.trans_le (min_le_left _ _)
  have hsmπ : θ - φ < Real.pi := hsmall.trans_le (min_le_right _ _)
  have he := hmean E hE δ hδ hE' (hδd.trans_le (min_le_left _ _))
    θ φ hinit hsmπ hp
  have hEE' : |E - (E + δ)| < d1 := by
    have heq : E - (E + δ) = -δ := by ring
    simpa only [heq, abs_neg, abs_of_nonneg hδ] using
      hδd.trans_le (min_le_right _ _)
  have hg := hgap E hE (E + δ) hE' hEE' θ φ
    (by rw [abs_of_nonneg (sub_nonneg.mpr hinit)]; exact hθφ.trans_le (min_le_right _ _))
  have hraw : |(Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      canonicalCrossingMean law E δ θ φ - Real.pi| ≤ Real.pi * ε := by
    calc
      _ = |((Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
          canonicalCrossingMean law E δ θ φ -
          (Real.pi - (stationaryCDFLift (ν E) θ - stationaryCDFLift (ν (E + δ)) φ))) -
          (stationaryCDFLift (ν E) θ - stationaryCDFLift (ν (E + δ)) φ)| := by
            congr 1
            ring
      _ ≤ _ := abs_sub_le_sum_abs _ _
      _ ≤ Real.pi * ε / 2 + Real.pi * ε / 2 := add_le_add he hg.le
      _ = Real.pi * ε := by ring
  have heq : |(Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      canonicalCrossingMean law E δ θ φ - Real.pi| = Real.pi *
      |(idsCandidate law (E + δ) - idsCandidate law E) *
        canonicalCrossingMean law E δ θ φ - 1| := by
    calc
      _ = |Real.pi * ((idsCandidate law (E + δ) - idsCandidate law E) *
          canonicalCrossingMean law E δ θ φ - 1)| := by congr 1; ring
      _ = |Real.pi| * |(idsCandidate law (E + δ) - idsCandidate law E) *
          canonicalCrossingMean law E δ θ φ - 1| := abs_mul _ _
      _ = _ := by rw [abs_of_pos Real.pi_pos]
  rw [heq] at hraw
  exact le_of_mul_le_mul_left hraw Real.pi_pos

include hweak hatom hstat in
/-- Starting just below the upper layer leaves uniformly little scaled
expected future time. This controls all remaining future, not one step. -/
theorem canonicalCrossingMean_upper_layer_uniform {K : Set ℝ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < Real.pi → |θ - φ - Real.pi| < d →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        (idsCandidate law (E + δ) - idsCandidate law E) *
          canonicalCrossingMean law E δ θ φ ≤ ε := by
  have hπ : 0 < Real.pi * ε / 2 := half_pos (mul_pos Real.pi_pos hε)
  obtain ⟨d0, hd0, hmean⟩ := canonicalCrossingMean_exit_error_uniform
    law ν hweak hatom hstat hK hπ
  obtain ⟨d1, hd1, hgap⟩ := stationaryCDFLift_period_gap_uniform
    ν hweak hatom hK hπ
  refine ⟨min d0 d1, lt_min hd0 hd1, ?_⟩
  intro E hE δ hδ hE' hδd θ φ hinit hsmall hclose hp
  have he := hmean E hE δ hδ hE' (hδd.trans_le (min_le_left _ _))
    θ φ hinit hsmall hp
  have hEE' : |E - (E + δ)| < d1 := by
    have heq : E - (E + δ) = -δ := by ring
    simpa only [heq, abs_neg, abs_of_nonneg hδ] using
      hδd.trans_le (min_le_right _ _)
  have hc : |θ - φ - (1 : ℤ) * Real.pi| < d1 := by
    simpa only [Int.cast_one, one_mul] using hclose.trans_le (min_le_right _ _)
  have hg := hgap E hE (E + δ) hE' hEE' θ φ 1 hc
  simp only [Int.cast_one, one_mul] at hg
  have hraw : (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
      canonicalCrossingMean law E δ θ φ ≤ Real.pi * ε := by
    have he' := (abs_le.mp he).2
    have hg' := (abs_lt.mp hg).1
    linarith
  apply le_of_mul_le_mul_left (a := Real.pi) ?_ Real.pi_pos
  simpa only [mul_assoc] using hraw

/-- Model specialization: all regularity and stationarity are derived
from the explicitly supplied qualitative Furstenberg data. -/
theorem inverseCrossingMean_exit_error_uniform (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < Real.pi →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        |(Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
            canonicalCrossingMean law E δ θ φ -
          (Real.pi - (stationaryCDFLift (input.atEnergy E).inverseMeasure θ -
            stationaryCDFLift (input.atEnergy (E + δ)).inverseMeasure φ))| ≤ ε :=
  canonicalCrossingMean_exit_error_uniform law
    (fun E => (input.atEnergy E).inverseMeasure)
    (continuous_selected_inverseMeasure law input)
    (fun E => (input.atEnergy E).inverse_null_singletons)
    (fun E => (input.atEnergy E).inverse_stationary) hK hε

theorem inverseCrossingMean_profile_uniform (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < Real.pi →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        |(Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)) *
            canonicalCrossingMean law E δ θ φ -
          (Real.pi - cdfSameEnergyGap (input.atEnergy E).inverseMeasure θ φ)| ≤ ε :=
  canonicalCrossingMean_profile_uniform law
    (fun E => (input.atEnergy E).inverseMeasure)
    (continuous_selected_inverseMeasure law input)
    (fun E => (input.atEnergy E).inverse_null_singletons)
    (fun E => (input.atEnergy E).inverse_stationary) hK hε

theorem inverseCrossingMean_small_gap_uniform (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < min d Real.pi →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        |(idsCandidate law (E + δ) - idsCandidate law E) *
            canonicalCrossingMean law E δ θ φ - 1| ≤ ε :=
  canonicalCrossingMean_small_gap_uniform law
    (fun E => (input.atEnergy E).inverseMeasure)
    (continuous_selected_inverseMeasure law input)
    (fun E => (input.atEnergy E).inverse_null_singletons)
    (fun E => (input.atEnergy E).inverse_stationary) hK hε

theorem inverseCrossingMean_upper_layer_uniform (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < Real.pi → |θ - φ - Real.pi| < d →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        (idsCandidate law (E + δ) - idsCandidate law E) *
          canonicalCrossingMean law E δ θ φ ≤ ε :=
  canonicalCrossingMean_upper_layer_uniform law
    (fun E => (input.atEnergy E).inverseMeasure)
    (continuous_selected_inverseMeasure law input)
    (fun E => (input.atEnergy E).inverse_null_singletons)
    (fun E => (input.atEnergy E).inverse_stationary) hK hε

end FixedCouplingPoisson.Furstenberg
