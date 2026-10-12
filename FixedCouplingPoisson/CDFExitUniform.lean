import FixedCouplingPoisson.CDFOccupation
import FixedCouplingPoisson.CDFLaplace


/-! Factored proof group: CDFExitUniform. -/

/-! Unchecked work draft. The actual killed-occupation estimate, exit
coordinate modulus and first moment close the uniform affine Laplace
profile. No second moment or additional model interface is used. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set Filter
open scoped Topology

theorem norm_cdfKilledCoordinateProcess_eq
    (ν ν' : ProbabilityMeasure ProjectivePoint) (E δ θ φ : ℝ)
    (n : ℕ) (ω : PotentialSpace) :
    ‖cdfKilledCoordinateProcess ν ν' E δ θ φ n ω‖ =
      cdfKilledNormProcess ν ν' E δ θ φ n ω := by
  unfold cdfKilledCoordinateProcess cdfKilledNormProcess
  split_ifs <;> simp only [Real.norm_eq_abs, abs_zero]

theorem geometric_rate_error_small {q : ℝ} (hq : 0 ≤ q)
    {r : ℝ} (hr : 0 < r) :
    ∃ d > 0, ∀ c : ℝ, 0 < c → c < d →
      0 ≤ q - Real.log (1 + q * c) / c ∧
        q - Real.log (1 + q * c) / c ≤ r := by
  obtain ⟨d, hd, h⟩ := Metric.tendsto_nhdsWithin_nhds.mp
    (Occupation.geometric_rate_tendsto q) r hr
  refine ⟨d, hd, ?_⟩
  intro c hc hcd
  have hb := h hc (by simpa only [Real.dist_eq, sub_zero, abs_of_pos hc] using hcd)
  have hrate := Occupation.geometric_rate_bounds hq hc
  refine ⟨sub_nonneg.mpr hrate.2, ?_⟩
  rw [Real.dist_eq] at hb
  have hleft := (abs_lt.mp hb).1
  linarith

/-- The full profile is uniform even when the initial gap is not small.
The initial affine term is retained explicitly. -/
theorem inverseCrossingLaplace_profile_uniform (law : PotentialLaw)
    (input : Input law) {K : Set ℝ} (hK : IsCompact K)
    {q : ℝ} (hq : 0 ≤ q) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < Real.pi →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        |(∫ ω, Real.exp
            (-(q * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))) *
              (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ)) ∂iidMeasure law) -
          (1 + q * (stationaryCDFLift (input.atEnergy E).inverseMeasure θ -
            stationaryCDFLift (input.atEnergy (E + δ)).inverseMeasure φ)) /
              (1 + q * Real.pi)| ≤ ε := by
  let ν : ℝ → ProbabilityMeasure ProjectivePoint :=
    fun E => (input.atEnergy E).inverseMeasure
  have hweak : Continuous ν := continuous_selected_inverseMeasure law input
  have hatom : ∀ E p, (ν E : Measure ProjectivePoint) {p} = 0 :=
    fun E => (input.atEnergy E).inverse_null_singletons
  have hstat : ∀ E, InverseStationary law E (ν E) :=
    fun E => (input.atEnergy E).inverse_stationary
  let M : ℝ := 5 * Real.pi + 1
  have hM : 0 < M := by dsimp [M]; positivity
  let r : ℝ := ε / (2 * (q + q ^ 2 + M + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  obtain ⟨d0, hd0, hoccupation⟩ := inverseCDFKilledNorm_occupation_uniform law input hK hr
  obtain ⟨d1, hd1, hexit⟩ := cdfGapProcess_exit_uniform ν hweak hatom hK hr
  obtain ⟨dc, hdc, hrate⟩ := geometric_rate_error_small hq hr
  obtain ⟨d2, hd2, hmass⟩ := scaled_idsCandidate_increment_uniform law hK hdc
  let d : ℝ := min 1 (min d0 (min d1 d2))
  have hd : 0 < d := lt_min zero_lt_one (lt_min hd0 (lt_min hd1 hd2))
  refine ⟨d, hd, ?_⟩
  intro E hE δ hδ hE' hδd θ φ hinit hsmall hp
  have hδ1 : δ < 1 := hδd.trans_le (min_le_left _ _)
  have htail : δ < min d0 (min d1 d2) := hδd.trans_le (min_le_right _ _)
  have hδd0 : δ < d0 := htail.trans_le (min_le_left _ _)
  have htail1 : δ < min d1 d2 := htail.trans_le (min_le_right _ _)
  have hδd1 : δ < d1 := htail1.trans_le (min_le_left _ _)
  have hδd2 : δ < d2 := htail1.trans_le (min_le_right _ _)
  let c : ℝ := Real.pi * (idsCandidate law (E + δ) - idsCandidate law E)
  let T : PotentialSpace → WithTop ℕ := canonicalCrossingTime E δ θ φ
  let I : ℝ := ∫ ω, Occupation.sumBefore
    (fun j η => ‖cdfKilledCoordinateProcess (ν E) (ν (E + δ)) E δ θ φ j η‖)
    ((T ω).untopD 0) ω ∂iidMeasure law
  let t : ℝ := ∫ ω, (((T ω).untopD 0 : ℕ) : ℝ) ∂iidMeasure law
  have hc : 0 < c := mul_pos Real.pi_pos hp
  have hI : 0 ≤ I := integral_nonneg (fun ω =>
    Finset.sum_nonneg (fun j _ => norm_nonneg _))
  have ht : 0 ≤ t := integral_nonneg (fun _ => Nat.cast_nonneg _)
  have hocc : c * I ≤ r := by
    have ho := hoccupation E hE δ hδ hE' hδd0 θ φ hinit hsmall hp
    dsimp only [c, I, T, ν]
    simpa only [Occupation.sumBefore, norm_cdfKilledCoordinateProcess_eq] using ho
  have hmean : c * t ≤ M :=
    (canonicalCrossingTime_scaled_mean_le law (ν E) (ν (E + δ)) E δ θ φ
      (hstat E) (hstat (E + δ)) hδ hinit hsmall.le hp).trans
      (add_le_add le_rfl hδ1.le)
  have hrange := hrate c hc ((hmass E hE δ hδ hE' hδd2).2)
  obtain ⟨hfinite, _, _⟩ := canonicalCrossingTime_finite_mean_IDS
    law (ν E) (ν (E + δ)) E δ θ φ (hstat E) (hstat (E + δ)) hδ hinit hsmall.le hp
  have hExit : ∀ᵐ ω ∂iidMeasure law,
      |cdfGapProcess (ν E) (ν (E + δ)) E δ θ φ ((T ω).untopD 0) ω - Real.pi| ≤ r := by
    filter_upwards [hfinite] with ω hω
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hω
    have he := hexit E hE δ hδ hE' hδd1 θ φ hsmall ω n hn.symm
    simpa only [T, ← hn, WithTop.untopD_coe] using he.le
  have herror := cdfGapProcess_exit_laplace_profile_error_le law (ν E) (ν (E + δ))
    E δ θ φ q r (hstat E) (hstat (E + δ)) hδ hinit hsmall.le hq hr.le hp hExit
  apply herror.trans
  change (q * r + q ^ 2 * c * I) / (1 + q * Real.pi) +
    (q - Real.log (1 + q * c) / c) * (c * t) ≤ ε
  have hnum0 : 0 ≤ q * r + q ^ 2 * c * I :=
    add_nonneg (mul_nonneg hq hr.le)
      (mul_nonneg (mul_nonneg (sq_nonneg q) hc.le) hI)
  have hden : 1 ≤ 1 + q * Real.pi := le_add_of_nonneg_right (mul_nonneg hq Real.pi_pos.le)
  have hnum : q * r + q ^ 2 * c * I ≤ (q + q ^ 2) * r := by
    calc
      _ = q * r + q ^ 2 * (c * I) := by ring
      _ ≤ q * r + q ^ 2 * r := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hocc (sq_nonneg q))
      _ = _ := by ring
  have hdiv := (div_le_self hnum0 hden).trans hnum
  have hconversion : (q - Real.log (1 + q * c) / c) * (c * t) ≤ r * M :=
    mul_le_mul hrange.2 hmean (mul_nonneg hc.le ht) hr.le
  have hrbudget : (q + q ^ 2 + M) * r ≤ ε / 2 := by
    have hdenr : 0 < q + q ^ 2 + M + 1 := by positivity
    calc
      _ ≤ (q + q ^ 2 + M + 1) * r :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hr.le
      _ = ε / 2 := by
        dsimp [r]
        field_simp [hdenr.ne']
        <;> ring
  linarith

/-- On the manuscript's scale `p*T`, a small angular initial gap gives
the Laplace transform of an exponential random variable with mean one. -/
theorem inverseCrossingLaplace_small_gap_uniform (law : PotentialLaw)
    (input : Input law) {K : Set ℝ} (hK : IsCompact K)
    {t : ℝ} (ht : 0 ≤ t) {ε : ℝ} (hε : 0 < ε) :
    ∃ d > 0, ∀ E ∈ K, ∀ δ ≥ 0, E + δ ∈ K → δ < d →
      ∀ θ φ : ℝ, φ ≤ θ → θ - φ < min d Real.pi →
        0 < idsCandidate law (E + δ) - idsCandidate law E →
        |(∫ ω, Real.exp
            (-(t * (idsCandidate law (E + δ) - idsCandidate law E)) *
              (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ)) ∂iidMeasure law) -
          (1 + t)⁻¹| ≤ ε := by
  let q : ℝ := t / Real.pi
  have hq : 0 ≤ q := div_nonneg ht Real.pi_pos.le
  have hqpi : q * Real.pi = t := div_mul_cancel₀ t Real.pi_ne_zero
  let ν : ℝ → ProbabilityMeasure ProjectivePoint :=
    fun E => (input.atEnergy E).inverseMeasure
  have hweak : Continuous ν := continuous_selected_inverseMeasure law input
  have hatom : ∀ E p, (ν E : Measure ProjectivePoint) {p} = 0 :=
    fun E => (input.atEnergy E).inverse_null_singletons
  let e : ℝ := ε / (4 * (q + 1))
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨d0, hd0, hprofile⟩ := inverseCrossingLaplace_profile_uniform law input hK hq (half_pos hε)
  obtain ⟨d1, hd1, hinitial⟩ := stationaryCDFLift_initial_gap_uniform ν hweak hatom hK he
  refine ⟨min d0 d1, lt_min hd0 hd1, ?_⟩
  intro E hE δ hδ hE' hδd θ φ hinit hsmall hp
  have hgap : θ - φ < min d0 d1 := hsmall.trans_le (min_le_left _ _)
  have hsmπ : θ - φ < Real.pi := hsmall.trans_le (min_le_right _ _)
  have hEE' : |E - (E + δ)| < d1 := by
    have heq : E - (E + δ) = -δ := by ring
    simpa only [heq, abs_neg, abs_of_nonneg hδ] using hδd.trans_le (min_le_right _ _)
  have hi := hinitial E hE (E + δ) hE' hEE' θ φ (by
    rw [abs_of_nonneg (sub_nonneg.mpr hinit)]
    exact hgap.trans_le (min_le_right _ _))
  let w : ℝ := stationaryCDFLift (ν E) θ - stationaryCDFLift (ν (E + δ)) φ
  have hw : |w| ≤ e := hi.le
  have h := hprofile E hE δ hδ hE' (hδd.trans_le (min_le_left _ _))
    θ φ hinit hsmπ hp
  have hexp : (fun ω => Real.exp
      (-(q * (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))) *
        (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ))) =
      (fun ω => Real.exp (-(t * (idsCandidate law (E + δ) - idsCandidate law E)) *
        (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ))) := by
    funext ω
    rw [← mul_assoc, hqpi]
  rw [hexp, hqpi] at h
  let L : ℝ := ∫ ω, Real.exp (-(t * (idsCandidate law (E + δ) - idsCandidate law E)) *
    (((canonicalCrossingTime E δ θ φ ω).untopD 0 : ℕ) : ℝ)) ∂iidMeasure law
  change |L - (1 + q * w) / (1 + t)| ≤ ε / 2 at h
  change |L - (1 + t)⁻¹| ≤ ε
  have hden : 0 < 1 + t := by positivity
  have hden1 : 1 ≤ 1 + t := le_add_of_nonneg_right ht
  have heq : (1 + q * w) / (1 + t) - (1 + t)⁻¹ = q * w / (1 + t) := by
    field_simp [hden.ne']
    <;> ring
  have hsmallProfile : |(1 + q * w) / (1 + t) - (1 + t)⁻¹| ≤ ε / 4 := by
    rw [heq, abs_div, abs_mul, abs_of_nonneg hq, abs_of_pos hden]
    calc
      _ ≤ q * |w| := div_le_self (mul_nonneg hq (abs_nonneg w)) hden1
      _ ≤ q * e := mul_le_mul_of_nonneg_left hw hq
      _ ≤ (q + 1) * e :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) he.le
      _ = ε / 4 := by
        dsimp [e]
        field_simp [show q + 1 ≠ 0 by positivity]
        <;> ring
  have htriangle := abs_sub_le L ((1 + q * w) / (1 + t)) ((1 + t)⁻¹)
  linarith

end FixedCouplingPoisson.Furstenberg
