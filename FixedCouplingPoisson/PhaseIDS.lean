import FixedCouplingPoisson.IDSExistence
import FixedCouplingPoisson.Sturm

/-! Mean phase speeds and the actual integrated density of states.

The actual finite-volume Sturm count identity identifies the iid shooting-phase
speed with the proved spectral IDS limit. Periodicity and monotonicity give the
same speed for every deterministic initial angle, and taking differences gives
the two-energy mean phase-gap speed. -/

namespace FixedCouplingPoisson
open Filter MeasureTheory
open scoped Topology

theorem measurable_shootingPhase (E : ℝ) (n : ℕ) :
    Measurable (fun ω : PotentialSpace => shootingPhase E ω n) :=
  canonicalPhaseProcess_measurable E 0 n

theorem integrable_shootingPhase (law : PotentialLaw) (E : ℝ) (n : ℕ) :
    Integrable (fun ω : PotentialSpace => shootingPhase E ω n) (iidMeasure law) := by
  apply (integrable_const ((n : ℝ) * Real.pi)).mono'
    (measurable_shootingPhase E n).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (shootingPhase_mem_closed E ω n).1]
      using (shootingPhase_mem_closed E ω n).2)

theorem integral_shootingPhase_count_error (law : PotentialLaw) (E : ℝ) (n : ℕ) :
    |meanSpectralCount law n E +
      (∫ ω, shootingPhase E ω n ∂iidMeasure law) / Real.pi - (n : ℝ)| ≤ 1 / 2 := by
  have hpot : ∀ ω : PotentialSpace, potentialBlock 0 n ω = (fun j => ω j.val) := by
    intro ω
    ext j
    simp only [potentialBlock, zero_add]
  have hb : ∀ ω : PotentialSpace,
      |(nonstrictSpectralCount n (potentialBlock 0 n ω) E : ℝ) +
        shootingPhase E ω n / Real.pi - (n : ℝ)| ≤ 1 / 2 := by
    intro ω
    rw [hpot]
    exact nonstrictSpectralCount_phase_error ω n E
  have hi := iidBlock_count_integrable law 0 n E
  have hp := (integrable_shootingPhase law E n).div_const Real.pi
  have hsum : Integrable (fun ω : PotentialSpace =>
      (nonstrictSpectralCount n (potentialBlock 0 n ω) E : ℝ) +
        shootingPhase E ω n / Real.pi) (iidMeasure law) := hi.add hp
  have h := norm_integral_le_of_norm_le_const (μ := iidMeasure law)
    (f := fun ω : PotentialSpace => (nonstrictSpectralCount n (potentialBlock 0 n ω) E : ℝ) +
      shootingPhase E ω n / Real.pi - (n : ℝ))
    (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb ω)
  simp only [Real.norm_eq_abs, probReal_univ, mul_one] at h
  rw [integral_sub hsum (integrable_const (n : ℝ)), integral_add hi hp, integral_div] at h
  simpa only [iidBlock_count_integral, integral_const, probReal_univ, one_smul] using h

theorem bounded_div_nat_tendsto_zero (b : ℕ → ℝ) (C : ℝ) (h : ∀ n, |b n| ≤ C) :
    Tendsto (fun n => b n / (n : ℝ)) atTop (nhds 0) := by
  apply squeeze_zero_norm (a := fun n : ℕ => C / (n : ℝ))
  · intro n
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ))]
    exact div_le_div_of_nonneg_right (h n) (Nat.cast_nonneg _)
  · exact tendsto_const_div_atTop_nhds_zero_nat C

theorem mean_shootingPhase_tendsto_idsCandidate (law : PotentialLaw) (E : ℝ) :
    Tendsto (fun n => (∫ ω, shootingPhase E ω n ∂iidMeasure law) / (n : ℝ)) atTop
      (nhds (Real.pi * (1 - idsCandidate law E))) := by
  let P := fun n => (∫ ω, shootingPhase E ω n ∂iidMeasure law) / Real.pi
  let b := fun n => meanSpectralCount law n E + P n - (n : ℝ)
  have hb : ∀ n, |b n| ≤ 1 / 2 := fun n => integral_shootingPhase_count_error law E n
  have hd := bounded_div_nat_tendsto_zero b (1 / 2) hb
  have ht := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hasIDS_idsCandidate law E)).add hd
  have hp : Tendsto (fun n => P n / (n : ℝ)) atTop
      (nhds (1 - idsCandidate law E)) := by
    have heq : (fun n => 1 - normalizedMeanCount law E n + b n / (n : ℝ)) =ᶠ[atTop]
        (fun n => P n / (n : ℝ)) := by
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
      dsimp [b, normalizedMeanCount]
      rw [sub_div, add_div, div_self hn0]
      ring
    simpa only [add_zero] using ht.congr' heq
  have hs := hp.const_mul Real.pi
  apply hs.congr'
  exact Filter.Eventually.of_forall (fun n => by
    dsimp [P]
    rw [← mul_div_assoc, mul_comm Real.pi, div_mul_cancel₀ _ Real.pi_ne_zero])

theorem integrable_canonicalGapProcess_zero (law : PotentialLaw) (E δ : ℝ) (n : ℕ) :
    Integrable (canonicalGapProcess E δ 0 0 n) (iidMeasure law) := by
  change Integrable (fun ω => canonicalPhaseProcess E 0 n ω -
    canonicalPhaseProcess (E + δ) 0 n ω) (iidMeasure law)
  have hi : Integrable (fun ω => shootingPhase E ω n - shootingPhase (E + δ) ω n)
      (iidMeasure law) :=
    (integrable_shootingPhase law E n).sub (integrable_shootingPhase law (E + δ) n)
  simpa only [← shootingPhase_eq_process] using hi

/-- The actual two-energy phase gap has the mean speed prescribed by the IDS increment. -/
theorem mean_canonicalGapProcess_tendsto_idsCandidate (law : PotentialLaw) (E δ : ℝ) :
    Tendsto (fun n => (∫ ω, canonicalGapProcess E δ 0 0 n ω ∂iidMeasure law) / (n : ℝ))
      atTop (nhds (Real.pi * (idsCandidate law (E + δ) - idsCandidate law E))) := by
  have ht := (mean_shootingPhase_tendsto_idsCandidate law E).sub
    (mean_shootingPhase_tendsto_idsCandidate law (E + δ))
  have hlim : Real.pi * (1 - idsCandidate law E) -
      Real.pi * (1 - idsCandidate law (E + δ)) =
      Real.pi * (idsCandidate law (E + δ) - idsCandidate law E) := by ring
  rw [hlim] at ht
  convert ht using 1
  funext n
  simp only [canonicalGapProcess, ← shootingPhase_eq_process,
    integral_sub (integrable_shootingPhase law E n) (integrable_shootingPhase law (E + δ) n),
    sub_div]

theorem canonicalPhaseProcess_monotone_initial (E : ℝ) (n : ℕ) (ω : PotentialSpace) :
    Monotone (fun θ => canonicalPhaseProcess E θ n ω) := by
  induction n with
  | zero => exact monotone_id
  | succ n ih =>
    intro θ φ h
    simp only [canonicalPhaseProcess_succ]
    exact (canonicalPhase_strictMono E (ω n)).monotone (ih h)

/-- Changing the initial angle changes the displacement by at most one period. -/
theorem canonicalPhaseProcess_initial_error (E θ : ℝ) (n : ℕ) (ω : PotentialSpace) :
    |canonicalPhaseProcess E θ n ω - shootingPhase E ω n - θ| ≤ Real.pi := by
  let k := Int.floor (θ / Real.pi)
  have hlo := Int.sub_floor_div_mul_nonneg θ Real.pi_pos
  have hhi := Int.sub_floor_div_mul_lt θ Real.pi_pos
  change 0 ≤ θ - (k : ℝ) * Real.pi at hlo
  change θ - (k : ℝ) * Real.pi < Real.pi at hhi
  have hleft : shootingPhase E ω n + (k : ℝ) * Real.pi ≤
      canonicalPhaseProcess E θ n ω := by
    have h := canonicalPhaseProcess_monotone_initial E n ω
      (show 0 + (k : ℝ) * Real.pi ≤ θ by linarith)
    simpa only [canonicalPhaseProcess_add_int, ← shootingPhase_eq_process] using h
  have hright : canonicalPhaseProcess E θ n ω ≤
      shootingPhase E ω n + ((k + 1 : ℤ) : ℝ) * Real.pi := by
    have h := canonicalPhaseProcess_monotone_initial E n ω
      (show θ ≤ 0 + ((k + 1 : ℤ) : ℝ) * Real.pi by
        push_cast
        linarith)
    simpa only [canonicalPhaseProcess_add_int, ← shootingPhase_eq_process] using h
  push_cast at hright
  rw [abs_le]
  constructor <;> linarith

theorem integrable_canonicalPhaseProcess (law : PotentialLaw) (E θ : ℝ) (n : ℕ) :
    Integrable (canonicalPhaseProcess E θ n) (iidMeasure law) := by
  apply (integrable_const ((n : ℝ) * Real.pi + |θ| + Real.pi)).mono'
    (canonicalPhaseProcess_measurable E θ n).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨he1, he2⟩ := abs_le.mp (canonicalPhaseProcess_initial_error E θ n ω)
    obtain ⟨hs1, hs2⟩ := shootingPhase_mem_closed E ω n
    have hp := Real.pi_pos
    have hn : 0 ≤ (n : ℝ) * Real.pi := mul_nonneg (Nat.cast_nonneg n) hp.le
    constructor <;> linarith [le_abs_self θ, neg_abs_le θ])

theorem integral_canonicalPhaseProcess_initial_error (law : PotentialLaw) (E θ : ℝ)
    (n : ℕ) :
    |(∫ ω, canonicalPhaseProcess E θ n ω ∂iidMeasure law) -
      (∫ ω, shootingPhase E ω n ∂iidMeasure law) - θ| ≤ Real.pi := by
  have hi := integrable_canonicalPhaseProcess law E θ n
  have hz := integrable_shootingPhase law E n
  have hsum : Integrable (fun ω => canonicalPhaseProcess E θ n ω - shootingPhase E ω n)
      (iidMeasure law) := hi.sub hz
  have h := norm_integral_le_of_norm_le_const (μ := iidMeasure law)
    (f := fun ω => canonicalPhaseProcess E θ n ω - shootingPhase E ω n - θ)
    (Filter.Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using canonicalPhaseProcess_initial_error E θ n ω)
  simp only [Real.norm_eq_abs, probReal_univ, mul_one] at h
  rw [integral_sub hsum (integrable_const θ), integral_sub hi hz] at h
  simpa only [integral_const, probReal_univ, one_smul] using h

/-- The mean rotation speed is independent of the deterministic initial direction. -/
theorem mean_canonicalPhaseProcess_tendsto_idsCandidate (law : PotentialLaw) (E θ : ℝ) :
    Tendsto (fun n => (∫ ω, canonicalPhaseProcess E θ n ω ∂iidMeasure law) / (n : ℝ))
      atTop (nhds (Real.pi * (1 - idsCandidate law E))) := by
  let b := fun n => (∫ ω, canonicalPhaseProcess E θ n ω ∂iidMeasure law) -
    (∫ ω, shootingPhase E ω n ∂iidMeasure law) - θ
  have hd := bounded_div_nat_tendsto_zero b Real.pi
    (fun n => integral_canonicalPhaseProcess_initial_error law E θ n)
  have ht := ((mean_shootingPhase_tendsto_idsCandidate law E).add
    (tendsto_const_div_atTop_nhds_zero_nat θ)).add hd
  have heq : (fun n => (∫ ω, shootingPhase E ω n ∂iidMeasure law) / (n : ℝ) +
      θ / (n : ℝ) + b n / (n : ℝ)) =
      (fun n => (∫ ω, canonicalPhaseProcess E θ n ω ∂iidMeasure law) / (n : ℝ)) := by
    funext n
    dsimp [b]
    rw [sub_div, sub_div]
    ring
  simpa only [add_zero, heq] using ht

end FixedCouplingPoisson
