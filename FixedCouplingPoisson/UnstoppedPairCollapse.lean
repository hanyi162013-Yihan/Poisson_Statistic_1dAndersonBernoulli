import FixedCouplingPoisson.ForcedMultiBlockContraction
import FixedCouplingPoisson.PhaseDistribution
import FixedCouplingPoisson.PhaseWindow
import FixedCouplingPoisson.CanonicalResidual

/-!
# Collapse of the actual unstopped pair along varying energies

The actual forced multiblock moment bound gives convergence for every
sequence of independent starting pairs, without a rate relation between
the energy difference and the deterministic observation time. The
oriented residual is thereby confined to its two endpoints. This module
does not identify which endpoint is selected.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter
open scoped Topology

/-- Actual shared-potential products become close in probability. -/
theorem twoEnergy_projective_distance_tail_tendsto_zero (law : PotentialLaw)
    (input : Input law) {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (E E' : ℕ → ℝ) (k : ℕ → ℕ) (p r : ℕ → ProjectivePoint)
    (hE : ∀ᶠ n in atTop, E n ∈ K)
    (hdiff : Tendsto (fun n => E n - E' n) atTop (𝓝 0))
    (hk : Tendsto k atTop atTop) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun n => iidMeasure law {ω | h ≤ projectiveDistance
      (projectiveProcess (E n) (p n) (k n) ω)
      (projectiveProcess (E' n) (r n) (k n) ω)}) atTop (𝓝 0) := by
  obtain ⟨N, hN, s, q, C, hs, _hs1, hq0, hq1, _hC, hbound⟩ :=
    exists_uniform_forced_multiblock_moment law input K hK hne
  have hgeom : Tendsto (fun n => q ^ (k n / N)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp
      ((Nat.tendsto_div_const_atTop hN.ne').comp hk)
  have habs : Tendsto (fun n => |E n - E' n|) atTop (𝓝 0) := by
    simpa only [abs_zero] using hdiff.abs
  have hpower : Tendsto (fun n => |E n - E' n| ^ s) atTop (𝓝 0) := by
    exact habs.rpow_const_nhds_zero hs
  have hB : Tendsto (fun n =>
      (q ^ (k n / N) + C * |E n - E' n| ^ s) / h ^ s) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, zero_div] using
      (hgeom.add (hpower.const_mul C)).div_const (h ^ s)
  have hreal : Tendsto (fun n => (iidMeasure law).real {ω | h ≤ projectiveDistance
      (projectiveProcess (E n) (p n) (k n) ω)
      (projectiveProcess (E' n) (r n) (k n) ω)}) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ hB
    filter_upwards [hE] with n hn
    exact twoEnergyPairDistanceMoment_measure_distance_ge_le law (E n) (E' n)
      s h _ hs.le hh (p n) (r n) (k n) (hbound (E n) hn (E' n) (k n) (p n) (r n))
  exact (ENNReal.tendsto_toReal_zero_iff (fun _ => measure_ne_top _ _)).mp hreal

/-- The same statement is about the actual canonical real phases. -/
theorem canonicalPhase_pair_distance_tail_tendsto_zero (law : PotentialLaw)
    (input : Input law) {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (E E' θ φ : ℕ → ℝ) (k : ℕ → ℕ)
    (hE : ∀ᶠ n in atTop, E n ∈ K)
    (hdiff : Tendsto (fun n => E n - E' n) atTop (𝓝 0))
    (hk : Tendsto k atTop atTop) {h : ℝ} (hh : 0 < h) :
    Tendsto (fun n => iidMeasure law {ω | h ≤ projectiveDistance
      (phaseProjective (canonicalPhaseProcess (E n) (θ n) (k n) ω))
      (phaseProjective (canonicalPhaseProcess (E' n) (φ n) (k n) ω))}) atTop (𝓝 0) := by
  simpa only [phaseProjective_canonicalPhaseProcess] using
    twoEnergy_projective_distance_tail_tendsto_zero law input hK hne E E' k
      (fun n => phaseProjective (θ n)) (fun n => phaseProjective (φ n)) hE hdiff hk hh

/-- The true determinant distance is the sine of the actual oriented remainder. -/
theorem canonicalCrossingResidual_distance_eq_sin (E δ θ φ : ℝ) (n : ℕ)
    (ω : PotentialSpace) :
    projectiveDistance (phaseProjective (canonicalPhaseProcess E θ n ω))
      (phaseProjective (canonicalPhaseProcess (E + δ) φ n ω)) =
        Real.sin (canonicalCrossingResidual E δ θ φ n ω) := by
  let r := canonicalCrossingResidual E δ θ φ n ω
  let k := canonicalCrossingCount E δ θ φ n ω
  have hp : phaseProjective (canonicalPhaseProcess E θ n ω) =
      phaseProjective (canonicalPhaseProcess (E + δ) φ n ω + r) := by
    have hθ : canonicalPhaseProcess E θ n ω =
        (canonicalPhaseProcess (E + δ) φ n ω + r) + (k : ℝ) * Real.pi := by
      dsimp only [r, k, canonicalCrossingResidual, canonicalGapProcess]
      ring
    rw [hθ, phaseProjective_add_int]
  rw [hp, projectiveDistance_phaseProjective]
  have heq : canonicalPhaseProcess (E + δ) φ n ω -
      (canonicalPhaseProcess (E + δ) φ n ω + r) = -r := by ring
  rw [heq, Real.sin_neg, abs_neg,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      (canonicalCrossingResidual_mem E δ θ φ n ω).1
      (canonicalCrossingResidual_mem E δ θ φ n ω).2.le)]

theorem canonicalCrossingResidual_middle_distance_lower (E δ θ φ : ℝ) (n : ℕ)
    (ω : PotentialSpace) {h : ℝ} (hh : 0 ≤ h)
    (hlo : h ≤ canonicalCrossingResidual E δ θ φ n ω)
    (hhi : canonicalCrossingResidual E δ θ φ n ω ≤ Real.pi - h) :
    (2 / Real.pi) * h ≤
      projectiveDistance (phaseProjective (canonicalPhaseProcess E θ n ω))
        (phaseProjective (canonicalPhaseProcess (E + δ) φ n ω)) := by
  rw [canonicalCrossingResidual_distance_eq_sin]
  let r := canonicalCrossingResidual E δ θ φ n ω
  have hr0 : 0 ≤ r := (canonicalCrossingResidual_mem E δ θ φ n ω).1
  have hrπ : r ≤ Real.pi := (canonicalCrossingResidual_mem E δ θ φ n ω).2.le
  have hc : 0 ≤ 2 / Real.pi := by positivity
  by_cases hrhalf : r ≤ Real.pi / 2
  · exact (mul_le_mul_of_nonneg_left hlo hc).trans (Real.mul_le_sin hr0 hrhalf)
  · have hother := Real.mul_le_sin (sub_nonneg.mpr hrπ)
      (show Real.pi - r ≤ Real.pi / 2 by linarith)
    rw [Real.sin_pi_sub] at hother
    exact (mul_le_mul_of_nonneg_left (show h ≤ Real.pi - r by linarith) hc).trans hother

/-- Arbitrary deterministic diverging observation times suffice for excluding
the middle of the residual interval. No relation between time and IDS is used. -/
theorem canonicalCrossingResidual_middle_tendsto_zero (law : PotentialLaw)
    (input : Input law) {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (E δ θ φ : ℕ → ℝ) (k : ℕ → ℕ)
    (hE : ∀ᶠ n in atTop, E n ∈ K)
    (hδ : Tendsto δ atTop (𝓝 0)) (hk : Tendsto k atTop atTop)
    {h : ℝ} (hh : 0 < h) :
    Tendsto (fun n => iidMeasure law {ω |
      h ≤ canonicalCrossingResidual (E n) (δ n) (θ n) (φ n) (k n) ω ∧
      canonicalCrossingResidual (E n) (δ n) (θ n) (φ n) (k n) ω ≤ Real.pi - h})
      atTop (𝓝 0) := by
  have hdiff : Tendsto (fun n => E n - (E n + δ n)) atTop (𝓝 0) := by
    have heq : (fun n => E n - (E n + δ n)) = (fun n => -δ n) := by
      funext n
      ring
    rw [heq]
    simpa only [neg_zero] using hδ.neg
  have htail := canonicalPhase_pair_distance_tail_tendsto_zero law input hK hne
    E (fun n => E n + δ n) θ φ k hE hdiff hk
    (show 0 < (2 / Real.pi) * h by positivity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail (fun _ => bot_le)
  intro n
  apply measure_mono
  intro ω hω
  exact canonicalCrossingResidual_middle_distance_lower (E n) (δ n) (θ n) (φ n)
    (k n) ω hh.le hω.1 hω.2

/-- Integer winding disappears exactly from the actual determinant distance. -/
theorem terminalWindow_step_distance_eq_sin_residual (θ : ℕ → ℝ) (i : ℕ) :
    projectiveDistance (phaseProjective (θ i)) (phaseProjective (θ (i + 1))) =
      Real.sin (terminalWindowResidual θ i) := by
  let r := terminalWindowResidual θ i
  let k := terminalWindowWinding θ i
  have hp : phaseProjective (θ i) = phaseProjective (θ (i + 1) + r) := by
    have hθ : θ i = (θ (i + 1) + r) + (k : ℝ) * Real.pi := by
      dsimp only [r, k]
      unfold terminalWindowResidual
      ring
    rw [hθ, phaseProjective_add_int]
  rw [hp, projectiveDistance_phaseProjective]
  have heq : θ (i + 1) - (θ (i + 1) + r) = -r := by ring
  rw [heq, Real.sin_neg, abs_neg,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi
      (terminalWindowResidual_mem θ i).1 (terminalWindowResidual_mem θ i).2.le)]

/-- A residual separated from both endpoints has a definite actual distance. -/
theorem terminalWindow_middle_residual_distance_lower (θ : ℕ → ℝ) (i : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (hlower : h ≤ terminalWindowResidual θ i)
    (hupper : terminalWindowResidual θ i ≤ Real.pi - h) :
    (2 / Real.pi) * h ≤
      projectiveDistance (phaseProjective (θ i)) (phaseProjective (θ (i + 1))) := by
  rw [terminalWindow_step_distance_eq_sin_residual]
  let r := terminalWindowResidual θ i
  have hr0 : 0 ≤ r := (terminalWindowResidual_mem θ i).1
  have hrπ : r ≤ Real.pi := (terminalWindowResidual_mem θ i).2.le
  have hcoef : 0 ≤ 2 / Real.pi := by positivity
  by_cases hrhalf : r ≤ Real.pi / 2
  · exact (mul_le_mul_of_nonneg_left hlower hcoef).trans
      (Real.mul_le_sin hr0 hrhalf)
  · have hother := Real.mul_le_sin (sub_nonneg.mpr hrπ)
      (show Real.pi - r ≤ Real.pi / 2 by linarith)
    rw [Real.sin_pi_sub] at hother
    exact (mul_le_mul_of_nonneg_left (show h ≤ Real.pi - r by linarith) hcoef).trans hother

/-- Actual residuals avoid every compact subinterval of `(0, pi)` in probability. -/
theorem actualWindow_middle_residual_tendsto_zero (law : PotentialLaw)
    (input : Input law) {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (e : ℕ → ℕ → ℝ) (i : ℕ)
    (hE : ∀ᶠ n in atTop, e n i ∈ K)
    (hdiff : Tendsto (fun n => e n i - e n (i + 1)) atTop (𝓝 0))
    {h : ℝ} (hh : 0 < h) :
    Tendsto (fun n => iidMeasure law {ω | h ≤ actualWindowResidual e n i ω ∧
      actualWindowResidual e n i ω ≤ Real.pi - h}) atTop (𝓝 0) := by
  have htail := canonicalPhase_pair_distance_tail_tendsto_zero law input hK hne
    (fun n => e n i) (fun n => e n (i + 1)) (fun _ => 0) (fun _ => 0)
    id hE hdiff tendsto_id (show 0 < (2 / Real.pi) * h by positivity)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htail (fun _ => bot_le)
  intro n
  apply measure_mono
  intro ω hω
  have hd := terminalWindow_middle_residual_distance_lower (actualEndpointPhase e n ω)
    i hh.le hω.1 hω.2
  simpa only [actualEndpointPhase, shootingPhase_eq_process, id_eq, Set.mem_ofPred_eq] using hd

end FixedCouplingPoisson.Furstenberg
