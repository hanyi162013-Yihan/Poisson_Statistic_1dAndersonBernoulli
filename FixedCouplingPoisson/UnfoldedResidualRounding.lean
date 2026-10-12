import FixedCouplingPoisson.ResidualPinningEventually
import FixedCouplingPoisson.UnfoldedEndpointGeometry

/-! Actual IDS-selected endpoints satisfy residual pinning and terminal rounding. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- The actual IDS mass has the exact asymptotic unfolding scale, including
the finite-prefix endpoint defaults in the definition. -/
theorem idsUnfoldingEndpointArray_scaled_rate_tendsto (law : PotentialLaw)
    {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ) (i : ℕ) :
    Tendsto (fun n =>
      (idsCandidate law (idsUnfoldingEndpointArray law E J x n (i + 1)) -
        idsCandidate law (idsUnfoldingEndpointArray law E J x n i)) * (n : ℝ))
      atTop (𝓝 (x (i + 1) - x i)) := by
  apply (tendsto_const_nhds : Tendsto (fun _n : ℕ => x (i + 1) - x i)
    atTop (𝓝 (x (i + 1) - x i))).congr'
  filter_upwards [idsUnfoldingEndpointArray_eventually_rate law hJ hstrict x i]
    with n hn
  exact hn.symm.trans (mul_comm _ _)

/-- Residual pinning for the actual inverse-IDS endpoints requires no
separate compact-energy, rate, or residual-tail interface. -/
theorem idsUnfoldingEndpointArray_residual_tails_tendsto_zero (law : PotentialLaw)
    (input : Input law) {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ) (i : ℕ)
    (hx : x i < x (i + 1)) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => iidMeasure law {ω |
      r < actualWindowResidual (idsUnfoldingEndpointArray law E J x) n i ω})
      atTop (𝓝 0) := by
  have hKnhds : Icc (E - 1) (E + 1) ∈ 𝓝 E :=
    Icc_mem_nhds (by linarith) (by linarith)
  exact actualWindowResidual_tails_tendsto_zero_eventually law input isCompact_Icc
    (idsUnfoldingEndpointArray law E J x) i
    ((idsUnfoldingEndpointArray_tendsto law hJ hstrict x i).eventually hKnhds)
    ((idsUnfoldingEndpointArray_tendsto law hJ hstrict x (i + 1)).eventually hKnhds)
    ((idsUnfoldingEndpointArray_eventually_lt law hJ hstrict x hx).mono fun _ hn => hn.le)
    (idsUnfoldingEndpointArray_eventually_ids_increment_pos law hJ hstrict x hx)
    (idsUnfoldingEndpointArray_gap_tendsto_zero law hJ hstrict x i)
    (idsUnfoldingEndpointArray_scaled_rate_tendsto law hJ hstrict x i) hr

/-- A fixed zero unfolding coordinate supplies the actual fixed-energy
anchor. All finite spectral counts then agree with their windings with
probability tending to one. -/
theorem idsUnfoldingEndpointArray_rounding_success_tendsto_one (law : PotentialLaw)
    (input : Input law) {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ) (s κ : ℕ)
    (hκ : κ ≤ s) (hzero : x κ = 0) (hx : ∀ i < s, x i < x (i + 1)) :
    Tendsto (fun n => iidMeasure law {ω | ∀ i, i < s →
      actualWindowSpectralCount (idsUnfoldingEndpointArray law E J x) n i ω =
        actualWindowWinding (idsUnfoldingEndpointArray law E J x) n i ω})
      atTop (𝓝 1) := by
  apply actualWindow_rounding_success_of_individual_residuals law E (input.atEnergy E)
    (idsUnfoldingEndpointArray law E J x) s κ hκ
    (fun n => idsUnfoldingEndpointArray_anchor law E J x κ hzero n)
  intro i hi r hr
  exact idsUnfoldingEndpointArray_residual_tails_tendsto_zero law input hJ hstrict x i
    (hx i hi) hr

/-- The actual unfolded spectral point counts have the same finite window
counts as the crossing windings with probability tending to one. -/
theorem idsUnfoldedWindowCount_eq_winding_probability_tendsto_one (law : PotentialLaw)
    (input : Input law) {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ) (s κ : ℕ)
    (hκ : κ ≤ s) (hzero : x κ = 0) (hx : ∀ i < s, x i < x (i + 1)) :
    Tendsto (fun n => iidMeasure law {ω | ∀ i, i < s →
      (idsUnfoldedWindowCount law E n (fun j => ω j.val) (x i) (x (i + 1)) : ℤ) =
        actualWindowWinding (idsUnfoldingEndpointArray law E J x) n i ω})
      atTop (𝓝 1) := by
  have hround := idsUnfoldingEndpointArray_rounding_success_tendsto_one law input hJ
    hstrict x s κ hκ hzero hx
  apply hround.congr'
  filter_upwards [idsUnfoldingEndpointArray_eventually_all_window_identities law hJ
    hstrict x s (fun i hi => (hx i hi).le)] with n hn
  congr 1
  ext ω
  constructor
  · intro h i hi
    rw [hn i (Finset.mem_range.mpr hi) ω]
    exact h i hi
  · intro h i hi
    rw [← hn i (Finset.mem_range.mpr hi) ω]
    exact h i hi

end FixedCouplingPoisson.Furstenberg
