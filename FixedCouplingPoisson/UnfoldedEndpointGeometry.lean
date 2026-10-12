import FixedCouplingPoisson.UnfoldedEndpointProcess

/-!
# Geometry of the actual IDS-selected endpoints

The chosen arrays converge to the fixed energy and eventually have the true
strict order of the unfolding targets. All endpoint and window properties
can be imposed simultaneously for finitely many adjacent windows.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set Filter
open scoped Topology

theorem idsUnfoldingEndpointArray_tendsto (law : PotentialLaw)
    {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ) (i : ℕ) :
    Tendsto (fun n => idsUnfoldingEndpointArray law E J x n i) atTop (𝓝 E) :=
  idsUnfoldingEndpoint_tendsto law hJ hstrict (x i)

theorem idsUnfoldingEndpointArray_gap_tendsto_zero (law : PotentialLaw)
    {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ) (i : ℕ) :
    Tendsto (fun n => idsUnfoldingEndpointArray law E J x n (i + 1) -
      idsUnfoldingEndpointArray law E J x n i) atTop (𝓝 0) := by
  simpa only [sub_self] using
    (idsUnfoldingEndpointArray_tendsto law hJ hstrict x (i + 1)).sub
      (idsUnfoldingEndpointArray_tendsto law hJ hstrict x i)

/-- The actual IDS masses shrink without requiring a derivative or a
power-law comparison between physical energy length and IDS mass. -/
theorem idsUnfoldingEndpointArray_ids_increment_tendsto_zero (law : PotentialLaw)
    {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ) (i : ℕ) :
    Tendsto (fun n =>
      idsCandidate law (idsUnfoldingEndpointArray law E J x n (i + 1)) -
        idsCandidate law (idsUnfoldingEndpointArray law E J x n i)) atTop (𝓝 0) := by
  simpa only [Function.comp_def, sub_self] using
    ((continuous_idsCandidate law).continuousAt.tendsto.comp
      (idsUnfoldingEndpointArray_tendsto law hJ hstrict x (i + 1))).sub
        ((continuous_idsCandidate law).continuousAt.tendsto.comp
          (idsUnfoldingEndpointArray_tendsto law hJ hstrict x i))

theorem idsUnfoldingEndpointArray_eventually_lt (law : PotentialLaw)
    {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ)
    {i j : ℕ} (hx : x i < x j) :
    ∀ᶠ n : ℕ in atTop, idsUnfoldingEndpointArray law E J x n i <
      idsUnfoldingEndpointArray law E J x n j := by
  filter_upwards [idsUnfoldingEndpoint_eventually_target law hJ hstrict (x i),
    idsUnfoldingEndpoint_eventually_target law hJ hstrict (x j),
    eventually_gt_atTop (0 : ℕ)] with n ha hb hn
  exact unfolded_endpoint_lt hstrict ha.1 hb.1 hn hx ha.2 hb.2

/-- A positive unfolding interval eventually has strictly positive actual
IDS mass, as required by the already proved finite crossing means. -/
theorem idsUnfoldingEndpointArray_eventually_ids_increment_pos (law : PotentialLaw)
    {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ)
    {i : ℕ} (hx : x i < x (i + 1)) :
    ∀ᶠ n : ℕ in atTop, 0 <
      idsCandidate law (idsUnfoldingEndpointArray law E J x n (i + 1)) -
        idsCandidate law (idsUnfoldingEndpointArray law E J x n i) := by
  filter_upwards [idsUnfoldingEndpoint_eventually_target law hJ hstrict (x i),
    idsUnfoldingEndpoint_eventually_target law hJ hstrict (x (i + 1)),
    idsUnfoldingEndpointArray_eventually_lt law hJ hstrict x hx] with n ha hb hlt
  exact sub_pos.mpr (hstrict ha.1 hb.1 hlt)

/-- A fixed neighborhood of the center eventually contains every endpoint
of a finite array. Compact brackets may be used for this neighborhood. -/
theorem idsUnfoldingEndpointArray_eventually_mem (law : PotentialLaw)
    {E : ℝ} {J K : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (hK : K ∈ 𝓝 E)
    (x : ℕ → ℝ) (s : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.range (s + 1),
      idsUnfoldingEndpointArray law E J x n i ∈ K := by
  apply (Finset.range (s + 1)).eventually_all.mpr
  intro i _
  exact (idsUnfoldingEndpointArray_tendsto law hJ hstrict x i).eventually hK

/-- The actual IDS normalization is exact simultaneously in all finitely
many adjacent intervals, and each physical interval has positive length. -/
theorem idsUnfoldingEndpointArray_eventually_positive_rates (law : PotentialLaw)
    {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ) (s : ℕ)
    (hx : ∀ i < s, x i < x (i + 1)) :
    ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.range s,
      0 < idsUnfoldingEndpointArray law E J x n (i + 1) -
          idsUnfoldingEndpointArray law E J x n i ∧
      (n : ℝ) * (idsCandidate law (idsUnfoldingEndpointArray law E J x n (i + 1)) -
        idsCandidate law (idsUnfoldingEndpointArray law E J x n i)) =
          x (i + 1) - x i := by
  apply (Finset.range s).eventually_all.mpr
  intro i hi
  have hxi := hx i (Finset.mem_range.mp hi)
  filter_upwards [idsUnfoldingEndpointArray_eventually_lt law hJ hstrict x hxi,
    idsUnfoldingEndpointArray_eventually_rate law hJ hstrict x i] with n hn hr
  exact ⟨sub_pos.mpr hn, hr⟩

/-- All actual finite unfolded windows equal the chosen physical phase
counts at the same sufficiently large volumes, for every iid realization. -/
theorem idsUnfoldingEndpointArray_eventually_all_window_identities (law : PotentialLaw)
    {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ) (s : ℕ)
    (hx : ∀ i < s, x i ≤ x (i + 1)) :
    ∀ᶠ n : ℕ in atTop, ∀ i ∈ Finset.range s, ∀ ω : PotentialSpace,
      (idsUnfoldedWindowCount law E n (fun j => ω j.val) (x i) (x (i + 1)) : ℤ) =
        actualWindowSpectralCount (idsUnfoldingEndpointArray law E J x) n i ω := by
  apply (Finset.range s).eventually_all.mpr
  intro i hi
  exact idsUnfoldingEndpointArray_eventually_window_identity law hJ hstrict x i
    (hx i (Finset.mem_range.mp hi))

end FixedCouplingPoisson.Furstenberg
