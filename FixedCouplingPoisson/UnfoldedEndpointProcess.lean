import FixedCouplingPoisson.UnfoldedPhaseWindow
import FixedCouplingPoisson.IDSContinuity

/-!
# Actual IDS unfolding endpoint selection

Zero targets and zero volume are assigned the fixed center. Every other
target uses an actual local solution when it exists, and the fixed center
as a default otherwise. Local strict increase and the already proved IDS
continuity imply eventual exactness, convergence to the center, and the
global finite spectral window identity for these selected endpoints.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set Filter
open scoped Topology

/-- An actual IDS inverse endpoint, with an explicit fixed-center default. -/
def idsUnfoldingEndpoint (law : PotentialLaw) (E : ℝ) (J : Set ℝ)
    (x : ℝ) (n : ℕ) : ℝ := by
  classical
  exact if x = 0 then E else if n = 0 then E else
    if h : ∃ e : ℝ, e ∈ J ∧ idsCandidate law e =
        idsCandidate law E + x / (n : ℝ) then Classical.choose h else E

@[simp] theorem idsUnfoldingEndpoint_zero (law : PotentialLaw) (E : ℝ)
    (J : Set ℝ) (n : ℕ) : idsUnfoldingEndpoint law E J 0 n = E := by
  unfold idsUnfoldingEndpoint
  exact if_pos rfl

@[simp] theorem idsUnfoldingEndpoint_volume_zero (law : PotentialLaw) (E : ℝ)
    (J : Set ℝ) (x : ℝ) : idsUnfoldingEndpoint law E J x 0 = E := by
  by_cases hx : x = 0 <;> simp only [idsUnfoldingEndpoint, hx, if_true, if_false]

/-- Local continuity and strict increase discharge eventual existence of
the chosen physical endpoint; it is not supplied as an input array. -/
theorem idsUnfoldingEndpoint_eventually_target (law : PotentialLaw)
    {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, idsUnfoldingEndpoint law E J x n ∈ J ∧
      idsCandidate law (idsUnfoldingEndpoint law E J x n) =
        idsCandidate law E + x / (n : ℝ) := by
  by_cases hx : x = 0
  · subst x
    exact Eventually.of_forall fun n => by
      simp only [idsUnfoldingEndpoint_zero, zero_div, add_zero, and_true]
      exact mem_of_mem_nhds hJ
  have hexists := unfolded_endpoint_eventually_exists_unique hJ
    (continuous_idsCandidate law).continuousOn hstrict x
  filter_upwards [hexists, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  obtain ⟨e, he, _⟩ := hn
  have hex : ∃ e : ℝ, e ∈ J ∧ idsCandidate law e =
      idsCandidate law E + x / (n : ℝ) := ⟨e, he⟩
  simpa only [idsUnfoldingEndpoint, if_neg hx, if_neg (ne_of_gt hn0), dif_pos hex]
    using Classical.choose_spec hex

/-- The selected endpoint is eventually the unique local solution. -/
theorem idsUnfoldingEndpoint_eventually_unique (law : PotentialLaw)
    {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ e : ℝ,
      e ∈ J → idsCandidate law e = idsCandidate law E + x / (n : ℝ) →
        e = idsUnfoldingEndpoint law E J x n := by
  filter_upwards [idsUnfoldingEndpoint_eventually_target law hJ hstrict x] with n hn
  intro e he hvalue
  exact hstrict.injOn he hn.1 (hvalue.trans hn.2.symm)

theorem idsUnfoldingEndpoint_tendsto (law : PotentialLaw)
    {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℝ) :
    Tendsto (idsUnfoldingEndpoint law E J x) atTop (𝓝 E) :=
  unfolded_endpoint_tendsto hJ hstrict x _
    (idsUnfoldingEndpoint_eventually_target law hJ hstrict x)

/-- The local normalization set is eventually a neighborhood of every
selected endpoint, even when the initially supplied set was not open. -/
theorem idsUnfoldingEndpoint_eventually_nhds (law : PotentialLaw)
    {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℝ) :
    ∀ᶠ n : ℕ in atTop, J ∈ 𝓝 (idsUnfoldingEndpoint law E J x n) := by
  obtain ⟨a, b, hE, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hJ
  have hev := (idsUnfoldingEndpoint_tendsto law hJ hstrict x).eventually
    (Ioo_mem_nhds hE.1 hE.2)
  exact hev.mono fun n hn => mem_of_superset (Ioo_mem_nhds hn.1 hn.2) hsub

/-- Endpoint arrays in the order expected by the actual phase window process. -/
def idsUnfoldingEndpointArray (law : PotentialLaw) (E : ℝ) (J : Set ℝ)
    (x : ℕ → ℝ) (n i : ℕ) : ℝ := idsUnfoldingEndpoint law E J (x i) n

theorem idsUnfoldingEndpointArray_anchor (law : PotentialLaw) (E : ℝ)
    (J : Set ℝ) (x : ℕ → ℝ) (κ : ℕ) (hκ : x κ = 0) (n : ℕ) :
    idsUnfoldingEndpointArray law E J x n κ = E := by
  simp only [idsUnfoldingEndpointArray, hκ, idsUnfoldingEndpoint_zero]

/-- The actual IDS rate of every adjacent chosen interval is eventually
exact, including its physical-endpoint defaults at small volumes. -/
theorem idsUnfoldingEndpointArray_eventually_rate (law : PotentialLaw)
    {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ) (i : ℕ) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) *
      (idsCandidate law (idsUnfoldingEndpointArray law E J x n (i + 1)) -
        idsCandidate law (idsUnfoldingEndpointArray law E J x n i)) = x (i + 1) - x i := by
  filter_upwards [idsUnfoldingEndpoint_eventually_target law hJ hstrict (x i),
    idsUnfoldingEndpoint_eventually_target law hJ hstrict (x (i + 1)),
    eventually_gt_atTop (0 : ℕ)] with n ha hb hn
  exact unfolded_adjacent_rate (ne_of_gt hn) ha.2 hb.2

/-- Selected actual unfolding endpoints yield the true finite spectral
window process for all sufficiently large volumes and every iid sample. -/
theorem idsUnfoldingEndpointArray_eventually_window_identity (law : PotentialLaw)
    {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ) (i : ℕ)
    (hab : x i ≤ x (i + 1)) :
    ∀ᶠ n : ℕ in atTop, ∀ ω : PotentialSpace,
      (idsUnfoldedWindowCount law E n (fun j => ω j.val) (x i) (x (i + 1)) : ℤ) =
        actualWindowSpectralCount (idsUnfoldingEndpointArray law E J x) n i ω := by
  filter_upwards [idsUnfoldingEndpoint_eventually_target law hJ hstrict (x i),
    idsUnfoldingEndpoint_eventually_target law hJ hstrict (x (i + 1)),
    idsUnfoldingEndpoint_eventually_nhds law hJ hstrict (x i),
    idsUnfoldingEndpoint_eventually_nhds law hJ hstrict (x (i + 1)),
    eventually_gt_atTop (0 : ℕ)] with n ha hb hna hnb hn
  intro ω
  exact idsUnfoldedWindowCount_eq_actualWindowSpectralCount law x
    (idsUnfoldingEndpointArray law E J x) n i hstrict hna hnb hn hab ha.2 hb.2 ω

end FixedCouplingPoisson.Furstenberg
