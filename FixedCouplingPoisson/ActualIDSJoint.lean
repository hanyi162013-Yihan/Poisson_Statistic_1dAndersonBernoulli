import FixedCouplingPoisson.ActualJointSpectral
import FixedCouplingPoisson.UnfoldedResidualRounding

/-! Discharging all endpoint and IDS scales for actual inverse-IDS windows. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology NNReal

theorem idsUnfoldingEndpointArray_scaled_pair_rate_tendsto (law : PotentialLaw)
    {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ) (a b : ℕ) :
    Tendsto (fun n =>
      (idsCandidate law (idsUnfoldingEndpointArray law E J x n b) -
        idsCandidate law (idsUnfoldingEndpointArray law E J x n a)) * (n : ℝ))
      atTop (𝓝 (x b - x a)) := by
  apply (tendsto_const_nhds : Tendsto (fun _n : ℕ => x b - x a)
    atTop (𝓝 (x b - x a))).congr'
  filter_upwards [idsUnfoldingEndpoint_eventually_target law hJ hstrict (x a),
    idsUnfoldingEndpoint_eventually_target law hJ hstrict (x b),
    eventually_gt_atTop (0 : ℕ)] with n ha hb hn
  exact (unfolded_adjacent_rate (Nat.ne_of_gt hn) ha.2 hb.2).symm.trans (mul_comm _ _)

theorem idsUnfoldingEndpointArray_eventually_pair_ids_increment_pos
    (law : PotentialLaw) {E : ℝ} {J : Set ℝ} (hJ : J ∈ 𝓝 E)
    (hstrict : StrictMonoOn (idsCandidate law) J) (x : ℕ → ℝ)
    {a b : ℕ} (hx : x a < x b) :
    ∀ᶠ n in atTop, 0 <
      idsCandidate law (idsUnfoldingEndpointArray law E J x n b) -
        idsCandidate law (idsUnfoldingEndpointArray law E J x n a) := by
  filter_upwards [idsUnfoldingEndpoint_eventually_target law hJ hstrict (x a),
    idsUnfoldingEndpoint_eventually_target law hJ hstrict (x b),
    idsUnfoldingEndpointArray_eventually_lt law hJ hstrict x hx] with n ha hb hn
  exact sub_pos.mpr (hstrict ha.1 hb.1 hn)

/-- Actual inverse-IDS endpoint windows have the independent Poisson law.
Endpoint existence, compactness, order, positive IDS masses and limiting
rates are proved here from the original local strict-IDS hypothesis. -/
theorem idsUnfolding_physicalWindowRealLaw_tendsto_poisson
    (law : PotentialLaw) (input : Input law) {E : ℝ} {J : Set ℝ}
    (hJ : J ∈ 𝓝 E) (hstrict : StrictMonoOn (idsCandidate law) J)
    (x : ℕ → ℝ) (s : ℕ) (hs : 0 < s) (hx : StrictMonoOn x (Iic s))
    (κ : ℕ) (hκ : κ ≤ s) (hzero : x κ = 0) :
    Tendsto (fun n => actualEnergyWindowCountRealLaw law
      (idsUnfoldingEndpointArray law E J x) s n) atTop
      (𝓝 (poissonRealProduct (fun i : Fin s =>
        (⟨x (i.val + 1) - x i.val, sub_nonneg.mpr
          (hx (by exact i.isLt.le) (by change i.val + 1 ≤ s; omega)
            (Nat.lt_succ_self i.val)).le⟩ : ℝ≥0)))) := by
  let e := idsUnfoldingEndpointArray law E J x
  have hadj (i : ℕ) (hi : i < s) : x i < x (i + 1) :=
    hx hi.le (by change i + 1 ≤ s; omega) (Nat.lt_succ_self i)
  have houterX : x 0 < x s := hx (Nat.zero_le s) (by change s ≤ s; exact le_rfl) hs
  have hKnhds : Icc (E - 1) (E + 1) ∈ 𝓝 E :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hcompact : ∀ᶠ n in atTop, ∀ i, i ≤ s → e n i ∈ Icc (E - 1) (E + 1) := by
    filter_upwards [idsUnfoldingEndpointArray_eventually_mem law hJ hstrict hKnhds x s]
      with n hn
    intro i hi
    exact hn i (Finset.mem_range.mpr (by omega))
  have horder : ∀ᶠ n in atTop, ∀ i, i < s → e n i ≤ e n (i + 1) := by
    have hfin : ∀ᶠ n in atTop, ∀ i ∈ Finset.range s, e n i ≤ e n (i + 1) := by
      apply (Finset.range s).eventually_all.mpr
      intro i hi
      exact (idsUnfoldingEndpointArray_eventually_lt law hJ hstrict x
        (hadj i (Finset.mem_range.mp hi))).mono fun n hn => hn.le
    exact hfin.mono fun n hn i hi => hn i (Finset.mem_range.mpr hi)
  have hp : ∀ᶠ n in atTop, ∀ i, i < s →
      0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i) := by
    have hfin : ∀ᶠ n in atTop, ∀ i ∈ Finset.range s,
        0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i) := by
      apply (Finset.range s).eventually_all.mpr
      intro i hi
      exact idsUnfoldingEndpointArray_eventually_ids_increment_pos law hJ hstrict x
        (hadj i (Finset.mem_range.mp hi))
    exact hfin.mono fun n hn i hi => hn i (Finset.mem_range.mpr hi)
  exact actualEnergyWindowCountRealLaw_tendsto_poisson law input isCompact_Icc e s E κ hκ
    (fun n => idsUnfoldingEndpointArray_anchor law E J x κ hzero n) hcompact horder
    ((idsUnfoldingEndpointArray_eventually_lt law hJ hstrict x houterX).mono fun n hn => hn.le)
    hp (idsUnfoldingEndpointArray_eventually_pair_ids_increment_pos law hJ hstrict x houterX)
    (fun i _ => idsUnfoldingEndpointArray_tendsto law hJ hstrict x i)
    _ (x s - x 0) (sub_nonneg.mpr houterX.le)
    (fun i => idsUnfoldingEndpointArray_scaled_rate_tendsto law hJ hstrict x i.val)
    (idsUnfoldingEndpointArray_scaled_pair_rate_tendsto law hJ hstrict x 0 s)

end FixedCouplingPoisson.Furstenberg
