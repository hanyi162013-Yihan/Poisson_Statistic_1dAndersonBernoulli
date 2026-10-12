import FixedCouplingPoisson.ActualJointSpectral
import FixedCouplingPoisson.Normalization

/-! The derivative-based linear endpoint normalization of actual spectra. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology NNReal

theorem positive_rate_eventually_positive_mass (p : ℕ → ℝ) {w : ℝ} (hw : 0 < w)
    (hscale : Tendsto (fun n => p n * (n : ℝ)) atTop (𝓝 w)) :
    ∀ᶠ n in atTop, 0 < p n := by
  filter_upwards [hscale.eventually (lt_mem_nhds hw), eventually_gt_atTop (0 : ℕ)]
    with n hn hn0
  exact (mul_pos_iff_of_pos_right (Nat.cast_pos.mpr hn0)).mp hn

/-- Only the original positive derivative at the center is needed for these
linear windows. Their positive IDS masses follow from the actual rates. -/
theorem linear_physicalWindowRealLaw_tendsto_poisson
    (law : PotentialLaw) (input : Input law) {E ρ : ℝ}
    (hderiv : HasDerivAt (idsCandidate law) ρ E) (hρ : 0 < ρ)
    (x : ℕ → ℝ) (s : ℕ) (hs : 0 < s) (hx : StrictMonoOn x (Iic s))
    (κ : ℕ) (hκ : κ ≤ s) (hzero : x κ = 0) :
    Tendsto (fun n => actualEnergyWindowCountRealLaw law
      (fun n i => linearEndpoint E ρ (x i) n) s n) atTop
      (𝓝 (poissonRealProduct (fun i : Fin s =>
        (⟨x (i.val + 1) - x i.val, sub_nonneg.mpr
          (hx (by exact i.isLt.le) (by change i.val + 1 ≤ s; omega)
            (Nat.lt_succ_self i.val)).le⟩ : ℝ≥0)))) := by
  let e : ℕ → ℕ → ℝ := fun n i => linearEndpoint E ρ (x i) n
  have hadj (i : ℕ) (hi : i < s) : x i < x (i + 1) :=
    hx hi.le (by change i + 1 ≤ s; omega) (Nat.lt_succ_self i)
  have houterX : x 0 < x s := hx (Nat.zero_le s) (by change s ≤ s; exact le_rfl) hs
  have hscale (a b : ℕ) : Tendsto (fun n =>
      (idsCandidate law (e n b) - idsCandidate law (e n a)) * (n : ℝ))
      atTop (𝓝 (x b - x a)) := by
    simpa only [e, mul_comm] using
      differentiable_adjacent_linear_rate hderiv hρ.ne' (x a) (x b)
  have hKnhds : Icc (E - 1) (E + 1) ∈ 𝓝 E :=
    Icc_mem_nhds (by linarith) (by linarith)
  have hcompact : ∀ᶠ n in atTop, ∀ i, i ≤ s → e n i ∈ Icc (E - 1) (E + 1) := by
    have hfin : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (s + 1),
        e n i ∈ Icc (E - 1) (E + 1) := by
      apply (Finset.range (s + 1)).eventually_all.mpr
      intro i hi
      exact (linearEndpoint_tendsto E ρ (x i)).eventually hKnhds
    exact hfin.mono fun n hn i hi => hn i (Finset.mem_range.mpr (by omega))
  have horder : ∀ᶠ n in atTop, ∀ i, i < s → e n i ≤ e n (i + 1) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    intro i hi
    exact (linearEndpoint_strictMono hρ hn (hadj i hi)).le
  have houter : ∀ᶠ n in atTop, e n 0 ≤ e n s := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (linearEndpoint_strictMono hρ hn houterX).le
  have hp : ∀ᶠ n in atTop, ∀ i, i < s →
      0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i) := by
    have hfin : ∀ᶠ n in atTop, ∀ i ∈ Finset.range s,
        0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i) := by
      apply (Finset.range s).eventually_all.mpr
      intro i hi
      exact positive_rate_eventually_positive_mass _
        (sub_pos.mpr (hadj i (Finset.mem_range.mp hi))) (hscale i (i + 1))
    exact hfin.mono fun n hn i hi => hn i (Finset.mem_range.mpr hi)
  exact actualEnergyWindowCountRealLaw_tendsto_poisson law input isCompact_Icc e s E κ hκ
    (fun n => by simp only [e, hzero, linearEndpoint_zero]) hcompact horder houter hp
    (positive_rate_eventually_positive_mass _ (sub_pos.mpr houterX) (hscale 0 s))
    (fun i _ => linearEndpoint_tendsto E ρ (x i))
    _ (x s - x 0) (sub_nonneg.mpr houterX.le) (fun i => hscale i.val (i.val + 1))
    (hscale 0 s)

end FixedCouplingPoisson.Furstenberg
