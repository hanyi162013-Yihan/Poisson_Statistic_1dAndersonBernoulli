import FixedCouplingPoisson.ResidualConsequences
import FixedCouplingPoisson.CrossingShortWindows

/-! One-sided residual pinning from actual short-window crossing control. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology

/-- Actual oriented residuals choose the zero endpoint. The short-window
control is supplied by the proved crossing-arrival chain, not by an interface. -/
theorem canonicalCrossingResidual_tails_tendsto_zero (law : PotentialLaw)
    (input : Input law) {K : Set ℝ} (hK : IsCompact K)
    (E δ θ φ : ℕ → ℝ)
    (hE : ∀ n, E n ∈ K) (hE' : ∀ n, E n + δ n ∈ K)
    (hδ0 : ∀ n, 0 ≤ δ n) (hinit : ∀ n, φ n ≤ θ n)
    (hp : ∀ n, 0 < idsCandidate law (E n + δ n) - idsCandidate law (E n))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hgap : Tendsto (fun n => θ n - φ n) atTop (𝓝 0))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop) {t : ℝ}
    (htime : Tendsto (fun n =>
      (idsCandidate law (E n + δ n) - idsCandidate law (E n)) * (k n : ℝ))
      atTop (𝓝 t)) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => iidMeasure law {ω |
      r < canonicalCrossingResidual (E n) (δ n) (θ n) (φ n) (k n) ω})
      atTop (𝓝 0) := by
  apply canonicalCrossingResidual_tails_of_short_windows law input hK
    ⟨E 0, hE 0⟩ E δ θ φ k (Eventually.of_forall hE) (Eventually.of_forall hE')
    (Eventually.of_forall hδ0) hδ hk (Eventually.of_forall hp) ?_ hr
  intro ε hε
  exact canonicalCrossingCount_short_windows law input hK E δ θ φ hE hE' hδ0 hinit hp
    hδ hgap k htime ε hε

/-- The actual terminal spectral-window remainder vanishes. -/
theorem actualWindowResidual_tails_tendsto_zero (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (e : ℕ → ℕ → ℝ) (i : ℕ)
    (hE : ∀ n, e n i ∈ K) (hE' : ∀ n, e n (i + 1) ∈ K)
    (horder : ∀ n, e n i ≤ e n (i + 1))
    (hp : ∀ n, 0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i))
    (hδ : Tendsto (fun n => e n (i + 1) - e n i) atTop (𝓝 0)) {t : ℝ}
    (htime : Tendsto (fun n =>
      (idsCandidate law (e n (i + 1)) - idsCandidate law (e n i)) * (n : ℝ))
      atTop (𝓝 t)) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => iidMeasure law {ω | r < actualWindowResidual e n i ω})
      atTop (𝓝 0) := by
  have hplus : ∀ n, e n i + (e n (i + 1) - e n i) = e n (i + 1) := by
    intro n
    ring
  have hg : Tendsto (fun _n : ℕ => (0 : ℝ) - 0) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ℝ))
      atTop (𝓝 0))
  have ht : Tendsto (fun n =>
      (idsCandidate law (e n i + (e n (i + 1) - e n i)) - idsCandidate law (e n i)) *
        (id n : ℝ)) atTop (𝓝 t) := by
    simpa only [hplus, id_eq] using htime
  have htail := canonicalCrossingResidual_tails_tendsto_zero law input hK
    (fun n => e n i) (fun n => e n (i + 1) - e n i) (fun _ => 0) (fun _ => 0)
    hE (by simpa only [hplus] using hE') (fun n => sub_nonneg.mpr (horder n))
    (fun _ => le_rfl) (by simpa only [hplus] using hp) hδ hg id tendsto_id ht hr
  simpa only [actualWindowResidual_eq_canonicalCrossingResidual, id_eq] using htail

/-- Exact terminal spectral counts agree simultaneously with the actual
crossing windings, with probability tending to one. All residual hypotheses
are discharged by the real arrival/short-window chain. -/
theorem actualWindow_rounding_success_from_IDS_scales (law : PotentialLaw)
    (input : Input law) (E : ℝ) {K : Set ℝ} (hK : IsCompact K)
    (e : ℕ → ℕ → ℝ) (s κ : ℕ) (hκ : κ ≤ s)
    (hanchor : ∀ n, e n κ = E)
    (hEnergy : ∀ n i, i ≤ s → e n i ∈ K)
    (horder : ∀ n i, i < s → e n i ≤ e n (i + 1))
    (hp : ∀ n i, i < s →
      0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i))
    (hδ : ∀ i < s, Tendsto (fun n => e n (i + 1) - e n i) atTop (𝓝 0))
    (w : ℕ → ℝ)
    (htime : ∀ i < s, Tendsto (fun n =>
      (idsCandidate law (e n (i + 1)) - idsCandidate law (e n i)) * (n : ℝ))
      atTop (𝓝 (w i))) :
    Tendsto (fun n => iidMeasure law {ω | ∀ i, i < s →
      actualWindowSpectralCount e n i ω = actualWindowWinding e n i ω})
      atTop (𝓝 1) := by
  apply actualWindow_rounding_success_of_individual_residuals law E (input.atEnergy E)
    e s κ hκ hanchor
  intro i hi r hr
  exact actualWindowResidual_tails_tendsto_zero law input hK e i
    (fun n => hEnergy n i hi.le)
    (fun n => hEnergy n (i + 1) (Nat.succ_le_of_lt hi))
    (fun n => horder n i hi) (fun n => hp n i hi) (hδ i hi) (htime i hi) hr

end FixedCouplingPoisson.Furstenberg
