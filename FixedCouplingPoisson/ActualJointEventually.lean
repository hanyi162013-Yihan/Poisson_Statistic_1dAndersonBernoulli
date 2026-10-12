import FixedCouplingPoisson.ActualJointLaplace
import FixedCouplingPoisson.ResidualPinningEventually

/-! The actual joint law depends only on eventual physical parameter validity. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology NNReal

theorem canonicalColoredCountRealLaw_tendsto_poisson_eventually
    (law : PotentialLaw) (input : Input law) {K : Set ℝ} (hK : IsCompact K)
    (e : ℕ → ℕ → ℝ) (s : ℕ) (E₀ : ℝ)
    (hcompact : ∀ᶠ n in atTop, ∀ i, i ≤ s → e n i ∈ K)
    (horder : ∀ᶠ n in atTop, ∀ i, i < s → e n i ≤ e n (i + 1))
    (houter : ∀ᶠ n in atTop, e n 0 ≤ e n s)
    (hp : ∀ᶠ n in atTop, ∀ i, i < s →
      0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i))
    (hpouter : ∀ᶠ n in atTop, 0 < idsCandidate law (e n s) - idsCandidate law (e n 0))
    (helim : ∀ i, i ≤ s → Tendsto (fun n => e n i) atTop (𝓝 E₀))
    (w : Fin s → ℝ≥0) (W : ℝ) (hW : 0 ≤ W)
    (hscale : ∀ i : Fin s, Tendsto (fun n =>
      (idsCandidate law (e n (i.val + 1)) - idsCandidate law (e n i.val)) * (n : ℝ))
      atTop (𝓝 (w i : ℝ)))
    (houterScale : Tendsto (fun n =>
      (idsCandidate law (e n s) - idsCandidate law (e n 0)) * (n : ℝ)) atTop (𝓝 W)) :
    Tendsto (fun n => canonicalColoredCountRealLaw law (e n) s n)
      atTop (𝓝 (poissonRealProduct w)) := by
  have hvalid : ∀ᶠ n in atTop,
      (∀ i, i ≤ s → e n i ∈ K) ∧ (∀ i, i < s → e n i ≤ e n (i + 1)) ∧
      e n 0 ≤ e n s ∧
      (∀ i, i < s → 0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i)) ∧
      0 < idsCandidate law (e n s) - idsCandidate law (e n 0) := by
    filter_upwards [hcompact, horder, houter, hp, hpouter] with n hn ho hO hp hP
    exact ⟨hn, ho, hO, hp, hP⟩
  obtain ⟨ρ, hρvalid, hρeq⟩ := exists_eventually_id_valid_selector hvalid
  have hρtop : Tendsto ρ atTop atTop := tendsto_id.congr' hρeq.symm
  have hscale' (i : Fin s) : Tendsto (fun n =>
      (idsCandidate law (e (ρ n) (i.val + 1)) - idsCandidate law (e (ρ n) i.val)) *
        (n : ℝ)) atTop (𝓝 (w i : ℝ)) := by
    apply (hscale i).congr'
    filter_upwards [hρeq] with n hn
    simp only [hn, id_eq]
  have houterScale' : Tendsto (fun n =>
      (idsCandidate law (e (ρ n) s) - idsCandidate law (e (ρ n) 0)) * (n : ℝ))
      atTop (𝓝 W) := by
    apply houterScale.congr'
    filter_upwards [hρeq] with n hn
    simp only [hn, id_eq]
  have h := canonicalColoredCountRealLaw_tendsto_poisson law input hK
    (fun n => e (ρ n)) s E₀
    (fun n => (hρvalid n).1) (fun n => (hρvalid n).2.1)
    (fun n => (hρvalid n).2.2.1) (fun n => (hρvalid n).2.2.2.1)
    (fun n => (hρvalid n).2.2.2.2)
    (fun i hi => (helim i hi).comp hρtop) w W hW hscale' houterScale'
  apply h.congr'
  filter_upwards [hρeq] with n hn
  simp only [hn, id_eq]

end FixedCouplingPoisson.Furstenberg
