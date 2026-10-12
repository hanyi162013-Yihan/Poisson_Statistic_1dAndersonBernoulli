import FixedCouplingPoisson.ScalarCrossingCounts

/-! The actual arrival CDF limit is uniform over the common initial phase
and all initial gaps below any prescribed vanishing cutoff. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

def canonicalCountTailProbability (law : PotentialLaw) (E δ θ d : ℝ) (k n : ℕ) : ℝ :=
  (iidMeasure law).real {ω | k ≤ canonicalNaturalCrossingCount E δ θ (θ - d) n ω}

theorem canonical_arrival_cdf_uniform_initial_gap
    (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (E δ r : ℕ → ℝ)
    (hE : ∀ n, E n ∈ K) (hE' : ∀ n, E n + δ n ∈ K)
    (hδ : ∀ n, 0 ≤ δ n) (hr : ∀ n, 0 ≤ r n)
    (hp : ∀ n, 0 < idsCandidate law (E n + δ n) - idsCandidate law (E n))
    (hδlim : Tendsto δ atTop (𝓝 0)) (hrlim : Tendsto r atTop (𝓝 0))
    (ℓ : ℕ → ℕ) {t : ℝ}
    (htime : Tendsto (fun n =>
      (idsCandidate law (E n + δ n) - idsCandidate law (E n)) * (ℓ n : ℝ)) atTop (𝓝 t))
    (k : ℕ) (hk : 0 < k) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ θ d : ℝ, 0 ≤ d → d ≤ r n →
      |canonicalCountTailProbability law (E n) (δ n) θ d k (ℓ n) -
        cdf (exponentialSumLaw k : Measure ℝ) t| < ε := by
  classical
  let bad : ℕ → ℝ × ℝ → Prop := fun n a =>
    0 ≤ a.2 ∧ a.2 ≤ r n ∧
      ¬ |canonicalCountTailProbability law (E n) (δ n) a.1 a.2 k (ℓ n) -
        cdf (exponentialSumLaw k : Measure ℝ) t| < ε
  let X (n : ℕ) : ℝ × ℝ :=
    if h : ∃ a, bad n a then Classical.choose h else (0, 0)
  have hXd (n : ℕ) : 0 ≤ (X n).2 ∧ (X n).2 ≤ r n := by
    by_cases h : ∃ a, bad n a
    · have hs : bad n (X n) := by
        dsimp only [X]
        rw [dif_pos h]
        exact Classical.choose_spec h
      exact ⟨hs.1, hs.2.1⟩
    · simp only [X, dif_neg h]
      exact ⟨le_rfl, hr n⟩
  have hdlim : Tendsto (fun n => (X n).2) atTop (𝓝 0) :=
    squeeze_zero (fun n => (hXd n).1) (fun n => (hXd n).2) hrlim
  have hinit (n : ℕ) : (X n).1 - (X n).2 ≤ (X n).1 := by
    linarith [(hXd n).1]
  have hgap : Tendsto (fun n => (X n).1 - ((X n).1 - (X n).2)) atTop (𝓝 0) := by
    convert hdlim using 1
    funext n
    ring
  have hchosen := canonicalNaturalCrossingCount_tail_tendsto law input hK
    E δ (fun n => (X n).1) (fun n => (X n).1 - (X n).2)
    hE hE' hδ hinit hp hδlim hgap ℓ htime k hk
  have hnear : ∀ᶠ n in atTop,
      |canonicalCountTailProbability law (E n) (δ n) (X n).1 (X n).2 k (ℓ n) -
        cdf (exponentialSumLaw k : Measure ℝ) t| < ε := by
    simpa only [Real.dist_eq, canonicalCountTailProbability] using
      (Metric.tendsto_nhds.mp hchosen ε hε)
  filter_upwards [hnear] with n hn
  intro θ d hd0 hdr
  by_contra hnot
  have hex : ∃ a, bad n a := ⟨(θ, d), hd0, hdr, hnot⟩
  have hs : bad n (X n) := by
    dsimp only [X]
    rw [dif_pos hex]
    exact Classical.choose_spec hex
  exact hs.2.2 hn

end FixedCouplingPoisson.Furstenberg
