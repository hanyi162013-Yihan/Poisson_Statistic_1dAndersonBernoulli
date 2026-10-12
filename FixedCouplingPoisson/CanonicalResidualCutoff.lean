import FixedCouplingPoisson.ResidualCutoff
import FixedCouplingPoisson.ResidualPinning

/-! One deterministic cutoff for finitely many actual residual block starts. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- The complement of the finite residual-tail event is the good-start event. -/
theorem finite_residual_good_tendsto_one_of_bad {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : ℕ → ι → Ω → ℝ) (hR : ∀ n i, Measurable (R n i)) (r : ℕ → ℝ)
    (hbad : Tendsto (fun n => μ {ω | ∃ i, r n < R n i ω}) atTop (𝓝 0)) :
    Tendsto (fun n => μ {ω | ∀ i, R n i ω ≤ r n}) atTop (𝓝 1) := by
  have ht := ENNReal.Tendsto.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop (𝓝 1)) hbad
    (Or.inl ENNReal.one_ne_top)
  simp only [tsub_zero] at ht
  convert ht using 1
  funext n
  let good := {ω | ∀ i, R n i ω ≤ r n}
  have hgood : MeasurableSet good := by
    simpa only [good, Set.setOf_forall] using
      MeasurableSet.iInter (fun i => measurableSet_le (hR n i) measurable_const)
  have hcompl : {ω | ∃ i, r n < R n i ω} = goodᶜ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, good, not_forall, not_le]
  rw [hcompl, measure_compl hgood (measure_ne_top _ _)]
  rw [measure_univ, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]

/-- The finite index may combine spectral windows and deterministic block starts.
The time-zero block is handled exactly; every other start uses proved model
pinning. No probabilistic tail premise is left in the conclusion. -/
theorem canonicalCrossingResidual_finite_exists_antitone_cutoff
    {ι : Type*} [Fintype ι] (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (E δ θ φ : ι → ℕ → ℝ) (k : ι → ℕ → ℕ)
    (hE : ∀ i n, E i n ∈ K) (hE' : ∀ i n, E i n + δ i n ∈ K)
    (hδ0 : ∀ i n, 0 ≤ δ i n) (hinit : ∀ i n, φ i n ≤ θ i n)
    (hp : ∀ i n, 0 < idsCandidate law (E i n + δ i n) - idsCandidate law (E i n))
    (hδ : ∀ i, Tendsto (δ i) atTop (𝓝 0))
    (hgap : ∀ i, Tendsto (fun n => θ i n - φ i n) atTop (𝓝 0))
    (hstart : ∀ i, (∀ n, k i n = 0 ∧ θ i n = φ i n) ∨
      Tendsto (k i) atTop atTop)
    (t : ι → ℝ)
    (htime : ∀ i, Tendsto (fun n =>
      (idsCandidate law (E i n + δ i n) - idsCandidate law (E i n)) * (k i n : ℝ))
      atTop (𝓝 (t i))) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Antitone r ∧
      Tendsto r atTop (𝓝 0) ∧ Tendsto (fun n => iidMeasure law {ω |
        ∃ i, r n < canonicalCrossingResidual (E i n) (δ i n) (θ i n) (φ i n)
          (k i n) ω}) atTop (𝓝 0) := by
  apply finite_residual_exists_antitone_cutoff (iidMeasure law)
    (fun n i ω => canonicalCrossingResidual (E i n) (δ i n) (θ i n) (φ i n) (k i n) ω)
  intro i r hr
  rcases hstart i with hzero | hk
  · have hz : ∀ n ω, canonicalCrossingResidual (E i n) (δ i n)
        (θ i n) (φ i n) (k i n) ω = 0 := by
      intro n ω
      simp only [canonicalCrossingResidual, canonicalCrossingCount,
        (hzero n).1, canonicalGapProcess_zero, (hzero n).2, sub_self,
        zero_div, Int.floor_zero, Int.cast_zero, mul_zero]
    simpa only [hz, not_lt_of_ge hr.le, Set.setOf_false, measure_empty] using
      (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ENNReal)) atTop (𝓝 0))
  · exact canonicalCrossingResidual_tails_tendsto_zero law input hK
      (E i) (δ i) (θ i) (φ i) (hE i) (hE' i) (hδ0 i) (hinit i) (hp i)
      (hδ i) (hgap i) (k i) hk (htime i) hr

end FixedCouplingPoisson.Furstenberg
