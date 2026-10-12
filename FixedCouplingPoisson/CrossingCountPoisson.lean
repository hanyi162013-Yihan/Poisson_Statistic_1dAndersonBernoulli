import FixedCouplingPoisson.ScalarCrossingCounts
import FixedCouplingPoisson.GammaIntegerCDF
import FixedCouplingPoisson.NatWeakConvergence

/-! Actual one-window crossing-count laws converge to the genuine
Mathlib Poisson probability law. No count-law premise is introduced. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

def poissonCountLaw (t : ℝ≥0) : ProbabilityMeasure ℕ :=
  ⟨poissonMeasure t, inferInstance⟩

theorem nat_singleton_probability_eq_tail_difference
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (X : Ω → ℕ) (hX : Measurable X) (k : ℕ) :
    μ.real {ω | X ω = k} = μ.real {ω | k ≤ X ω} - μ.real {ω | k + 1 ≤ X ω} := by
  have hs : {ω | X ω = k} = {ω | k ≤ X ω} \ {ω | k + 1 ≤ X ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
    omega
  rw [hs]
  exact measureReal_sdiff (fun ω hω => (Nat.le_succ k).trans hω)
    (measurableSet_le measurable_const hX)

namespace Furstenberg

theorem canonicalNaturalCrossingCountLaw_singleton_eq_tail_difference
    (law : PotentialLaw) (E δ θ φ : ℝ) (n k : ℕ) :
    (canonicalNaturalCrossingCountLaw law E δ θ φ n : Measure ℕ).real {k} =
      (iidMeasure law).real {ω | k ≤ canonicalNaturalCrossingCount E δ θ φ n ω} -
        (iidMeasure law).real {ω | k + 1 ≤ canonicalNaturalCrossingCount E δ θ φ n ω} := by
  have hmap : (canonicalNaturalCrossingCountLaw law E δ θ φ n : Measure ℕ).real {k} =
      (iidMeasure law).real {ω | canonicalNaturalCrossingCount E δ θ φ n ω = k} := by
    change (((iidMeasure law).map (canonicalNaturalCrossingCount E δ θ φ n)) {k}).toReal = _
    rw [Measure.map_apply (canonicalNaturalCrossingCount_measurable E δ θ φ n)
      (measurableSet_singleton k)]
    rfl
  rw [hmap]
  exact nat_singleton_probability_eq_tail_difference (iidMeasure law) _
    (canonicalNaturalCrossingCount_measurable E δ θ φ n) k

theorem canonicalNaturalCrossingCountLaw_singleton_tendsto_poisson
    {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (E δ θ φ : ι → ℝ)
    (hE : ∀ i, E i ∈ K) (hE' : ∀ i, E i + δ i ∈ K)
    (hδ : ∀ i, 0 ≤ δ i) (hinit : ∀ i, φ i ≤ θ i)
    (hp : ∀ i, 0 < idsCandidate law (E i + δ i) - idsCandidate law (E i))
    (hδlim : Tendsto δ F (𝓝 0))
    (hgap : Tendsto (fun i => θ i - φ i) F (𝓝 0))
    (n : ι → ℕ) (t : ℝ≥0)
    (htime : Tendsto (fun i =>
      (idsCandidate law (E i + δ i) - idsCandidate law (E i)) * (n i : ℝ)) F (𝓝 (t : ℝ)))
    (k : ℕ) :
    Tendsto (fun i =>
      (canonicalNaturalCrossingCountLaw law (E i) (δ i) (θ i) (φ i) (n i) : Measure ℕ).real {k})
      F (𝓝 ((poissonMeasure t).real {k})) := by
  have htail (m : ℕ) : Tendsto (fun i => (iidMeasure law).real
      {ω | m ≤ canonicalNaturalCrossingCount (E i) (δ i) (θ i) (φ i) (n i) ω})
        F (𝓝 (cdf (exponentialSumLaw m : Measure ℝ) t)) := by
    cases m with
    | zero =>
      have hs (i : ι) : (iidMeasure law).real
          {ω | 0 ≤ canonicalNaturalCrossingCount (E i) (δ i) (θ i) (φ i) (n i) ω} = 1 := by
        simp
      rw [cdf_exponentialSumLaw_zero (t : ℝ) t.property]
      simpa only [hs] using
        (tendsto_const_nhds : Tendsto (fun _ : ι => (1 : ℝ)) F (𝓝 1))
    | succ m =>
      exact canonicalNaturalCrossingCount_tail_tendsto law input hK
        E δ θ φ hE hE' hδ hinit hp hδlim hgap n htime (m + 1) (Nat.succ_pos m)
  have ht := (htail k).sub (htail (k + 1))
  simpa only [← canonicalNaturalCrossingCountLaw_singleton_eq_tail_difference,
    exponentialSumLaw_cdf_difference_eq_poissonMeasure] using ht

theorem canonicalNaturalCrossingCountLaw_tendsto_poisson
    {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (E δ θ φ : ι → ℝ)
    (hE : ∀ i, E i ∈ K) (hE' : ∀ i, E i + δ i ∈ K)
    (hδ : ∀ i, 0 ≤ δ i) (hinit : ∀ i, φ i ≤ θ i)
    (hp : ∀ i, 0 < idsCandidate law (E i + δ i) - idsCandidate law (E i))
    (hδlim : Tendsto δ F (𝓝 0))
    (hgap : Tendsto (fun i => θ i - φ i) F (𝓝 0))
    (n : ι → ℕ) (t : ℝ≥0)
    (htime : Tendsto (fun i =>
      (idsCandidate law (E i + δ i) - idsCandidate law (E i)) * (n i : ℝ)) F (𝓝 (t : ℝ))) :
    Tendsto (fun i => canonicalNaturalCrossingCountLaw law (E i) (δ i) (θ i) (φ i) (n i))
      F (𝓝 (poissonCountLaw t)) := by
  apply nat_probabilityMeasures_tendsto_of_singletons
  intro k
  exact canonicalNaturalCrossingCountLaw_singleton_tendsto_poisson law input hK
    E δ θ φ hE hE' hδ hinit hp hδlim hgap n t htime k

end Furstenberg
end FixedCouplingPoisson
