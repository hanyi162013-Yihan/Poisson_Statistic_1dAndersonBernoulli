import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Ordinary weak convergence of natural-number probability laws

Singleton masses determine convergence on the discrete natural numbers.
For each open set its limiting mass is a supremum of finite sums of
singleton masses. Finite sums converge and are bounded by the
approximating law's mass of that set, proving the Portmanteau lower bound.
-/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Filter Set
open scoped Topology BigOperators

theorem nat_measure_eq_tsum_singletons (ν : Measure ℕ) (G : Set ℕ) :
    ν G = ∑' k : G, ν {(k : ℕ)} := by
  have h := tsum_measure_preimage_singleton (μ := ν) (s := G) (f := id)
    (to_countable G) (fun k _ => by simp)
  simpa using h.symm

/-- On the discrete natural numbers, point masses converging to those of
an actual probability law imply ordinary weak convergence. -/
theorem nat_probabilityMeasures_tendsto_of_singletons_ennreal
    {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (hm : ∀ k : ℕ, Tendsto (fun i => (μs i : Measure ℕ) {k}) F
      (𝓝 ((μ : Measure ℕ) {k}))) :
    Tendsto μs F (𝓝 μ) := by
  rcases F.eq_or_neBot with rfl | hF
  · simp
  let : NeBot F := hF
  apply tendsto_of_forall_isOpen_le_liminf'
  intro G _hG
  calc
    (μ : Measure ℕ) G = ∑' k : G, (μ : Measure ℕ) {(k : ℕ)} :=
      nat_measure_eq_tsum_singletons (μ : Measure ℕ) G
    _ ≤ F.liminf (fun i => (μs i : Measure ℕ) G) := by
      rw [ENNReal.tsum_eq_iSup_sum]
      refine iSup_le fun s => ?_
      have hs : Tendsto (fun i => ∑ k ∈ s, (μs i : Measure ℕ) {(k : ℕ)}) F
          (𝓝 (∑ k ∈ s, (μ : Measure ℕ) {(k : ℕ)})) :=
        tendsto_finsetSum s fun k _ => hm (k : ℕ)
      rw [← hs.liminf_eq]
      have hle : ∀ᶠ i in F,
          (∑ k ∈ s, (μs i : Measure ℕ) {(k : ℕ)}) ≤ (μs i : Measure ℕ) G :=
        Eventually.of_forall fun i => by
          rw [nat_measure_eq_tsum_singletons (μs i : Measure ℕ) G]
          exact ENNReal.sum_le_tsum s
      exact liminf_le_liminf hle

/-- Real-valued point masses suffice; the target is the usual weak topology
on actual `ProbabilityMeasure ℕ`. -/
theorem nat_probabilityMeasures_tendsto_of_singletons
    {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    {μs : ι → ProbabilityMeasure ℕ} {μ : ProbabilityMeasure ℕ}
    (hm : ∀ k : ℕ, Tendsto (fun i => (μs i : Measure ℕ).real {k}) F
      (𝓝 ((μ : Measure ℕ).real {k}))) :
    Tendsto μs F (𝓝 μ) := by
  apply nat_probabilityMeasures_tendsto_of_singletons_ennreal
  intro k
  exact (ENNReal.tendsto_toReal_iff
    (fun i => measure_ne_top (μs i : Measure ℕ) {k})
    (measure_ne_top (μ : Measure ℕ) {k})).mp (hm k)

end FixedCouplingPoisson
