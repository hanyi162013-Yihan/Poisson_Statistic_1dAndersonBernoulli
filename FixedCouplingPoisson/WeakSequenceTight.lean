import Mathlib.MeasureTheory.Measure.Prokhorov

/-! Tightness of an actually convergent sequence of probability measures. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Filter Set
open scoped Topology ENNReal

theorem isTightMeasureSet_insert_range_of_weak_tendsto {S : Type*}
    [MetricSpace S] [SecondCountableTopology S] [CompleteSpace S]
    [MeasurableSpace S] [BorelSpace S]
    (νs : ℕ → ProbabilityMeasure S) (ν : ProbabilityMeasure S)
    (hν : Tendsto νs atTop (𝓝 ν)) :
    IsTightMeasureSet (insert (ν : Measure S) (range (fun n => (νs n : Measure S)))) := by
  have hcomp : IsCompact (insert ν (range νs)) := hν.isCompact_insert_range
  have hclosure : IsCompact (closure (insert ν (range νs))) := by
    rwa [hcomp.isClosed.closure_eq]
  have h := isTightMeasureSet_of_isCompact_closure hclosure
  have heq : {μ : Measure S | ∃ Q ∈ insert ν (range νs), (Q : Measure S) = μ} =
      insert (ν : Measure S) (range (fun n => (νs n : Measure S))) := by
    ext μ
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      rcases hQ with rfl | ⟨n, rfl⟩
      · exact mem_insert _ _
      · exact mem_insert_of_mem _ (mem_range_self n)
    · rintro (rfl | ⟨n, rfl⟩)
      · exact ⟨ν, mem_insert _ _, rfl⟩
      · exact ⟨νs n, mem_insert_of_mem _ (mem_range_self n), rfl⟩
  rwa [heq] at h

/-- Both the sequence and its actual limit have uniform real upper tails. -/
theorem exists_uniform_upper_tail_of_weak_tendsto
    (νs : ℕ → ProbabilityMeasure ℝ) (ν : ProbabilityMeasure ℝ)
    (hν : Tendsto νs atTop (𝓝 ν)) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧
      (∀ n, (νs n : Measure ℝ) (Ioi M) ≤ ε) ∧ (ν : Measure ℝ) (Ioi M) ≤ ε := by
  have htight := isTightMeasureSet_insert_range_of_weak_tendsto νs ν hν
  obtain ⟨K, hK, hbound⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight ε hε
  obtain ⟨R, hR⟩ := hK.bddAbove
  let M : ℝ := max R 0 + 1
  have hM : 0 < M := by dsimp [M]; linarith [le_max_right R 0]
  have hsub : Ioi M ⊆ Kᶜ := by
    intro x hx hxK
    have hRle : R ≤ M := by dsimp [M]; linarith [le_max_left R 0]
    exact (not_lt_of_ge ((hR hxK).trans hRle)) hx
  refine ⟨M, hM, fun n => (measure_mono hsub).trans (hbound _ ?_),
    (measure_mono hsub).trans (hbound _ (mem_insert _ _))⟩
  exact mem_insert_of_mem _ (mem_range_self n)

end FixedCouplingPoisson
