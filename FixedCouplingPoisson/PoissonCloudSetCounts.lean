import FixedCouplingPoisson.PoissonCloudIntervalCounts

/-! Finite-cell natural counts for arbitrary bounded Borel sets. The support
condition is proved concretely for interval families in the interval-law file. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal unitInterval Topology

def poissonCloudSetCount (s : Finset ℤ) (A : Set ℝ) (ω : PoissonCloud) : ℕ :=
  ∑ z ∈ s, poissonCellCount z A (ω z)

theorem measurable_poissonCloudSetCount (s : Finset ℤ) (A : Set ℝ) (hA : MeasurableSet A) :
    Measurable (poissonCloudSetCount s A) := by
  unfold poissonCloudSetCount
  exact Finset.measurable_sum _ (fun z hz =>
    (measurable_poissonCellCount z A hA).comp (measurable_pi_apply z))

theorem poissonCellMeasure_eq_zero_of_cell_disjoint (A : Set ℝ) (z : ℤ)
    (hz : ∀ u : I, (z : ℝ) + (u : ℝ) ∉ A) (p : ℕ × (ℕ → I)) :
    poissonCellMeasure z p A = 0 := by
  classical
  rw [poissonCellMeasure, Measure.finsetSum_apply]
  exact Finset.sum_eq_zero (fun j hj => by simp [Measure.dirac_apply, hz (p.2 j)])

theorem poissonCloudMeasure_apply_eq_nat_setCount (A : Set ℝ) (s : Finset ℤ)
    (hs : ∀ z ∉ s, ∀ u : I, (z : ℝ) + (u : ℝ) ∉ A) (ω : PoissonCloud) :
    poissonCloudMeasure ω A = (poissonCloudSetCount s A ω : ℝ≥0∞) := by
  classical
  rw [poissonCloudMeasure, Measure.sum_apply_of_countable,
    tsum_eq_sum (s := s) (fun z hz =>
      poissonCellMeasure_eq_zero_of_cell_disjoint A z (hs z hz) (ω z))]
  simp_rw [poissonCellMeasure_apply_eq_count]
  simp only [poissonCloudSetCount, Nat.cast_sum]

theorem poissonCloudMeasure_apply_ne_top_of_cells (A : Set ℝ) (s : Finset ℤ)
    (hs : ∀ z ∉ s, ∀ u : I, (z : ℝ) + (u : ℝ) ∉ A) (ω : PoissonCloud) :
    poissonCloudMeasure ω A ≠ ∞ := by
  rw [poissonCloudMeasure_apply_eq_nat_setCount A s hs ω]
  simp

theorem poissonCloudMeasure_real_apply_eq_nat_setCount (A : Set ℝ) (s : Finset ℤ)
    (hs : ∀ z ∉ s, ∀ u : I, (z : ℝ) + (u : ℝ) ∉ A) (ω : PoissonCloud) :
    (poissonCloudMeasure ω).real A = (poissonCloudSetCount s A ω : ℝ) := by
  rw [measureReal_def, poissonCloudMeasure_apply_eq_nat_setCount A s hs ω]
  simp

end FixedCouplingPoisson
