import FixedCouplingPoisson.PoissonCloudMeasure

/-! Actual interval counts of the locally finite cloud, with a natural-valued
measurable count agreeing pathwise with the constructed random measure. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal unitInterval Topology

def poissonCellCount (z : ℤ) (A : Set ℝ) (p : ℕ × (ℕ → I)) : ℕ :=
  ∑ j ∈ Finset.range p.1, A.indicator (fun _ : ℝ => (1 : ℕ))
    ((z : ℝ) + (p.2 j : ℝ))

theorem measurable_poissonCellCount (z : ℤ) (A : Set ℝ) (hA : MeasurableSet A) :
    Measurable (poissonCellCount z A) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun u : ℕ → I => ∑ j ∈ Finset.range n,
    A.indicator (fun _ : ℝ => (1 : ℕ)) ((z : ℝ) + (u j : ℝ)))
  fun_prop

theorem poissonCellMeasure_apply_eq_count (z : ℤ) (A : Set ℝ) (p : ℕ × (ℕ → I)) :
    poissonCellMeasure z p A = (poissonCellCount z A p : ℝ≥0∞) := by
  classical
  rw [poissonCellMeasure, Measure.finsetSum_apply, poissonCellCount, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : (z : ℝ) + (p.2 j : ℝ) ∈ A <;> simp [Measure.dirac_apply, h]

def poissonCloudIntervalCount (a b : ℝ) (ω : PoissonCloud) : ℕ :=
  ∑ z ∈ Finset.Icc ⌊a - 1⌋ ⌈b⌉, poissonCellCount z (Ioc a b) (ω z)

theorem measurable_poissonCloudIntervalCount (a b : ℝ) :
    Measurable (poissonCloudIntervalCount a b) := by
  unfold poissonCloudIntervalCount
  exact Finset.measurable_sum _ (fun z hz =>
    (measurable_poissonCellCount z _ measurableSet_Ioc).comp (measurable_pi_apply z))

theorem poissonCellMeasure_Ioc_eq_zero_of_not_mem (ω : PoissonCloud) (a b : ℝ)
    (z : ℤ) (hz : z ∉ Finset.Icc ⌊a - 1⌋ ⌈b⌉) :
    poissonCellMeasure z (ω z) (Ioc a b) = 0 := by
  classical
  rw [poissonCellMeasure, Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  have hn : (z : ℝ) + ((ω z).2 j : ℝ) ∉ Ioc a b := by
    intro ha
    apply hz
    apply Finset.mem_Icc.mpr
    constructor
    · have hfl := Int.floor_le (a - 1)
      have hr : (⌊a - 1⌋ : ℝ) ≤ (z : ℝ) := by linarith [ha.1, ((ω z).2 j).property.2]
      exact_mod_cast hr
    · have hce := Int.le_ceil b
      have hr : (z : ℝ) ≤ (⌈b⌉ : ℝ) := by linarith [ha.2, ((ω z).2 j).property.1]
      exact_mod_cast hr
  simp [Measure.dirac_apply, hn]

theorem poissonCloudMeasure_Ioc_eq_nat_count (a b : ℝ) (ω : PoissonCloud) :
    poissonCloudMeasure ω (Ioc a b) = (poissonCloudIntervalCount a b ω : ℝ≥0∞) := by
  classical
  rw [poissonCloudMeasure, Measure.sum_apply _ measurableSet_Ioc,
    tsum_eq_sum (s := Finset.Icc ⌊a - 1⌋ ⌈b⌉)
      (fun z hz => poissonCellMeasure_Ioc_eq_zero_of_not_mem ω a b z hz)]
  simp_rw [poissonCellMeasure_apply_eq_count]
  simp only [poissonCloudIntervalCount, Nat.cast_sum]

theorem poissonCloudMeasure_real_Ioc_eq_nat_count (a b : ℝ) (ω : PoissonCloud) :
    (poissonCloudMeasure ω).real (Ioc a b) = (poissonCloudIntervalCount a b ω : ℝ) := by
  rw [measureReal_def, poissonCloudMeasure_Ioc_eq_nat_count]
  simp

end FixedCouplingPoisson
