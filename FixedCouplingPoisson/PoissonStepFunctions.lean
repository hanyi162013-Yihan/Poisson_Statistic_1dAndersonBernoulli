import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Exact finite disjoint-step identities for Poisson interval tests. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Set
open scoped ENNReal

section FiniteDimension
variable {d : Type*} [Fintype d]

def poissonStepDensity (A : d → Set ℝ) (t : d → ℝ) (x : ℝ) : ℝ :=
  ∑ j, (A j).indicator (fun _ : ℝ => t j) x

theorem measurable_poissonStepDensity (A : d → Set ℝ) (t : d → ℝ)
    (hA : ∀ j, MeasurableSet (A j)) : Measurable (poissonStepDensity A t) := by
  unfold poissonStepDensity
  exact Finset.measurable_sum _ (fun j hj => measurable_const.indicator (hA j))

theorem poissonStepDensity_nonneg (A : d → Set ℝ) (t : d → ℝ)
    (ht : ∀ j, 0 ≤ t j) (x : ℝ) : 0 ≤ poissonStepDensity A t x := by
  classical
  apply Finset.sum_nonneg
  intro j hj
  exact Set.indicator_nonneg (fun _ _ => ht j) x

theorem poissonStepDensity_eq_of_mem (A : d → Set ℝ) (t : d → ℝ)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (x : ℝ) (j : d) (hx : x ∈ A j) :
    poissonStepDensity A t x = t j := by
  classical
  unfold poissonStepDensity
  rw [Finset.sum_eq_single j]
  · exact Set.indicator_of_mem hx _
  · intro k hk hkj
    have hxk : x ∉ A k := by
      intro hkx
      exact Set.disjoint_left.mp (hdisj hkj) hkx hx
    exact Set.indicator_of_notMem hxk _
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

theorem poissonStepDensity_eq_zero_of_not_mem (A : d → Set ℝ) (t : d → ℝ)
    (x : ℝ) (hx : ∀ j, x ∉ A j) : poissonStepDensity A t x = 0 := by
  classical
  exact Finset.sum_eq_zero (fun j hj => Set.indicator_of_notMem (hx j) _)

theorem poissonStepDensity_defect (A : d → Set ℝ) (t : d → ℝ)
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) (x : ℝ) :
    1 - Real.exp (-poissonStepDensity A t x) =
      poissonStepDensity A (fun j => 1 - Real.exp (-t j)) x := by
  classical
  by_cases hx : ∃ j, x ∈ A j
  · obtain ⟨j, hj⟩ := hx
    rw [poissonStepDensity_eq_of_mem A t hdisj x j hj,
      poissonStepDensity_eq_of_mem A _ hdisj x j hj]
  · have h : ∀ j, x ∉ A j := by simpa only [not_exists] using hx
    rw [poissonStepDensity_eq_zero_of_not_mem A t x h,
      poissonStepDensity_eq_zero_of_not_mem A _ x h]
    simp

theorem integrable_poissonStepDensity (A : d → Set ℝ) (t : d → ℝ)
    (hA : ∀ j, MeasurableSet (A j)) (μ : Measure ℝ) (hμ : ∀ j, μ (A j) ≠ ∞) :
    Integrable (poissonStepDensity A t) μ := by
  classical
  exact integrable_finsetSum _ (fun j hj =>
    (integrableOn_const (hμ j)).integrable_indicator (hA j))

theorem integral_poissonStepDensity (A : d → Set ℝ) (t : d → ℝ)
    (hA : ∀ j, MeasurableSet (A j)) (μ : Measure ℝ) (hμ : ∀ j, μ (A j) ≠ ∞) :
    (∫ x, poissonStepDensity A t x ∂μ) = ∑ j, μ.real (A j) * t j := by
  classical
  change (∫ x, ∑ j, (A j).indicator (fun _ : ℝ => t j) x ∂μ) = _
  rw [integral_finsetSum _ (fun j hj =>
    (integrableOn_const (hμ j)).integrable_indicator (hA j))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_indicator_const _ (hA j), smul_eq_mul]

end FiniteDimension
end FixedCouplingPoisson
