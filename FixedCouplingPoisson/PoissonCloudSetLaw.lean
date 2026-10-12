import FixedCouplingPoisson.PoissonCloudSetCounts
import FixedCouplingPoisson.PoissonCloudMeasurableLaplace
import FixedCouplingPoisson.PoissonStepFunctions
import FixedCouplingPoisson.PoissonProduct

/-! Joint independent Poisson identification for actual cloud counts in finite
families of disjoint bounded Borel sets. All laws are constructed measures. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal unitInterval Topology

section FiniteDimension
variable {d : Type*} [Fintype d]

theorem integral_poissonCloudSetCounts_mixedLaplace (A : d → Set ℝ)
    (hA : ∀ j, MeasurableSet (A j))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hvol : ∀ j, volume (A j) ≠ ∞) (s : Finset ℤ)
    (hs : ∀ z ∉ s, ∀ u : I, ∀ j, (z : ℝ) + (u : ℝ) ∉ A j)
    (t : d → ℝ) (ht : ∀ j, 0 ≤ t j) :
    (∫ ω, poissonMixedLaplaceTest t (fun j => poissonCloudSetCount s (A j) ω)
      ∂(poissonCloudLaw : Measure PoissonCloud)) =
        Real.exp (-(∑ j, volume.real (A j) * (1 - Real.exp (-t j)))) := by
  classical
  let f : ℝ → ℝ := poissonStepDensity A t
  have hfm : Measurable f := measurable_poissonStepDensity A t hA
  have hf0 : ∀ x, 0 ≤ f x := poissonStepDensity_nonneg A t ht
  have hfω : ∀ ω, Integrable f (poissonCloudMeasure ω) := by
    intro ω
    exact integrable_poissonStepDensity A t hA (poissonCloudMeasure ω)
      (fun j => poissonCloudMeasure_apply_ne_top_of_cells (A j) s
        (fun z hz u => hs z hz u j) ω)
  have hdef : (fun x => 1 - Real.exp (-f x)) =
      poissonStepDensity A (fun j => 1 - Real.exp (-t j)) :=
    funext (poissonStepDensity_defect A t hdisj)
  have hfi : Integrable (fun x => 1 - Real.exp (-f x)) := by
    rw [hdef]
    exact integrable_poissonStepDensity A _ hA volume hvol
  have hcell : ∀ z ∉ s, ∀ u : I, f ((z : ℝ) + (u : ℝ)) = 0 := by
    intro z hz u
    exact poissonStepDensity_eq_zero_of_not_mem A t _ (hs z hz u)
  have hstep : ∀ ω,
      (∫ x, f x ∂poissonCloudMeasure ω) =
        ∑ j, t j * (poissonCloudSetCount s (A j) ω : ℝ) := by
    intro ω
    change (∫ x, poissonStepDensity A t x ∂poissonCloudMeasure ω) = _
    rw [integral_poissonStepDensity A t hA (poissonCloudMeasure ω)
      (fun j => poissonCloudMeasure_apply_ne_top_of_cells (A j) s
        (fun z hz u => hs z hz u j) ω)]
    apply Finset.sum_congr rfl
    intro j hj
    rw [poissonCloudMeasure_real_apply_eq_nat_setCount (A j) s
      (fun z hz u => hs z hz u j) ω]
    ring
  have h := integral_poissonCloudLaplace_measurable f hfm hf0 hfω hfi s hcell
  simp_rw [hstep] at h
  rw [hdef, integral_poissonStepDensity A _ hA volume hvol] at h
  exact h

theorem poissonCloudSetCounts_real_law (A : d → Set ℝ)
    (hA : ∀ j, MeasurableSet (A j))
    (hdisj : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hvol : ∀ j, volume (A j) ≠ ∞) (s : Finset ℤ)
    (hs : ∀ z ∉ s, ∀ u : I, ∀ j, (z : ℝ) + (u : ℝ) ∉ A j)
    (w : d → ℝ≥0) (hw : ∀ j, volume.real (A j) = (w j : ℝ)) :
    poissonCloudLaw.map
      (show Measurable (fun ω : PoissonCloud =>
        fun j => (poissonCloudSetCount s (A j) ω : ℝ)) from by
          apply measurable_pi_lambda
          intro j
          exact (show Measurable (fun n : ℕ => (n : ℝ)) from by fun_prop).comp
            (measurable_poissonCloudSetCount s (A j) (hA j))).aemeasurable =
      poissonRealProduct w := by
  classical
  let Y : PoissonCloud → d → ℕ := fun ω j => poissonCloudSetCount s (A j) ω
  have hY : Measurable Y := by
    apply measurable_pi_lambda
    intro j
    exact measurable_poissonCloudSetCount s (A j) (hA j)
  have hLaplace : ∀ m : d → ℕ,
      (∫ ω, poissonMixedLaplaceTest (fun j => (m j : ℝ)) (Y ω)
        ∂(poissonCloudLaw : Measure PoissonCloud)) =
          Real.exp (-(∑ j, (w j : ℝ) * (1 - Real.exp (-(m j : ℝ))))) := by
    intro m
    simpa only [hw] using integral_poissonCloudSetCounts_mixedLaplace A hA hdisj hvol s hs
      (fun j => (m j : ℝ)) (fun j => Nat.cast_nonneg (m j))
  have hT := poissonReal_laws_tendsto_of_mixed_integer_laplace
    (ι := ℕ) (F := atTop) poissonCloudLaw (fun _ ω => Y ω) (fun _ => hY) w
    (fun m => by simp_rw [hLaplace m]; exact tendsto_const_nhds)
  exact tendsto_nhds_unique tendsto_const_nhds hT

end FiniteDimension
end FixedCouplingPoisson
