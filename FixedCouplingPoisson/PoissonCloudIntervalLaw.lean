import FixedCouplingPoisson.PoissonCloudSetLaw

/-! The original definition of the unit-intensity PPP is verified on every
finite family of disjoint bounded half-open intervals: actual counts have the
actual independent Poisson product law, with means equal to interval lengths. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal unitInterval Topology

section FiniteDimension
variable {d : Type*} [Fintype d]

def poissonIntervalCells (a b : d → ℝ) : Finset ℤ := by
  classical
  exact Finset.univ.biUnion (fun j => Finset.Icc ⌊a j - 1⌋ ⌈b j⌉)

theorem poissonIntervalCells_outside (a b : d → ℝ) (z : ℤ)
    (hz : z ∉ poissonIntervalCells a b) (u : I) (j : d) :
    (z : ℝ) + (u : ℝ) ∉ Ioc (a j) (b j) := by
  classical
  intro hx
  apply hz
  apply Finset.mem_biUnion.mpr
  refine ⟨j, Finset.mem_univ j, Finset.mem_Icc.mpr ⟨?_, ?_⟩⟩
  · have hfl := Int.floor_le (a j - 1)
    have hr : (⌊a j - 1⌋ : ℝ) ≤ (z : ℝ) := by linarith [hx.1, u.property.2]
    exact_mod_cast hr
  · have hce := Int.le_ceil (b j)
    have hr : (z : ℝ) ≤ (⌈b j⌉ : ℝ) := by linarith [hx.2, u.property.1]
    exact_mod_cast hr

theorem poissonCloudIntervalCounts_real_law (a b : d → ℝ) (hab : ∀ j, a j ≤ b j)
    (hdisj : Pairwise (fun i j => Disjoint (Ioc (a i) (b i)) (Ioc (a j) (b j)))) :
    poissonCloudLaw.map
      (show Measurable (fun ω : PoissonCloud =>
        fun j => (poissonCloudIntervalCount (a j) (b j) ω : ℝ)) from by
          apply measurable_pi_lambda
          intro j
          exact (show Measurable (fun n : ℕ => (n : ℝ)) from by fun_prop).comp
            (measurable_poissonCloudIntervalCount (a j) (b j))).aemeasurable =
      poissonRealProduct (fun j => ⟨b j - a j, sub_nonneg.mpr (hab j)⟩) := by
  classical
  let A : d → Set ℝ := fun j => Ioc (a j) (b j)
  let s : Finset ℤ := poissonIntervalCells a b
  have hs : ∀ z ∉ s, ∀ u : I, ∀ j, (z : ℝ) + (u : ℝ) ∉ A j :=
    fun z hz u j => poissonIntervalCells_outside a b z hz u j
  have hA : ∀ j, MeasurableSet (A j) := fun j => measurableSet_Ioc
  have hsetM : Measurable (fun ω : PoissonCloud =>
      fun j => (poissonCloudSetCount s (A j) ω : ℝ)) := by
    apply measurable_pi_lambda
    intro j
    exact (show Measurable (fun n : ℕ => (n : ℝ)) from by fun_prop).comp
      (measurable_poissonCloudSetCount s (A j) (hA j))
  have hsource : poissonCloudLaw.map
      (show Measurable (fun ω : PoissonCloud =>
        fun j => (poissonCloudIntervalCount (a j) (b j) ω : ℝ)) from by
          apply measurable_pi_lambda
          intro j
          exact (show Measurable (fun n : ℕ => (n : ℝ)) from by fun_prop).comp
            (measurable_poissonCloudIntervalCount (a j) (b j))).aemeasurable =
        poissonCloudLaw.map hsetM.aemeasurable := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    congr 1
    funext ω j
    rw [← poissonCloudMeasure_real_Ioc_eq_nat_count (a j) (b j) ω,
      poissonCloudMeasure_real_apply_eq_nat_setCount (A j) s
        (fun z hz u => hs z hz u j) ω]
  rw [hsource]
  exact poissonCloudSetCounts_real_law A hA hdisj
    (fun j => by simp [A, Real.volume_Ioc]) s hs
    (fun j => ⟨b j - a j, sub_nonneg.mpr (hab j)⟩)
    (fun j => Real.volume_real_Ioc_of_le (hab j))

end FiniteDimension
end FixedCouplingPoisson
