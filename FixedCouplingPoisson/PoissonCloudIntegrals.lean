import FixedCouplingPoisson.PoissonCloudMeasure
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.ContinuousOn

/-! Compactly supported integrals of the actual locally finite cloud depend on
finitely many cells, and are continuous in the concrete sample coordinates. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter CompactlySupported
open scoped NNReal unitInterval Topology

theorem integral_poissonCellMeasure (z : ℤ) (p : ℕ × (ℕ → I)) (f : ℝ → ℝ) :
    (∫ x, f x ∂poissonCellMeasure z p) =
      ∑ j ∈ Finset.range p.1, f ((z : ℝ) + (p.2 j : ℝ)) := by
  classical
  unfold poissonCellMeasure
  rw [integral_finsetSum_measure (fun j hj => integrable_dirac (by simp))]
  simp only [integral_dirac]

theorem exists_poissonCloud_activeCells (f : C_c(ℝ, ℝ)) :
    ∃ s : Finset ℤ, ∀ z ∉ s, ∀ u : I, f ((z : ℝ) + (u : ℝ)) = 0 := by
  classical
  obtain ⟨a, ha⟩ := f.hasCompactSupport.bddBelow
  obtain ⟨b, hb⟩ := f.hasCompactSupport.bddAbove
  refine ⟨Finset.Icc ⌊a - 1⌋ ⌈b⌉, ?_⟩
  intro z hz u
  by_contra hn
  have hs : (z : ℝ) + (u : ℝ) ∈ tsupport f :=
    subset_tsupport f (Function.mem_support.mpr hn)
  have hlo := ha hs
  have hhi := hb hs
  apply hz
  apply Finset.mem_Icc.mpr
  constructor
  · have hfl := Int.floor_le (a - 1)
    have hr : (⌊a - 1⌋ : ℝ) ≤ (z : ℝ) := by linarith [u.property.2]
    exact_mod_cast hr
  · have hce := Int.le_ceil b
    have hr : (z : ℝ) ≤ (⌈b⌉ : ℝ) := by linarith [u.property.1]
    exact_mod_cast hr

theorem integral_poissonCloudMeasure_finite (f : C_c(ℝ, ℝ)) (s : Finset ℤ)
    (hs : ∀ z ∉ s, ∀ u : I, f ((z : ℝ) + (u : ℝ)) = 0) (ω : PoissonCloud) :
    (∫ x, f x ∂poissonCloudMeasure ω) =
      ∑ z ∈ s, ∑ j ∈ Finset.range (ω z).1, f ((z : ℝ) + ((ω z).2 j : ℝ)) := by
  classical
  letI := poissonCloudMeasure_isLocallyFiniteMeasure ω
  have hf : Integrable f (poissonCloudMeasure ω) := f.integrable
  rw [poissonCloudMeasure, integral_sum_measure hf]
  rw [tsum_eq_sum (s := s) (fun z hz => by
    rw [integral_poissonCellMeasure]
    exact Finset.sum_eq_zero (fun j hj => hs z hz ((ω z).2 j)))]
  simp_rw [integral_poissonCellMeasure]

theorem continuous_integral_poissonCellMeasure (f : C_c(ℝ, ℝ)) (z : ℤ) :
    Continuous (fun p : ℕ × (ℕ → I) => ∫ x, f x ∂poissonCellMeasure z p) := by
  simp_rw [integral_poissonCellMeasure]
  apply continuous_prod_of_discrete_left.mpr
  intro n
  change Continuous (fun u : ℕ → I =>
    ∑ j ∈ Finset.range n, f ((z : ℝ) + (u j : ℝ)))
  fun_prop

theorem continuous_integral_poissonCloudMeasure (f : C_c(ℝ, ℝ)) :
    Continuous (fun ω : PoissonCloud => ∫ x, f x ∂poissonCloudMeasure ω) := by
  obtain ⟨s, hs⟩ := exists_poissonCloud_activeCells f
  simp_rw [integral_poissonCloudMeasure_finite f s hs]
  have hcell : ∀ z : ℤ, Continuous (fun ω : PoissonCloud =>
      ∑ j ∈ Finset.range (ω z).1, f ((z : ℝ) + ((ω z).2 j : ℝ))) := by
    intro z
    have h := (continuous_integral_poissonCellMeasure f z).comp
      (show Continuous (fun ω : PoissonCloud => ω z) from continuous_apply z)
    simpa only [integral_poissonCellMeasure, Function.comp_def] using h
  exact continuous_finsetSum s (fun z hz => hcell z)

end FixedCouplingPoisson
