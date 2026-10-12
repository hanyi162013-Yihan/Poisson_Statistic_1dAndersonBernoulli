import FixedCouplingPoisson.PoissonGeneratingFunction
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod

/-! An actual Poisson number of independent uniform marks in one unit cell.
The law and the finite-mark generating identity are concrete constructions. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set
open scoped NNReal unitInterval

def uniformMarksLaw : ProbabilityMeasure (ℕ → I) :=
  ⟨Measure.infinitePi (fun _ : ℕ => (volume : Measure I)), inferInstance⟩

def poissonUnitCellLaw (a : ℝ≥0) : ProbabilityMeasure (ℕ × (ℕ → I)) :=
  ⟨(poissonMeasure a).prod (uniformMarksLaw : Measure (ℕ → I)), inferInstance⟩

def poissonUnitCellFunctional (g : I → ℝ) (p : ℕ × (ℕ → I)) : ℝ :=
  ∏ j ∈ Finset.range p.1, g (p.2 j)

theorem integral_uniformMarksLaw_prod (s : Finset ℕ) (g : I → ℝ)
    (hg : Measurable g) :
    (∫ ω, ∏ j ∈ s, g (ω j) ∂(uniformMarksLaw : Measure (ℕ → I))) =
      (∫ u : I, g u) ^ s.card := by
  classical
  have hm : Measurable (fun u : s → I => ∏ j, g (u j)) := by fun_prop
  calc
    (∫ ω, ∏ j ∈ s, g (ω j) ∂(uniformMarksLaw : Measure (ℕ → I))) =
        ∫ ω, ∏ j : s, g (ω j) ∂Measure.infinitePi (fun _ : ℕ => (volume : Measure I)) := by
      change (∫ ω : ℕ → I, ∏ j ∈ s, g (ω j)
        ∂Measure.infinitePi (fun _ : ℕ => (volume : Measure I))) = _
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => (Finset.prod_coe_sort s (fun j => g (ω j))).symm)
    _ = ∫ u : s → I, ∏ j, g (u j) ∂Measure.pi (fun _ : s => (volume : Measure I)) := by
      simpa only [Finset.restrict, Function.comp_def] using
        (integral_restrict_infinitePi (μ := fun _ : ℕ => (volume : Measure I))
          (s := s) hm.aestronglyMeasurable)
    _ = (∫ u : I, g u) ^ s.card := by
      rw [integral_fintype_prod_eq_prod (μ := fun _ : s => (volume : Measure I))
        (fun _ (u : I) => g u)]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_coe]

theorem measurable_poissonUnitCellFunctional (g : I → ℝ) (hg : Measurable g) :
    Measurable (poissonUnitCellFunctional g) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun ω : ℕ → I => ∏ j ∈ Finset.range n, g (ω j))
  fun_prop

theorem integrable_poissonUnitCellFunctional (a : ℝ≥0) (g : I → ℝ)
    (hg : Measurable g) (hg0 : ∀ u, 0 ≤ g u) (hg1 : ∀ u, g u ≤ 1) :
    Integrable (poissonUnitCellFunctional g)
      (poissonUnitCellLaw a : Measure (ℕ × (ℕ → I))) := by
  apply Integrable.of_bound (measurable_poissonUnitCellFunctional g hg).aestronglyMeasurable 1
  exact ae_of_all _ fun p => by
    change ‖∏ j ∈ Finset.range p.1, g (p.2 j)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun j _ => hg0 (p.2 j)))]
    exact Finset.prod_le_one (fun j _ => hg0 (p.2 j)) (fun j _ => hg1 (p.2 j))

/-- The conditional finite product of uniform marks, mixed with the actual
Poisson count, has the expected Poisson generating function. -/
theorem integral_poissonUnitCellFunctional (a : ℝ≥0) (g : I → ℝ)
    (hg : Measurable g) (hg0 : ∀ u, 0 ≤ g u) (hg1 : ∀ u, g u ≤ 1) :
    (∫ p, poissonUnitCellFunctional g p
      ∂(poissonUnitCellLaw a : Measure (ℕ × (ℕ → I)))) =
        Real.exp ((a : ℝ) * ((∫ u : I, g u) - 1)) := by
  change (∫ p, poissonUnitCellFunctional g p
    ∂(poissonMeasure a).prod (uniformMarksLaw : Measure (ℕ → I))) = _
  rw [integral_prod _ (integrable_poissonUnitCellFunctional a g hg hg0 hg1)]
  simp_rw [poissonUnitCellFunctional, integral_uniformMarksLaw_prod _ g hg, Finset.card_range]
  exact integral_poissonGeneratingFunction a (∫ u : I, g u)

end FixedCouplingPoisson
