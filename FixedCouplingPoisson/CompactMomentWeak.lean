import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Integer moments determine weak convergence on the actual compact interval
`[0,1]`. Polynomial approximation is proved by Mathlib's Weierstrass theorem;
no uniqueness or distributional conclusion is assumed. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Filter
open scoped Topology Polynomial

abbrev MomentInterval := Set.Icc (0 : ℝ) 1

/-- The actual integer moment of a probability measure on `[0,1]`. -/
def compactMoment (μ : ProbabilityMeasure MomentInterval) (m : ℕ) : ℝ :=
  ∫ x, (x : ℝ) ^ m ∂(μ : Measure MomentInterval)

private theorem integrable_interval_continuousMap
    (μ : ProbabilityMeasure MomentInterval) (f : C(MomentInterval, ℝ)) :
    Integrable f (μ : Measure MomentInterval) :=
  (BoundedContinuousFunction.mkOfCompact f).integrable (μ : Measure MomentInterval)

private theorem integrable_interval_polynomial
    (μ : ProbabilityMeasure MomentInterval) (p : ℝ[X]) :
    Integrable (fun x : MomentInterval => p.eval (x : ℝ)) (μ : Measure MomentInterval) :=
  integrable_interval_continuousMap μ (p.toContinuousMapOn MomentInterval)

/-- Moment convergence gives convergence against every actual polynomial. -/
theorem integral_polynomial_tendsto_of_moments {ι : Type*} {F : Filter ι}
    (μs : ι → ProbabilityMeasure MomentInterval) (μ : ProbabilityMeasure MomentInterval)
    (hmom : ∀ m : ℕ, Tendsto (fun i => compactMoment (μs i) m) F
      (𝓝 (compactMoment μ m))) (p : ℝ[X]) :
    Tendsto (fun i => ∫ x : MomentInterval, p.eval (x : ℝ) ∂(μs i : Measure MomentInterval))
      F (𝓝 (∫ x : MomentInterval, p.eval (x : ℝ) ∂(μ : Measure MomentInterval))) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add, integral_add (integrable_interval_polynomial _ _)
        (integrable_interval_polynomial _ _)] using hp.add hq
  | monomial m a =>
      simpa only [Polynomial.eval_monomial, integral_const_mul, compactMoment] using
        (hmom m).const_mul a

/-- Uniform approximation transfers the polynomial limits to continuous tests. -/
theorem integral_continuousMap_tendsto_of_moments {ι : Type*} {F : Filter ι}
    (μs : ι → ProbabilityMeasure MomentInterval) (μ : ProbabilityMeasure MomentInterval)
    (hmom : ∀ m : ℕ, Tendsto (fun i => compactMoment (μs i) m) F
      (𝓝 (compactMoment μ m))) (f : C(MomentInterval, ℝ)) :
    Tendsto (fun i => ∫ x, f x ∂(μs i : Measure MomentInterval))
      F (𝓝 (∫ x, f x ∂(μ : Measure MomentInterval))) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨p, hp⟩ := exists_polynomial_near_continuousMap 0 1 f (ε / 4) (by positivity)
  have happ (ν : ProbabilityMeasure MomentInterval) :
      |(∫ x : MomentInterval, p.eval (x : ℝ) ∂(ν : Measure MomentInterval)) -
        (∫ x, f x ∂(ν : Measure MomentInterval))| ≤ ε / 4 := by
    rw [← integral_sub (integrable_interval_polynomial ν p)
      (integrable_interval_continuousMap ν f), ← Real.norm_eq_abs]
    have hbound : ∀ᵐ (x : MomentInterval) ∂(ν : Measure MomentInterval),
        ‖p.eval (x : ℝ) - f x‖ ≤ ε / 4 := ae_of_all _ fun x => by
      have hx := (p.toContinuousMapOn MomentInterval - f).norm_coe_le_norm x
      exact hx.trans hp.le
    simpa using norm_integral_le_of_norm_le_const hbound
  have hpoly := integral_polynomial_tendsto_of_moments μs μ hmom p
  have hevent := Metric.tendsto_nhds.mp hpoly (ε / 4) (by positivity)
  filter_upwards [hevent] with i hi
  rw [Real.dist_eq] at hi ⊢
  have ha := happ (μs i)
  have hb := happ μ
  have ht1 := abs_sub_le
    (∫ x, f x ∂(μs i : Measure MomentInterval))
    (∫ x : MomentInterval, p.eval (x : ℝ) ∂(μs i : Measure MomentInterval))
    (∫ x, f x ∂(μ : Measure MomentInterval))
  have ht2 := abs_sub_le
    (∫ x : MomentInterval, p.eval (x : ℝ) ∂(μs i : Measure MomentInterval))
    (∫ x : MomentInterval, p.eval (x : ℝ) ∂(μ : Measure MomentInterval))
    (∫ x, f x ∂(μ : Measure MomentInterval))
  rw [abs_sub_comm (∫ x, f x ∂(μs i : Measure MomentInterval))
    (∫ x : MomentInterval, p.eval (x : ℝ) ∂(μs i : Measure MomentInterval))] at ht1
  linarith

/-- For probability measures on `[0,1]`, convergence of all integer moments
implies genuine weak convergence. The target measure is arbitrary. -/
theorem probabilityMeasure_tendsto_of_compactMoments {ι : Type*} {F : Filter ι}
    (μs : ι → ProbabilityMeasure MomentInterval) (μ : ProbabilityMeasure MomentInterval)
    (hmom : ∀ m : ℕ, Tendsto (fun i => compactMoment (μs i) m) F
      (𝓝 (compactMoment μ m))) :
    Tendsto μs F (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  exact integral_continuousMap_tendsto_of_moments μs μ hmom f.toContinuousMap

end FixedCouplingPoisson
