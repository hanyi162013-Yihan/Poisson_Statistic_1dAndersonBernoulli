import FixedCouplingPoisson.CompactMomentWeak
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.MvPolynomial

/-! Actual mixed integer moments determine weak convergence on any finite
unit cube. The multivariate polynomial algebra and its point-separation are
constructed here; the target probability measure is arbitrary. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Filter
open scoped Topology

abbrev MomentCube (d : Type*) := d → MomentInterval

section FiniteCube
variable {d : Type*} [Fintype d]

/-- Actual mixed monomials on a finite unit cube. -/
def mixedMonomial (m : d → ℕ) (x : MomentCube d) : ℝ :=
  ∏ j, (x j : ℝ) ^ m j

/-- The actual mixed moment of a probability measure on the finite cube. -/
def mixedMoment (μ : ProbabilityMeasure (MomentCube d)) (m : d → ℕ) : ℝ :=
  ∫ x, mixedMonomial m x ∂(μ : Measure (MomentCube d))

theorem continuous_mixedMonomial (m : d → ℕ) : Continuous (mixedMonomial m) := by
  unfold mixedMonomial
  exact continuous_finset_prod _ fun j _ =>
    (continuous_subtype_val.comp (continuous_apply j)).pow (m j)

/-- Evaluation of an actual multivariate polynomial on the cube. -/
def cubePolynomial (p : MvPolynomial d ℝ) : C(MomentCube d, ℝ) where
  toFun x := MvPolynomial.eval (fun j => (x j : ℝ)) p
  continuous_toFun := p.continuous_eval.comp (continuous_pi fun j =>
    continuous_subtype_val.comp (continuous_apply j))

/-- The actual algebra of polynomial restrictions to the cube. -/
def cubePolynomialAlgebra : Subalgebra ℝ C(MomentCube d, ℝ) where
  carrier := Set.range cubePolynomial
  zero_mem' := ⟨0, by ext x; simp [cubePolynomial]⟩
  one_mem' := ⟨1, by ext x; simp [cubePolynomial]⟩
  add_mem' := by
    rintro f g ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p + q, by ext x; simp [cubePolynomial, MvPolynomial.eval_add]⟩
  mul_mem' := by
    rintro f g ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p * q, by ext x; simp [cubePolynomial, MvPolynomial.eval_mul]⟩
  algebraMap_mem' a := ⟨MvPolynomial.C a, by ext x; simp [cubePolynomial]⟩

theorem cubePolynomialAlgebra_separatesPoints :
    (cubePolynomialAlgebra (d := d)).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
  refine ⟨fun z : MomentCube d => (z j : ℝ), ?_, ?_⟩
  · exact ⟨cubePolynomial (MvPolynomial.X j), ⟨MvPolynomial.X j, rfl⟩,
      by ext z; simp [cubePolynomial]⟩
  · exact fun h => hj (Subtype.ext h)

private theorem integrable_cube_continuousMap
    (μ : ProbabilityMeasure (MomentCube d)) (f : C(MomentCube d, ℝ)) :
    Integrable f (μ : Measure (MomentCube d)) :=
  (BoundedContinuousFunction.mkOfCompact f).integrable (μ : Measure (MomentCube d))

private theorem integrable_mixedMonomial
    (μ : ProbabilityMeasure (MomentCube d)) (m : d → ℕ) :
    Integrable (mixedMonomial m) (μ : Measure (MomentCube d)) :=
  integrable_cube_continuousMap μ ⟨_, continuous_mixedMonomial m⟩

theorem integral_cubePolynomial_eq_sum
    (μ : ProbabilityMeasure (MomentCube d)) (p : MvPolynomial d ℝ) :
    (∫ x, cubePolynomial p x ∂(μ : Measure (MomentCube d))) =
      ∑ m ∈ p.support, p.coeff m * mixedMoment μ (fun j => m j) := by
  classical
  change (∫ x : MomentCube d, MvPolynomial.eval (fun j => (x j : ℝ)) p
    ∂(μ : Measure (MomentCube d))) = _
  simp_rw [MvPolynomial.eval_eq']
  rw [integral_finset_sum]
  · simp only [integral_const_mul, mixedMoment, mixedMonomial]
  · intro m hm
    exact (integrable_mixedMonomial μ (fun j => m j)).const_mul _

/-- Mixed moment limits give limits against every actual multivariate polynomial. -/
theorem integral_cubePolynomial_tendsto_of_mixedMoments {ι : Type*} {F : Filter ι}
    (μs : ι → ProbabilityMeasure (MomentCube d)) (μ : ProbabilityMeasure (MomentCube d))
    (hmom : ∀ m : d → ℕ, Tendsto (fun i => mixedMoment (μs i) m) F
      (𝓝 (mixedMoment μ m))) (p : MvPolynomial d ℝ) :
    Tendsto (fun i => ∫ x, cubePolynomial p x ∂(μs i : Measure (MomentCube d)))
      F (𝓝 (∫ x, cubePolynomial p x ∂(μ : Measure (MomentCube d)))) := by
  classical
  simp_rw [integral_cubePolynomial_eq_sum]
  exact tendsto_finsetSum p.support fun m _ => (hmom (fun j => m j)).const_mul _

/-- Stone-Weierstrass approximation transfers actual mixed moment limits to
all continuous tests on the finite cube. -/
theorem integral_cubeContinuousMap_tendsto_of_mixedMoments {ι : Type*} {F : Filter ι}
    (μs : ι → ProbabilityMeasure (MomentCube d)) (μ : ProbabilityMeasure (MomentCube d))
    (hmom : ∀ m : d → ℕ, Tendsto (fun i => mixedMoment (μs i) m) F
      (𝓝 (mixedMoment μ m))) (f : C(MomentCube d, ℝ)) :
    Tendsto (fun i => ∫ x, f x ∂(μs i : Measure (MomentCube d)))
      F (𝓝 (∫ x, f x ∂(μ : Measure (MomentCube d)))) := by
  classical
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨g, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      (cubePolynomialAlgebra (d := d)) cubePolynomialAlgebra_separatesPoints
      f (ε / 4) (by positivity)
  obtain ⟨p, hp⟩ := g.property
  have happrox : ‖cubePolynomial p - f‖ < ε / 4 := by
    rw [hp]
    exact hg
  have happ (ν : ProbabilityMeasure (MomentCube d)) :
      |(∫ x, cubePolynomial p x ∂(ν : Measure (MomentCube d))) -
        (∫ x, f x ∂(ν : Measure (MomentCube d)))| ≤ ε / 4 := by
    rw [← integral_sub (integrable_cube_continuousMap ν (cubePolynomial p))
      (integrable_cube_continuousMap ν f), ← Real.norm_eq_abs]
    have hbound : ∀ᵐ (x : MomentCube d) ∂(ν : Measure (MomentCube d)),
        ‖cubePolynomial p x - f x‖ ≤ ε / 4 := ae_of_all _ fun x =>
      ((cubePolynomial p - f).norm_coe_le_norm x).trans happrox.le
    simpa using norm_integral_le_of_norm_le_const hbound
  have hpoly := integral_cubePolynomial_tendsto_of_mixedMoments μs μ hmom p
  have hevent := Metric.tendsto_nhds.mp hpoly (ε / 4) (by positivity)
  filter_upwards [hevent] with i hi
  rw [Real.dist_eq] at hi ⊢
  have ha := happ (μs i)
  have hb := happ μ
  have ht1 := abs_sub_le
    (∫ x, f x ∂(μs i : Measure (MomentCube d)))
    (∫ x, cubePolynomial p x ∂(μs i : Measure (MomentCube d)))
    (∫ x, f x ∂(μ : Measure (MomentCube d)))
  have ht2 := abs_sub_le
    (∫ x, cubePolynomial p x ∂(μs i : Measure (MomentCube d)))
    (∫ x, cubePolynomial p x ∂(μ : Measure (MomentCube d)))
    (∫ x, f x ∂(μ : Measure (MomentCube d)))
  rw [abs_sub_comm (∫ x, f x ∂(μs i : Measure (MomentCube d)))
    (∫ x, cubePolynomial p x ∂(μs i : Measure (MomentCube d)))] at ht1
  linarith

/-- Actual finite-cube probability laws converge weakly whenever all mixed
integer moments converge to those of the given target law. -/
theorem probabilityMeasure_tendsto_of_mixedMoments {ι : Type*} {F : Filter ι}
    (μs : ι → ProbabilityMeasure (MomentCube d)) (μ : ProbabilityMeasure (MomentCube d))
    (hmom : ∀ m : d → ℕ, Tendsto (fun i => mixedMoment (μs i) m) F
      (𝓝 (mixedMoment μ m))) : Tendsto μs F (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  exact integral_cubeContinuousMap_tendsto_of_mixedMoments μs μ hmom f.toContinuousMap

end FiniteCube
end FixedCouplingPoisson
