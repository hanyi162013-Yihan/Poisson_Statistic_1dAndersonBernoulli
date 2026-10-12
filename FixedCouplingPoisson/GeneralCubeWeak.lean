import FixedCouplingPoisson.MixedMomentWeak

/-! Finite-support mixed moments identify actual laws on arbitrary compact unit products. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Filter
open scoped Topology

/-- The full product topology with its genuine Borel sigma algebra, including
uncountable index sets. This definition has a separate typeclass head so the
ordinary cylinder sigma algebra of a Pi type is not silently substituted. -/
def BorelMomentCube (d : Type*) := d → MomentInterval

instance (d : Type*) : TopologicalSpace (BorelMomentCube d) := Pi.topologicalSpace
instance (d : Type*) : CompactSpace (BorelMomentCube d) := by
  delta BorelMomentCube
  infer_instance
instance (d : Type*) : T2Space (BorelMomentCube d) := by
  delta BorelMomentCube
  infer_instance
instance (d : Type*) : MeasurableSpace (BorelMomentCube d) := borel (BorelMomentCube d)
instance (d : Type*) : BorelSpace (BorelMomentCube d) := ⟨rfl⟩

variable {d : Type*}

/-- Polynomial restrictions on the full Borel cube, with no finiteness
restriction on the index type. -/
def borelCubePolynomial (p : MvPolynomial d ℝ) : C(BorelMomentCube d, ℝ) where
  toFun x := MvPolynomial.eval (fun j => (x j : ℝ)) p
  continuous_toFun := p.continuous_eval.comp (continuous_pi fun j =>
    continuous_subtype_val.comp (continuous_apply j))

/-- The polynomial restriction algebra on the full cube. -/
def borelCubePolynomialAlgebra : Subalgebra ℝ C(BorelMomentCube d, ℝ) where
  carrier := Set.range borelCubePolynomial
  zero_mem' := ⟨0, by ext x; simp [borelCubePolynomial]⟩
  one_mem' := ⟨1, by ext x; simp [borelCubePolynomial]⟩
  add_mem' := by
    rintro f g ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p + q, by ext x; simp [borelCubePolynomial, MvPolynomial.eval_add]⟩
  mul_mem' := by
    rintro f g ⟨p, rfl⟩ ⟨q, rfl⟩
    exact ⟨p * q, by ext x; simp [borelCubePolynomial, MvPolynomial.eval_mul]⟩
  algebraMap_mem' a := ⟨MvPolynomial.C a, by ext x; simp [borelCubePolynomial]⟩

private theorem borelCubePolynomialAlgebra_separatesPoints :
    (borelCubePolynomialAlgebra (d := d)).SeparatesPoints := by
  classical
  intro x y hxy
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hxy
  refine ⟨fun z : BorelMomentCube d => (z j : ℝ), ?_, ?_⟩
  · exact ⟨borelCubePolynomial (MvPolynomial.X j), ⟨MvPolynomial.X j, rfl⟩,
      by ext z; simp [borelCubePolynomial]⟩
  · exact fun h => hj (Subtype.ext h)

/-- A true finite-support monomial on the possibly uncountable unit product. -/
def supportedMonomial (m : d →₀ ℕ) (x : BorelMomentCube d) : ℝ :=
  ∏ j ∈ m.support, (x j : ℝ) ^ m j

def supportedMoment (μ : ProbabilityMeasure (BorelMomentCube d)) (m : d →₀ ℕ) : ℝ :=
  ∫ x, supportedMonomial m x ∂(μ : Measure (BorelMomentCube d))

theorem continuous_supportedMonomial (m : d →₀ ℕ) : Continuous (supportedMonomial m) := by
  unfold supportedMonomial
  exact continuous_finsetProd _ fun j _ =>
    (continuous_subtype_val.comp (continuous_apply j)).pow (m j)

private theorem integrable_arbitrary_cube_continuousMap
    (μ : ProbabilityMeasure (BorelMomentCube d)) (f : C(BorelMomentCube d, ℝ)) :
    Integrable f (μ : Measure (BorelMomentCube d)) :=
  (BoundedContinuousFunction.mkOfCompact f).integrable (μ : Measure (BorelMomentCube d))

private theorem integrable_supportedMonomial
    (μ : ProbabilityMeasure (BorelMomentCube d)) (m : d →₀ ℕ) :
    Integrable (supportedMonomial m) (μ : Measure (BorelMomentCube d)) :=
  integrable_arbitrary_cube_continuousMap μ ⟨_, continuous_supportedMonomial m⟩

theorem integral_cubePolynomial_eq_supported_sum
    (μ : ProbabilityMeasure (BorelMomentCube d)) (p : MvPolynomial d ℝ) :
    (∫ x, borelCubePolynomial p x ∂(μ : Measure (BorelMomentCube d))) =
      ∑ m ∈ p.support, p.coeff m * supportedMoment μ m := by
  classical
  change (∫ x : BorelMomentCube d, MvPolynomial.eval (fun j => (x j : ℝ)) p
    ∂(μ : Measure (BorelMomentCube d))) = _
  simp_rw [MvPolynomial.eval_eq]
  rw [integral_finsetSum]
  · simp only [integral_const_mul, supportedMoment, supportedMonomial]
  · intro m hm
    exact (integrable_supportedMonomial μ m).const_mul _

/-- Mixed moment limits give limits against every actual multivariate polynomial. -/
theorem integral_cubePolynomial_tendsto_of_supportedMoments {ι : Type*} {F : Filter ι}
    (μs : ι → ProbabilityMeasure (BorelMomentCube d)) (μ : ProbabilityMeasure (BorelMomentCube d))
    (hmom : ∀ m : d →₀ ℕ, Tendsto (fun i => supportedMoment (μs i) m) F
      (𝓝 (supportedMoment μ m))) (p : MvPolynomial d ℝ) :
    Tendsto (fun i => ∫ x, borelCubePolynomial p x ∂(μs i : Measure (BorelMomentCube d)))
      F (𝓝 (∫ x, borelCubePolynomial p x ∂(μ : Measure (BorelMomentCube d)))) := by
  classical
  simp_rw [integral_cubePolynomial_eq_supported_sum]
  exact tendsto_finsetSum p.support fun m _ => (hmom m).const_mul _

/-- Stone-Weierstrass approximation transfers actual mixed moment limits to
all continuous tests on the arbitrary compact cube. -/
theorem integral_cubeContinuousMap_tendsto_of_supportedMoments {ι : Type*} {F : Filter ι}
    (μs : ι → ProbabilityMeasure (BorelMomentCube d)) (μ : ProbabilityMeasure (BorelMomentCube d))
    (hmom : ∀ m : d →₀ ℕ, Tendsto (fun i => supportedMoment (μs i) m) F
      (𝓝 (supportedMoment μ m))) (f : C(BorelMomentCube d, ℝ)) :
    Tendsto (fun i => ∫ x, f x ∂(μs i : Measure (BorelMomentCube d)))
      F (𝓝 (∫ x, f x ∂(μ : Measure (BorelMomentCube d)))) := by
  classical
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  obtain ⟨g, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
      (borelCubePolynomialAlgebra (d := d)) borelCubePolynomialAlgebra_separatesPoints
      f (ε / 4) (by positivity)
  obtain ⟨p, hp⟩ := g.property
  have happrox : ‖borelCubePolynomial p - f‖ < ε / 4 := by
    rw [hp]
    exact hg
  have happ (ν : ProbabilityMeasure (BorelMomentCube d)) :
      |(∫ x, borelCubePolynomial p x ∂(ν : Measure (BorelMomentCube d))) -
        (∫ x, f x ∂(ν : Measure (BorelMomentCube d)))| ≤ ε / 4 := by
    rw [← integral_sub (integrable_arbitrary_cube_continuousMap ν (borelCubePolynomial p))
      (integrable_arbitrary_cube_continuousMap ν f), ← Real.norm_eq_abs]
    have hbound : ∀ᵐ (x : BorelMomentCube d) ∂(ν : Measure (BorelMomentCube d)),
        ‖borelCubePolynomial p x - f x‖ ≤ ε / 4 := ae_of_all _ fun x =>
      ((borelCubePolynomial p - f).norm_coe_le_norm x).trans happrox.le
    simpa using norm_integral_le_of_norm_le_const hbound
  have hpoly := integral_cubePolynomial_tendsto_of_supportedMoments μs μ hmom p
  have hevent := Metric.tendsto_nhds.mp hpoly (ε / 4) (by positivity)
  filter_upwards [hevent] with i hi
  rw [Real.dist_eq] at hi ⊢
  have ha := happ (μs i)
  have hb := happ μ
  have ht1 := abs_sub_le
    (∫ x, f x ∂(μs i : Measure (BorelMomentCube d)))
    (∫ x, borelCubePolynomial p x ∂(μs i : Measure (BorelMomentCube d)))
    (∫ x, f x ∂(μ : Measure (BorelMomentCube d)))
  have ht2 := abs_sub_le
    (∫ x, borelCubePolynomial p x ∂(μs i : Measure (BorelMomentCube d)))
    (∫ x, borelCubePolynomial p x ∂(μ : Measure (BorelMomentCube d)))
    (∫ x, f x ∂(μ : Measure (BorelMomentCube d)))
  rw [abs_sub_comm (∫ x, f x ∂(μs i : Measure (BorelMomentCube d)))
    (∫ x, borelCubePolynomial p x ∂(μs i : Measure (BorelMomentCube d)))] at ht1
  linarith

/-- Actual arbitrary-cube probability laws converge weakly whenever all mixed
integer moments converge to those of the given target law. -/
theorem probabilityMeasure_tendsto_of_supportedMoments {ι : Type*} {F : Filter ι}
    (μs : ι → ProbabilityMeasure (BorelMomentCube d)) (μ : ProbabilityMeasure (BorelMomentCube d))
    (hmom : ∀ m : d →₀ ℕ, Tendsto (fun i => supportedMoment (μs i) m) F
      (𝓝 (supportedMoment μ m))) : Tendsto μs F (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  exact integral_cubeContinuousMap_tendsto_of_supportedMoments μs μ hmom f.toContinuousMap


end FixedCouplingPoisson
