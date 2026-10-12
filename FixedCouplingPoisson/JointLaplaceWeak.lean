import FixedCouplingPoisson.MixedMomentWeak
import FixedCouplingPoisson.LaplaceWeak

/-! Genuine joint-law identification from mixed integer Laplace transforms.
The exponential coordinate map is an open embedding of the nonnegative
orthant into the finite unit cube. Weak convergence is pulled back using
open-set Portmanteau inequalities, so no continuity of log at zero and no
nonatomicity assumption on the target law is needed. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

/-- Weak convergence can be recovered through an actual open embedding. -/
theorem probabilityMeasure_tendsto_of_openEmbedding
    {A B ι : Type*} [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A]
    [MeasurableSpace B] [TopologicalSpace B] [BorelSpace B] [HasOuterApproxClosed B]
    {F : Filter ι} [F.IsCountablyGenerated] (f : A → B) (hf : Topology.IsOpenEmbedding f)
    (μs : ι → ProbabilityMeasure A) (μ : ProbabilityMeasure A)
    (hmap : Tendsto (fun i => (μs i).map hf.continuous.measurable.aemeasurable) F
      (𝓝 (μ.map hf.continuous.measurable.aemeasurable))) : Tendsto μs F (𝓝 μ) := by
  apply tendsto_of_forall_isOpen_le_liminf'
  intro U hU
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hmap
    (hf.isOpenMap U hU)
  have hident (ν : ProbabilityMeasure A) :
      (ν.map hf.continuous.measurable.aemeasurable : Measure B) (f '' U) =
        (ν : Measure A) U := by
    rw [ProbabilityMeasure.map_apply' _ _ (hf.isOpenMap U hU).measurableSet,
      Set.preimage_image_eq U hf.injective]
  simpa only [hident] using hlim

abbrev PositiveMomentInterval := {y : MomentInterval // 0 < (y : ℝ)}

/-- The genuine exponential coordinate on the nonnegative half-line. -/
def nnNegativeExp (x : ℝ≥0) : MomentInterval :=
  ⟨Real.exp (-(x : ℝ)), Real.exp_nonneg _,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr x.property)⟩

theorem continuous_nnNegativeExp : Continuous nnNegativeExp :=
  (continuous_subtype_val.neg.rexp).subtype_mk (fun x =>
    ⟨Real.exp_nonneg _, Real.exp_le_one_iff.mpr (neg_nonpos.mpr x.property)⟩)

/-- Log is used only on the strictly positive part of the compact interval. -/
def nnNegativeExpHomeomorph : ℝ≥0 ≃ₜ PositiveMomentInterval where
  toFun x := ⟨nnNegativeExp x, Real.exp_pos _⟩
  invFun y := ⟨-Real.log (y.val : ℝ),
    neg_nonneg.mpr (Real.log_nonpos y.val.property.1 y.val.property.2)⟩
  left_inv x := by
    apply Subtype.ext
    change -Real.log (Real.exp (-(x : ℝ))) = (x : ℝ)
    rw [Real.log_exp, neg_neg]
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    change Real.exp (-(-Real.log (y.val : ℝ))) = (y.val : ℝ)
    rw [neg_neg, Real.exp_log y.property]
  continuous_toFun := continuous_nnNegativeExp.subtype_mk (fun x => Real.exp_pos _)
  continuous_invFun := by
    have hpos : Continuous (fun y : PositiveMomentInterval =>
        (⟨(y.val : ℝ), y.property⟩ : Set.Ioi (0 : ℝ))) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk (fun y => y.property)
    exact (Real.continuous_log'.comp hpos).neg.subtype_mk (fun y =>
      neg_nonneg.mpr (Real.log_nonpos y.val.property.1 y.val.property.2))

theorem isOpenEmbedding_nnNegativeExp : Topology.IsOpenEmbedding nnNegativeExp := by
  have hpos : IsOpen {y : MomentInterval | 0 < (y : ℝ)} :=
    isOpen_lt continuous_const continuous_subtype_val
  exact hpos.isOpenEmbedding_subtypeVal.comp nnNegativeExpHomeomorph.isOpenEmbedding

section FiniteDimension
variable {d : Type*} [Fintype d]

/-- The actual finite coordinate exponential map. -/
def cubeNegativeExp (x : d → ℝ≥0) : MomentCube d := fun j => nnNegativeExp (x j)

theorem isOpenEmbedding_cubeNegativeExp : Topology.IsOpenEmbedding (cubeNegativeExp (d := d)) := by
  exact Topology.IsOpenEmbedding.piMap (fun _ : d => isOpenEmbedding_nnNegativeExp)

/-- The mixed integer Laplace test on actual nonnegative vectors. -/
def mixedLaplaceTest (m : d → ℕ) (x : d → ℝ≥0) : ℝ :=
  Real.exp (-(∑ j, (m j : ℝ) * (x j : ℝ)))

theorem continuous_mixedLaplaceTest (m : d → ℕ) : Continuous (mixedLaplaceTest m) := by
  unfold mixedLaplaceTest
  exact (continuous_finset_sum _ fun j _ =>
    (continuous_subtype_val.comp (continuous_apply j)).const_mul (m j : ℝ)).neg.rexp

/-- The actual mixed integer Laplace transform of a given probability law. -/
def mixedLaplace (μ : ProbabilityMeasure (d → ℝ≥0)) (m : d → ℕ) : ℝ :=
  ∫ x, mixedLaplaceTest m x ∂(μ : Measure (d → ℝ≥0))

theorem mixedMonomial_cubeNegativeExp (m : d → ℕ) (x : d → ℝ≥0) :
    mixedMonomial m (cubeNegativeExp x) = mixedLaplaceTest m x := by
  classical
  change (∏ j, Real.exp (-(x j : ℝ)) ^ m j) = Real.exp (-(∑ j, (m j : ℝ) * (x j : ℝ)))
  calc
    _ = ∏ j, Real.exp (-((m j : ℝ) * (x j : ℝ))) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ = _ := by
      simpa only [Finset.sum_neg_distrib] using
        (Real.exp_sum Finset.univ (fun j => -((m j : ℝ) * (x j : ℝ)))).symm

theorem mixedMoment_cubeNegativeExp_map
    (μ : ProbabilityMeasure (d → ℝ≥0)) (m : d → ℕ) :
    mixedMoment (μ.map isOpenEmbedding_cubeNegativeExp.continuous.measurable.aemeasurable) m =
      mixedLaplace μ m := by
  rw [mixedMoment, ProbabilityMeasure.toMeasure_map,
    integral_map (μ := (μ : Measure (d → ℝ≥0)))
      isOpenEmbedding_cubeNegativeExp.continuous.measurable.aemeasurable
      (continuous_mixedMonomial m).measurable.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ fun x => mixedMonomial_cubeNegativeExp m x)

/-- Given an arbitrary actual target law on the nonnegative orthant, its
mixed integer Laplace transforms determine genuine joint weak convergence. -/
theorem probabilityMeasure_tendsto_of_mixedIntegerLaplace {ι : Type*} {F : Filter ι}
    [F.IsCountablyGenerated] (μs : ι → ProbabilityMeasure (d → ℝ≥0))
    (μ : ProbabilityMeasure (d → ℝ≥0))
    (hlaplace : ∀ m : d → ℕ, Tendsto (fun i => mixedLaplace (μs i) m) F
      (𝓝 (mixedLaplace μ m))) : Tendsto μs F (𝓝 μ) := by
  apply probabilityMeasure_tendsto_of_openEmbedding cubeNegativeExp
    isOpenEmbedding_cubeNegativeExp μs μ
  apply probabilityMeasure_tendsto_of_mixedMoments
  intro m
  simpa only [mixedMoment_cubeNegativeExp_map] using hlaplace m

theorem mixedLaplace_map {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → d → ℝ≥0) (hX : Measurable X) (m : d → ℕ) :
    mixedLaplace (P.map hX.aemeasurable) m =
      ∫ ω, mixedLaplaceTest m (X ω) ∂(P : Measure Ω) := by
  rw [mixedLaplace, ProbabilityMeasure.toMeasure_map,
    integral_map hX.aemeasurable (continuous_mixedLaplaceTest m).measurable.aestronglyMeasurable]

/-- Actual nonnegative-vector random variables inherit the generic joint
identification theorem for their genuine push-forward laws. -/
theorem nnreal_laws_tendsto_of_mixed_integer_laplace
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    (P : ProbabilityMeasure Ω) (Xs : ι → Ω → d → ℝ≥0) (hX : ∀ i, Measurable (Xs i))
    (ν : ProbabilityMeasure (d → ℝ≥0))
    (hlaplace : ∀ m : d → ℕ, Tendsto
      (fun i => ∫ ω, mixedLaplaceTest m (Xs i ω) ∂(P : Measure Ω)) F
      (𝓝 (mixedLaplace ν m))) :
    Tendsto (fun i => P.map (hX i).aemeasurable) F (𝓝 ν) := by
  apply probabilityMeasure_tendsto_of_mixedIntegerLaplace
  intro m
  have hmoment (i : ι) : mixedLaplace (P.map (hX i).aemeasurable) m =
      ∫ ω, mixedLaplaceTest m (Xs i ω) ∂(P : Measure Ω) :=
    mixedLaplace_map P (Xs i) (hX i) m
  simpa only [hmoment] using hlaplace m

/-- Coordinatewise clipping into the nonnegative orthant, used only as a
continuous total extension. It is exactly the identity on nonnegative vectors. -/
def toNNRealVector (x : d → ℝ) : d → ℝ≥0 := fun j => Real.toNNReal (x j)

def coeNNRealVector (x : d → ℝ≥0) : d → ℝ := fun j => (x j : ℝ)

theorem continuous_toNNRealVector : Continuous (toNNRealVector (d := d)) :=
  continuous_pi fun j => continuous_real_toNNReal.comp (continuous_apply j)

theorem continuous_coeNNRealVector : Continuous (coeNNRealVector (d := d)) :=
  continuous_pi fun j => continuous_subtype_val.comp (continuous_apply j)

theorem coeNNRealVector_toNNRealVector (x : d → ℝ) (hx : ∀ j, 0 ≤ x j) :
    coeNNRealVector (toNNRealVector x) = x := by
  funext j
  exact Real.coe_toNNReal _ (hx j)

/-- The actual real-vector mixed integer Laplace test. -/
def realMixedLaplaceTest (m : d → ℕ) (x : d → ℝ) : ℝ :=
  Real.exp (-(∑ j, (m j : ℝ) * x j))

theorem mixedLaplaceTest_toNNRealVector (m : d → ℕ) (x : d → ℝ)
    (hx : ∀ j, 0 ≤ x j) : mixedLaplaceTest m (toNNRealVector x) = realMixedLaplaceTest m x := by
  unfold mixedLaplaceTest toNNRealVector realMixedLaplaceTest
  simp_rw [Real.coe_toNNReal _ (hx _)]

/-- Mixed integer Laplace convergence identifies a genuine joint weak law
for real-valued nonnegative vectors. The target is arbitrary and may have
atoms; its nonnegative support is an explicit almost-everywhere premise. -/
theorem laws_tendsto_of_mixed_integer_laplace
    {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    (P : ProbabilityMeasure Ω) (Xs : ι → Ω → d → ℝ) (hX : ∀ i, Measurable (Xs i))
    (hX0 : ∀ i ω j, 0 ≤ Xs i ω j) (ν : ProbabilityMeasure (d → ℝ))
    (hν0 : ∀ᵐ x ∂(ν : Measure (d → ℝ)), ∀ j, 0 ≤ x j)
    (hlaplace : ∀ m : d → ℕ, Tendsto
      (fun i => ∫ ω, realMixedLaplaceTest m (Xs i ω) ∂(P : Measure Ω)) F
      (𝓝 (∫ x, realMixedLaplaceTest m x ∂(ν : Measure (d → ℝ))))) :
    Tendsto (fun i => P.map (hX i).aemeasurable) F (𝓝 ν) := by
  let Xn : ι → Ω → d → ℝ≥0 := fun i ω => toNNRealVector (Xs i ω)
  have hXn (i : ι) : Measurable (Xn i) :=
    continuous_toNNRealVector.measurable.comp (hX i)
  let νn : ProbabilityMeasure (d → ℝ≥0) :=
    ν.map continuous_toNNRealVector.measurable.aemeasurable
  have hsource (m : d → ℕ) (i : ι) :
      (∫ ω, mixedLaplaceTest m (Xn i ω) ∂(P : Measure Ω)) =
        ∫ ω, realMixedLaplaceTest m (Xs i ω) ∂(P : Measure Ω) :=
    integral_congr_ae (ae_of_all _ fun ω => mixedLaplaceTest_toNNRealVector m _ (hX0 i ω))
  have htarget (m : d → ℕ) : mixedLaplace νn m =
      ∫ x, realMixedLaplaceTest m x ∂(ν : Measure (d → ℝ)) := by
    rw [mixedLaplace_map ν toNNRealVector continuous_toNNRealVector.measurable]
    apply integral_congr_ae
    filter_upwards [hν0] with x hx
    exact mixedLaplaceTest_toNNRealVector m x hx
  have hn : Tendsto (fun i => P.map (hXn i).aemeasurable) F (𝓝 νn) := by
    apply nnreal_laws_tendsto_of_mixed_integer_laplace P Xn hXn νn
    intro m
    simpa only [hsource, htarget] using hlaplace m
  have hreal := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun i => P.map (hXn i).aemeasurable) νn hn continuous_coeNNRealVector
  have hmapSource (i : ι) :
      (P.map (hXn i).aemeasurable).map continuous_coeNNRealVector.measurable.aemeasurable =
        P.map (hX i).aemeasurable := by
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map continuous_coeNNRealVector.measurable (hXn i)]
    have heq : coeNNRealVector ∘ Xn i = Xs i := by
      funext ω
      exact coeNNRealVector_toNNRealVector _ (hX0 i ω)
    rw [heq]
  have hmapTarget : νn.map continuous_coeNNRealVector.measurable.aemeasurable = ν := by
    apply ProbabilityMeasure.toMeasure_injective
    change ((ν : Measure (d → ℝ)).map toNNRealVector).map coeNNRealVector = _
    rw [Measure.map_map continuous_coeNNRealVector.measurable continuous_toNNRealVector.measurable]
    have heq : coeNNRealVector ∘ toNNRealVector =ᵐ[(ν : Measure (d → ℝ))] id := by
      filter_upwards [hν0] with x hx
      exact coeNNRealVector_toNNRealVector x hx
    rw [Measure.map_congr heq, Measure.map_id]
  simpa only [hmapSource, hmapTarget] using hreal

end FiniteDimension
end FixedCouplingPoisson
