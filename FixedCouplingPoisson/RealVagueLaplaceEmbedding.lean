import FixedCouplingPoisson.RealVagueLaplaceCube
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The full genuine Laplace coordinate map preserves exactly the vague topology. -/
noncomputable section
namespace FixedCouplingPoisson.RealVagueMeasure
open MeasureTheory Filter Topology
open scoped Topology CompactlySupported

private theorem compactTest_pos_sub_neg (f : C_c(ℝ, ℝ)) :
    f = (f ⊔ 0) - ((-f) ⊔ 0) := by
  ext x
  simp only [CompactlySupportedContinuousMap.sub_apply,
    CompactlySupportedContinuousMap.sup_apply,
    CompactlySupportedContinuousMap.zero_apply,
    CompactlySupportedContinuousMap.neg_apply]
  by_cases hx : 0 ≤ f x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    simp
  · have hx' : f x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
    simp

/-- All nonnegative compact Laplace coordinates recover vague convergence
for arbitrary nets and filters, using the logarithm only at strictly positive values. -/
theorem tendsto_iff_nonneg_laplaceTest {ι : Type*} {F : Filter ι}
    {u : ι → RealVagueMeasure} {μ : RealVagueMeasure} :
    Tendsto u F (𝓝 μ) ↔ ∀ f : C_c(ℝ, ℝ), 0 ≤ f →
      Tendsto (fun i => laplaceTest f (u i)) F (𝓝 (laplaceTest f μ)) := by
  constructor
  · intro h f _
    exact ((continuous_laplaceTest f).tendsto μ).comp h
  · intro h
    have hIntegral (f : C_c(ℝ, ℝ)) (hf : 0 ≤ f) :
        Tendsto (fun i => testIntegral (u i) f) F (𝓝 (testIntegral μ f)) := by
      have hlog := (Real.continuousAt_log (Real.exp_ne_zero (-testIntegral μ f))).tendsto.comp
        (h f hf)
      simpa only [Function.comp_apply, laplaceTest, Real.log_exp, neg_neg] using hlog.neg
    apply tendsto_iff_testIntegral.mpr
    intro f
    have hdiff := (hIntegral (f ⊔ 0) le_sup_right).sub
      (hIntegral ((-f) ⊔ 0) le_sup_right)
    have heq (ν : RealVagueMeasure) :
        testIntegral ν (f ⊔ 0) - testIntegral ν ((-f) ⊔ 0) = testIntegral ν f := by
      rw [← testIntegral_sub, ← compactTest_pos_sub_neg]
    simpa only [heq] using hdiff

/-- The complete Borel Laplace cube has exactly the original vague convergence criterion. -/
theorem tendsto_iff_laplaceCubeCoordinates {ι : Type*} {F : Filter ι}
    {u : ι → RealVagueMeasure} {μ : RealVagueMeasure} :
    Tendsto u F (𝓝 μ) ↔ Tendsto (laplaceCubeCoordinates ∘ u) F
      (𝓝 (laplaceCubeCoordinates μ)) := by
  constructor
  · intro h
    exact (continuous_laplaceCubeCoordinates.tendsto μ).comp h
  · intro h
    apply tendsto_iff_nonneg_laplaceTest.mpr
    intro f hf
    have hcoord := ((continuous_apply (⟨f, hf⟩ : NonnegCompactTest)).tendsto
      (laplaceCubeCoordinates μ)).comp h
    exact (continuous_subtype_val.tendsto _).comp hcoord

/-- This is a genuine topological embedding, stronger than point separation. -/
theorem isEmbedding_laplaceCubeCoordinates : IsEmbedding laplaceCubeCoordinates := by
  refine ⟨isInducing_iff_nhds.mpr (fun μ => ?_), laplaceCubeCoordinates_injective⟩
  apply le_antisymm
  · exact (continuous_laplaceCubeCoordinates.tendsto μ).le_comap
  · have h : Tendsto id
        (comap laplaceCubeCoordinates (𝓝 (laplaceCubeCoordinates μ))) (𝓝 μ) :=
      tendsto_iff_laplaceCubeCoordinates.mpr tendsto_comap
    exact tendsto_id'.mp h

end FixedCouplingPoisson.RealVagueMeasure
