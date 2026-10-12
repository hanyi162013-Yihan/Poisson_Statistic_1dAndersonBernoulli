import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# The real locally finite measure space with its actual vague topology

This ambient space contains counting measures and infinite-mass Poisson
measures. Its topology is induced by all compactly supported continuous
real test integrals. Its measurable space is the Borel space of that topology;
no identification with the Giry sigma algebra is presumed.
-/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Filter Topology
open scoped Topology CompactlySupported

/-- Locally finite Borel measures on the real line, bundled independently
of the original measurable-space structure on `Measure ℝ`. -/
structure RealVagueMeasure where
  toMeasure : Measure ℝ
  locallyFinite : IsLocallyFiniteMeasure toMeasure

namespace RealVagueMeasure

instance : CoeTC RealVagueMeasure (Measure ℝ) := ⟨toMeasure⟩

instance (μ : RealVagueMeasure) : IsLocallyFiniteMeasure (μ : Measure ℝ) :=
  μ.locallyFinite

/-- Bundle an actual locally finite measure. -/
def ofMeasure (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] : RealVagueMeasure :=
  ⟨μ, inferInstance⟩

@[simp] theorem coe_ofMeasure (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    (ofMeasure μ : Measure ℝ) = μ := rfl

theorem toMeasure_injective : Function.Injective toMeasure := by
  rintro ⟨μ, hμ⟩ ⟨ν, hν⟩ h
  cases h
  rfl

/-- A compactly supported continuous real test integral. -/
def testIntegral (μ : RealVagueMeasure) (f : C_c(ℝ, ℝ)) : ℝ :=
  ∫ x, f x ∂(μ : Measure ℝ)

theorem test_integrable (μ : RealVagueMeasure) (f : C_c(ℝ, ℝ)) :
    Integrable f (μ : Measure ℝ) := f.integrable

/-- The complete family of vague coordinates. -/
def coordinates (μ : RealVagueMeasure) : C_c(ℝ, ℝ) → ℝ :=
  fun f => testIntegral μ f

/-- RMK separation is applicable because real locally finite Borel measures
are automatically regular. -/
@[ext] theorem ext_of_testIntegral {μ ν : RealVagueMeasure}
    (h : ∀ f : C_c(ℝ, ℝ), testIntegral μ f = testIntegral ν f) : μ = ν := by
  apply toMeasure_injective
  exact Measure.ext_of_integral_eq_on_compactlySupported h

theorem coordinates_injective : Function.Injective coordinates := by
  intro μ ν h
  apply ext_of_testIntegral
  intro f
  exact congrFun h f

/-- The vague topology is the topology induced by the actual test integrals. -/
instance : TopologicalSpace RealVagueMeasure :=
  TopologicalSpace.induced coordinates inferInstance

theorem isEmbedding_coordinates : IsEmbedding coordinates :=
  coordinates_injective.isEmbedding_induced

theorem continuous_coordinates : Continuous coordinates :=
  continuous_induced_dom

instance : T2Space RealVagueMeasure := isEmbedding_coordinates.t2Space

/-- This is the Borel sigma algebra of the vague topology. -/
instance : MeasurableSpace RealVagueMeasure := borel RealVagueMeasure

instance : BorelSpace RealVagueMeasure := ⟨rfl⟩

theorem continuous_testIntegral (f : C_c(ℝ, ℝ)) :
    Continuous (fun μ : RealVagueMeasure => testIntegral μ f) :=
  (continuous_apply f).comp continuous_coordinates

theorem measurable_testIntegral (f : C_c(ℝ, ℝ)) :
    Measurable (fun μ : RealVagueMeasure => testIntegral μ f) :=
  (continuous_testIntegral f).measurable

/-- The definition gives the full-filter vague convergence criterion. -/
theorem tendsto_iff_testIntegral {ι : Type*} {F : Filter ι}
    {u : ι → RealVagueMeasure} {μ : RealVagueMeasure} :
    Tendsto u F (𝓝 μ) ↔ ∀ f : C_c(ℝ, ℝ),
      Tendsto (fun i => testIntegral (u i) f) F (𝓝 (testIntegral μ f)) := by
  constructor
  · intro h f
    exact ((continuous_testIntegral f).continuousAt.tendsto).comp h
  · intro h
    apply isEmbedding_coordinates.tendsto_nhds_iff.mpr
    exact tendsto_pi_nhds.mpr h

/-- A map into the vague space is continuous precisely when each genuine
compactly supported test integral is continuous. -/
theorem continuous_iff_testIntegral {X : Type*} [TopologicalSpace X]
    {u : X → RealVagueMeasure} :
    Continuous u ↔ ∀ f : C_c(ℝ, ℝ), Continuous (fun x => testIntegral (u x) f) := by
  constructor
  · intro h f
    exact (continuous_testIntegral f).comp h
  · intro h
    apply isEmbedding_coordinates.continuous_iff.mpr
    exact continuous_pi h

theorem testIntegral_nonneg (μ : RealVagueMeasure) (f : C_c(ℝ, ℝ))
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ testIntegral μ f := integral_nonneg hf

end RealVagueMeasure
end FixedCouplingPoisson
