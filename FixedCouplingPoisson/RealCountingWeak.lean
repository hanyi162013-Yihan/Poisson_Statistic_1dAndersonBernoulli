import FixedCouplingPoisson.SingletonTightEmbeddingWeak
import FixedCouplingPoisson.RealCountingMeasure

/-! Ordinary weak convergence in the actual space of locally finite counting measures. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Filter Topology
open scoped Topology

instance : T35Space RealVagueMeasure := RealVagueMeasure.isEmbedding_coordinates.t35Space

namespace RealCountingMeasure

/-- Bundle an actual counting-valued vague measure using the named counting-space type. -/
def ofVague (μ : RealVagueMeasure) (hμ : μ.IsCounting) : RealCountingMeasure := ⟨μ, hμ⟩

@[simp] theorem toVague_ofVague (μ : RealVagueMeasure) (hμ : μ.IsCounting) :
    toVague (ofVague μ hμ) = μ := rfl

/-- The exact counting-space Borel structure is induced by the vague inclusion. -/
theorem measurable_iff_toVague {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → RealCountingMeasure} : Measurable X ↔ Measurable (toVague ∘ X) := by
  change @Measurable Ω RealCountingMeasure _ (borel RealCountingMeasure) X ↔ _
  rw [show borel RealCountingMeasure = (borel RealVagueMeasure).comap toVague from borel_comap]
  exact measurable_comap_iff

/-- Every measurable actual vague process with counting values lifts measurably
to the exact counting space. -/
theorem measurable_mk {Ω : Type*} [MeasurableSpace Ω] {X : Ω → RealVagueMeasure}
    (hX : Measurable X) (hc : ∀ ω, (X ω).IsCounting) :
    Measurable (fun ω => ofVague (X ω) (hc ω)) :=
  (measurable_iff_toVague (X := fun ω => ofVague (X ω) (hc ω))).mpr hX

/-- The lifted actual source law has precisely its original vague pushforward. -/
theorem law_mk_map_toVague {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) {X : Ω → RealVagueMeasure}
    (hX : Measurable X) (hc : ∀ ω, (X ω).IsCounting) :
    (P.map (f := fun ω => ofVague (X ω) (hc ω))
      (measurable_mk hX hc).aemeasurable).map (f := toVague) measurable_toVague.aemeasurable =
      P.map hX.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((P : Measure Ω).map (fun ω => ofVague (X ω) (hc ω))).map
    toVague = (P : Measure Ω).map X
  rw [Measure.map_map measurable_toVague (measurable_mk hX hc)]
  rfl

/-- Convergence of the actual vague pushforwards reflects to ordinary weak convergence
in the exact counting-measure subspace whenever the target counting law is tight. -/
theorem probabilityMeasure_tendsto_of_vague_tendsto
    {ι : Type*} {F : Filter ι} (μs : ι → ProbabilityMeasure RealCountingMeasure)
    (μ : ProbabilityMeasure RealCountingMeasure)
    (htight : IsTightMeasureSet {(μ : Measure RealCountingMeasure)})
    (hmap : Tendsto (fun i => (μs i).map measurable_toVague.aemeasurable) F
      (𝓝 (μ.map measurable_toVague.aemeasurable))) : Tendsto μs F (𝓝 μ) :=
  probabilityMeasure_tendsto_of_target_tight_of_isEmbedding
    toVague isEmbedding_toVague μs μ htight hmap

end RealCountingMeasure

/-- In particular, actual vague convergence to the true Poisson law implies ordinary
weak convergence to its actual counting-space lift. The target tightness is proved
from the Polish Poisson sample space in `RealCountingMeasure`. -/
theorem probabilityMeasure_tendsto_poissonCountingLaw_of_vague_tendsto
    {ι : Type*} {F : Filter ι} (μs : ι → ProbabilityMeasure RealCountingMeasure)
    (hmap : Tendsto (fun i => (μs i).map RealCountingMeasure.measurable_toVague.aemeasurable)
      F (𝓝 poissonVagueLaw)) : Tendsto μs F (𝓝 poissonCountingLaw) := by
  apply RealCountingMeasure.probabilityMeasure_tendsto_of_vague_tendsto
    μs poissonCountingLaw isTightMeasureSet_poissonCountingLaw
  simpa only [poissonCountingLaw_map_toVague] using hmap

end FixedCouplingPoisson
