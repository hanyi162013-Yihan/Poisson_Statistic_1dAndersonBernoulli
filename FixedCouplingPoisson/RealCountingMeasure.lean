import FixedCouplingPoisson.RealVagueAtoms
import FixedCouplingPoisson.PoissonCloudAtoms
import FixedCouplingPoisson.PoissonCloudVagueLaw

/-! Actual locally finite counting measures with the induced vague topology.
The Borel sigma algebra is explicit. The true Poisson target is continuously
lifted from its actual Polish uniform-mark sample space. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal unitInterval Topology

def RealVagueMeasure.IsCounting (μ : RealVagueMeasure) : Prop :=
  ∃ (ι : Type) (_h : Countable ι) (x : ι → ℝ),
    μ.toMeasure = Measure.sum (fun i => Measure.dirac (x i))

def RealCountingMeasure := {μ : RealVagueMeasure // μ.IsCounting}

namespace RealCountingMeasure

def toVague (μ : RealCountingMeasure) : RealVagueMeasure := μ.val

instance : CoeTC RealCountingMeasure RealVagueMeasure := ⟨toVague⟩

theorem toVague_injective : Function.Injective toVague := Subtype.val_injective

def toMeasure (μ : RealCountingMeasure) : Measure ℝ := (toVague μ).toMeasure

instance : CoeTC RealCountingMeasure (Measure ℝ) := ⟨toMeasure⟩

instance (μ : RealCountingMeasure) : IsLocallyFiniteMeasure (μ : Measure ℝ) :=
  (toVague μ).locallyFinite

theorem toMeasure_injective : Function.Injective toMeasure := by
  intro μ ν h
  apply toVague_injective
  exact RealVagueMeasure.toMeasure_injective h

instance : TopologicalSpace RealCountingMeasure :=
  TopologicalSpace.induced toVague inferInstance

theorem isEmbedding_toVague : IsEmbedding toVague :=
  toVague_injective.isEmbedding_induced

theorem continuous_toVague : Continuous toVague := isEmbedding_toVague.continuous

instance : T2Space RealCountingMeasure := isEmbedding_toVague.t2Space

instance : MeasurableSpace RealCountingMeasure := borel RealCountingMeasure

instance : BorelSpace RealCountingMeasure := ⟨rfl⟩

theorem measurable_toVague : Measurable toVague := continuous_toVague.measurable

theorem isCounting_finiteAtoms {ι : Type} [Fintype ι] (x : ι → ℝ) :
    (RealVagueMeasure.finiteAtoms x).IsCounting := by
  refine ⟨ι, inferInstance, x, ?_⟩
  change (∑ i, Measure.dirac (x i)) = Measure.sum (fun i => Measure.dirac (x i))
  ext A hA
  rw [Measure.sum_apply _ hA, Measure.finsetSum_apply, tsum_fintype]

def finiteAtoms {ι : Type} [Fintype ι] (x : ι → ℝ) : RealCountingMeasure :=
  ⟨RealVagueMeasure.finiteAtoms x, isCounting_finiteAtoms x⟩

@[simp] theorem toVague_finiteAtoms {ι : Type} [Fintype ι] (x : ι → ℝ) :
    toVague (finiteAtoms x) = RealVagueMeasure.finiteAtoms x := rfl

theorem continuous_finiteAtoms {ι : Type} [Fintype ι] :
    Continuous (finiteAtoms : (ι → ℝ) → RealCountingMeasure) := by
  apply isEmbedding_toVague.continuous_iff.mpr
  exact RealVagueMeasure.continuous_finiteAtoms

def finitePrefixAtoms (N : ℕ) (x : ℕ → ℝ) : RealCountingMeasure :=
  finiteAtoms (fun i : Fin N => x i.val)

@[simp] theorem toVague_finitePrefixAtoms (N : ℕ) (x : ℕ → ℝ) :
    toVague (finitePrefixAtoms N x) = RealVagueMeasure.finitePrefixAtoms N x := rfl

theorem continuous_finitePrefixAtoms :
    Continuous (fun z : ℕ × (ℕ → ℝ) => finitePrefixAtoms z.1 z.2) := by
  apply isEmbedding_toVague.continuous_iff.mpr
  exact RealVagueMeasure.continuous_finitePrefixAtoms

end RealCountingMeasure

theorem isCounting_poissonCloudVagueMeasure (ω : PoissonCloud) :
    (poissonCloudVagueMeasure ω).IsCounting := by
  refine ⟨PoissonCloudAtomIndex ω, inferInstance, poissonCloudAtom ω, ?_⟩
  exact poissonCloudMeasure_eq_sum_atoms ω

def poissonCountingMeasure (ω : PoissonCloud) : RealCountingMeasure :=
  ⟨poissonCloudVagueMeasure ω, isCounting_poissonCloudVagueMeasure ω⟩

@[simp] theorem toVague_poissonCountingMeasure (ω : PoissonCloud) :
    RealCountingMeasure.toVague (poissonCountingMeasure ω) = poissonCloudVagueMeasure ω := rfl

theorem continuous_poissonCountingMeasure : Continuous poissonCountingMeasure := by
  apply RealCountingMeasure.isEmbedding_toVague.continuous_iff.mpr
  exact continuous_poissonCloudVagueMeasure

def poissonCountingLaw : ProbabilityMeasure RealCountingMeasure :=
  poissonCloudLaw.map continuous_poissonCountingMeasure.measurable.aemeasurable

theorem poissonCountingLaw_map_toVague :
    poissonCountingLaw.map RealCountingMeasure.measurable_toVague.aemeasurable =
      poissonVagueLaw := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((poissonCloudLaw : Measure PoissonCloud).map poissonCountingMeasure).map
    RealCountingMeasure.toVague =
      (poissonCloudLaw : Measure PoissonCloud).map poissonCloudVagueMeasure
  rw [Measure.map_map RealCountingMeasure.measurable_toVague
    continuous_poissonCountingMeasure.measurable]
  rfl

theorem isTightMeasureSet_poissonCountingLaw :
    IsTightMeasureSet {(poissonCountingLaw : Measure RealCountingMeasure)} := by
  have h : IsTightMeasureSet {(poissonCloudLaw : Measure PoissonCloud)} :=
    isTightMeasureSet_singleton
  simpa only [Set.image_singleton, poissonCountingLaw, ProbabilityMeasure.toMeasure_map] using
    h.map continuous_poissonCountingMeasure

end FixedCouplingPoisson
