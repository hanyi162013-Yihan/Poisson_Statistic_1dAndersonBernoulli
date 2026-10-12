import FixedCouplingPoisson.RealVagueSpace
import Mathlib.Topology.ContinuousOn

/-! Actual finite point measures and discrete-count atom arrays in the vague space. -/
noncomputable section
namespace FixedCouplingPoisson.RealVagueMeasure
open MeasureTheory
open scoped Topology CompactlySupported BigOperators

/-- The actual finite sum of unit Dirac atoms. -/
def finiteAtoms {ι : Type*} [Fintype ι] (x : ι → ℝ) : RealVagueMeasure :=
  ofMeasure (∑ i, Measure.dirac (x i))

@[simp] theorem coe_finiteAtoms {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    (finiteAtoms x : Measure ℝ) = ∑ i, Measure.dirac (x i) := rfl

theorem testIntegral_finiteAtoms {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (f : C_c(ℝ, ℝ)) : testIntegral (finiteAtoms x) f = ∑ i, f (x i) := by
  change (∫ y, f y ∂(∑ i, Measure.dirac (x i))) = _
  rw [integral_finsetSum_measure (fun i _ => f.integrable)]
  simp only [integral_dirac]

/-- Moving finitely many points continuously moves their actual point measure
continuously in the vague topology. -/
theorem continuous_finiteAtoms {ι : Type*} [Fintype ι] :
    Continuous (finiteAtoms : (ι → ℝ) → RealVagueMeasure) := by
  apply continuous_iff_testIntegral.mpr
  intro f
  simpa only [testIntegral_finiteAtoms, Function.comp_apply,
    CompactlySupportedContinuousMap.coe_toContinuousMap] using
    continuous_finsetSum Finset.univ (fun i _ => f.continuous.comp (continuous_apply i))

/-- The first `N` atoms of an actual real sequence. -/
def finitePrefixAtoms (N : ℕ) (x : ℕ → ℝ) : RealVagueMeasure :=
  finiteAtoms (fun i : Fin N => x i.val)

theorem testIntegral_finitePrefixAtoms (N : ℕ) (x : ℕ → ℝ)
    (f : C_c(ℝ, ℝ)) :
    testIntegral (finitePrefixAtoms N x) f = ∑ i : Fin N, f (x i.val) :=
  testIntegral_finiteAtoms _ _

/-- The atom count has its genuine discrete topology. No global bound on the
count is needed for joint continuity with the sequence of marks. -/
theorem continuous_finitePrefixAtoms :
    Continuous (fun z : ℕ × (ℕ → ℝ) => finitePrefixAtoms z.1 z.2) := by
  apply continuous_prod_of_discrete_left.mpr
  intro N
  exact continuous_finiteAtoms.comp (continuous_pi fun i : Fin N => continuous_apply i.val)

theorem measurable_finitePrefixAtoms :
    Measurable (fun z : ℕ × (ℕ → ℝ) => finitePrefixAtoms z.1 z.2) :=
  continuous_finitePrefixAtoms.measurable

end FixedCouplingPoisson.RealVagueMeasure
