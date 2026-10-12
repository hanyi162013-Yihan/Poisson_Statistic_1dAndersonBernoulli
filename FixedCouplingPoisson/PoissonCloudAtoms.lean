import FixedCouplingPoisson.PoissonCloudMeasure
import Mathlib.Algebra.BigOperators.Fin

/-! An explicit countable atom index for every path of the cloud. This is the
counting-measure representation, including multiplicities. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal unitInterval Topology

abbrev PoissonCloudAtomIndex (ω : PoissonCloud) := Σ z : ℤ, Fin (ω z).1

instance (ω : PoissonCloud) : Countable (PoissonCloudAtomIndex ω) := inferInstance

def poissonCloudAtom (ω : PoissonCloud) (i : PoissonCloudAtomIndex ω) : ℝ :=
  (i.1 : ℝ) + ((ω i.1).2 i.2 : ℝ)

theorem poissonCloudMeasure_eq_sum_atoms (ω : PoissonCloud) :
    poissonCloudMeasure ω =
      Measure.sum (fun i : PoissonCloudAtomIndex ω => Measure.dirac (poissonCloudAtom ω i)) := by
  ext A hA
  rw [poissonCloudMeasure, Measure.sum_apply _ hA, Measure.sum_apply _ hA, ENNReal.tsum_sigma']
  apply tsum_congr
  intro z
  rw [poissonCellMeasure, Measure.finsetSum_apply, tsum_fintype]
  exact Finset.sum_range (fun j => Measure.dirac ((z : ℝ) + ((ω z).2 j : ℝ)) A)

end FixedCouplingPoisson
