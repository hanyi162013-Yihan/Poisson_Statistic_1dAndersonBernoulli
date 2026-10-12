import FixedCouplingPoisson.ProjectiveSL2Harmonic
import FixedCouplingPoisson.FurstenbergNoAtoms
import FixedCouplingPoisson.CompactRightPreservers

/-! Strict positivity for the actual Schrödinger SL₂ cocycle.
This proof uses atomlessness, elementary row bounds, stationarity and the
explicit two-transfer shear obstruction. It uses no `Furstenberg.Input`,
uniqueness theorem, Oseledets theorem or assumed random-product conclusion. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set
open scoped Topology

theorem forwardStationary_stationaryMean_pos (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : ForwardStationary law E ν) :
    0 < stationaryMean law E ν := by
  letI : T2Space RealSL2 :=
    (Matrix.SpecialLinearGroup.isClosedEmbedding_val
      (n := Fin 2) (R := ℝ)).isEmbedding.t2Space
  have hnoatom : ∀ p, (ν : Measure ProjectivePoint) {p} = 0 :=
    forwardStationary_null_singletons law E ν hν
  obtain ⟨A₀, hmin⟩ := exists_stationarySL2Mean_minimizer ν hnoatom
  have hnonneg := stationaryMean_nonneg_of_sl2_minimizer law E ν hν A₀ hmin
  by_contra hpos
  have hzero : stationaryMean law E ν = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
  let K : Set RealSL2 := {A | stationarySL2Mean ν A ≤ stationarySL2Mean ν A₀}
  have hK : IsCompact K := isCompact_stationarySL2Mean_sublevel ν hnoatom _
  have hne : K.Nonempty := by
    refine ⟨A₀, ?_⟩
    change stationarySL2Mean ν A₀ ≤ stationarySL2Mean ν A₀
    exact le_rfl
  have hpreserve (v : ℝ) (hv : v ∈ law.measure.support) :
      schrodingerTransferSL2 E v ∈ rightPreserverSubmonoid K := by
    intro A hA
    change stationarySL2Mean ν A ≤ stationarySL2Mean ν A₀ at hA
    have hEq : stationarySL2Mean ν A = stationarySL2Mean ν A₀ :=
      le_antisymm hA (hmin A)
    have hminA : ∀ B : RealSL2, stationarySL2Mean ν A ≤ stationarySL2Mean ν B := by
      intro B
      rw [hEq]
      exact hmin B
    have h := sl2_minimizer_right_transfer_of_zero_mean law E ν hν hzero A hminA v hv
    change stationarySL2Mean ν (A * schrodingerTransferSL2 E v) ≤ stationarySL2Mean ν A₀
    exact (h.trans hEq).le
  obtain ⟨a, b, ha, hb, hab⟩ := AtomArgument.exists_two_potentials law
    law.measure.support_mem_ae
  exact no_compact_submonoid_two_schrodinger_transfers E a b hab
    (rightPreserverSubmonoid K) (isCompact_rightPreserverSubmonoid hK hne)
    (hpreserve a ha) (hpreserve b hb)

end FixedCouplingPoisson.Furstenberg
