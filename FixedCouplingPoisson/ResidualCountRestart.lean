import FixedCouplingPoisson.ResidualUpper
import FixedCouplingPoisson.ScalarCrossingCounts

/-! Complete count restart at the actual deterministic residual state. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set

/-- Every integer crossing increment is the true fresh-path count.
This exact floor-shift identity needs no ordering of the two energies. -/
theorem canonicalResidualState_count_restart (E δ θ φ : ℝ) (j L : ℕ)
    (ω : PotentialSpace) :
    canonicalCrossingCount E δ (canonicalResidualState E δ θ φ j ω).1
      (canonicalResidualState E δ θ φ j ω).2 L (potentialShift j ω) =
        canonicalCrossingCount E δ θ φ (j + L) ω -
          canonicalCrossingCount E δ θ φ j ω := by
  change ⌊canonicalGapProcess E δ (canonicalPhaseProcess E θ j ω)
      (canonicalPhaseProcess (E + δ) φ j ω +
        (canonicalCrossingCount E δ θ φ j ω : ℝ) * Real.pi) L (potentialShift j ω) /
          Real.pi⌋ = _
  rw [canonicalGapProcess_restart]
  have heq : (canonicalGapProcess E δ θ φ (j + L) ω -
      (canonicalCrossingCount E δ θ φ j ω : ℝ) * Real.pi) / Real.pi =
        canonicalGapProcess E δ θ φ (j + L) ω / Real.pi -
          (canonicalCrossingCount E δ θ φ j ω : ℝ) := by
    field_simp [Real.pi_ne_zero] <;> ring
  rw [heq, Int.floor_sub_intCast]
  rfl

/-- All fresh level-arrival events, including the first two, are exactly
the corresponding increment events on the original iid path. -/
theorem canonicalResidualState_arrival_le_iff_count_increment (E δ θ φ : ℝ)
    (hδ : 0 ≤ δ) (j L k : ℕ) (ω : PotentialSpace) :
    canonicalLevelCrossingTime E δ (canonicalResidualState E δ θ φ j ω).1
      (canonicalResidualState E δ θ φ j ω).2 k (potentialShift j ω) ≤ L ↔
        (k : ℤ) ≤ canonicalCrossingCount E δ θ φ (j + L) ω -
          canonicalCrossingCount E δ θ φ j ω := by
  rw [← canonicalCrossingCount_ge_iff_arrival _ _ _ _ hδ,
    canonicalResidualState_count_restart]

theorem canonicalResidualState_natural_count_restart (E δ θ φ : ℝ) (j L : ℕ)
    (ω : PotentialSpace) :
    canonicalNaturalCrossingCount E δ (canonicalResidualState E δ θ φ j ω).1
      (canonicalResidualState E δ θ φ j ω).2 L (potentialShift j ω) =
        (canonicalCrossingCount E δ θ φ (j + L) ω -
          canonicalCrossingCount E δ θ φ j ω).toNat := by
  unfold canonicalNaturalCrossingCount
  rw [canonicalResidualState_count_restart]

end FixedCouplingPoisson.Furstenberg
