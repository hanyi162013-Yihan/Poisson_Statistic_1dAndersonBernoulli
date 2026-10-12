import FixedCouplingPoisson.RealVagueImage

/-! Compact boxes in the actual real vague measure state space. -/
noncomputable section
namespace FixedCouplingPoisson.RealVagueMeasure
open MeasureTheory Topology Set
open scoped Topology CompactlySupported

/-- The box constrains each genuine compactly supported continuous test integral. -/
def coordinateBox (a b : C_c(ℝ, ℝ) → ℝ) : Set RealVagueMeasure :=
  {μ | ∀ f, a f ≤ testIntegral μ f ∧ testIntegral μ f ≤ b f}

/-- Arbitrary coordinatewise finite bounds give a compact vague set. This is
Tychonoff plus the proved closed RMK coordinate image, not a tightness interface. -/
theorem isCompact_coordinateBox (a b : C_c(ℝ, ℝ) → ℝ) :
    IsCompact (coordinateBox a b) := by
  have hcompact : IsCompact {L : C_c(ℝ, ℝ) → ℝ | ∀ f, L f ∈ Icc (a f) (b f)} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  exact isClosedEmbedding_coordinates.isCompact_preimage hcompact

/-- A closed family whose every test integral is uniformly bounded is compact. -/
theorem isCompact_of_isClosed_of_testIntegral_bounded {S : Set RealVagueMeasure}
    (hS : IsClosed S) (a b : C_c(ℝ, ℝ) → ℝ)
    (hbound : ∀ μ ∈ S, ∀ f, a f ≤ testIntegral μ f ∧ testIntegral μ f ≤ b f) :
    IsCompact S :=
  (isCompact_coordinateBox a b).of_isClosed_subset hS hbound

/-- Symmetric coordinate bounds are often convenient for cutoff-mass tightness. -/
theorem isCompact_abs_coordinateBox (M : C_c(ℝ, ℝ) → ℝ) :
    IsCompact {μ : RealVagueMeasure | ∀ f, |testIntegral μ f| ≤ M f} := by
  simpa only [coordinateBox, abs_le] using isCompact_coordinateBox (fun f => -M f) M

end FixedCouplingPoisson.RealVagueMeasure
