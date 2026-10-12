import FixedCouplingPoisson.RealVagueSpace
import Mathlib.Topology.Compactness.Compact

/-! The actual vague coordinate image is a closed positive-linear cone. -/
noncomputable section
namespace FixedCouplingPoisson.RealVagueMeasure
open MeasureTheory Filter Topology Set
open scoped Topology CompactlySupported

/-- These are explicit pointwise algebraic/order constraints, not a new
mathematical input. RMK realizes every function satisfying them. -/
def IsPositiveCoordinate (L : C_c(ℝ, ℝ) → ℝ) : Prop :=
  (∀ f g, L (f + g) = L f + L g) ∧
  (∀ (c : ℝ) f, L (c • f) = c • L f) ∧
  (∀ f, 0 ≤ f → 0 ≤ L f)

/-- Form the genuine positive linear functional from the stated constraints. -/
def positiveLinearMapOfCoordinates (L : C_c(ℝ, ℝ) → ℝ) (h : IsPositiveCoordinate L) :
    C_c(ℝ, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := L, map_add' := h.1, map_smul' := h.2.1 } h.2.2

/-- RMK constructs an actual real locally finite measure from the coordinates. -/
def ofPositiveCoordinates (L : C_c(ℝ, ℝ) → ℝ) (h : IsPositiveCoordinate L) :
    RealVagueMeasure :=
  ofMeasure (RealRMK.rieszMeasure (positiveLinearMapOfCoordinates L h))

theorem coordinates_ofPositiveCoordinates (L : C_c(ℝ, ℝ) → ℝ)
    (h : IsPositiveCoordinate L) : coordinates (ofPositiveCoordinates L h) = L := by
  funext f
  change (∫ x, f x ∂RealRMK.rieszMeasure (positiveLinearMapOfCoordinates L h)) = L f
  exact RealRMK.integral_rieszMeasure _ f

theorem coordinates_are_positive (μ : RealVagueMeasure) :
    IsPositiveCoordinate (coordinates μ) := by
  let Λ := CompactlySupportedContinuousMap.integralPositiveLinearMap (μ : Measure ℝ)
  exact ⟨(fun f g => map_add Λ f g), (fun c f => map_smul Λ c f),
    (fun f hf => Λ.map_nonneg hf)⟩

theorem range_coordinates : Set.range coordinates =
    {L : C_c(ℝ, ℝ) → ℝ | IsPositiveCoordinate L} := by
  ext L
  constructor
  · rintro ⟨μ, rfl⟩
    exact coordinates_are_positive μ
  · intro h
    exact ⟨ofPositiveCoordinates L h, coordinates_ofPositiveCoordinates L h⟩

/-- All positive-linear coordinate constraints are closed in the full product. -/
theorem isClosed_positiveCoordinates :
    IsClosed {L : C_c(ℝ, ℝ) → ℝ | IsPositiveCoordinate L} := by
  have hadd : IsClosed {L : C_c(ℝ, ℝ) → ℝ | ∀ f g, L (f + g) = L f + L g} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun g =>
      isClosed_eq (continuous_apply (f + g)) ((continuous_apply f).add (continuous_apply g))
  have hsmul : IsClosed {L : C_c(ℝ, ℝ) → ℝ | ∀ (c : ℝ) f, L (c • f) = c • L f} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun c => isClosed_iInter fun f =>
      isClosed_eq (continuous_apply (c • f)) (continuous_const.mul (continuous_apply f))
  have hpos : IsClosed {L : C_c(ℝ, ℝ) → ℝ | ∀ f, 0 ≤ f → 0 ≤ L f} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun (_hf : 0 ≤ f) =>
      isClosed_le continuous_const (continuous_apply f)
  exact hadd.inter (hsmul.inter hpos)

theorem isClosed_range_coordinates : IsClosed (Set.range coordinates) := by
  rw [range_coordinates]
  exact isClosed_positiveCoordinates

/-- The vague state space is a genuine closed subspace of the coordinate product. -/
theorem isClosedEmbedding_coordinates : IsClosedEmbedding coordinates :=
  ⟨isEmbedding_coordinates, isClosed_range_coordinates⟩

end FixedCouplingPoisson.RealVagueMeasure
