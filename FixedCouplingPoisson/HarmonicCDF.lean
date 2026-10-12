import FixedCouplingPoisson.CDFWinding
import Mathlib.MeasureTheory.Integral.Prod

/-!
Work draft: inverse stationarity gives the exact mean gap identity of the
actual CDF lift. Integer transport retains all angular cut corrections.
Stationarity is used as the precisely authorized qualitative Furstenberg
input; the harmonic identity itself is proved from actual matrix actions.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Real Set Matrix
open scoped Topology
local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

theorem transferProjective_transferInverse (E v : ℝ) (p : ProjectivePoint) :
    transferProjective E v (transferInverseProjective E v p) = p := by
  rw [← Projectivization.mk_rep p, transferInverseProjective_mk, transferProjective_mk]
  apply (Projectivization.mk_eq_mk_iff' ℝ _ _ _ _).mpr
  refine ⟨1, ?_⟩
  simp only [one_smul, Matrix.mulVec_mulVec, transfer_mul_transferInv, Matrix.one_mulVec]

theorem canonicalPhase_inverse_coordinate (E v : ℝ) (p : ProjectivePoint) :
    ∃ k : ℤ,
      canonicalPhase E v (projectiveCoordinate (transferInverseProjective E v p)) =
        projectiveCoordinate p + k * Real.pi := by
  have hproj :
      phaseProjective (canonicalPhase E v (projectiveCoordinate (transferInverseProjective E v p))) =
        phaseProjective (projectiveCoordinate p) := by
    have hcanon :
        phaseProjective (canonicalPhase E v (projectiveCoordinate (transferInverseProjective E v p))) =
          transferProjective E v (phaseProjective (projectiveCoordinate (transferInverseProjective E v p))) :=
      canonicalPhase_projective E v _
    rw [phaseProjective_projectiveCoordinate, transferProjective_transferInverse] at hcanon
    exact hcanon.trans (phaseProjective_projectiveCoordinate p).symm
  have hcoe := (phaseProjective_eq_iff_coe _ _).mp hproj
  have hm := QuotientAddGroup.eq_iff_sub_mem.mp hcoe
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  rw [zsmul_eq_mul] at hk
  exact ⟨k, by linarith⟩

theorem indexObservable_transport_difference (E v θ φ : ℝ) (p : ProjectivePoint) :
    indexObservable (canonicalPhase E v θ) p - indexObservable (canonicalPhase E v φ) p =
      indexObservable θ (transferInverseProjective E v p) -
        indexObservable φ (transferInverseProjective E v p) := by
  obtain ⟨k, hk⟩ := canonicalPhase_inverse_coordinate E v p
  simpa only [indexObservable, Int.cast_sub, canonicalPhaseLift] using congrArg (fun n : ℤ => (n : ℝ))
    (angularIndex_transport_difference (canonicalPhaseLift E v) θ φ
      (projectiveCoordinate p) (projectiveCoordinate (transferInverseProjective E v p)) k hk)

theorem stationaryCDFLift_transferred_gap (ν : ProbabilityMeasure ProjectivePoint)
    (E v θ φ : ℝ) :
    stationaryCDFLift ν (canonicalPhase E v θ) - stationaryCDFLift ν (canonicalPhase E v φ) =
      Real.pi * (∫ p, indexObservable θ (transferInverseProjective E v p) -
        indexObservable φ (transferInverseProjective E v p) ∂(ν : Measure ProjectivePoint)) := by
  rw [stationaryCDFLift_difference_integral_index]
  congr 1
  apply integral_congr_ae
  exact ae_of_all _ (indexObservable_transport_difference E v θ φ)

theorem integrable_inverse_index_difference (law : PotentialLaw) (E θ φ : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) :
    Integrable (fun z : ℝ × ProjectivePoint =>
      indexObservable θ (inverseStep E z) - indexObservable φ (inverseStep E z))
      (inputDistribution law ν : Measure (ℝ × ProjectivePoint)) := by
  apply (integrable_const (|(Int.floor (θ / Real.pi) : ℝ)| + 1 +
    (|(Int.floor (φ / Real.pi) : ℝ)| + 1))).mono'
  · exact (((measurable_indexObservable θ).comp (measurable_inverseStep E)).sub
      ((measurable_indexObservable φ).comp (measurable_inverseStep E))).aestronglyMeasurable
  · exact ae_of_all _ fun z => (norm_sub_le _ _).trans
      (add_le_add (norm_indexObservable_le θ _) (norm_indexObservable_le φ _))

/-- The exact gap identity holds for arbitrary real lifts, including all
wrapped arcs and all complete periods. -/
theorem inverse_stationary_exact_gap (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (hν : InverseStationary law E ν) (θ φ : ℝ) :
    (∫ v, stationaryCDFLift ν (canonicalPhase E v θ) -
      stationaryCDFLift ν (canonicalPhase E v φ) ∂law.measure) =
        stationaryCDFLift ν θ - stationaryCDFLift ν φ := by
  have hstat := inverse_stationary_integral law E ν hν
    (fun p => indexObservable θ p - indexObservable φ p)
    ((measurable_indexObservable θ).sub (measurable_indexObservable φ))
  calc
    _ = ∫ v, Real.pi * (∫ p, indexObservable θ (transferInverseProjective E v p) -
        indexObservable φ (transferInverseProjective E v p) ∂(ν : Measure ProjectivePoint))
        ∂law.measure := by
      apply integral_congr_ae
      exact ae_of_all _ fun v => stationaryCDFLift_transferred_gap ν E v θ φ
    _ = Real.pi * (∫ v, ∫ p, indexObservable θ (transferInverseProjective E v p) -
        indexObservable φ (transferInverseProjective E v p) ∂(ν : Measure ProjectivePoint)
        ∂law.measure) := integral_const_mul _ _
    _ = Real.pi * (∫ z : ℝ × ProjectivePoint,
        indexObservable θ (inverseStep E z) - indexObservable φ (inverseStep E z)
        ∂(inputDistribution law ν : Measure (ℝ × ProjectivePoint))) := by
      congr 1
      exact (integral_prod _ (integrable_inverse_index_difference law E θ φ ν)).symm
    _ = Real.pi * (∫ p, indexObservable θ p - indexObservable φ p
        ∂(ν : Measure ProjectivePoint)) := congrArg (fun x => Real.pi * x) hstat.symm
    _ = _ := (stationaryCDFLift_difference_integral_index ν θ φ).symm

end FixedCouplingPoisson.Furstenberg
