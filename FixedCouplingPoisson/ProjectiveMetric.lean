import FixedCouplingPoisson.AngleProjective
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
Work draft: triangle and energy perturbation for the genuine determinant
distance, obtained through the checked actual angular parametrization.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open Real

theorem euclideanNorm_angularUnit (θ : ℝ) : euclideanNorm (angleVector θ) = 1 := by
  change Real.sqrt (Real.cos θ ^ 2 + Real.sin θ ^ 2) = 1
  have h : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [h, Real.sqrt_one]

theorem projectiveDistance_phaseProjective (θ φ : ℝ) :
    projectiveDistance (phaseProjective θ) (phaseProjective φ) = |Real.sin (φ - θ)| := by
  unfold phaseProjective
  rw [projectiveDistance_mk, determinantDistance, wedge_angleVector,
    euclideanNorm_angularUnit, euclideanNorm_angularUnit]
  simp

theorem projectiveDistance_triangle (p q r : ProjectivePoint) :
    projectiveDistance p r ≤ projectiveDistance p q + projectiveDistance q r := by
  obtain ⟨α, rfl⟩ := phaseProjective_surjective p
  obtain ⟨β, rfl⟩ := phaseProjective_surjective q
  obtain ⟨γ, rfl⟩ := phaseProjective_surjective r
  simp only [projectiveDistance_phaseProjective]
  have h : γ - α = (γ - β) + (β - α) := by ring
  rw [h, Real.sin_add]
  calc
    _ ≤ |Real.sin (γ - β) * Real.cos (β - α)| +
        |Real.cos (γ - β) * Real.sin (β - α)| := abs_add_le _ _
    _ = |Real.sin (γ - β)| * |Real.cos (β - α)| +
        |Real.cos (γ - β)| * |Real.sin (β - α)| := by rw [abs_mul, abs_mul]
    _ ≤ |Real.sin (γ - β)| * 1 + 1 * |Real.sin (β - α)| :=
      add_le_add
        (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _) (abs_nonneg _))
    _ = _ := by ring

theorem phaseProjective_canonicalPhase (E v θ : ℝ) :
    phaseProjective (canonicalPhase E v θ) = transferProjective E v (phaseProjective θ) :=
  canonicalPhase_projective E v θ

theorem projectiveDistance_transfer_energy_le (E E' v : ℝ) (p : ProjectivePoint) :
    projectiveDistance (transferProjective E v p) (transferProjective E' v p) ≤ |E - E'| := by
  obtain ⟨θ, rfl⟩ := phaseProjective_surjective p
  rw [← phaseProjective_canonicalPhase, ← phaseProjective_canonicalPhase,
    projectiveDistance_phaseProjective]
  have h := Real.abs_sin_le_abs (x := canonicalPhase E' v θ - canonicalPhase E v θ)
  have hc := canonicalPhase_energy_abs_le E' E v θ
  exact h.trans (by simpa only [abs_sub_comm E' E] using hc)

theorem projectiveDistance_transfer_pair_energy_le (E E' v : ℝ) (p q : ProjectivePoint) :
    projectiveDistance (transferProjective E v p) (transferProjective E' v q) ≤
      projectiveDistance (transferProjective E v p) (transferProjective E v q) + |E - E'| :=
  (projectiveDistance_triangle (transferProjective E v p) (transferProjective E v q)
    (transferProjective E' v q)).trans
      (add_le_add le_rfl (projectiveDistance_transfer_energy_le E E' v q))

end FixedCouplingPoisson.Furstenberg
