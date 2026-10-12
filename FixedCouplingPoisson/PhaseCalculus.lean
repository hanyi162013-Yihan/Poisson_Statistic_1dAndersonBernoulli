import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
A concrete local argument chart for the Schrödinger transfer action.
The global canonical lift, and its compatibility across the chart cuts, are
separate outstanding obligations. All derivatives in this module are actual
`HasDerivAt` statements about explicit real functions.
-/
namespace FixedCouplingPoisson
open Real Set

/-- On the chart `-π/2 < θ < π/2`, this is the angle in `(0,π)` of
`((E-v) cos θ - sin θ, cos θ)`. -/
noncomputable def chartPhase (E v θ : ℝ) : ℝ :=
  Real.pi / 2 - arctan ((E - v) - tan θ)

theorem chartPhase_mem (E v θ : ℝ) : chartPhase E v θ ∈ Ioo 0 Real.pi := by
  have h₁ := arctan_lt_pi_div_two ((E - v) - tan θ)
  have h₂ := neg_pi_div_two_lt_arctan ((E - v) - tan θ)
  constructor <;> dsimp [chartPhase] <;> linarith

theorem chartPhase_strictAnti_energy (v θ : ℝ) : StrictAnti (fun E => chartPhase E v θ) := by
  intro E E' h
  have := arctan_strictMono (show (E - v) - tan θ < (E' - v) - tan θ by linarith)
  dsimp [chartPhase]
  linarith

theorem chartPhase_strictMono_angle (E v : ℝ) :
    StrictMonoOn (chartPhase E v) (Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  intro θ hθ φ hφ h
  have htan := strictMonoOn_tan hθ hφ h
  have := arctan_strictMono (show (E - v) - tan φ < (E - v) - tan θ by linarith)
  dsimp [chartPhase]
  linarith

theorem chartPhase_hasDerivAt_energy (E v θ : ℝ) :
    HasDerivAt (fun e => chartPhase e v θ)
      (-(1 / (1 + ((E - v) - tan θ) ^ 2))) E := by
  have hlin : HasDerivAt (fun e : ℝ => (e - v) - tan θ) 1 E := by
    exact ((hasDerivAt_id E).sub_const v).sub_const (tan θ)
  simpa only [chartPhase, mul_one] using hlin.arctan.const_sub (Real.pi / 2)

theorem chartPhase_energy_slope_bound (E v θ : ℝ) :
    |-(1 / (1 + ((E - v) - tan θ) ^ 2))| ≤ 1 := by
  have hsq := sq_nonneg ((E - v) - tan θ)
  have hden : 0 < 1 + ((E - v) - tan θ) ^ 2 := by linarith
  rw [abs_neg, abs_of_nonneg (div_nonneg zero_le_one hden.le)]
  exact (div_le_one hden).mpr (by linarith)

/-- Integrating the actual energy derivative gives the chart perturbation bound. -/
theorem chartPhase_energy_close (E v θ δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ chartPhase E v θ - chartPhase (E + δ) v θ ∧
      chartPhase E v θ - chartPhase (E + δ) v θ ≤ δ := by
  have hlo : 0 ≤ chartPhase E v θ - chartPhase (E + δ) v θ :=
    sub_nonneg.mpr ((chartPhase_strictAnti_energy v θ).antitone (by linarith))
  have habs : |chartPhase (E + δ) v θ - chartPhase E v θ| ≤ |(E + δ) - E| := by
    have hb :=
      (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun e _ => (chartPhase_hasDerivAt_energy e v θ).hasDerivWithinAt)
        (fun e _ => by simpa only [Real.norm_eq_abs] using chartPhase_energy_slope_bound e v θ)
        (mem_univ E) (mem_univ (E + δ))
    simpa only [Real.norm_eq_abs, one_mul] using hb
  have harg : (E + δ) - E = δ := by ring
  rw [harg, abs_of_nonneg hδ, abs_sub_comm,
    abs_of_nonneg hlo] at habs
  exact ⟨hlo, habs⟩

/-- The actual squared Euclidean norm of the transfer image of a unit angle. -/
noncomputable def transferAngleNormSq (E v θ : ℝ) : ℝ :=
  ((E - v) * cos θ - sin θ)^2 + cos θ ^ 2

theorem transferAngleNormSq_pos (E v θ : ℝ) : 0 < transferAngleNormSq E v θ := by
  have hs := sin_sq_add_cos_sq θ
  by_cases hc : cos θ = 0
  · dsimp [transferAngleNormSq]
    simp only [hc, mul_zero, zero_sub, neg_sq]
    nlinarith
  · exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hc)

theorem transferAngleNormSq_ge_cos_sq (E v θ : ℝ) :
    cos θ ^ 2 ≤ transferAngleNormSq E v θ := by
  dsimp [transferAngleNormSq]
  linarith [sq_nonneg ((E - v) * cos θ - sin θ)]

/-- Algebraic bound for the energy-derivative expression at all angles,
including the chart boundary where `cos θ = 0`. -/
theorem transfer_energy_derivative_expression_bounds (E v θ : ℝ) :
    0 ≤ cos θ ^ 2 / transferAngleNormSq E v θ ∧
      cos θ ^ 2 / transferAngleNormSq E v θ ≤ 1 := by
  exact ⟨div_nonneg (sq_nonneg _) (transferAngleNormSq_pos E v θ).le,
    (div_le_one (transferAngleNormSq_pos E v θ)).mpr (transferAngleNormSq_ge_cos_sq E v θ)⟩

end FixedCouplingPoisson
