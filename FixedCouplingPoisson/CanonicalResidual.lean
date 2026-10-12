import FixedCouplingPoisson.PhaseWindow

/-! Actual crossing counts and oriented residuals on the original iid space. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set

def canonicalCrossingCount (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) : ℤ :=
  ⌊canonicalGapProcess E δ θ φ n ω / Real.pi⌋

def canonicalCrossingResidual (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) : ℝ :=
  canonicalGapProcess E δ θ φ n ω -
    Real.pi * (canonicalCrossingCount E δ θ φ n ω : ℝ)

theorem canonicalCrossingCount_past_measurable (E δ θ φ : ℝ) (n : ℕ) :
    Measurable[pastMeasurableSpace n] (canonicalCrossingCount E δ θ φ n) := by
  letI : MeasurableSpace PotentialSpace := pastMeasurableSpace n
  exact (((canonicalPhaseProcess_past_measurable E θ n).sub
    (canonicalPhaseProcess_past_measurable (E + δ) φ n)).div_const Real.pi).floor

theorem canonicalCrossingCount_measurable (E δ θ φ : ℝ) (n : ℕ) :
    Measurable (canonicalCrossingCount E δ θ φ n) :=
  (canonicalCrossingCount_past_measurable E δ θ φ n).mono
    (pastMeasurableSpace_le n) le_rfl

theorem canonicalCrossingResidual_past_measurable (E δ θ φ : ℝ) (n : ℕ) :
    Measurable[pastMeasurableSpace n] (canonicalCrossingResidual E δ θ φ n) := by
  have hk : Measurable[pastMeasurableSpace n]
      (fun ω => (canonicalCrossingCount E δ θ φ n ω : ℝ)) :=
    (measurable_of_countable (fun k : ℤ => (k : ℝ))).comp
      (canonicalCrossingCount_past_measurable E δ θ φ n)
  exact ((canonicalPhaseProcess_past_measurable E θ n).sub
    (canonicalPhaseProcess_past_measurable (E + δ) φ n)).sub (hk.const_mul Real.pi)

theorem canonicalCrossingResidual_measurable (E δ θ φ : ℝ) (n : ℕ) :
    Measurable (canonicalCrossingResidual E δ θ φ n) :=
  (canonicalCrossingResidual_past_measurable E δ θ φ n).mono
    (pastMeasurableSpace_le n) le_rfl

theorem canonicalCrossingResidual_mem (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) :
    canonicalCrossingResidual E δ θ φ n ω ∈ Ico 0 Real.pi := by
  have hlo := Int.floor_le (canonicalGapProcess E δ θ φ n ω / Real.pi)
  have hhi := Int.lt_floor_add_one (canonicalGapProcess E δ θ φ n ω / Real.pi)
  have hmul := div_mul_cancel₀ (canonicalGapProcess E δ θ φ n ω) Real.pi_ne_zero
  have hlo' := mul_le_mul_of_nonneg_right hlo Real.pi_pos.le
  have hhi' := mul_lt_mul_of_pos_right hhi Real.pi_pos
  unfold canonicalCrossingResidual canonicalCrossingCount
  constructor <;> nlinarith

theorem canonicalCrossing_gap_decomposition (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) :
    canonicalGapProcess E δ θ φ n ω =
      Real.pi * (canonicalCrossingCount E δ θ φ n ω : ℝ) +
        canonicalCrossingResidual E δ θ φ n ω := by
  unfold canonicalCrossingResidual
  ring

theorem actualWindowWinding_eq_canonicalCrossingCount (e : ℕ → ℕ → ℝ)
    (n i : ℕ) (ω : PotentialSpace) :
    actualWindowWinding e n i ω =
      canonicalCrossingCount (e n i) (e n (i + 1) - e n i) 0 0 n ω :=
  actualWindowWinding_eq_canonicalGap_floor e n i ω

theorem actualWindowResidual_eq_canonicalCrossingResidual (e : ℕ → ℕ → ℝ)
    (n i : ℕ) (ω : PotentialSpace) :
    actualWindowResidual e n i ω =
      canonicalCrossingResidual (e n i) (e n (i + 1) - e n i) 0 0 n ω :=
  actualWindowResidual_eq_canonicalGap_residual e n i ω

end FixedCouplingPoisson.Furstenberg
