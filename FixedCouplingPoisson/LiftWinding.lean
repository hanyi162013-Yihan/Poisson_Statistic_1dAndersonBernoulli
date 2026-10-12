import FixedCouplingPoisson.Phase
import Mathlib.MeasureTheory.Function.Floor

/-!
Work draft. Integer crossing counts for increasing degree-one lifts keep the
cut correction explicit in the inverse-stationary harmonic identity.
-/
namespace FixedCouplingPoisson
open Real Set

noncomputable def angularIndex (θ a : ℝ) : ℤ := Int.floor ((θ - a) / Real.pi)

theorem angularIndex_add_int (θ a : ℝ) (k : ℤ) :
    angularIndex (θ + k * Real.pi) a = angularIndex θ a + k := by
  unfold angularIndex
  have h : (θ + (k : ℝ) * Real.pi - a) / Real.pi = (θ - a) / Real.pi + k := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [h, Int.floor_add_intCast]

theorem angularIndex_shift_base (θ a : ℝ) (k : ℤ) :
    angularIndex θ (a + k * Real.pi) = angularIndex θ a - k := by
  unfold angularIndex
  have h : (θ - (a + (k : ℝ) * Real.pi)) / Real.pi = (θ - a) / Real.pi - k := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [h, Int.floor_sub_intCast]

theorem angularIndex_fundamental_of_le {θ a : ℝ}
    (hθ : θ ∈ Ico 0 Real.pi) (ha : a ∈ Ico 0 Real.pi) (hle : a ≤ θ) :
    angularIndex θ a = 0 := by
  apply Int.floor_eq_iff.mpr
  constructor
  · exact (le_div_iff₀ Real.pi_pos).mpr (by simp only [Int.cast_zero, zero_mul]; linarith)
  · exact (div_lt_iff₀ Real.pi_pos).mpr (by simp only [Int.cast_zero, zero_add, one_mul]; linarith [hθ.2, ha.1])

theorem angularIndex_fundamental_of_gt {θ a : ℝ}
    (hθ : θ ∈ Ico 0 Real.pi) (ha : a ∈ Ico 0 Real.pi) (hgt : θ < a) :
    angularIndex θ a = -1 := by
  apply Int.floor_eq_iff.mpr
  constructor
  · exact (le_div_iff₀ Real.pi_pos).mpr (by norm_num; linarith [hθ.1, ha.2])
  · exact (div_lt_iff₀ Real.pi_pos).mpr (by norm_num; linarith)

theorem angularIndex_bounds (θ a : ℝ) (ha : a ∈ Ico 0 Real.pi) :
    Int.floor (θ / Real.pi) - 1 ≤ angularIndex θ a ∧
      angularIndex θ a ≤ Int.floor (θ / Real.pi) := by
  constructor
  · have h := Int.floor_mono
      (div_le_div_of_nonneg_right (show θ - Real.pi ≤ θ - a by linarith [ha.2]) Real.pi_pos.le)
    have heq : (θ - Real.pi) / Real.pi = θ / Real.pi - (1 : ℤ) := by
      field_simp [Real.pi_ne_zero]
      norm_num
    rw [heq, Int.floor_sub_intCast] at h
    exact h
  · exact Int.floor_mono
      (div_le_div_of_nonneg_right (show θ - a ≤ θ by linarith [ha.1]) Real.pi_pos.le)

/-- The integer origin correction is independent of the tested angle. -/
theorem angularIndex_transport (F : PhaseLift) (θ a b : ℝ) (k : ℤ)
    (hFb : F b = a + k * Real.pi) :
    angularIndex (F θ) a = angularIndex θ b + k := by
  let n := angularIndex θ b
  have hlo : b + (n : ℝ) * Real.pi ≤ θ := by
    have h := (le_div_iff₀ Real.pi_pos).mp (Int.floor_le ((θ - b) / Real.pi))
    change b + (Int.floor ((θ - b) / Real.pi) : ℝ) * Real.pi ≤ θ
    linarith
  have hhi : θ < b + ((n : ℝ) + 1) * Real.pi := by
    have h := (div_lt_iff₀ Real.pi_pos).mp (Int.lt_floor_add_one ((θ - b) / Real.pi))
    change θ < b + ((Int.floor ((θ - b) / Real.pi) : ℝ) + 1) * Real.pi
    linarith
  have hlow := F.strictMono.monotone hlo
  rw [F.equivariant, hFb] at hlow
  have hhi' : θ < b + ((n + 1 : ℤ) : ℝ) * Real.pi := by simpa only [Int.cast_add, Int.cast_one] using hhi
  have hupp' := F.strictMono hhi'
  rw [F.equivariant, hFb] at hupp'
  simp only [Int.cast_add, Int.cast_one] at hupp'
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ Real.pi_pos).mpr
    push_cast
    change ((n : ℝ) + k) * Real.pi ≤ F θ - a
    nlinarith [hlow]
  · apply (div_lt_iff₀ Real.pi_pos).mpr
    push_cast
    change F θ - a < ((n : ℝ) + k + 1) * Real.pi
    nlinarith [hupp']

theorem angularIndex_transport_difference (F : PhaseLift) (θ φ a b : ℝ) (k : ℤ)
    (hFb : F b = a + k * Real.pi) :
    angularIndex (F θ) a - angularIndex (F φ) a = angularIndex θ b - angularIndex φ b := by
  rw [angularIndex_transport F θ a b k hFb, angularIndex_transport F φ a b k hFb]
  omega

end FixedCouplingPoisson
