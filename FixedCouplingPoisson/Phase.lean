import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Deterministic lift lemmas used in `lem:overshoot`, `prop:drift`, and `cor:restart`.
The canonical argument lift of the concrete transfer matrix is NOT constructed here.
`PhaseLift` records its deterministic lift properties; connection to `Transfer`
is an outstanding obligation, not an axiom or a completed manuscript lemma.
-/
namespace FixedCouplingPoisson

/-- An increasing lift with angular period π. -/
structure PhaseLift where
  toFun : ℝ → ℝ
  strictMono : StrictMono toFun
  equivariant : ∀ (x : ℝ) (k : ℤ), toFun (x + k * Real.pi) = toFun x + k * Real.pi

instance : CoeFun PhaseLift (fun _ => ℝ → ℝ) := ⟨PhaseLift.toFun⟩

/-- A nondecreasing degree-one CDF lift, allowing flat intervals. -/
structure CDFLift where
  toFun : ℝ → ℝ
  monotone : Monotone toFun
  equivariant : ∀ (x : ℝ) (k : ℤ), toFun (x + k * Real.pi) = toFun x + k * Real.pi
  normalized : toFun 0 = 0

instance : CoeFun CDFLift (fun _ => ℝ → ℝ) := ⟨CDFLift.toFun⟩

variable {F G : PhaseLift} {δ θ φ : ℝ}

/-- A completed integer period cannot be lost in the next step. -/
theorem gap_step_lower (horder : ∀ x, G x ≤ F x) (k : ℤ)
    (hgap : k * Real.pi ≤ θ - φ) : k * Real.pi ≤ F θ - G φ := by
  have hθ : φ + k * Real.pi ≤ θ := by linarith
  have h := F.strictMono.monotone hθ
  rw [F.equivariant] at h
  have := horder φ
  linarith

/-- A one-step overshoot uses only the perturbation at this step. -/
theorem gap_step_upper (hclose : ∀ x, F x - G x ≤ δ) (k : ℤ)
    (hgap : θ - φ < k * Real.pi) : F θ - G φ < k * Real.pi + δ := by
  have hθ : θ < φ + k * Real.pi := by linarith
  have h := F.strictMono hθ
  rw [F.equivariant] at h
  have := hclose φ
  linarith

theorem crossingCount_step_mono (horder : ∀ x, G x ≤ F x) :
    Int.floor ((θ - φ) / Real.pi) ≤ Int.floor ((F θ - G φ) / Real.pi) := by
  apply Int.le_floor.mpr
  apply (le_div_iff₀ Real.pi_pos).mpr
  apply gap_step_lower horder
  exact (le_div_iff₀ Real.pi_pos).mp (Int.floor_le _)

/-- Iterated real lift, in transfer-recursion order. -/
def orbit (F : ℝ → PhaseLift) (v : ℕ → ℝ) (θ : ℝ) : ℕ → ℝ
  | 0 => θ
  | n + 1 => F (v n) (orbit F v θ n)

@[simp] theorem orbit_zero (F : ℝ → PhaseLift) (v : ℕ → ℝ) (θ : ℝ) :
    orbit F v θ 0 = θ := rfl

@[simp] theorem orbit_succ (F : ℝ → PhaseLift) (v : ℕ → ℝ) (θ : ℝ) (n : ℕ) :
    orbit F v θ (n + 1) = F (v n) (orbit F v θ n) := rfl

theorem orbit_add_period (F : ℝ → PhaseLift) (v : ℕ → ℝ) (θ : ℝ) (k : ℤ) (n : ℕ) :
    orbit F v (θ + k * Real.pi) n = orbit F v θ n + k * Real.pi := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [orbit_succ, ih, (F (v n)).equivariant]

/-- Restarting at a path index uses the tail of the same potential sequence. -/
theorem orbit_restart (F : ℝ → PhaseLift) (v : ℕ → ℝ) (θ : ℝ) (t n : ℕ) :
    orbit F (fun j => v (t + j)) (orbit F v θ t) n = orbit F v θ (t + n) := by
  induction n with
  | zero => simp only [orbit_zero, Nat.add_zero]
  | succ n ih => simp only [orbit_succ, ih, Nat.add_succ]

def pairGap (F G : ℝ → PhaseLift) (v : ℕ → ℝ) (θ φ : ℝ) (n : ℕ) : ℝ :=
  orbit F v θ n - orbit G v φ n

theorem pairGap_nonneg (F G : ℝ → PhaseLift) (v : ℕ → ℝ) (θ φ : ℝ)
    (horder : ∀ v x, G v x ≤ F v x) (hinit : φ ≤ θ) (n : ℕ) :
    0 ≤ pairGap F G v θ φ n := by
  induction n with
  | zero => simpa [pairGap] using sub_nonneg.mpr hinit
  | succ n ih =>
    have h := gap_step_lower (θ := orbit F v θ n) (φ := orbit G v φ n) (horder (v n)) (0 : ℤ) (by simpa [pairGap] using ih)
    simpa [pairGap] using h

theorem pairCount_monotone (F G : ℝ → PhaseLift) (v : ℕ → ℝ) (θ φ : ℝ)
    (horder : ∀ v x, G v x ≤ F v x) :
    Monotone (fun n => Int.floor (pairGap F G v θ φ n / Real.pi)) := by
  apply monotone_nat_of_le_succ
  intro n
  exact crossingCount_step_mono (horder (v n))

/-- At a first-crossing step the overshoot is bounded independently of waiting time. -/
theorem pairGap_crossing_overshoot (F G : ℝ → PhaseLift) (v : ℕ → ℝ)
    (θ φ δ : ℝ) (hclose : ∀ v x, F v x - G v x ≤ δ) (m : ℤ) (n : ℕ)
    (hprev : pairGap F G v θ φ n < m * Real.pi)
    (hcross : m * Real.pi ≤ pairGap F G v θ φ (n + 1)) :
    m * Real.pi ≤ pairGap F G v θ φ (n + 1) ∧
      pairGap F G v θ φ (n + 1) ≤ m * Real.pi + δ := by
  exact ⟨hcross, (gap_step_upper (hclose (v n)) m hprev).le⟩

/-- Exact pathwise restart, removing completed integer periods. -/
theorem pairGap_restart (F G : ℝ → PhaseLift) (v : ℕ → ℝ) (θ φ : ℝ)
    (t n : ℕ) (k : ℤ) :
    pairGap F G (fun j => v (t + j)) (orbit F v θ t)
        (orbit G v φ t + k * Real.pi) n =
      pairGap F G v θ φ (t + n) - k * Real.pi := by
  unfold pairGap
  rw [orbit_add_period, orbit_restart, orbit_restart]
  ring

variable (H : CDFLift)

def CDFLift.cdfGap (θ φ : ℝ) : ℝ := H θ - H φ

theorem cdfGap_nonneg (h : φ ≤ θ) : 0 ≤ H.cdfGap θ φ :=
  sub_nonneg.mpr (H.monotone h)

theorem cdfGap_le_pi (h : θ - φ ≤ Real.pi) : H.cdfGap θ φ ≤ Real.pi := by
  have hx : θ ≤ φ + (1 : ℤ) * Real.pi := by simp only [Int.cast_one, one_mul]; linarith
  have hm := H.monotone hx
  rw [H.equivariant] at hm
  simp only [Int.cast_one, one_mul] at hm
  dsimp [CDFLift.cdfGap]
  linarith

theorem cdfGap_upper_deficit (θ d : ℝ) :
    Real.pi - H.cdfGap θ (θ - d) = H (θ + Real.pi - d) - H θ := by
  have h := H.equivariant (θ - d) 1
  simp only [Int.cast_one, one_mul] at h
  have harg : θ + Real.pi - d = θ - d + Real.pi := by ring
  rw [harg, h]
  dsimp [CDFLift.cdfGap]
  ring

theorem coordinate_error (H J : CDFLift) (θ φ a : ℝ)
    (hclose : |H φ - J φ| ≤ a) :
    |(H θ - J φ) - H.cdfGap θ φ| ≤ a := by
  simpa only [CDFLift.cdfGap, sub_sub_sub_cancel_left] using hclose

end FixedCouplingPoisson
