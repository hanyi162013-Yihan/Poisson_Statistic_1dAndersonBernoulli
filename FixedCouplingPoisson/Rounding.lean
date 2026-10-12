import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Integer carries and terminal spectral rounding

These are deterministic algebraic lemmas used in the joint floor identity and
in the exact terminal rounding error. No Sturm theorem or stochastic convergence
is assumed or proved in this module.
-/

open scoped BigOperators

namespace FixedCouplingPoisson

/-- Adding a residual in `[0,1]` can raise the integer ceiling by at most one. -/
theorem ceil_residual_bounds (θ r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ ⌈θ + r⌉ - ⌈θ⌉ ∧ ⌈θ + r⌉ - ⌈θ⌉ ≤ 1 := by
  have hlo := Int.ceil_mono (show θ ≤ θ + r by linarith)
  have hhi := Int.ceil_mono (show θ + r ≤ θ + 1 by linarith)
  rw [Int.ceil_add_one] at hhi
  omega

/-- The terminal rounding discrepancy is exactly zero or one, including all
possible boundary equalities. -/
theorem ceil_residual_zero_or_one (θ r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ⌈θ + r⌉ - ⌈θ⌉ = 0 ∨ ⌈θ + r⌉ - ⌈θ⌉ = 1 := by
  obtain ⟨hlo, hhi⟩ := ceil_residual_bounds θ r hr0 hr1
  omega

@[simp] theorem ceil_zero_residual (θ : ℝ) : ⌈θ + (0 : ℝ)⌉ - ⌈θ⌉ = 0 := by simp

/-- The integer winding separates exactly from terminal rounding. -/
theorem ceil_winding_residual (θ r : ℝ) (k : ℤ) :
    (⌈θ + (k : ℝ) + r⌉ - ⌈θ⌉) - k = ⌈θ + r⌉ - ⌈θ⌉ := by
  have heq : θ + (k : ℝ) + r = (θ + r) + (k : ℝ) := by ring
  rw [heq, Int.ceil_add_intCast]
  omega

/-- A discrepancy occurs precisely when an integer cut lies in the increasing
half-open interval `[θ, θ+r)`. The half-open convention treats atoms exactly. -/
theorem ceil_residual_eq_one_iff_cut (θ r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ⌈θ + r⌉ - ⌈θ⌉ = 1 ↔ ∃ z : ℤ, θ ≤ (z : ℝ) ∧ (z : ℝ) < θ + r := by
  constructor
  · intro h
    refine ⟨⌈θ⌉, Int.le_ceil θ, ?_⟩
    apply Int.lt_ceil.mp
    omega
  · rintro ⟨z, hz0, hz1⟩
    have hceil : ⌈θ⌉ ≤ z := Int.ceil_le.mpr hz0
    have hreal : (⌈θ⌉ : ℝ) < θ + r := lt_of_le_of_lt (by exact_mod_cast hceil) hz1
    have hlt : ⌈θ⌉ < ⌈θ + r⌉ := Int.lt_ceil.mpr hreal
    obtain ⟨_, hhi⟩ := ceil_residual_bounds θ r hr0 hr1
    omega

/-- Finite sums of winding integers separate from their residual carry. -/
theorem floor_sum_winding_residual {ι : Type*} (s : Finset ι)
    (K : ι → ℤ) (R : ι → ℝ) :
    ⌊∑ i ∈ s, ((K i : ℝ) + R i)⌋ - ∑ i ∈ s, K i = ⌊∑ i ∈ s, R i⌋ := by
  rw [Finset.sum_add_distrib]
  have hcast : (∑ i ∈ s, (K i : ℝ)) = ((∑ i ∈ s, K i : ℤ) : ℝ) := by
    simp
  rw [hcast, Int.floor_intCast_add]
  omega

/-- Nonnegative oriented residuals give a nonnegative total carry. -/
theorem floor_sum_residual_nonneg {ι : Type*} (s : Finset ι) (R : ι → ℝ)
    (hR : ∀ i ∈ s, 0 ≤ R i) : 0 ≤ ⌊∑ i ∈ s, R i⌋ := by
  exact Int.floor_nonneg.mpr (Finset.sum_nonneg hR)

/-- The floor carry identity in angular units. -/
theorem floor_scaled_sum_winding_residual {ι : Type*} (s : Finset ι)
    (K : ι → ℤ) (R : ι → ℝ) {p : ℝ} (hp : p ≠ 0) :
    ⌊(∑ i ∈ s, (p * (K i : ℝ) + R i)) / p⌋ - ∑ i ∈ s, K i =
      ⌊(∑ i ∈ s, R i) / p⌋ := by
  have heq : (∑ i ∈ s, (p * (K i : ℝ) + R i)) / p =
      ∑ i ∈ s, ((K i : ℝ) + R i / p) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [hp]
  rw [heq]
  simpa only [Finset.sum_div] using floor_sum_winding_residual s K (fun i ↦ R i / p)

/-- Exact winding separation before dividing an angular phase by its period. -/
theorem ceil_angular_winding_residual (θ cut r : ℝ) (k : ℤ)
    {p : ℝ} (hp : p ≠ 0) :
    (⌈(θ + p * (k : ℝ) + r - cut) / p⌉ - ⌈(θ - cut) / p⌉) - k =
      ⌈(θ - cut) / p + r / p⌉ - ⌈(θ - cut) / p⌉ := by
  have heq : (θ + p * (k : ℝ) + r - cut) / p =
      (θ - cut) / p + (k : ℝ) + r / p := by
    field_simp [hp]
    <;> ring
  rw [heq]
  exact ceil_winding_residual ((θ - cut) / p) (r / p) k

/-- The terminal spectral rounding discrepancy is zero or one in angular units.
The period can in particular be `π`, and the Dirichlet cut can be `π/2`. -/
theorem ceil_angular_residual_zero_or_one (θ cut r : ℝ) (k : ℤ)
    {p : ℝ} (hp : 0 < p) (hr0 : 0 ≤ r) (hrp : r ≤ p) :
    ((⌈(θ + p * (k : ℝ) + r - cut) / p⌉ - ⌈(θ - cut) / p⌉) - k = 0) ∨
    ((⌈(θ + p * (k : ℝ) + r - cut) / p⌉ - ⌈(θ - cut) / p⌉) - k = 1) := by
  rw [ceil_angular_winding_residual θ cut r k (ne_of_gt hp)]
  exact ceil_residual_zero_or_one ((θ - cut) / p) (r / p)
    (div_nonneg hr0 hp.le) ((div_le_one hp).mpr hrp)

/-- In particular, nonnegative oriented angular residuals yield a nonnegative
carry after dividing by a positive period. -/
theorem floor_scaled_sum_residual_nonneg {ι : Type*} (s : Finset ι) (R : ι → ℝ)
    {p : ℝ} (hp : 0 < p) (hR : ∀ i ∈ s, 0 ≤ R i) :
    0 ≤ ⌊(∑ i ∈ s, R i) / p⌋ := by
  exact Int.floor_nonneg.mpr (div_nonneg (Finset.sum_nonneg hR) hp.le)

end FixedCouplingPoisson
