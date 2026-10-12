import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Equal integer block partitions and their scaled times

The endpoint of block b is floor(b*N/m). Rounding changes each scaled
endpoint by at most p, and p tends to zero in the model application.
All results concern explicit integer times, not a probabilistic interface.
-/
noncomputable section
namespace FixedCouplingPoisson
open Filter
open scoped Topology BigOperators

def equalBlockEndpoint (m b N : ℕ) : ℕ := b * N / m

def equalBlockLength (m b N : ℕ) : ℕ :=
  equalBlockEndpoint m (b + 1) N - equalBlockEndpoint m b N

@[simp] theorem equalBlockEndpoint_zero (m N : ℕ) : equalBlockEndpoint m 0 N = 0 := by
  simp [equalBlockEndpoint]

@[simp] theorem equalBlockEndpoint_last {m : ℕ} (hm : 0 < m) (N : ℕ) :
    equalBlockEndpoint m m N = N :=
  Nat.mul_div_cancel_left N hm

theorem equalBlockEndpoint_monotone (m N : ℕ) :
    Monotone (fun b => equalBlockEndpoint m b N) := by
  intro b c hbc
  exact Nat.div_le_div_right (Nat.mul_le_mul_right N hbc)

theorem equalBlockEndpoint_le_total {m b : ℕ} (hm : 0 < m) (hbm : b ≤ m) (N : ℕ) :
    equalBlockEndpoint m b N ≤ N := by
  simpa only [equalBlockEndpoint_last hm] using equalBlockEndpoint_monotone m N hbm

theorem equalBlockEndpoint_add_length (m b N : ℕ) :
    equalBlockEndpoint m b N + equalBlockLength m b N = equalBlockEndpoint m (b + 1) N :=
  Nat.add_sub_of_le (equalBlockEndpoint_monotone m N (Nat.le_succ b))

theorem equalBlockLength_sum {m : ℕ} (hm : 0 < m) (N : ℕ) :
    (∑ b ∈ Finset.range m, equalBlockLength m b N) = N := by
  simpa only [equalBlockLength, equalBlockEndpoint_last hm,
    equalBlockEndpoint_zero, Nat.sub_zero] using
    Finset.sum_range_tsub (equalBlockEndpoint_monotone m N) m

/-- Every block has at least floor(N/m) sites. -/
theorem equalBlockLength_ge_div (m b N : ℕ) : N / m ≤ equalBlockLength m b N := by
  have h : b * N / m + N / m ≤ (b * N + N) / m := Nat.div_add_div_le_add_div
  unfold equalBlockLength equalBlockEndpoint
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem equalBlockEndpoint_cast_eq {m : ℕ} (hm : 0 < m) (b N : ℕ) :
    (equalBlockEndpoint m b N : ℝ) =
      (b : ℝ) * (N : ℝ) / (m : ℝ) - ((b * N % m : ℕ) : ℝ) / (m : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  have hcast : ((b * N % m : ℕ) : ℝ) +
      (m : ℝ) * (equalBlockEndpoint m b N : ℝ) = (b : ℝ) * (N : ℝ) := by
    exact_mod_cast Nat.mod_add_div (b * N) m
  rw [← sub_div, eq_div_iff hmR]
  nlinarith

/-- The sole rounding error needed downstream is at most one site. -/
theorem equalBlockEndpoint_cast_error_le_one {m : ℕ} (hm : 0 < m) (b N : ℕ) :
    |(equalBlockEndpoint m b N : ℝ) - (b : ℝ) * (N : ℝ) / (m : ℝ)| ≤ 1 := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hmod : ((b * N % m : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.mod_lt (b * N) hm).le
  have hnonneg : 0 ≤ ((b * N % m : ℕ) : ℝ) / (m : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hmR.le
  have heq : (equalBlockEndpoint m b N : ℝ) - (b : ℝ) * (N : ℝ) / (m : ℝ) =
      -(((b * N % m : ℕ) : ℝ) / (m : ℝ)) := by
    rw [equalBlockEndpoint_cast_eq hm]
    ring
  rw [heq, abs_neg, abs_of_nonneg hnonneg]
  exact (div_le_one hmR).mpr hmod

theorem equalBlockEndpoint_scaled_error_le {m : ℕ} (hm : 0 < m) (b N : ℕ)
    {p : ℝ} (hp : 0 ≤ p) :
    |p * (equalBlockEndpoint m b N : ℝ) - (b : ℝ) * (p * (N : ℝ)) / (m : ℝ)| ≤ p := by
  have heq : p * (equalBlockEndpoint m b N : ℝ) -
      (b : ℝ) * (p * (N : ℝ)) / (m : ℝ) =
      p * ((equalBlockEndpoint m b N : ℝ) - (b : ℝ) * (N : ℝ) / (m : ℝ)) := by ring
  rw [heq, abs_mul, abs_of_nonneg hp]
  calc
    _ ≤ p * 1 := mul_le_mul_of_nonneg_left (equalBlockEndpoint_cast_error_le_one hm b N) hp
    _ = p := mul_one _

/-- Fixed positive-index endpoints diverge for every diverging total length. -/
theorem equalBlockEndpoint_tendsto_atTop {m b : ℕ} (hm : 0 < m) (hb : 0 < b)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => equalBlockEndpoint m b (N n)) atTop atTop := by
  have hmul : Tendsto (fun n => b * N n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left (N n) hb) hN
  exact (Nat.tendsto_div_const_atTop (Nat.ne_of_gt hm)).comp hmul

/-- Every individual block diverges, including the first one. -/
theorem equalBlockLength_tendsto_atTop {m : ℕ} (hm : 0 < m) (b : ℕ)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    Tendsto (fun n => equalBlockLength m b (N n)) atTop atTop :=
  tendsto_atTop_mono (fun n => equalBlockLength_ge_div m b (N n))
    ((Nat.tendsto_div_const_atTop (Nat.ne_of_gt hm)).comp hN)

/-- A vanishing lattice scale removes the endpoint rounding error. -/
theorem equalBlockEndpoint_scaled_tendsto {m : ℕ} (hm : 0 < m) (b : ℕ)
    {N : ℕ → ℕ} {p : ℕ → ℝ} {w : ℝ} (hp : ∀ n, 0 ≤ p n)
    (hpzero : Tendsto p atTop (𝓝 0))
    (hscale : Tendsto (fun n => p n * (N n : ℝ)) atTop (𝓝 w)) :
    Tendsto (fun n => p n * (equalBlockEndpoint m b (N n) : ℝ)) atTop
      (𝓝 ((b : ℝ) * w / (m : ℝ))) := by
  have hlin := (hscale.const_mul (b : ℝ)).div_const (m : ℝ)
  have hdiff : Tendsto (fun n => p n * (equalBlockEndpoint m b (N n) : ℝ) -
      (b : ℝ) * (p n * (N n : ℝ)) / (m : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => ?_) hpzero
    simpa only [Real.norm_eq_abs] using equalBlockEndpoint_scaled_error_le hm b (N n) (hp n)
  simpa only [zero_add, sub_add_cancel] using hdiff.add hlin

/-- All fixed blocks have the same limiting scaled duration. -/
theorem equalBlockLength_scaled_tendsto {m : ℕ} (hm : 0 < m) (b : ℕ)
    {N : ℕ → ℕ} {p : ℕ → ℝ} {w : ℝ} (hp : ∀ n, 0 ≤ p n)
    (hpzero : Tendsto p atTop (𝓝 0))
    (hscale : Tendsto (fun n => p n * (N n : ℝ)) atTop (𝓝 w)) :
    Tendsto (fun n => p n * (equalBlockLength m b (N n) : ℝ)) atTop
      (𝓝 (w / (m : ℝ))) := by
  have h := (equalBlockEndpoint_scaled_tendsto hm (b + 1) hp hpzero hscale).sub
    (equalBlockEndpoint_scaled_tendsto hm b hp hpzero hscale)
  have hfun : (fun n => p n * (equalBlockEndpoint m (b + 1) (N n) : ℝ) -
      p n * (equalBlockEndpoint m b (N n) : ℝ)) =
      (fun n => p n * (equalBlockLength m b (N n) : ℝ)) := by
    funext n
    rw [equalBlockLength, Nat.cast_sub (equalBlockEndpoint_monotone m (N n) (Nat.le_succ b))]
    ring
  have hval : ((b + 1 : ℕ) : ℝ) * w / (m : ℝ) -
      (b : ℝ) * w / (m : ℝ) = w / (m : ℝ) := by
    push_cast
    ring
  simpa only [hfun, hval] using h

end FixedCouplingPoisson
