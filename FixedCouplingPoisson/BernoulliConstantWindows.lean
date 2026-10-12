import FixedCouplingPoisson.BernoulliConstantSpectrum
import FixedCouplingPoisson.PhaseWindow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! Arbitrarily many actual constant-chain eigenvalues in any interval
which meets the interior of its band. The neighboring grid points use
only a floor error of at most one and ordinary cosine continuity. -/
noncomputable section
namespace FixedCouplingPoisson
open Filter Real Set Furstenberg
open scoped Topology

theorem constantChainGridEigenvalue_injective (c : ℝ) (L : ℕ) :
    Function.Injective (constantChainGridEigenvalue c L) := by
  intro i j hij
  have hinj := (Finset.range L).nodup_map_iff_injOn.mp
    (Polynomial.Chebyshev.roots_U_real_nodup L)
  apply Fin.ext
  apply hinj (Finset.mem_range.mpr i.isLt) (Finset.mem_range.mpr j.isLt)
  unfold constantChainGridEigenvalue at hij
  linarith

/-- Any distinct grid points in the window are distinct actual eigenvalues. -/
theorem constantChain_windowCount_ge_of_grid (c E F : ℝ) (L r : ℕ)
    (indices : Fin r → Fin L) (hinj : Function.Injective indices)
    (hwindow : ∀ j, E < constantChainGridEigenvalue c L (indices j) ∧
      constantChainGridEigenvalue c L (indices j) ≤ F) :
    r ≤ dirichletEnergyWindowCount L (fun _ => c) E F := by
  classical
  let f : Fin r → Fin L := fun j => (constantChain_grid_eq_eigenvalue c L (indices j)).choose
  have hf (j : Fin r) : dirichletEigenvalues L (fun _ => c) (f j) =
      constantChainGridEigenvalue c L (indices j) :=
    (constantChain_grid_eq_eigenvalue c L (indices j)).choose_spec
  let s : Finset (Fin L) := Finset.univ.filter (fun i =>
    E < dirichletEigenvalues L (fun _ => c) i ∧ dirichletEigenvalues L (fun _ => c) i ≤ F)
  let f' : Fin r → s := fun j => ⟨f j, by simpa [s, hf j] using hwindow j⟩
  have hf' : Function.Injective f' := by
    intro i j hij
    have hvalues := congrArg (fun z : s => dirichletEigenvalues L (fun _ => c) z.val) hij
    simp only [f', hf] at hvalues
    exact hinj (constantChainGridEigenvalue_injective c L hvalues)
  change r ≤ s.card
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f' hf'

/-- A floor-selected grid point and any fixed finite offset approach the
chosen fractional angle. -/
theorem constantChain_floor_angle_tendsto (a : ℝ) (ha : 0 ≤ a) (j : ℕ) :
    Tendsto (fun n : ℕ =>
      ((Nat.floor (a * ((n : ℝ) + 1)) : ℝ) + (j : ℝ) + 1) / ((n : ℝ) + 1))
      atTop (𝓝 a) := by
  have hd : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)
  have hf := (tendsto_nat_floor_mul_div_atTop ha).comp hd
  have hj : Tendsto (fun n : ℕ => ((j : ℝ) + 1) / ((n : ℝ) + 1))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp hd) :
        Tendsto (fun n : ℕ => ((j : ℝ) + 1) * ((n : ℝ) + 1)⁻¹)
          atTop (𝓝 (((j : ℝ) + 1) * 0)))
  have h : Tendsto (fun n : ℕ =>
      (Nat.floor (a * ((n : ℝ) + 1)) : ℝ) / ((n : ℝ) + 1) +
        ((j : ℝ) + 1) / ((n : ℝ) + 1)) atTop (𝓝 a) := by
    simpa only [Function.comp_def, add_zero] using hf.add hj
  convert h using 1
  funext n
  rw [← add_div]
  ring

/-- Every open interval meeting the interior of a constant-potential band
contains at least any prescribed finite number of actual eigenvalues of
some fixed sufficiently long chain. -/
theorem constantChain_exists_windowCount_ge (c E F z : ℝ)
    (hzband : z ∈ Ioo (c - 2) (c + 2)) (hzwindow : z ∈ Ioo E F) (r : ℕ) :
    ∃ L : ℕ, 0 < L ∧ r ≤ dirichletEnergyWindowCount L (fun _ => c) E F := by
  classical
  let x := (z - c) / 2
  have hx₀ : -1 < x := by dsimp [x]; linarith [hzband.1]
  have hx₁ : x < 1 := by dsimp [x]; linarith [hzband.2]
  let a := Real.arccos x / Real.pi
  have ha₀ : 0 < a := div_pos (Real.arccos_pos.mpr hx₁) Real.pi_pos
  have ha₁ : a < 1 := (div_lt_one Real.pi_pos).mpr (Real.arccos_lt_pi.mpr hx₀)
  have hevent : ∀ j : Fin r, ∀ᶠ n : ℕ in atTop,
      Nat.floor (a * ((n : ℝ) + 1)) + j.val < n ∧
      E < c + 2 * Real.cos
        (((Nat.floor (a * ((n : ℝ) + 1)) : ℝ) + (j.val : ℝ) + 1) /
          ((n : ℝ) + 1) * Real.pi) ∧
      c + 2 * Real.cos
        (((Nat.floor (a * ((n : ℝ) + 1)) : ℝ) + (j.val : ℝ) + 1) /
          ((n : ℝ) + 1) * Real.pi) < F := by
    intro j
    have hang := constantChain_floor_angle_tendsto a ha₀.le j.val
    have hvalue : Tendsto (fun n : ℕ => c + 2 * Real.cos
        (((Nat.floor (a * ((n : ℝ) + 1)) : ℝ) + (j.val : ℝ) + 1) /
          ((n : ℝ) + 1) * Real.pi)) atTop (𝓝 (c + 2 * Real.cos (a * Real.pi))) :=
      tendsto_const_nhds.add
        (((Real.continuous_cos.tendsto (a * Real.pi)).comp
          (hang.mul_const Real.pi)).const_mul 2)
    have hlimit : c + 2 * Real.cos (a * Real.pi) = z := by
      dsimp [a]
      rw [div_mul_cancel₀ _ Real.pi_ne_zero, Real.cos_arccos hx₀.le hx₁.le]
      dsimp [x]
      ring
    rw [hlimit] at hvalue
    filter_upwards [hang.eventually (gt_mem_nhds ha₁),
      hvalue.eventually (Ioo_mem_nhds hzwindow.1 hzwindow.2)] with n hn hw
    refine ⟨?_, hw⟩
    have hden : 0 < (n : ℝ) + 1 := by positivity
    have hnum := (div_lt_one hden).mp hn
    have hh : (Nat.floor (a * ((n : ℝ) + 1)) : ℝ) + (j.val : ℝ) < n := by linarith
    exact_mod_cast hh
  have hall : ∀ᶠ n : ℕ in atTop, ∀ j : Fin r,
      Nat.floor (a * ((n : ℝ) + 1)) + j.val < n ∧
      E < c + 2 * Real.cos
        (((Nat.floor (a * ((n : ℝ) + 1)) : ℝ) + (j.val : ℝ) + 1) /
          ((n : ℝ) + 1) * Real.pi) ∧
      c + 2 * Real.cos
        (((Nat.floor (a * ((n : ℝ) + 1)) : ℝ) + (j.val : ℝ) + 1) /
          ((n : ℝ) + 1) * Real.pi) < F := Filter.eventually_all.mpr hevent
  obtain ⟨L, hL, hpoints⟩ := (eventually_ge_atTop 1 |>.and hall).exists
  let indices : Fin r → Fin L := fun j =>
    ⟨Nat.floor (a * ((L : ℝ) + 1)) + j.val, (hpoints j).1⟩
  refine ⟨L, hL, constantChain_windowCount_ge_of_grid c E F L r indices ?_ ?_⟩
  · intro i j hij
    apply Fin.ext
    have hh := congrArg Fin.val hij
    dsimp [indices] at hh
    omega
  · intro j
    have hj := (hpoints j).2
    have heq : constantChainGridEigenvalue c L (indices j) =
        c + 2 * Real.cos
          (((Nat.floor (a * ((L : ℝ) + 1)) : ℝ) + (j.val : ℝ) + 1) /
            ((L : ℝ) + 1) * Real.pi) := by
      simp only [constantChainGridEigenvalue, indices, Nat.cast_add]
      congr 3
      ring
    rw [heq]
    exact ⟨hj.1, hj.2.le⟩

end FixedCouplingPoisson
