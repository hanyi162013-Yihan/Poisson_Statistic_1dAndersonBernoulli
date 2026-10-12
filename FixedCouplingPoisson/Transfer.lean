import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Transfer matrices and finite Dirichlet matrices

The indexing follows the manuscript: `v j` occurs in the equation for
`u (j+1)`, and transfer products multiply each new step on the left.
All matrices here are actual real matrices, not abstract assumptions.
-/

namespace FixedCouplingPoisson

open Matrix

abbrev Vector2 := Fin 2 → ℝ
abbrev Matrix2 := Matrix (Fin 2) (Fin 2) ℝ

/-- The one-step Schrödinger transfer matrix. -/
def transfer (E v : ℝ) : Matrix2 := !![E - v, -1; 1, 0]

/-- An explicit two-sided inverse of the transfer matrix. -/
def transferInv (E v : ℝ) : Matrix2 := !![0, 1; -1, E - v]

/-- An upper unipotent shear. -/
def shear (t : ℝ) : Matrix2 := !![1, t; 0, 1]

@[simp] theorem transfer_det (E v : ℝ) : (transfer E v).det = 1 := by
  simp [transfer, Matrix.det_fin_two]

@[simp] theorem transfer_mul_transferInv (E v : ℝ) :
    transfer E v * transferInv E v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transfer, transferInv, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem transferInv_mul_transfer (E v : ℝ) :
    transferInv E v * transfer E v = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transfer, transferInv, Matrix.mul_apply, Fin.sum_univ_two]

/-- The algebraic shear identity used to check the random-matrix hypotheses. -/
theorem transfer_mul_inverse_eq_shear (E a b : ℝ) :
    transfer E a * transferInv E b = shear (b - a) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [transfer, transferInv, shear, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem shear_zero : shear 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shear]

@[simp] theorem shear_mul (s t : ℝ) : shear s * shear t = shear (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shear, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The powers of the support-generated shear have a linearly growing entry. -/
theorem shear_pow (t : ℝ) (n : ℕ) : shear t ^ n = shear ((n : ℝ) * t) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, shear_mul]; congr 1; simp only [Nat.cast_add, Nat.cast_one]; ring

@[simp] theorem transfer_mulVec (E v : ℝ) (u : Vector2) :
    transfer E v *ᵥ u = ![(E - v) * u 0 - u 1, u 0] := by
  ext i
  fin_cases i <;> simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two, sub_eq_add_neg]

@[simp] theorem shear_mulVec (t : ℝ) (u : Vector2) :
    shear t *ᵥ u = ![u 0 + t * u 1, u 1] := by
  ext i
  fin_cases i <;> simp [shear, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The determinant of two column vectors. -/
def wedge (u w : Vector2) : ℝ := u 0 * w 1 - u 1 * w 0

/-- A nontrivial shear can preserve a vector's projective line only on the
horizontal axis. This is the finite-orbit algebra needed in the manuscript. -/
theorem shear_wedge_eq_zero_iff (t : ℝ) (ht : t ≠ 0) (u : Vector2) :
    wedge u (shear t *ᵥ u) = 0 ↔ u 1 = 0 := by
  rw [shear_mulVec]
  change u 0 * u 1 - u 1 * (u 0 + t * u 1) = 0 ↔ u 1 = 0
  constructor
  · intro h
    have hid : u 0 * u 1 - u 1 * (u 0 + t * u 1) = -(t * u 1 * u 1) := by ring
    have hprod : t * u 1 * u 1 = 0 := by rwa [hid, neg_eq_zero] at h
    rcases mul_eq_zero.mp hprod with htu | hu
    · exact (mul_eq_zero.mp htu).resolve_left ht
    · exact hu
  · intro h; simp [h]

/-- No two distinct shear iterates of a nonhorizontal line are collinear. -/
theorem shear_iterates_not_collinear (t : ℝ) (ht : t ≠ 0) (u : Vector2)
    (hu : u 1 ≠ 0) (m n : ℕ) (hmn : m ≠ n) :
    wedge (shear t ^ m *ᵥ u) (shear t ^ n *ᵥ u) ≠ 0 := by
  rw [shear_pow, shear_pow, shear_mulVec, shear_mulVec]
  change (u 0 + (m : ℝ) * t * u 1) * u 1 -
    u 1 * (u 0 + (n : ℝ) * t * u 1) ≠ 0
  have hcast : (m : ℝ) - (n : ℝ) ≠ 0 := sub_ne_zero.mpr (by intro h; exact hmn (Nat.cast_injective h))
  have hp : ((m : ℝ) - (n : ℝ)) * t * u 1 * u 1 ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hcast ht) hu) hu
  convert hp using 1; ring

/-- The shear powers are unbounded already in a single matrix entry. -/
theorem shear_powers_entry_unbounded (t : ℝ) (ht : t ≠ 0) (B : ℝ) :
    ∃ n : ℕ, B < |(shear t ^ n) 0 1| := by
  obtain ⟨n, hn⟩ := exists_nat_gt (B / |t|)
  refine ⟨n, ?_⟩
  have hlt : B < (n : ℝ) * |t| := (div_lt_iff₀ (abs_pos.mpr ht)).mp hn
  rw [shear_pow]
  simpa [shear, abs_mul] using hlt

/-- The transfer matrix moves the horizontal line away from itself. -/
theorem transfer_horizontal_not_collinear (E v : ℝ) :
    wedge (![1, 0] : Vector2) (transfer E v *ᵥ ![1, 0]) = 1 := by
  simp [wedge]

/-- The actual product in its order of action. -/
def transferProduct (E : ℝ) (v : ℕ → ℝ) : ℕ → Matrix2
  | 0 => 1
  | n + 1 => transfer E (v n) * transferProduct E v n

@[simp] theorem transferProduct_det (E : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    (transferProduct E v n).det = 1 := by
  induction n with
  | zero => simp [transferProduct]
  | succ n ih => simp [transferProduct, Matrix.det_mul, ih]

/-- The Dirichlet solution with left boundary values `(u 1, u 0) = (1,0)`. -/
def dirichletSolution (E : ℝ) (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | n + 2 => (E - v n) * dirichletSolution E v (n + 1) - dirichletSolution E v n

@[simp] theorem dirichletSolution_zero (E : ℝ) (v : ℕ → ℝ) :
    dirichletSolution E v 0 = 0 := rfl

@[simp] theorem dirichletSolution_one (E : ℝ) (v : ℕ → ℝ) :
    dirichletSolution E v 1 = 1 := rfl

theorem dirichletSolution_recurrence (E : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    dirichletSolution E v (n + 2) =
      (E - v n) * dirichletSolution E v (n + 1) - dirichletSolution E v n := rfl

/-- The product yields precisely the pair of consecutive Dirichlet values. -/
theorem transferProduct_dirichlet (E : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    transferProduct E v n *ᵥ ![1, 0] =
      ![dirichletSolution E v (n + 1), dirichletSolution E v n] := by
  induction n with
  | zero => simp [transferProduct]
  | succ n ih =>
    rw [transferProduct, ← Matrix.mulVec_mulVec, ih, transfer_mulVec]
    rfl

/-- Consecutive Dirichlet values never vanish simultaneously, so their
projective direction is defined at every energy and every step. -/
theorem dirichletSolution_pair_ne_zero (E : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    (![dirichletSolution E v (n + 1), dirichletSolution E v n] : Vector2) ≠ 0 := by
  induction n with
  | zero =>
    intro h
    have h0 := congrFun h 0
    simp at h0
  | succ n ih =>
    intro h
    have hnext : dirichletSolution E v (n + 2) = 0 := congrFun h 0
    have hcurrent : dirichletSolution E v (n + 1) = 0 := congrFun h 1
    have hprev : dirichletSolution E v n = 0 := by
      rw [dirichletSolution_recurrence, hcurrent] at hnext
      simpa using hnext
    apply ih
    ext i
    fin_cases i <;> simp [hcurrent, hprev]

/-- The actual finite Dirichlet Jacobi matrix, with hopping coefficient one. -/
def dirichletMatrix (n : ℕ) (v : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if i = j then v i else if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0

/-- The finite-volume matrix is real symmetric. -/
theorem dirichletMatrix_isSymm (n : ℕ) (v : Fin n → ℝ) :
    (dirichletMatrix n v).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  by_cases hij : i = j
  · subst j; rfl
  · simp [dirichletMatrix, hij, Ne.symm hij, or_comm]

/-- If a vector vanishes through site `k`, the Jacobi equation at `k`
contains only its next component. -/
private theorem dirichletMatrix_mulVec_of_prefix_zero {n k : ℕ} (hk : k < n)
    (v x : Fin (n + 1) → ℝ) (hx : ∀ i, i.val ≤ k → x i = 0) :
    (dirichletMatrix (n + 1) v *ᵥ x) ⟨k, by omega⟩ = x ⟨k + 1, by omega⟩ := by
  change (∑ j : Fin (n + 1), dirichletMatrix (n + 1) v ⟨k, by omega⟩ j * x j) = _
  rw [Finset.sum_eq_single (⟨k + 1, by omega⟩ : Fin (n + 1))]
  · have hneq : (⟨k, by omega⟩ : Fin (n + 1)) ≠ ⟨k + 1, by omega⟩ := by
      intro h; have := congrArg Fin.val h; simp only at this; omega
    simp [dirichletMatrix, hneq]
  · intro j _ hj
    by_cases hjk : j.val ≤ k
    · simp [hx j hjk]
    · have hjnext : j.val ≠ k + 1 := by
        intro h; apply hj; exact Fin.ext h
      have hneq : (⟨k, by omega⟩ : Fin (n + 1)) ≠ j := by
        intro h; have := congrArg Fin.val h; simp only at this; omega
      have hadj : ¬ (k + 1 = j.val ∨ j.val + 1 = k) := by omega
      simp [dirichletMatrix, hneq, hadj]
  · simp

/-- A Dirichlet eigenvector is determined by its first component: if that
component vanishes, the whole eigenvector vanishes. -/
theorem dirichlet_eigenvector_eq_zero_of_first_eq_zero {n : ℕ}
    (v x : Fin (n + 1) → ℝ) (E : ℝ)
    (heig : dirichletMatrix (n + 1) v *ᵥ x = E • x) (hfirst : x 0 = 0) : x = 0 := by
  have hprefix : ∀ k : ℕ, k ≤ n → ∀ i : Fin (n + 1), i.val ≤ k → x i = 0 := by
    intro k
    induction k with
    | zero =>
      intro _ i hi
      have hi0 : i = 0 := Fin.ext (by simpa using Nat.eq_zero_of_le_zero hi)
      simpa [hi0] using hfirst
    | succ k ih =>
      intro hk i hi
      have hprev := ih (by omega)
      by_cases hik : i.val ≤ k
      · exact hprev i hik
      · have hiv : i.val = k + 1 := by omega
        have hi_eq : i = (⟨k + 1, by omega⟩ : Fin (n + 1)) := Fin.ext hiv
        have hrow := congrFun heig (⟨k, by omega⟩ : Fin (n + 1))
        rw [dirichletMatrix_mulVec_of_prefix_zero (by omega) v x hprev] at hrow
        have hxk : x (⟨k, by omega⟩ : Fin (n + 1)) = 0 := hprev _ (by simp)
        simpa [hi_eq, hxk] using hrow
  funext i
  exact hprefix n le_rfl i (by omega)

/-- Every nonzero eigenvector of a finite Dirichlet matrix has nonzero first
component. This proves the uniqueness mechanism behind simple spectrum. -/
theorem dirichlet_eigenvector_first_ne_zero {n : ℕ}
    (v x : Fin (n + 1) → ℝ) (E : ℝ)
    (heig : dirichletMatrix (n + 1) v *ᵥ x = E • x) (hx : x ≠ 0) : x 0 ≠ 0 := by
  intro hfirst
  exact hx (dirichlet_eigenvector_eq_zero_of_first_eq_zero v x E heig hfirst)

/-- Two eigenvectors at the same energy and with the same first component
coincide. -/
theorem dirichlet_eigenvector_ext_of_first {n : ℕ}
    (v x y : Fin (n + 1) → ℝ) (E : ℝ)
    (hx : dirichletMatrix (n + 1) v *ᵥ x = E • x)
    (hy : dirichletMatrix (n + 1) v *ᵥ y = E • y) (hfirst : x 0 = y 0) : x = y := by
  have hdiff : dirichletMatrix (n + 1) v *ᵥ (x - y) = E • (x - y) := by
    rw [Matrix.mulVec_sub, hx, hy, smul_sub]
  have hzero : x - y = 0 := dirichlet_eigenvector_eq_zero_of_first_eq_zero
    v (x - y) E hdiff (by simp [hfirst])
  exact sub_eq_zero.mp hzero

/-- Every eigenvector is a scalar multiple of any fixed nonzero eigenvector
at the same energy; thus every eigenspace has at most one dimension. -/
theorem dirichlet_eigenvector_proportional {n : ℕ}
    (v x y : Fin (n + 1) → ℝ) (E : ℝ)
    (hx : dirichletMatrix (n + 1) v *ᵥ x = E • x)
    (hy : dirichletMatrix (n + 1) v *ᵥ y = E • y) (hyne : y ≠ 0) :
    x = (x 0 / y 0) • y := by
  have hy0 : y 0 ≠ 0 := dirichlet_eigenvector_first_ne_zero v y E hy hyne
  apply dirichlet_eigenvector_ext_of_first v x ((x 0 / y 0) • y) E hx
  · rw [Matrix.mulVec_smul, hy]
    exact smul_comm _ _ _
  · simp [Pi.smul_apply, hy0]

end FixedCouplingPoisson
