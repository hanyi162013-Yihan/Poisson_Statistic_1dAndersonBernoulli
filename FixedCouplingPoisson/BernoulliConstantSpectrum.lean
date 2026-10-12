import FixedCouplingPoisson.Sturm
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Tactic

/-!
# The actual spectrum of a constant Dirichlet chain

The shooting recurrence is the second-kind Chebyshev recurrence. Its
already formalized cosine roots and simplicity of the actual Dirichlet
spectrum identify the complete finite spectrum, without normalized
quasimodes or a spectral-projection estimate.
-/
noncomputable section
namespace FixedCouplingPoisson
open Polynomial Polynomial.Chebyshev Real Set

/-- The cosine grid for an L-site constant chain. -/
def constantChainGridEigenvalue (c : ℝ) (L : ℕ) (k : Fin L) : ℝ :=
  c + 2 * Real.cos (((k.val : ℝ) + 1) * Real.pi / ((L : ℝ) + 1))

theorem dirichletSolution_constant_eq_chebyshev (E c : ℝ) (n : ℕ) :
    dirichletSolution E (fun _ => c) (n + 1) =
      (Polynomial.Chebyshev.U ℝ (n : ℤ)).eval ((E - c) / 2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    norm_num [dirichletSolution_recurrence, Polynomial.Chebyshev.U_one]; ring
  | more n ih0 ih1 =>
    push_cast
    push_cast at ih1
    rw [dirichletSolution_recurrence E (fun _ => c) (n + 1), ih1, ih0,
      Polynomial.Chebyshev.U_add_two]
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X]
    ring

theorem constantChain_eigenvalue_chebyshev_zero (c : ℝ) (L : ℕ) (i : Fin L) :
    (Polynomial.Chebyshev.U ℝ (L : ℤ)).eval
      ((dirichletEigenvalues L (fun _ => c) i - c) / 2) = 0 := by
  cases L with
  | zero => exact Fin.elim0 i
  | succ n =>
    have hz := dirichletEigenvalue_shooting_zero (fun _ => c) n i
    exact (dirichletSolution_constant_eq_chebyshev
      (dirichletEigenvalues (n + 1) (fun _ => c) i) c (n + 1)).symm.trans hz

/-- Every actual eigenvalue belongs to the explicit cosine grid. -/
theorem constantChain_eigenvalue_eq_grid (c : ℝ) (L : ℕ) (i : Fin L) :
    ∃ k : Fin L, dirichletEigenvalues L (fun _ => c) i = constantChainGridEigenvalue c L k := by
  classical
  have hne : Polynomial.Chebyshev.U ℝ (L : ℤ) ≠ 0 :=
    Polynomial.Chebyshev.U_ne_zero ℝ (L : ℤ) (by omega)
  have hroot : ((dirichletEigenvalues L (fun _ => c) i - c) / 2) ∈
      (Polynomial.Chebyshev.U ℝ (L : ℤ)).roots :=
    (Polynomial.mem_roots hne).mpr (constantChain_eigenvalue_chebyshev_zero c L i)
  rw [Polynomial.Chebyshev.roots_U_real] at hroot
  obtain ⟨k, hk, hcos⟩ := Finset.mem_image.mp (Finset.mem_val.mp hroot)
  refine ⟨⟨k, Finset.mem_range.mp hk⟩, ?_⟩
  unfold constantChainGridEigenvalue
  dsimp
  linarith

/-- Every cosine-grid value is an actual eigenvalue. Finite cardinality and
simplicity supply the converse without choosing a normalized eigenvector. -/
theorem constantChain_grid_eq_eigenvalue (c : ℝ) (L : ℕ) (k : Fin L) :
    ∃ i : Fin L, dirichletEigenvalues L (fun _ => c) i = constantChainGridEigenvalue c L k := by
  classical
  let f : Fin L → Fin L := fun i => (constantChain_eigenvalue_eq_grid c L i).choose
  have hspec (i : Fin L) : dirichletEigenvalues L (fun _ => c) i =
      constantChainGridEigenvalue c L (f i) :=
    (constantChain_eigenvalue_eq_grid c L i).choose_spec
  have hinj : Function.Injective f := by
    intro i j hij
    apply dirichletEigenvalues_injective L (fun _ => c)
    rw [hspec i, hspec j, hij]
  obtain ⟨i, hi⟩ := Finite.surjective_of_injective hinj k
  exact ⟨i, (hspec i).trans (congrArg (constantChainGridEigenvalue c L) hi)⟩

end FixedCouplingPoisson
