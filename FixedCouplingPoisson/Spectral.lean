import FixedCouplingPoisson.Transfer
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Data.Finset.Card

/-!
# Simple finite Dirichlet spectrum

This connects the explicit Jacobi matrix to mathlib's finite-dimensional
spectral theorem and proves the endpoint count bound for its actual eigenvalues.
-/

namespace FixedCouplingPoisson

open Matrix

/-- Real symmetry gives the Hermitian hypothesis of mathlib's spectral theorem. -/
theorem dirichletMatrix_isHermitian (n : ℕ) (v : Fin n → ℝ) :
    (dirichletMatrix n v).IsHermitian :=
  Matrix.isHermitian_iff_isSymm.mpr (dirichletMatrix_isSymm n v)

/-- The actual eigenvalues returned by the spectral theorem. -/
noncomputable def dirichletEigenvalues (n : ℕ) (v : Fin n → ℝ) : Fin n → ℝ :=
  (dirichletMatrix_isHermitian n v).eigenvalues

/-- The finite Dirichlet spectrum is simple: its list of spectral-theorem
values has no repetitions. -/
theorem dirichletEigenvalues_injective (n : ℕ) (v : Fin n → ℝ) :
    Function.Injective (dirichletEigenvalues n v) := by
  classical
  cases n with
  | zero => intro i; exact Fin.elim0 i
  | succ n =>
    let hA := dirichletMatrix_isHermitian (n + 1) v
    let b := hA.eigenvectorBasis
    intro i j hij
    by_contra hne
    have hy : dirichletMatrix (n + 1) v *ᵥ ⇑(b j) =
        dirichletEigenvalues (n + 1) v i • ⇑(b j) := by
      rw [hij]
      exact hA.mulVec_eigenvectorBasis j
    have hyne : (⇑(b j) : Fin (n + 1) → ℝ) ≠ 0 := by
      intro h
      apply b.orthonormal.ne_zero j
      ext k
      exact congrFun h k
    have hprop := dirichlet_eigenvector_proportional v (⇑(b i)) (⇑(b j))
      (dirichletEigenvalues (n + 1) v i) (hA.mulVec_eigenvectorBasis i) hy hyne
    have hprop' : b i = (b i 0 / b j 0) • b j := by
      ext k
      exact congrFun hprop k
    have hrepr := congrArg (fun z => b.repr z i) hprop'
    simp [OrthonormalBasis.repr_self, hne] at hrepr

/-- The strict count at an energy. -/
noncomputable def strictSpectralCount (n : ℕ) (v : Fin n → ℝ) (E : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => dirichletEigenvalues n v i < E)).card

/-- The non-strict count at an energy. -/
noncomputable def nonstrictSpectralCount (n : ℕ) (v : Fin n → ℝ) (E : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => dirichletEigenvalues n v i ≤ E)).card

/-- Every strict spectral count is bounded by the matrix size. -/
theorem strictSpectralCount_le_size (n : ℕ) (v : Fin n → ℝ) (E : ℝ) :
    strictSpectralCount n v E ≤ n := by
  classical
  simpa [strictSpectralCount] using
    Finset.card_filter_le (Finset.univ : Finset (Fin n))
      (fun i => dirichletEigenvalues n v i < E)

/-- Every non-strict spectral count is bounded by the matrix size. -/
theorem nonstrictSpectralCount_le_size (n : ℕ) (v : Fin n → ℝ) (E : ℝ) :
    nonstrictSpectralCount n v E ≤ n := by
  classical
  simpa [nonstrictSpectralCount] using
    Finset.card_filter_le (Finset.univ : Finset (Fin n))
      (fun i => dirichletEigenvalues n v i ≤ E)

/-- The endpoint convention only adds eigenvalues. -/
theorem strictSpectralCount_le_nonstrict (n : ℕ) (v : Fin n → ℝ) (E : ℝ) :
    strictSpectralCount n v E ≤ nonstrictSpectralCount n v E := by
  classical
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.le⟩

/-- At most one actual Dirichlet eigenvalue lies at any fixed energy. -/
theorem dirichletEigenvalues_level_card_le_one (n : ℕ) (v : Fin n → ℝ) (E : ℝ) :
    (Finset.univ.filter (fun i => dirichletEigenvalues n v i = E)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi j hj
  apply dirichletEigenvalues_injective n v
  exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm

/-- Strict and non-strict counts differ by at most one, with the exact endpoint
conventions used in the manuscript. -/
theorem spectralCount_endpoint_difference (n : ℕ) (v : Fin n → ℝ) (E : ℝ) :
    nonstrictSpectralCount n v E - strictSpectralCount n v E ≤ 1 := by
  classical
  let s := Finset.univ.filter (fun i => dirichletEigenvalues n v i < E)
  let t := Finset.univ.filter (fun i => dirichletEigenvalues n v i ≤ E)
  have hsub : s ⊆ t := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.le⟩
  have hdiff : t \ s = Finset.univ.filter (fun i => dirichletEigenvalues n v i = E) := by
    ext i
    simp only [s, t, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hle, hnlt⟩
      exact le_antisymm hle (le_of_not_gt hnlt)
    · intro heq
      exact ⟨heq.le, by simp [heq]⟩
  have hcard := dirichletEigenvalues_level_card_le_one n v E
  rw [← hdiff, Finset.card_sdiff_of_subset hsub] at hcard
  exact hcard

/-- An additive version of the endpoint bound, convenient for expectations. -/
theorem spectralCount_endpoint_le_add_one (n : ℕ) (v : Fin n → ℝ) (E : ℝ) :
    nonstrictSpectralCount n v E ≤ strictSpectralCount n v E + 1 := by
  have h := spectralCount_endpoint_difference n v E
  omega

end FixedCouplingPoisson
