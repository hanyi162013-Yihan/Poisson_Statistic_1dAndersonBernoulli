import FixedCouplingPoisson.SpectralCounting
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Tactic.Linarith

/-!
# Finite-rank stability of the actual Hermitian spectral counts

Quadratic-form inertia and rank-nullity prove the perturbation estimate;
the estimate is not an external hypothesis. This module currently contains
the finite-dimensional ingredients. An infinite-volume IDS convergence
theorem is not yet asserted here.
-/

open Matrix Module QuadraticForm QuadraticMap
open scoped BigOperators

namespace FixedCouplingPoisson

theorem sigPos_le_add_range {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]
    (Q₁ Q₂ : QuadraticForm ℝ V) (T : V →ₗ[ℝ] W)
    (hQ : ∀ x ∈ LinearMap.ker T, Q₁ x = Q₂ x) :
    sigPos Q₁ ≤ sigPos Q₂ + finrank ℝ (LinearMap.range T) := by
  obtain ⟨S, hSdim, hSpos⟩ := exists_finrank_eq_sigPos_and_posDef Q₁
  let K := LinearMap.ker T
  have hpos : (Q₂.restrict (S ⊓ K)).PosDef := by
    intro x hx
    have hx0 : (x : V) ≠ 0 := fun h => hx (Subtype.ext h)
    have hp := hSpos ⟨x, x.2.1⟩ (fun h => hx0 (congrArg Subtype.val h))
    change 0 < Q₂ x
    change 0 < Q₁ x at hp
    rwa [← hQ x x.2.2]
  have hi := le_sigPos_of_posDef Q₂ hpos
  have hd := S.finrank_sup_add_finrank_inf_eq K
  have hle := (S ⊔ K).finrank_le
  have hr := T.finrank_range_add_finrank_ker
  dsimp [K] at hd hi hle
  omega

theorem toQuadraticForm'_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A U : Matrix ι ι ℝ) (x : ι → ℝ) :
    A.toQuadraticForm' (U *ᵥ x) = (Uᵀ * A * U).toQuadraticForm' x := by
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply']
  rw [← mulVec_mulVec, ← mulVec_mulVec, Matrix.dotProduct_transpose_mulVec, dotProduct_comm]

theorem toQuadraticForm'_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) :
    (Matrix.diagonal w).toQuadraticForm' = QuadraticMap.weightedSumSquares ℝ w := by
  ext x
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', QuadraticMap.weightedSumSquares_apply,
    dotProduct, mulVec_diagonal, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem weighted_equivalent_conjugate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (U : Matrix.unitaryGroup ι ℝ) :
    QuadraticMap.Equivalent (QuadraticMap.weightedSumSquares ℝ w)
      (((U : Matrix ι ι ℝ) * Matrix.diagonal w * star (U : Matrix ι ι ℝ)).toQuadraticForm') := by
  refine ⟨{ Matrix.UnitaryGroup.toLinearEquiv U with map_app' := ?_ }⟩
  intro x
  change (((U : Matrix ι ι ℝ) * Matrix.diagonal w * star (U : Matrix ι ι ℝ)).toQuadraticForm'
    ((U : Matrix ι ι ℝ) *ᵥ x)) = _
  rw [toQuadraticForm'_mulVec]
  have hU : (U : Matrix ι ι ℝ)ᵀ = star (U : Matrix ι ι ℝ) := by
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  rw [hU]
  have hm : star (U : Matrix ι ι ℝ) *
      ((U : Matrix ι ι ℝ) * diagonal w * star (U : Matrix ι ι ℝ)) * (U : Matrix ι ι ℝ) =
      diagonal w := by
    calc
      _ = (star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)) * diagonal w *
          (star (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ)) := by simp only [Matrix.mul_assoc]
      _ = diagonal w := by rw [Unitary.coe_star_mul_self]; simp
  rw [hm, toQuadraticForm'_diagonal]

theorem belowForm_equivalent {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (E : ℝ) :
    QuadraticMap.Equivalent ((E • (1 : Matrix ι ι ℝ) - A).toQuadraticForm')
      (QuadraticMap.weightedSumSquares ℝ (fun i => E - hA.eigenvalues i)) := by
  let U := hA.eigenvectorUnitary
  have hspec : A = Unitary.conjStarAlgAut ℝ _ U (diagonal hA.eigenvalues) := by
    simpa [U] using hA.spectral_theorem
  have hd : diagonal (fun i => E - hA.eigenvalues i) = E • (1 : Matrix ι ι ℝ) -
      diagonal hA.eigenvalues := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hm : E • (1 : Matrix ι ι ℝ) - A =
      (U : Matrix ι ι ℝ) * diagonal (fun i => E - hA.eigenvalues i) *
        star (U : Matrix ι ι ℝ) := by
    calc
      _ = Unitary.conjStarAlgAut ℝ _ U (diagonal (fun i => E - hA.eigenvalues i)) := by
        rw [hd, map_sub, map_smul, map_one, ← hspec]
      _ = _ := Unitary.conjStarAlgAut_apply U _
  rw [hm]
  exact (weighted_equivalent_conjugate _ U).symm

noncomputable def hermitianStrictCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (E : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => hA.eigenvalues i < E)).card

noncomputable def hermitianNonstrictCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (E : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => hA.eigenvalues i ≤ E)).card

theorem belowForm_sigPos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (E : ℝ) :
    sigPos (E • (1 : Matrix ι ι ℝ) - A).toQuadraticForm' = hermitianStrictCount hA E := by
  classical
  rw [QuadraticForm.sigPos_of_equiv_weightedSumSquares (belowForm_equivalent hA E)]
  simp [hermitianStrictCount, sub_pos, Set.ncard_eq_toFinset_card']

theorem nonstrict_add_belowForm_sigNeg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (E : ℝ) :
    hermitianNonstrictCount hA E + sigNeg (E • (1 : Matrix ι ι ℝ) - A).toQuadraticForm' =
      Fintype.card ι := by
  classical
  rw [QuadraticForm.sigNeg_of_equiv_weightedSumSquares (belowForm_equivalent hA E)]
  simp only [sub_neg, Set.ncard_eq_toFinset_card']
  simpa [hermitianNonstrictCount] using
    Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => hA.eigenvalues i ≤ E)

theorem belowForms_eq_on_ker {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (E : ℝ) {x : ι → ℝ}
    (hx : x ∈ LinearMap.ker (A - B).mulVecLin) :
    (E • (1 : Matrix ι ι ℝ) - A).toQuadraticForm' x =
      (E • (1 : Matrix ι ι ℝ) - B).toQuadraticForm' x := by
  have hAB : A *ᵥ x = B *ᵥ x := by
    apply sub_eq_zero.mp
    simpa only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.sub_mulVec] using hx
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply', Matrix.sub_mulVec, hAB]

/-- The strict count can change by at most the actual rank of the perturbation. -/
theorem hermitianStrictCount_le_add_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) (E : ℝ) :
    hermitianStrictCount hA E ≤ hermitianStrictCount hB E + (A - B).rank := by
  have h := sigPos_le_add_range
    (E • (1 : Matrix ι ι ℝ) - A).toQuadraticForm'
    (E • (1 : Matrix ι ι ℝ) - B).toQuadraticForm' (A - B).mulVecLin
    (fun x hx => belowForms_eq_on_ker A B E hx)
  rw [belowForm_sigPos hA E, belowForm_sigPos hB E] at h
  exact h

theorem hermitianNonstrictCount_le_add_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) (E : ℝ) :
    hermitianNonstrictCount hA E ≤ hermitianNonstrictCount hB E + (A - B).rank := by
  have h := sigPos_le_add_range
    (-(E • (1 : Matrix ι ι ℝ) - B).toQuadraticForm')
    (-(E • (1 : Matrix ι ι ℝ) - A).toQuadraticForm') (A - B).mulVecLin
    (fun x hx => by
      exact congrArg (fun t : ℝ => -t) (belowForms_eq_on_ker A B E hx).symm)
  have ha := nonstrict_add_belowForm_sigNeg hA E
  have hb := nonstrict_add_belowForm_sigNeg hB E
  change sigNeg (E • (1 : Matrix ι ι ℝ) - B).toQuadraticForm' ≤
    sigNeg (E • (1 : Matrix ι ι ℝ) - A).toQuadraticForm' + (A - B).rank at h
  omega

theorem hermitianNonstrictCount_rank_abs {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) (E : ℝ) :
    |(hermitianNonstrictCount hA E : ℝ) - hermitianNonstrictCount hB E| ≤ (A - B).rank := by
  apply abs_le.mpr
  have hab := hermitianNonstrictCount_le_add_rank hA hB E
  have hba := hermitianNonstrictCount_le_add_rank hB hA E
  have hr : (B - A).rank = (A - B).rank := by
    rw [← neg_sub A B]
    simpa only [neg_one_smul] using
      (Matrix.rank_smul_of_mem_nonZeroDivisors (c := (-1 : ℝ)) (A - B) (by simp))
  rw [hr] at hba
  have habR : (hermitianNonstrictCount hA E : ℝ) ≤
      hermitianNonstrictCount hB E + ((A - B).rank : ℝ) := by exact_mod_cast hab
  have hbaR : (hermitianNonstrictCount hB E : ℝ) ≤
      hermitianNonstrictCount hA E + ((A - B).rank : ℝ) := by exact_mod_cast hba
  constructor <;> linarith

/-- Characteristic-polynomial roots identify the count independently of the
chosen eigenbasis or ordering. -/
theorem hermitianNonstrictCount_eq_roots {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (E : ℝ) :
    hermitianNonstrictCount hA E = (A.charpoly.roots.filter (fun x => x ≤ E)).card := by
  classical
  rw [hA.roots_charpoly_eq_eigenvalues, Multiset.filter_map, Multiset.card_map]
  simp only [Function.comp_def, RCLike.ofReal_real_eq_id, id_eq]
  exact congrArg Multiset.card (Finset.filter_val _ _).symm

theorem hermitianNonstrictCount_reindex {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (e : ι ≃ κ) (E : ℝ) :
    hermitianNonstrictCount (hA.reindex e) E = hermitianNonstrictCount hA E := by
  rw [hermitianNonstrictCount_eq_roots, hermitianNonstrictCount_eq_roots, Matrix.charpoly_reindex]

theorem hermitianNonstrictCount_fromBlocks {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (E : ℝ) :
    hermitianNonstrictCount (hA.fromBlocks (B := 0) (C := 0) (by simp) hB) E =
      hermitianNonstrictCount hA E + hermitianNonstrictCount hB E := by
  classical
  simp only [hermitianNonstrictCount_eq_roots, Matrix.charpoly_fromBlocks_zero₁₂]
  rw [Polynomial.roots_mul (mul_ne_zero (Matrix.charpoly_monic A).ne_zero
    (Matrix.charpoly_monic B).ne_zero), Multiset.filter_add, Multiset.card_add]

end FixedCouplingPoisson
