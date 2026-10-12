import FixedCouplingPoisson.SchrodingerSemigroupNoncompact
import FixedCouplingPoisson.EnergyContinuity
import FixedCouplingPoisson.PhaseWeakTools

/-! Elementary growth estimates for the actual real SL₂ group.
No qualitative Furstenberg input is assumed. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Matrix Set
open scoped Topology

def sl2RowRadius (A : RealSL2) : ℝ :=
  max (euclideanNorm (A 0)) (euclideanNorm (A 1))

theorem sl2_row_norm_le_radius (A : RealSL2) (i : Fin 2) :
    euclideanNorm (A i) ≤ sl2RowRadius A := by
  fin_cases i
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem sl2RowRadius_nonneg (A : RealSL2) : 0 ≤ sl2RowRadius A :=
  (euclideanNorm_nonneg (A 0)).trans (le_max_left _ _)

theorem one_le_sl2RowRadius (A : RealSL2) : 1 ≤ sl2RowRadius A := by
  have hd : wedge (A 0) (A 1) = 1 := by
    simpa only [wedge, Matrix.det_fin_two] using A.det_coe
  have h := wedge_abs_le_euclideanNorm_mul (A 0) (A 1)
  rw [hd, abs_one] at h
  have hmul : euclideanNorm (A 0) * euclideanNorm (A 1) ≤
      sl2RowRadius A * sl2RowRadius A :=
    mul_le_mul (sl2_row_norm_le_radius A 0) (sl2_row_norm_le_radius A 1)
      (euclideanNorm_nonneg _) (sl2RowRadius_nonneg A)
  nlinarith [sl2RowRadius_nonneg A]

theorem sl2RowRadius_pos (A : RealSL2) : 0 < sl2RowRadius A :=
  lt_of_lt_of_le zero_lt_one (one_le_sl2RowRadius A)

theorem continuous_sl2RowRadius : Continuous sl2RowRadius := by
  have h0 : Continuous (fun A : RealSL2 => (A 0 : Vector2)) := by fun_prop
  have h1 : Continuous (fun A : RealSL2 => (A 1 : Vector2)) := by fun_prop
  exact (continuous_euclideanNorm.comp h0).max (continuous_euclideanNorm.comp h1)

theorem coefficientSquareSum_le_sl2RowRadius (A : RealSL2) :
    coefficientSquareSum (A : Matrix2) ≤ (2 * sl2RowRadius A) ^ 2 := by
  have h0 := sl2_row_norm_le_radius A 0
  have h1 := sl2_row_norm_le_radius A 1
  have h0sq : euclideanNorm (A 0) ^ 2 ≤ sl2RowRadius A ^ 2 :=
    pow_le_pow_left₀ (euclideanNorm_nonneg _) h0 2
  have h1sq : euclideanNorm (A 1) ^ 2 ≤ sl2RowRadius A ^ 2 :=
    pow_le_pow_left₀ (euclideanNorm_nonneg _) h1 2
  rw [euclideanNorm_sq] at h0sq h1sq
  unfold coefficientSquareSum euclideanNormSq at *
  nlinarith [sq_nonneg (sl2RowRadius A)]

theorem coefficientSquareSum_sl2_inv (A : RealSL2) :
    coefficientSquareSum ((A⁻¹ : RealSL2) : Matrix2) =
      coefficientSquareSum (A : Matrix2) := by
  rw [SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp only [coefficientSquareSum, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_sq]
  ring

theorem euclideanNorm_coordinate_le (u : Vector2) (i : Fin 2) :
    |u i| ≤ euclideanNorm u := by
  apply abs_le_of_sq_le_sq _ (euclideanNorm_nonneg u)
  rw [euclideanNorm_sq]
  fin_cases i
  · change u 0 ^ 2 ≤ u 0 ^ 2 + u 1 ^ 2
    linarith [sq_nonneg (u 1)]
  · change u 1 ^ 2 ≤ u 0 ^ 2 + u 1 ^ 2
    linarith [sq_nonneg (u 0)]

theorem sl2_entry_abs_le_radius (A : RealSL2) (i j : Fin 2) :
    |A i j| ≤ sl2RowRadius A :=
  (euclideanNorm_coordinate_le (A i) j).trans (sl2_row_norm_le_radius A i)

theorem projectiveGrowth_sl2_pos (A : RealSL2) (p : ProjectivePoint) :
    0 < projectiveGrowth (A : Matrix2) p := by
  induction p using Projectivization.ind with
  | h u hu =>
    rw [projectiveGrowth_mk, vectorGrowth]
    exact div_pos (euclideanNorm_pos _ (sl2_mulVec_ne_zero A A.det_coe u hu))
      (euclideanNorm_pos u hu)

theorem projectiveGrowth_sl2_le (A : RealSL2) (p : ProjectivePoint) :
    projectiveGrowth (A : Matrix2) p ≤ 2 * sl2RowRadius A := by
  induction p using Projectivization.ind with
  | h u hu =>
    rw [projectiveGrowth_mk, vectorGrowth]
    exact (div_le_iff₀ (euclideanNorm_pos u hu)).mpr
      (euclideanNorm_mulVec_le A _
        (mul_nonneg (by norm_num) (sl2RowRadius_nonneg A))
        (coefficientSquareSum_le_sl2RowRadius A) u)

theorem inv_sl2RowRadius_le_projectiveGrowth (A : RealSL2) (p : ProjectivePoint) :
    (2 * sl2RowRadius A)⁻¹ ≤ projectiveGrowth (A : Matrix2) p := by
  induction p using Projectivization.ind with
  | h u hu =>
    have hi : coefficientSquareSum ((A⁻¹ : RealSL2) : Matrix2) ≤
        (2 * sl2RowRadius A) ^ 2 := by
      rw [coefficientSquareSum_sl2_inv]
      exact coefficientSquareSum_le_sl2RowRadius A
    have h := euclideanNorm_mulVec_le ((A⁻¹ : RealSL2) : Matrix2)
      (2 * sl2RowRadius A)
      (mul_nonneg (by norm_num) (sl2RowRadius_nonneg A)) hi ((A : Matrix2) *ᵥ u)
    have hcancel : ((A⁻¹ : RealSL2) : Matrix2) * (A : Matrix2) = 1 := by
      simpa only [← SpecialLinearGroup.coe_mul, inv_mul_cancel,
        SpecialLinearGroup.coe_one]
    rw [Matrix.mulVec_mulVec, hcancel, Matrix.one_mulVec] at h
    rw [projectiveGrowth_mk, vectorGrowth]
    apply (le_div_iff₀ (euclideanNorm_pos u hu)).mpr
    apply (inv_mul_le_iff₀ (mul_pos (by norm_num) (sl2RowRadius_pos A))).mpr
    simpa only [mul_comm] using h

def sl2RowPerpendicular (A : RealSL2) (i : Fin 2) : Vector2 :=
  ![-A i 1, A i 0]

theorem euclideanNorm_sl2RowPerpendicular (A : RealSL2) (i : Fin 2) :
    euclideanNorm (sl2RowPerpendicular A i) = euclideanNorm (A i) := by
  unfold euclideanNorm euclideanNormSq sl2RowPerpendicular
  congr 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_sq]
  ring

theorem sl2RowPerpendicular_ne_zero (A : RealSL2) (i : Fin 2) :
    sl2RowPerpendicular A i ≠ 0 := by
  intro hz
  have hn := euclideanNorm_sl2RowPerpendicular A i
  rw [hz] at hn
  have hp := euclideanNorm_pos (A i) (A.row_ne_zero i)
  have hzero : euclideanNorm (0 : Vector2) = 0 := by simp [euclideanNorm, euclideanNormSq]
  rw [hzero] at hn
  linarith

def sl2RowKernel (A : RealSL2) (i : Fin 2) : ProjectivePoint :=
  Projectivization.mk ℝ (sl2RowPerpendicular A i) (sl2RowPerpendicular_ne_zero A i)

theorem row_norm_mul_projectiveDistance_le_growth (A : RealSL2) (i : Fin 2)
    (p : ProjectivePoint) :
    euclideanNorm (A i) * projectiveDistance p (sl2RowKernel A i) ≤
      projectiveGrowth (A : Matrix2) p := by
  induction p using Projectivization.ind with
  | h u hu =>
    rw [sl2RowKernel, projectiveDistance_mk, projectiveGrowth_mk]
    have hcoord := euclideanNorm_coordinate_le ((A : Matrix2) *ᵥ u) i
    have hw : wedge u (sl2RowPerpendicular A i) = ((A : Matrix2) *ᵥ u) i := by
      simp [wedge, sl2RowPerpendicular, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      ring
    unfold determinantDistance vectorGrowth
    rw [euclideanNorm_sl2RowPerpendicular, hw]
    calc
      euclideanNorm (A i) *
          (|((A : Matrix2) *ᵥ u) i| / (euclideanNorm u * euclideanNorm (A i))) =
          |((A : Matrix2) *ᵥ u) i| / euclideanNorm u := by
        field_simp [(euclideanNorm_pos u hu).ne',
          (euclideanNorm_pos (A i) (A.row_ne_zero i)).ne']
      _ ≤ euclideanNorm ((A : Matrix2) *ᵥ u) / euclideanNorm u :=
        div_le_div_of_nonneg_right hcoord (euclideanNorm_nonneg u)

theorem exists_sl2RowKernel_growth_lower (A : RealSL2) :
    ∃ β : ProjectivePoint, ∀ p,
      sl2RowRadius A * projectiveDistance p β ≤ projectiveGrowth (A : Matrix2) p := by
  by_cases h : euclideanNorm (A 0) ≤ euclideanNorm (A 1)
  · refine ⟨sl2RowKernel A 1, fun p => ?_⟩
    simpa only [sl2RowRadius, max_eq_right h] using
      row_norm_mul_projectiveDistance_le_growth A 1 p
  · refine ⟨sl2RowKernel A 0, fun p => ?_⟩
    simpa only [sl2RowRadius, max_eq_left (le_of_not_ge h)] using
      row_norm_mul_projectiveDistance_le_growth A 0 p

theorem continuous_sl2_projectiveGrowth :
    Continuous (fun z : RealSL2 × ProjectivePoint => projectiveGrowth (z.1 : Matrix2) z.2) := by
  have hcoeff : Continuous (fun A : RealSL2 => (fun i j : Fin 2 => A i j)) :=
    continuous_pi (fun i => SpecialLinearGroup.continuous_apply id continuous_id i)
  have hpair : Continuous (fun z : RealSL2 × ProjectivePoint =>
      ((fun i j : Fin 2 => z.1 i j), z.2)) :=
    (hcoeff.comp continuous_fst).prodMk continuous_snd
  have hmatrix : Continuous (fun A : Fin 2 → Fin 2 → ℝ => (A : Matrix2)) := by
    exact continuous_pi (fun i => continuous_apply i)
  have hc : Continuous (fun z : (Fin 2 → Fin 2 → ℝ) × ProjectivePoint =>
      projectiveGrowth (z.1 : Matrix2) z.2) :=
    continuous_projectiveGrowth (S := Fin 2 → Fin 2 → ℝ) (fun A => A) hmatrix
  have hcomp := hc.comp hpair
  have heq : ((fun z : (Fin 2 → Fin 2 → ℝ) × ProjectivePoint =>
      projectiveGrowth (z.1 : Matrix2) z.2) ∘
      (fun z : RealSL2 × ProjectivePoint => ((fun i j : Fin 2 => z.1 i j), z.2))) =
      (fun z : RealSL2 × ProjectivePoint => projectiveGrowth (z.1 : Matrix2) z.2) := by
    rfl
  rw [heq] at hcomp
  exact hcomp

theorem continuous_sl2_projectiveLogGrowth :
    Continuous (fun z : RealSL2 × ProjectivePoint => projectiveLogGrowth z.1 z.2) :=
  continuous_sl2_projectiveGrowth.log (fun z => (projectiveGrowth_sl2_pos z.1 z.2).ne')

def sl2LogContinuousMap (A : RealSL2) : C(ProjectivePoint, ℝ) where
  toFun := projectiveLogGrowth A
  continuous_toFun := by
    exact (continuous_projectiveGrowth_fixed (A : Matrix2)).log
      (fun p => (projectiveGrowth_sl2_pos A p).ne')

theorem continuous_sl2LogContinuousMap : Continuous sl2LogContinuousMap := by
  apply ContinuousMap.continuous_of_continuous_uncurry sl2LogContinuousMap
  exact continuous_sl2_projectiveLogGrowth

theorem continuous_schrodingerTransferSL2_fixed (E : ℝ) :
    Continuous (schrodingerTransferSL2 E) :=
  (continuous_transfer_fixed E).subtype_mk (fun v => transfer_det E v)

def stationarySL2Mean (ν : ProbabilityMeasure ProjectivePoint) (A : RealSL2) : ℝ :=
  ∫ p, projectiveLogGrowth A p ∂(ν : Measure ProjectivePoint)

theorem continuous_stationarySL2Mean (ν : ProbabilityMeasure ProjectivePoint) :
    Continuous (stationarySL2Mean ν) := by
  have hpair : Continuous (fun A : RealSL2 => (sl2LogContinuousMap A, ν)) :=
    continuous_sl2LogContinuousMap.prodMk continuous_const
  exact continuous_testIntegral.comp hpair

theorem projectiveLogGrowth_sl2_mul_transfer (A : RealSL2) (E v : ℝ)
    (p : ProjectivePoint) :
    projectiveLogGrowth (A * schrodingerTransferSL2 E v : RealSL2) p =
      projectiveLogGrowth A (transferProjective E v p) + transferLogCocycle E v p := by
  induction p using Projectivization.ind with
  | h u hu =>
    have hn := (euclideanNorm_pos _
      (sl2_mulVec_ne_zero _ (transfer_det E v) u hu)).ne'
    have hu' := (euclideanNorm_pos u hu).ne'
    have hg : projectiveGrowth (A * schrodingerTransferSL2 E v : RealSL2)
        (Projectivization.mk ℝ u hu) =
        projectiveGrowth A (transferProjective E v (Projectivization.mk ℝ u hu)) *
          projectiveGrowth (transfer E v) (Projectivization.mk ℝ u hu) := by
      rw [transferProjective_mk]
      simp only [projectiveGrowth_mk, vectorGrowth, SpecialLinearGroup.coe_mul,
        schrodingerTransferSL2_coe, ← Matrix.mulVec_mulVec]
      field_simp [hn, hu']
    change Real.log _ = Real.log _ + Real.log _
    rw [hg, Real.log_mul (projectiveGrowth_sl2_pos _ _).ne'
      (projectiveGrowth_transfer_pos E v _).ne']

end FixedCouplingPoisson.Furstenberg
