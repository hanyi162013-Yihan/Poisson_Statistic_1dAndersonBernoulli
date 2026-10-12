import FixedCouplingPoisson.Phase
import FixedCouplingPoisson.PhaseCalculus
import FixedCouplingPoisson.Projective
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The actual canonical Schrödinger phase lift

The construction uses the arccos angle of the real transfer vector on the
closed fundamental interval `[-π/2, π/2]`. Subtracting the input angle gives
equal values at both endpoints, so `AddCircle.liftIco` supplies a continuous
periodic displacement. Adding the input angle constructs the global lift.
No phase-lift property is assumed as a hypothesis.
-/
namespace FixedCouplingPoisson

open Real Set Matrix

local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

/-- First coordinate of the actual transfer image of the angular unit vector. -/
noncomputable def transferAngleX (E v θ : ℝ) : ℝ := (E - v) * cos θ - sin θ

/-- The arccos branch is the upper-half-plane transfer angle on the
fundamental interval. It is continuous even at its two endpoints. -/
noncomputable def closedChartPhase (E v θ : ℝ) : ℝ :=
  arccos (transferAngleX E v θ / sqrt (transferAngleNormSq E v θ))

theorem closedChartPhase_continuous (E v : ℝ) : Continuous (closedChartPhase E v) := by
  apply Continuous.arccos
  apply Continuous.div
  · unfold transferAngleX
    fun_prop
  · unfold transferAngleNormSq
    fun_prop
  · intro θ
    exact ne_of_gt (Real.sqrt_pos.mpr (transferAngleNormSq_pos E v θ))

@[simp] theorem closedChartPhase_left (E v : ℝ) :
    closedChartPhase E v (-(Real.pi / 2)) = 0 := by
  simp [closedChartPhase, transferAngleX, transferAngleNormSq]

@[simp] theorem closedChartPhase_right (E v : ℝ) :
    closedChartPhase E v (Real.pi / 2) = Real.pi := by
  simp [closedChartPhase, transferAngleX, transferAngleNormSq]

theorem transferAngleX_factor (E v θ : ℝ) (hc : cos θ ≠ 0) :
    transferAngleX E v θ = cos θ * ((E - v) - tan θ) := by
  unfold transferAngleX
  rw [tan_eq_sin_div_cos]
  field_simp

theorem transferAngleNormSq_factor (E v θ : ℝ) (hc : cos θ ≠ 0) :
    transferAngleNormSq E v θ = cos θ ^ 2 * (1 + ((E - v) - tan θ) ^ 2) := by
  change (transferAngleX E v θ) ^ 2 + cos θ ^ 2 = _
  rw [transferAngleX_factor E v θ hc]
  ring

theorem closedChartPhase_eq_chartPhase (E v θ : ℝ)
    (hθ : θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    closedChartPhase E v θ = chartPhase E v θ := by
  have hc := cos_pos_of_mem_Ioo hθ
  have hnorm : sqrt (transferAngleNormSq E v θ) =
      cos θ * sqrt (1 + ((E - v) - tan θ) ^ 2) := by
    rw [transferAngleNormSq_factor E v θ hc.ne', sqrt_mul (sq_nonneg _), sqrt_sq hc.le]
  apply arccos_eq_of_eq_cos (chartPhase_mem E v θ).1.le (chartPhase_mem E v θ).2.le
  rw [transferAngleX_factor E v θ hc.ne', hnorm]
  simp only [chartPhase, cos_pi_div_two_sub, sin_arctan]
  exact mul_div_mul_left _ _ hc.ne'

/-- Displacement on the quotient circle, glued using the equal endpoint values. -/
noncomputable def canonicalDisplacement (E v : ℝ) : AddCircle Real.pi → ℝ :=
  AddCircle.liftIco Real.pi (-(Real.pi / 2)) (fun θ => closedChartPhase E v θ - θ)

/-- The actual globally defined lift, normalized at π/2. -/
noncomputable def canonicalPhase (E v θ : ℝ) : ℝ :=
  θ + canonicalDisplacement E v (θ : AddCircle Real.pi)

theorem canonicalDisplacement_continuous (E v : ℝ) : Continuous (canonicalDisplacement E v) := by
  apply AddCircle.liftIco_continuous
  · have harg : -(Real.pi / 2) + Real.pi = Real.pi / 2 := by ring
    rw [harg, closedChartPhase_left, closedChartPhase_right]
    ring
  · exact ((closedChartPhase_continuous E v).sub continuous_id).continuousOn

theorem canonicalPhase_continuous (E v : ℝ) : Continuous (canonicalPhase E v) := by
  exact continuous_id.add ((canonicalDisplacement_continuous E v).comp
    (AddCircle.continuous_mk' Real.pi))

theorem canonicalPhase_eq_closedChart (E v θ : ℝ)
    (hθ : θ ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) :
    canonicalPhase E v θ = closedChartPhase E v θ := by
  have hθ' : θ ∈ Ico (-(Real.pi / 2)) (-(Real.pi / 2) + Real.pi) := by
    constructor <;> linarith [hθ.1, hθ.2]
  unfold canonicalPhase canonicalDisplacement
  rw [AddCircle.liftIco_coe_apply hθ']
  ring

theorem canonicalPhase_eq_chartPhase (E v θ : ℝ)
    (hθ : θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    canonicalPhase E v θ = chartPhase E v θ := by
  rw [canonicalPhase_eq_closedChart E v θ ⟨hθ.1.le, hθ.2⟩,
    closedChartPhase_eq_chartPhase E v θ hθ]

/-- The integer period is exactly π. -/
theorem canonicalPhase_add_int (E v θ : ℝ) (k : ℤ) :
    canonicalPhase E v (θ + k * Real.pi) = canonicalPhase E v θ + k * Real.pi := by
  have hcoe : ((θ + k * Real.pi : ℝ) : AddCircle Real.pi) = (θ : AddCircle Real.pi) := by
    rw [AddCircle.coe_add]
    have hzero : ((k * Real.pi : ℝ) : AddCircle Real.pi) = 0 :=
      (AddCircle.coe_eq_zero_iff Real.pi).mpr ⟨k, by simp [zsmul_eq_mul]⟩
    rw [hzero, add_zero]
  simp only [canonicalPhase, hcoe]
  ring

@[simp] theorem canonicalPhase_left (E v : ℝ) : canonicalPhase E v (-(Real.pi / 2)) = 0 := by
  rw [canonicalPhase_eq_closedChart E v _ ⟨le_rfl, by linarith [Real.pi_pos]⟩,
    closedChartPhase_left]

@[simp] theorem canonicalPhase_normalized (E v : ℝ) : canonicalPhase E v (Real.pi / 2) = Real.pi := by
  have h := canonicalPhase_add_int E v (-(Real.pi / 2)) 1
  have harg : -(Real.pi / 2) + (1 : ℤ) * Real.pi = Real.pi / 2 := by norm_num; ring
  rw [harg, canonicalPhase_left] at h
  simpa using h

/-- The integer fundamental interval index is independent of the energy. -/
noncomputable def phaseCell (θ : ℝ) : ℤ := Int.floor ((θ + Real.pi / 2) / Real.pi)

noncomputable def reducedPhase (θ : ℝ) : ℝ := θ - phaseCell θ * Real.pi

theorem reducedPhase_mem (θ : ℝ) : reducedPhase θ ∈ Ico (-(Real.pi / 2)) (Real.pi / 2) := by
  have hlo := Int.sub_floor_div_mul_nonneg (θ + Real.pi / 2) Real.pi_pos
  have hhi := Int.sub_floor_div_mul_lt (θ + Real.pi / 2) Real.pi_pos
  change -(Real.pi / 2) ≤ θ - (phaseCell θ : ℝ) * Real.pi ∧
    θ - (phaseCell θ : ℝ) * Real.pi < Real.pi / 2
  dsimp [phaseCell] at *
  constructor <;> linarith

theorem canonicalPhase_cell_formula (E v θ : ℝ) :
    canonicalPhase E v θ = closedChartPhase E v (reducedPhase θ) + phaseCell θ * Real.pi := by
  have h := canonicalPhase_add_int E v (reducedPhase θ) (phaseCell θ)
  have harg : reducedPhase θ + (phaseCell θ : ℝ) * Real.pi = θ := by
    unfold reducedPhase
    ring
  rw [harg, canonicalPhase_eq_closedChart E v _ (reducedPhase_mem θ)] at h
  exact h

theorem closedChartPhase_mem (E v θ : ℝ)
    (hθ : θ ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) :
    closedChartPhase E v θ ∈ Ico 0 Real.pi := by
  by_cases hleft : θ = -(Real.pi / 2)
  · subst θ
    simp only [closedChartPhase_left, mem_Ico, le_refl, true_and]
    exact Real.pi_pos
  · have hθ' : θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨lt_of_le_of_ne hθ.1 (Ne.symm hleft), hθ.2⟩
    rw [closedChartPhase_eq_chartPhase E v θ hθ']
    exact ⟨(chartPhase_mem E v θ).1.le, (chartPhase_mem E v θ).2⟩

theorem closedChartPhase_strictMonoOn (E v : ℝ) :
    StrictMonoOn (closedChartPhase E v) (Ico (-(Real.pi / 2)) (Real.pi / 2)) := by
  intro θ hθ φ hφ hlt
  have hφ' : φ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨lt_of_le_of_lt hθ.1 hlt, hφ.2⟩
  by_cases hleft : θ = -(Real.pi / 2)
  · rw [hleft, closedChartPhase_left, closedChartPhase_eq_chartPhase E v φ hφ']
    exact (chartPhase_mem E v φ).1
  · have hθ' : θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨lt_of_le_of_ne hθ.1 (Ne.symm hleft), hθ.2⟩
    rw [closedChartPhase_eq_chartPhase E v θ hθ', closedChartPhase_eq_chartPhase E v φ hφ']
    exact chartPhase_strictMono_angle E v hθ' hφ' hlt

theorem phaseCell_monotone : Monotone phaseCell := by
  intro θ φ h
  apply Int.floor_mono
  exact div_le_div_of_nonneg_right (by linarith) Real.pi_pos.le

/-- Strict angle monotonicity follows from the actual chart and the ordered
fundamental cells; it is not an assumed property of the new lift. -/
theorem canonicalPhase_strictMono (E v : ℝ) : StrictMono (canonicalPhase E v) := by
  intro θ φ hlt
  have hk := phaseCell_monotone hlt.le
  rw [canonicalPhase_cell_formula, canonicalPhase_cell_formula]
  by_cases heq : phaseCell θ = phaseCell φ
  · have hr : reducedPhase θ < reducedPhase φ := by
      unfold reducedPhase
      rw [heq]
      linarith
    have hh := closedChartPhase_strictMonoOn E v (reducedPhase_mem θ) (reducedPhase_mem φ) hr
    rw [heq]
    linarith
  · have hklt : phaseCell θ < phaseCell φ := lt_of_le_of_ne hk heq
    have hstep' : (((phaseCell θ + 1 : ℤ) : ℝ)) ≤ (phaseCell φ : ℝ) :=
      Int.cast_le.mpr (Int.add_one_le_iff.mpr hklt)
    have hstep : (phaseCell θ : ℝ) + 1 ≤ (phaseCell φ : ℝ) := by simpa using hstep'
    have hm := mul_le_mul_of_nonneg_right hstep Real.pi_pos.le
    have hθ := (closedChartPhase_mem E v _ (reducedPhase_mem θ)).2
    have hφ := (closedChartPhase_mem E v _ (reducedPhase_mem φ)).1
    linarith

/-- The actual transfer phase now inhabits the previously abstract interface. -/
noncomputable def canonicalPhaseLift (E v : ℝ) : PhaseLift where
  toFun := canonicalPhase E v
  strictMono := canonicalPhase_strictMono E v
  equivariant := canonicalPhase_add_int E v

theorem closedChartPhase_energy_close (E v θ δ : ℝ) (hδ : 0 ≤ δ)
    (hθ : θ ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) :
    0 ≤ closedChartPhase E v θ - closedChartPhase (E + δ) v θ ∧
      closedChartPhase E v θ - closedChartPhase (E + δ) v θ ≤ δ := by
  by_cases hleft : θ = -(Real.pi / 2)
  · subst θ
    simp only [closedChartPhase_left, sub_self, le_refl, true_and]
    exact hδ
  · have hθ' : θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨lt_of_le_of_ne hθ.1 (Ne.symm hleft), hθ.2⟩
    rw [closedChartPhase_eq_chartPhase E v θ hθ',
      closedChartPhase_eq_chartPhase (E + δ) v θ hθ']
    exact chartPhase_energy_close E v θ δ hδ

/-- The manuscript's exact all-angle one-step energy perturbation bound. -/
theorem canonicalPhase_energy_close (E v θ δ : ℝ) (hδ : 0 ≤ δ) :
    0 ≤ canonicalPhase E v θ - canonicalPhase (E + δ) v θ ∧
      canonicalPhase E v θ - canonicalPhase (E + δ) v θ ≤ δ := by
  rw [canonicalPhase_cell_formula, canonicalPhase_cell_formula]
  have h := closedChartPhase_energy_close E v (reducedPhase θ) δ hδ (reducedPhase_mem θ)
  constructor <;> linarith [h.1, h.2]

/-- Increasing the energy can only decrease the constructed lift. -/
theorem canonicalPhase_antitone_energy (v θ : ℝ) : Antitone (fun E => canonicalPhase E v θ) := by
  intro E E' hEE'
  have h := (canonicalPhase_energy_close E v θ (E' - E) (sub_nonneg.mpr hEE')).1
  have harg : E + (E' - E) = E' := by ring
  rw [harg] at h
  exact sub_nonneg.mp h

/-- The actual Euclidean unit vector at an angle. -/
noncomputable def angleVector (θ : ℝ) : Vector2 := ![cos θ, sin θ]

theorem angleVector_ne_zero (θ : ℝ) : angleVector θ ≠ 0 := by
  intro h
  have hc : cos θ = 0 := congrFun h 0
  have hs : sin θ = 0 := congrFun h 1
  have hunit := sin_sq_add_cos_sq θ
  rw [hc, hs] at hunit
  norm_num at hunit

theorem angleVector_add_int (θ : ℝ) (k : ℤ) :
    angleVector (θ + k * Real.pi) = (-1 : ℝ) ^ k • angleVector θ := by
  ext i
  fin_cases i <;> simp [angleVector, cos_add_int_mul_pi, sin_add_int_mul_pi]

theorem euclideanNorm_transfer_angleVector (E v θ : ℝ) :
    euclideanNorm (transfer E v *ᵥ angleVector θ) = sqrt (transferAngleNormSq E v θ) := by
  simp [euclideanNorm, euclideanNormSq, transfer_mulVec, angleVector, transferAngleNormSq]

theorem transferAngleNorm_sqrt_factor (E v θ : ℝ)
    (hθ : θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    sqrt (transferAngleNormSq E v θ) = cos θ * sqrt (1 + ((E - v) - tan θ) ^ 2) := by
  have hc := cos_pos_of_mem_Ioo hθ
  rw [transferAngleNormSq_factor E v θ hc.ne', sqrt_mul (sq_nonneg _), sqrt_sq hc.le]

/-- On the fundamental interval, the actual transfer vector is a positive
Euclidean length times the vector at the constructed angle. -/
theorem closedChartPhase_actual_vector (E v θ : ℝ)
    (hθ : θ ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) :
    transfer E v *ᵥ angleVector θ =
      sqrt (transferAngleNormSq E v θ) • angleVector (closedChartPhase E v θ) := by
  by_cases hleft : θ = -(Real.pi / 2)
  · subst θ
    simp [angleVector, transfer_mulVec, transferAngleNormSq]
  · have hθ' : θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨lt_of_le_of_ne hθ.1 (Ne.symm hleft), hθ.2⟩
    have hc := cos_pos_of_mem_Ioo hθ'
    have hsqrt : sqrt (1 + ((E - v) - tan θ) ^ 2) ≠ 0 := by
      apply ne_of_gt
      apply sqrt_pos.mpr
      linarith [sq_nonneg ((E - v) - tan θ)]
    rw [closedChartPhase_eq_chartPhase E v θ hθ', transfer_mulVec]
    ext i
    fin_cases i
    · simp only [angleVector, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
      change transferAngleX E v θ = sqrt (transferAngleNormSq E v θ) * cos (chartPhase E v θ)
      rw [transferAngleX_factor E v θ hc.ne', transferAngleNorm_sqrt_factor E v θ hθ']
      simp only [chartPhase, cos_pi_div_two_sub, sin_arctan]
      field_simp
    · simp only [angleVector, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one]
      change cos θ = sqrt (transferAngleNormSq E v θ) * sin (chartPhase E v θ)
      rw [transferAngleNorm_sqrt_factor E v θ hθ']
      simp only [chartPhase, sin_pi_div_two_sub, cos_arctan]
      field_simp

/-- Global correspondence with the actual vector, including its orientation.
The scaling factor is the positive Euclidean norm of the transfer image. -/
theorem canonicalPhase_actual_vector (E v θ : ℝ) :
    transfer E v *ᵥ angleVector θ =
      euclideanNorm (transfer E v *ᵥ angleVector θ) • angleVector (canonicalPhase E v θ) := by
  let k := phaseCell θ
  let r := reducedPhase θ
  have harg : r + (k : ℝ) * Real.pi = θ := by
    dsimp [r, k, reducedPhase]
    ring
  have hin : angleVector θ = (-1 : ℝ) ^ k • angleVector r := by
    rw [← harg, angleVector_add_int]
  have hout : angleVector (canonicalPhase E v θ) =
      (-1 : ℝ) ^ k • angleVector (closedChartPhase E v r) := by
    rw [canonicalPhase_cell_formula, angleVector_add_int]
  have hsabs : |(-1 : ℝ) ^ k| = 1 := by simp
  have hnorm : euclideanNorm (transfer E v *ᵥ angleVector θ) =
      sqrt (transferAngleNormSq E v r) := by
    rw [hin, Matrix.mulVec_smul, euclideanNorm_smul, hsabs, one_mul,
      euclideanNorm_transfer_angleVector]
  rw [hnorm, hout, hin, Matrix.mulVec_smul,
    closedChartPhase_actual_vector E v r (reducedPhase_mem θ)]
  exact smul_comm _ _ _

/-- The constructed real lift induces exactly the already defined actual
Schrödinger projective action. -/
theorem canonicalPhase_projective (E v θ : ℝ) :
    Projectivization.mk ℝ (angleVector (canonicalPhase E v θ))
        (angleVector_ne_zero (canonicalPhase E v θ)) =
      transferProjective E v (Projectivization.mk ℝ (angleVector θ) (angleVector_ne_zero θ)) := by
  rw [transferProjective_mk]
  apply (wedge_eq_zero_iff_projective_eq _ _ _ _).mp
  rw [canonicalPhase_actual_vector, wedge_smul_right, wedge_self, mul_zero]

/-- The squared norm of the transfer image is π-periodic. -/
theorem transferAngleNormSq_add_int (E v θ : ℝ) (k : ℤ) :
    transferAngleNormSq E v (θ + k * Real.pi) = transferAngleNormSq E v θ := by
  have hsabs : |(-1 : ℝ) ^ k| = 1 := by simp
  have hs : ((-1 : ℝ) ^ k) ^ 2 = 1 := by
    rw [← sq_abs, hsabs]
    norm_num
  simp only [transferAngleNormSq, cos_add_int_mul_pi, sin_add_int_mul_pi]
  calc
    ((E - v) * ((-1) ^ k * cos θ) - (-1) ^ k * sin θ) ^ 2 +
        ((-1) ^ k * cos θ) ^ 2 =
        ((-1) ^ k) ^ 2 * (((E - v) * cos θ - sin θ) ^ 2 + cos θ ^ 2) := by ring
    _ = _ := by rw [hs, one_mul]

theorem cos_sq_add_int (θ : ℝ) (k : ℤ) : cos (θ + k * Real.pi) ^ 2 = cos θ ^ 2 := by
  rw [cos_add_int_mul_pi, mul_pow, ← sq_abs]
  simp

/-- The actual energy derivative extends across the fundamental chart boundary. -/
theorem closedChartPhase_hasDerivAt_energy (E v θ : ℝ)
    (hθ : θ ∈ Ico (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt (fun e => closedChartPhase e v θ)
      (-(cos θ ^ 2 / transferAngleNormSq E v θ)) E := by
  by_cases hleft : θ = -(Real.pi / 2)
  · subst θ
    simpa only [closedChartPhase_left, cos_neg, cos_pi_div_two, zero_pow (by norm_num : 2 ≠ 0),
      zero_div, neg_zero] using hasDerivAt_const E (0 : ℝ)
  · have hθ' : θ ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
      ⟨lt_of_le_of_ne hθ.1 (Ne.symm hleft), hθ.2⟩
    have hc := cos_pos_of_mem_Ioo hθ'
    have hratio : cos θ ^ 2 / transferAngleNormSq E v θ =
        1 / (1 + ((E - v) - tan θ) ^ 2) := by
      rw [transferAngleNormSq_factor E v θ hc.ne', div_mul_eq_div_div,
        div_self (pow_ne_zero 2 hc.ne')]
    have hfun : (fun e => closedChartPhase e v θ) = (fun e => chartPhase e v θ) :=
      funext (fun e => closedChartPhase_eq_chartPhase e v θ hθ')
    rw [hfun, hratio]
    exact chartPhase_hasDerivAt_energy E v θ

/-- The global derivative is exactly the manuscript's squared-cosine formula,
including angles where the cosine vanishes. -/
theorem canonicalPhase_hasDerivAt_energy (E v θ : ℝ) :
    HasDerivAt (fun e => canonicalPhase e v θ)
      (-(cos θ ^ 2 / transferAngleNormSq E v θ)) E := by
  have hfun : (fun e => canonicalPhase e v θ) =
      (fun e => closedChartPhase e v (reducedPhase θ) + phaseCell θ * Real.pi) :=
    funext (fun e => canonicalPhase_cell_formula e v θ)
  have harg : reducedPhase θ + (phaseCell θ : ℝ) * Real.pi = θ := by
    unfold reducedPhase
    ring
  have hratio : cos θ ^ 2 / transferAngleNormSq E v θ =
      cos (reducedPhase θ) ^ 2 / transferAngleNormSq E v (reducedPhase θ) := by
    conv_lhs => rw [← harg]
    rw [cos_sq_add_int, transferAngleNormSq_add_int]
  rw [hfun, hratio]
  exact (closedChartPhase_hasDerivAt_energy E v _ (reducedPhase_mem θ)).add_const _

/-- Changing the potential is exactly an opposite change of energy. -/
theorem canonicalPhase_sub_potential (E v θ : ℝ) :
    canonicalPhase E v θ = canonicalPhase (E - v) 0 θ := by
  simp only [canonicalPhase, canonicalDisplacement, closedChartPhase, transferAngleX,
    transferAngleNormSq, sub_zero]

theorem canonicalPhase_energy_abs_le (E E' v θ : ℝ) :
    |canonicalPhase E v θ - canonicalPhase E' v θ| ≤ |E - E'| := by
  by_cases hEE' : E ≤ E'
  · have hc := canonicalPhase_energy_close E v θ (E' - E) (sub_nonneg.mpr hEE')
    have harg : E + (E' - E) = E' := by ring
    rw [harg] at hc
    rw [abs_of_nonneg hc.1, abs_of_nonpos (sub_nonpos.mpr hEE')]
    linarith [hc.2]
  · have hE'E := le_of_not_ge hEE'
    have hc := canonicalPhase_energy_close E' v θ (E - E') (sub_nonneg.mpr hE'E)
    have harg : E' + (E - E') = E := by ring
    rw [harg] at hc
    rw [abs_sub_comm, abs_of_nonneg hc.1, abs_of_nonneg (sub_nonneg.mpr hE'E)]
    exact hc.2

/-- Uniform energy Lipschitz continuity, with constant one at every angle. -/
theorem canonicalPhase_energy_lipschitz (v θ : ℝ) :
    LipschitzWith 1 (fun E => canonicalPhase E v θ) := by
  apply LipschitzWith.of_dist_le_mul
  intro E E'
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
    canonicalPhase_energy_abs_le E E' v θ

/-- Joint energy/angle continuity follows from the proved uniform energy
Lipschitz estimate and the constructed angle continuity. -/
theorem canonicalPhase_continuous_energy_angle (v : ℝ) :
    Continuous (fun p : ℝ × ℝ => canonicalPhase p.1 v p.2) :=
  continuous_prod_of_continuous_lipschitzWith _ 1
    (fun E => canonicalPhase_continuous E v) (fun θ => canonicalPhase_energy_lipschitz v θ)

/-- Joint potential/angle continuity of the real canonical transfer map. -/
theorem canonicalPhase_continuous_potential_angle (E : ℝ) :
    Continuous (fun p : ℝ × ℝ => canonicalPhase E p.1 p.2) := by
  have hfun : (fun p : ℝ × ℝ => canonicalPhase E p.1 p.2) =
      (fun p : ℝ × ℝ => canonicalPhase (E - p.1) 0 p.2) :=
    funext (fun p => canonicalPhase_sub_potential E p.1 p.2)
  rw [hfun]
  exact (canonicalPhase_continuous_energy_angle 0).comp
    ((continuous_const.sub continuous_fst).prodMk continuous_snd)

/-- The actual phase step is jointly Borel measurable. -/
theorem canonicalPhase_measurable_potential_angle (E : ℝ) :
    Measurable (fun p : ℝ × ℝ => canonicalPhase E p.1 p.2) :=
  (canonicalPhase_continuous_potential_angle E).measurable

end FixedCouplingPoisson
