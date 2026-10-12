import FixedCouplingPoisson.Model
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.Floor

/-!
# Measurability and expectations of the actual finite-volume spectral counts

The eigenvalues here are the spectral-theorem eigenvalues of the explicit
Dirichlet matrix. Continuous scalar cut approximations, matrix functional
calculus, and the trace establish measurability without assuming that an
eigenvalue enumeration is measurable. No infinite-volume limit is asserted.
-/

namespace FixedCouplingPoisson
open Matrix Filter MeasureTheory
open scoped Matrix.Norms.L2Operator Topology BigOperators

theorem continuous_dirichletMatrix (n : ℕ) : Continuous (dirichletMatrix n) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold dirichletMatrix
  split_ifs <;> first | exact continuous_apply i | exact continuous_const

theorem continuous_trace_cfc_dirichletMatrix (n : ℕ) (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (fun v => Matrix.trace (cfc f (dirichletMatrix n v))) := by
  have hc : Continuous (fun v => cfc f (dirichletMatrix n v)) :=
    (continuous_dirichletMatrix n).cfc_of_mem_nhdsSet f (s := Set.univ) (by simp)
      (fun v => (dirichletMatrix_isHermitian n v).isSelfAdjoint) hf.continuousOn
  exact hc.matrix_trace

theorem trace_cfc_dirichletMatrix (n : ℕ) (v : Fin n → ℝ) (f : ℝ → ℝ) :
    Matrix.trace (cfc f (dirichletMatrix n v)) = ∑ i, f (dirichletEigenvalues n v i) := by
  rw [(dirichletMatrix_isHermitian n v).cfc_eq f, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp [dirichletEigenvalues]

/-- A continuous approximation of the strict cut below `E`. -/
def lowerCutRamp (k : ℕ) (E x : ℝ) : ℝ :=
  max 0 (min 1 ((k : ℝ) * (E - x)))

theorem continuous_lowerCutRamp (k : ℕ) (E : ℝ) : Continuous (lowerCutRamp k E) := by
  exact continuous_const.max
    (continuous_const.min (continuous_const.mul (continuous_const.sub continuous_id)))

theorem lowerCutRamp_tendsto (E x : ℝ) :
    Tendsto (fun k => lowerCutRamp k E x) atTop (𝓝 (if x < E then 1 else 0)) := by
  by_cases hx : x < E
  · obtain ⟨K, hK⟩ := exists_nat_ge (1 / (E - x))
    have hpos : 0 < E - x := sub_pos.mpr hx
    have heq : ∀ᶠ k : ℕ in atTop, lowerCutRamp k E x = 1 := by
      filter_upwards [eventually_ge_atTop K] with k hk
      have hdiv : 1 / (E - x) ≤ (k : ℝ) := hK.trans (by exact_mod_cast hk)
      have hmul : 1 ≤ (k : ℝ) * (E - x) := (div_le_iff₀ hpos).mp hdiv
      simp [lowerCutRamp, min_eq_left hmul]
    simpa [hx] using tendsto_const_nhds.congr' (heq.mono (fun _ hk => hk.symm))
  · have heq (k : ℕ) : lowerCutRamp k E x = 0 := by
      have hmul : (k : ℝ) * (E - x) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (sub_nonpos.mpr (le_of_not_gt hx))
      simp [lowerCutRamp, min_eq_right (hmul.trans zero_le_one), max_eq_left hmul]
    simpa only [heq, if_neg hx] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem strictSpectralCount_eq_sum (n : ℕ) (v : Fin n → ℝ) (E : ℝ) :
    (strictSpectralCount n v E : ℝ) =
      ∑ i, if dirichletEigenvalues n v i < E then (1 : ℝ) else 0 := by
  classical
  simp [strictSpectralCount]

theorem nonstrictSpectralCount_eq_sum (n : ℕ) (v : Fin n → ℝ) (E : ℝ) :
    (nonstrictSpectralCount n v E : ℝ) =
      ∑ i, if dirichletEigenvalues n v i ≤ E then (1 : ℝ) else 0 := by
  classical
  simp [nonstrictSpectralCount]

theorem trace_lowerCutRamp_tendsto (n : ℕ) (v : Fin n → ℝ) (E : ℝ) :
    Tendsto (fun k => Matrix.trace (cfc (lowerCutRamp k E) (dirichletMatrix n v)))
      atTop (𝓝 (strictSpectralCount n v E : ℝ)) := by
  simp_rw [trace_cfc_dirichletMatrix]
  rw [strictSpectralCount_eq_sum]
  exact tendsto_finsetSum _ (fun i _ => lowerCutRamp_tendsto E _)

theorem trace_upperCutRamp_tendsto (n : ℕ) (v : Fin n → ℝ) (E : ℝ) :
    Tendsto (fun k => Matrix.trace
      (cfc (fun x => 1 - lowerCutRamp k (-E) (-x)) (dirichletMatrix n v)))
      atTop (𝓝 (nonstrictSpectralCount n v E : ℝ)) := by
  simp_rw [trace_cfc_dirichletMatrix]
  rw [nonstrictSpectralCount_eq_sum]
  apply tendsto_finsetSum
  intro i _
  have h := (lowerCutRamp_tendsto (-E) (-dirichletEigenvalues n v i)).const_sub 1
  by_cases hi : dirichletEigenvalues n v i ≤ E
  · simpa [neg_lt_neg_iff, not_lt.mpr hi, hi] using h
  · simpa [neg_lt_neg_iff, lt_of_not_ge hi, hi] using h

/-- The real-valued count is measurable for the actual Dirichlet spectrum. -/
theorem measurable_strictSpectralCount_real (n : ℕ) (E : ℝ) :
    Measurable (fun v => (strictSpectralCount n v E : ℝ)) := by
  apply measurable_of_tendsto_metrizable
    (fun k => (continuous_trace_cfc_dirichletMatrix n _ (continuous_lowerCutRamp k E)).measurable)
  exact tendsto_pi_nhds.mpr (fun v => trace_lowerCutRamp_tendsto n v E)

theorem measurable_nonstrictSpectralCount_real (n : ℕ) (E : ℝ) :
    Measurable (fun v => (nonstrictSpectralCount n v E : ℝ)) := by
  apply measurable_of_tendsto_metrizable
    (fun k => (continuous_trace_cfc_dirichletMatrix n _
      (continuous_const.sub ((continuous_lowerCutRamp k (-E)).comp continuous_neg))).measurable)
  exact tendsto_pi_nhds.mpr (fun v => trace_upperCutRamp_tendsto n v E)

theorem measurable_strictSpectralCount (n : ℕ) (E : ℝ) :
    Measurable (fun v => strictSpectralCount n v E) := by
  simpa using (measurable_strictSpectralCount_real n E).nat_floor

theorem measurable_nonstrictSpectralCount (n : ℕ) (E : ℝ) :
    Measurable (fun v => nonstrictSpectralCount n v E) := by
  simpa using (measurable_nonstrictSpectralCount_real n E).nat_floor

theorem strictSpectralCount_real_bounds (n : ℕ) (v : Fin n → ℝ) (E : ℝ) :
    0 ≤ (strictSpectralCount n v E : ℝ) ∧ (strictSpectralCount n v E : ℝ) ≤ n := by
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast strictSpectralCount_le_size n v E⟩

theorem nonstrictSpectralCount_real_bounds (n : ℕ) (v : Fin n → ℝ) (E : ℝ) :
    0 ≤ (nonstrictSpectralCount n v E : ℝ) ∧ (nonstrictSpectralCount n v E : ℝ) ≤ n := by
  exact ⟨Nat.cast_nonneg _, by exact_mod_cast nonstrictSpectralCount_le_size n v E⟩

/-- The finite spectral counts are integrable for every finite measure on potentials. -/
theorem integrable_strictSpectralCount (n : ℕ) (E : ℝ)
    (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun v => (strictSpectralCount n v E : ℝ)) μ := by
  apply (integrable_const (n : ℝ)).mono'
    (measurable_strictSpectralCount_real n E).aestronglyMeasurable
  exact ae_of_all _ (fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (strictSpectralCount_real_bounds n v E).1]
    exact (strictSpectralCount_real_bounds n v E).2)

theorem integrable_nonstrictSpectralCount (n : ℕ) (E : ℝ)
    (μ : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun v => (nonstrictSpectralCount n v E : ℝ)) μ := by
  apply (integrable_const (n : ℝ)).mono'
    (measurable_nonstrictSpectralCount_real n E).aestronglyMeasurable
  exact ae_of_all _ (fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (nonstrictSpectralCount_real_bounds n v E).1]
    exact (nonstrictSpectralCount_real_bounds n v E).2)

theorem integral_nonstrictSpectralCount_bounds (n : ℕ) (E : ℝ)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] :
    0 ≤ ∫ v, (nonstrictSpectralCount n v E : ℝ) ∂μ ∧
      (∫ v, (nonstrictSpectralCount n v E : ℝ) ∂μ) ≤ n := by
  constructor
  · exact integral_nonneg (fun v => (nonstrictSpectralCount_real_bounds n v E).1)
  · have h := integral_mono (integrable_nonstrictSpectralCount n E μ)
      (integrable_const (n : ℝ)) (fun v => (nonstrictSpectralCount_real_bounds n v E).2)
    simpa using h

theorem integral_strictSpectralCount_bounds (n : ℕ) (E : ℝ)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] :
    0 ≤ ∫ v, (strictSpectralCount n v E : ℝ) ∂μ ∧
      (∫ v, (strictSpectralCount n v E : ℝ) ∂μ) ≤ n := by
  constructor
  · exact integral_nonneg (fun v => (strictSpectralCount_real_bounds n v E).1)
  · have h := integral_mono (integrable_strictSpectralCount n E μ)
      (integrable_const (n : ℝ)) (fun v => (strictSpectralCount_real_bounds n v E).2)
    simpa using h

theorem monotone_strictSpectralCount (n : ℕ) (v : Fin n → ℝ) :
    Monotone (strictSpectralCount n v) := by
  classical
  intro E F hEF
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans_le hEF

theorem monotone_nonstrictSpectralCount (n : ℕ) (v : Fin n → ℝ) :
    Monotone (nonstrictSpectralCount n v) := by
  classical
  intro E F hEF
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact hi.trans hEF

theorem meanSpectralCount_bounds (law : PotentialLaw) (n : ℕ) (E : ℝ) :
    0 ≤ meanSpectralCount law n E ∧ meanSpectralCount law n E ≤ n :=
  integral_nonstrictSpectralCount_bounds n E (finitePotentialMeasure law n)

theorem monotone_meanSpectralCount (law : PotentialLaw) (n : ℕ) :
    Monotone (meanSpectralCount law n) := by
  intro E F hEF
  apply integral_mono (integrable_nonstrictSpectralCount n E _)
    (integrable_nonstrictSpectralCount n F _)
  intro v
  exact Nat.cast_le.mpr (monotone_nonstrictSpectralCount n v hEF)

theorem normalizedMeanCount_bounds (law : PotentialLaw) (E : ℝ) (n : ℕ) :
    0 ≤ normalizedMeanCount law E n ∧ normalizedMeanCount law E n ≤ 1 := by
  constructor
  · exact div_nonneg (meanSpectralCount_bounds law n E).1 (Nat.cast_nonneg _)
  · by_cases hn : n = 0
    · simp [normalizedMeanCount, hn]
    · exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero hn)).mpr
        (meanSpectralCount_bounds law n E).2

theorem monotone_normalizedMeanCount (law : PotentialLaw) (n : ℕ) :
    Monotone (fun E => normalizedMeanCount law E n) := by
  intro E F hEF
  exact div_le_div_of_nonneg_right (monotone_meanSpectralCount law n hEF) (Nat.cast_nonneg _)

/-- For the actual simple Dirichlet spectrum, endpoint conventions change the
expected count by at most one, for every probability measure on potentials. -/
theorem integral_spectralCount_endpoint_bounds (n : ℕ) (E : ℝ)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] :
    (∫ v, (strictSpectralCount n v E : ℝ) ∂μ) ≤
        ∫ v, (nonstrictSpectralCount n v E : ℝ) ∂μ ∧
      (∫ v, (nonstrictSpectralCount n v E : ℝ) ∂μ) ≤
        (∫ v, (strictSpectralCount n v E : ℝ) ∂μ) + 1 := by
  constructor
  · apply integral_mono (integrable_strictSpectralCount n E μ)
      (integrable_nonstrictSpectralCount n E μ)
    intro v
    exact Nat.cast_le.mpr (strictSpectralCount_le_nonstrict n v E)
  · have h := integral_mono (integrable_nonstrictSpectralCount n E μ)
      ((integrable_strictSpectralCount n E μ).add (integrable_const (1 : ℝ)))
      (fun v => show (nonstrictSpectralCount n v E : ℝ) ≤ (strictSpectralCount n v E : ℝ) + 1 by
        exact_mod_cast spectralCount_endpoint_le_add_one n v E)
    simpa [integral_add (integrable_strictSpectralCount n E μ) (integrable_const (1 : ℝ))] using h

end FixedCouplingPoisson
