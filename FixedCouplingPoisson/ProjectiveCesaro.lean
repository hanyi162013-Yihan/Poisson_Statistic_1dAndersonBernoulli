import FixedCouplingPoisson.ProjectiveFeller
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Uniform Cesàro convergence of actual transfer-law probabilities

The empirical probabilities are normalized finite sums of actual Markov
iterates. Their test defects telescope and tend to zero uniformly over all
initial probabilities. Compactness and stationary-law uniqueness identify
all cluster points. Only uniqueness is taken from `QualitativeData`; Cesàro
convergence and the finite positive averaging block are derived here.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Matrix Filter
open scoped Topology

abbrev probabilityOrbit (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (k : ℕ) : ProbabilityMeasure ProjectivePoint :=
  (forwardDistribution law E)^[k] ν

def cesaroFinite (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (n : ℕ) : FiniteMeasure ProjectivePoint :=
  ∑ k ∈ Finset.range (n + 1), (probabilityOrbit law E ν k).toFiniteMeasure

def empiricalCesaro (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (n : ℕ) : ProbabilityMeasure ProjectivePoint :=
  (cesaroFinite law E ν n).normalize

theorem finiteMeasure_mass_add (μ ν : FiniteMeasure ProjectivePoint) :
    (μ + ν).mass = μ.mass + ν.mass := by
  change (μ + ν) Set.univ = μ Set.univ + ν Set.univ
  rw [FiniteMeasure.coeFn_add]
  rfl

theorem cesaroFinite_mass (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (n : ℕ) :
    (cesaroFinite law E ν n).mass = (n + 1 : ℕ) := by
  induction n with
  | zero => simp [cesaroFinite, ProbabilityMeasure.mass_toFiniteMeasure]
  | succ n ih =>
    have hs : cesaroFinite law E ν (n + 1) = cesaroFinite law E ν n +
        (probabilityOrbit law E ν (n + 1)).toFiniteMeasure := by
      unfold cesaroFinite
      rw [Finset.sum_range_succ]
    rw [hs, finiteMeasure_mass_add, ih, ProbabilityMeasure.mass_toFiniteMeasure]
    norm_num

theorem cesaroFinite_ne_zero (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (n : ℕ) : cesaroFinite law E ν n ≠ 0 := by
  apply (FiniteMeasure.mass_nonzero_iff _).mp
  rw [cesaroFinite_mass]
  exact_mod_cast Nat.succ_ne_zero n

theorem cesaroFinite_toMeasure (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (n : ℕ) :
    (cesaroFinite law E ν n : Measure ProjectivePoint) =
      ∑ k ∈ Finset.range (n + 1), (probabilityOrbit law E ν k : Measure ProjectivePoint) := by
  simp only [cesaroFinite, FiniteMeasure.toMeasure_sum,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]

theorem integrable_continuous_test (f : C(ProjectivePoint, ℝ))
    (ν : ProbabilityMeasure ProjectivePoint) : Integrable f (ν : Measure ProjectivePoint) := by
  apply (integrable_const ‖f‖).mono' f.continuous.measurable.aestronglyMeasurable
  exact Filter.Eventually.of_forall f.norm_coe_le_norm

theorem integral_empiricalCesaro (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (n : ℕ) (f : C(ProjectivePoint, ℝ)) :
    (∫ p, f p ∂(empiricalCesaro law E ν n : Measure ProjectivePoint)) =
      ((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ k ∈ Finset.range (n + 1), ∫ p, f p ∂(probabilityOrbit law E ν k : Measure ProjectivePoint) := by
  change (∫ p, f p ∂((cesaroFinite law E ν n).normalize : Measure ProjectivePoint)) = _
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero _ (cesaroFinite_ne_zero law E ν n),
    integral_smul_nnreal_measure, cesaroFinite_mass, cesaroFinite_toMeasure]
  rw [integral_finsetSum_measure (fun k _ => integrable_continuous_test f _)]
  simp only [NNReal.coe_inv, NNReal.coe_natCast, NNReal.smul_def, smul_eq_mul]


@[simp] theorem probabilityOrbit_succ (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (k : ℕ) :
    probabilityOrbit law E ν (k + 1) = forwardDistribution law E (probabilityOrbit law E ν k) :=
  Function.iterate_succ_apply' _ _ _

theorem empiricalCesaro_test_defect (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (n : ℕ) (f : C(ProjectivePoint, ℝ)) :
    forwardTestDefect law E f (empiricalCesaro law E ν n) =
      ((n + 1 : ℕ) : ℝ)⁻¹ *
        ((∫ p, f p ∂(probabilityOrbit law E ν (n + 1) : Measure ProjectivePoint)) -
          ∫ p, f p ∂(ν : Measure ProjectivePoint)) := by
  change (∫ p, (forwardContinuousAverage law E f) p
      ∂(empiricalCesaro law E ν n : Measure ProjectivePoint)) -
    (∫ p, f p ∂(empiricalCesaro law E ν n : Measure ProjectivePoint)) = _
  rw [integral_empiricalCesaro, integral_empiricalCesaro, ← mul_sub,
    ← Finset.sum_sub_distrib]
  congr 1
  calc
    (∑ k ∈ Finset.range (n + 1),
        ((∫ p, (forwardContinuousAverage law E f) p ∂(probabilityOrbit law E ν k : Measure ProjectivePoint)) -
          ∫ p, f p ∂(probabilityOrbit law E ν k : Measure ProjectivePoint))) =
      ∑ k ∈ Finset.range (n + 1),
        ((∫ p, f p ∂(probabilityOrbit law E ν (k + 1) : Measure ProjectivePoint)) -
          ∫ p, f p ∂(probabilityOrbit law E ν k : Measure ProjectivePoint)) := by
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        exact (forwardDistribution_average_integral law E f _).symm.trans
          (by rw [probabilityOrbit_succ])
    _ = _ := Finset.sum_range_sub
      (fun k => ∫ p, f p ∂(probabilityOrbit law E ν k : Measure ProjectivePoint)) (n + 1)

theorem abs_integral_continuous_test_le (f : C(ProjectivePoint, ℝ))
    (ν : ProbabilityMeasure ProjectivePoint) :
    |∫ p, f p ∂(ν : Measure ProjectivePoint)| ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const
    (μ := (ν : Measure ProjectivePoint)) (Filter.Eventually.of_forall f.norm_coe_le_norm)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using h

theorem abs_empiricalCesaro_test_defect_le (law : PotentialLaw) (E : ℝ)
    (ν : ProbabilityMeasure ProjectivePoint) (n : ℕ) (f : C(ProjectivePoint, ℝ)) :
    |forwardTestDefect law E f (empiricalCesaro law E ν n)| ≤
      (2 * ‖f‖) / ((n + 1 : ℕ) : ℝ) := by
  rw [empiricalCesaro_test_defect, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
  have h₁ := abs_integral_continuous_test_le f (probabilityOrbit law E ν (n + 1))
  have h₂ := abs_integral_continuous_test_le f ν
  have hs : |(∫ p, f p ∂(probabilityOrbit law E ν (n + 1) : Measure ProjectivePoint)) -
      ∫ p, f p ∂(ν : Measure ProjectivePoint)| ≤ 2 * ‖f‖ :=
    (abs_sub _ _).trans (by linarith)
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * (2 * ‖f‖) :=
      mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = _ := by rw [div_eq_mul_inv, mul_comm]

theorem empiricalCesaro_test_defect_tendsto (law : PotentialLaw) (E : ℝ)
    (ν : ℕ → ProbabilityMeasure ProjectivePoint) (f : C(ProjectivePoint, ℝ)) :
    Tendsto (fun n => forwardTestDefect law E f (empiricalCesaro law E (ν n) n))
      atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => by
    simpa only [Real.norm_eq_abs] using abs_empiricalCesaro_test_defect_le law E (ν n) n f)
  simpa only [mul_zero, one_div, div_eq_mul_inv, one_mul, Nat.cast_add, Nat.cast_one] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2 * ‖f‖)

/-- This uses only the qualitative stationary-law uniqueness. No Cesàro
convergence or contraction conclusion is included in `QualitativeData`. -/
theorem empiricalCesaro_tendsto (law : PotentialLaw) (E : ℝ)
    (data : QualitativeData law E) (ν : ℕ → ProbabilityMeasure ProjectivePoint) :
    Tendsto (fun n => empiricalCesaro law E (ν n) n) atTop (𝓝 data.forwardMeasure) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro μ hμ
  apply data.forward_unique μ
  exact forward_stationary_of_cluster_vanishing_defect law E _ μ hμ
    (empiricalCesaro_test_defect_tendsto law E ν)


/-- Uniformity over *all* initial probabilities is derived by choosing a
counterexample initial probability at each bad time, then using the preceding
actual-measure convergence theorem. -/
theorem eventually_uniform_integral_empiricalCesaro (law : PotentialLaw) (E : ℝ)
    (data : QualitativeData law E) (f : C(ProjectivePoint, ℝ)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ ν : ProbabilityMeasure ProjectivePoint,
      |(∫ p, f p ∂(empiricalCesaro law E ν n : Measure ProjectivePoint)) -
        ∫ p, f p ∂(data.forwardMeasure : Measure ProjectivePoint)| < ε := by
  classical
  by_contra h
  let bad (n : ℕ) : Prop := ∃ ν : ProbabilityMeasure ProjectivePoint,
    ε ≤ |(∫ p, f p ∂(empiricalCesaro law E ν n : Measure ProjectivePoint)) -
      ∫ p, f p ∂(data.forwardMeasure : Measure ProjectivePoint)|
  have hb : ∃ᶠ n in atTop, bad n := by
    change ¬ ∀ᶠ n in atTop, ¬ bad n
    simpa only [bad, not_exists, not_le] using h
  let initial (n : ℕ) : ProbabilityMeasure ProjectivePoint :=
    if hn : bad n then Classical.choose hn else data.forwardMeasure
  have hint := (ProbabilityMeasure.continuous_integral_continuousMap f).tendsto
    data.forwardMeasure |>.comp (empiricalCesaro_tendsto law E data initial)
  have ha : Tendsto (fun n =>
      |(∫ p, f p ∂(empiricalCesaro law E (initial n) n : Measure ProjectivePoint)) -
        ∫ p, f p ∂(data.forwardMeasure : Measure ProjectivePoint)|) atTop (𝓝 0) := by
    simpa only [sub_self, abs_zero, Function.comp_def] using
      (hint.sub_const (∫ p, f p ∂(data.forwardMeasure : Measure ProjectivePoint))).abs
  have he : ∀ᶠ n in atTop,
      |(∫ p, f p ∂(empiricalCesaro law E (initial n) n : Measure ProjectivePoint)) -
        ∫ p, f p ∂(data.forwardMeasure : Measure ProjectivePoint)| < ε :=
    ha.eventually (gt_mem_nhds hε)
  have hc : ∃ᶠ n in atTop,
      ε ≤ |(∫ p, f p ∂(empiricalCesaro law E (initial n) n : Measure ProjectivePoint)) -
        ∫ p, f p ∂(data.forwardMeasure : Measure ProjectivePoint)| := by
    apply hb.mono
    intro n hn
    simpa only [initial, dif_pos hn] using Classical.choose_spec hn
  exact hc (he.mono fun _ hn => not_le.mpr hn)

/-- A finite averaging block with positive mean, for a genuine continuous
observable. Specialization to actual log growth still requires the cocycle
additivity / iid model bridge and is not claimed by this theorem. -/
theorem exists_positive_average_block (law : PotentialLaw) (E : ℝ)
    (data : QualitativeData law E) (f : C(ProjectivePoint, ℝ))
    (hpos : 0 < ∫ p, f p ∂(data.forwardMeasure : Measure ProjectivePoint)) :
    ∃ n : ℕ, ∀ ν : ProbabilityMeasure ProjectivePoint,
      (∫ p, f p ∂(data.forwardMeasure : Measure ProjectivePoint)) / 2 ≤
        ∫ p, f p ∂(empiricalCesaro law E ν n : Measure ProjectivePoint) := by
  obtain ⟨n, hn⟩ := (eventually_uniform_integral_empiricalCesaro law E data f
    ((∫ p, f p ∂(data.forwardMeasure : Measure ProjectivePoint)) / 2) (half_pos hpos)).exists
  refine ⟨n, fun ν => ?_⟩
  have h := (abs_lt.mp (hn ν)).1
  linarith

end FixedCouplingPoisson.Furstenberg
