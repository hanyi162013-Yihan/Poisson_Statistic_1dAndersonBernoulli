import FixedCouplingPoisson.ProductCocycle
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A common small negative moment for actual iid products

A bounded real random variable with positive mean has a negative exponential
moment below one at a sufficiently small positive scale. The Taylor estimate
uses actual Bochner integrals with explicit integrability. The same scale
works for a family with common bounds. Actual product-log bounds and means
then discharge the premises for every pair of projective directions.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter

theorem exists_negative_moment_scale (K m : ℝ) (hK : 0 ≤ K) (hm : 0 < m) :
    ∃ s : ℝ, 0 < s ∧ s ≤ 1 ∧ s * K ≤ 1 ∧ s * K ^ 2 ≤ m / 2 ∧ s * m ≤ 1 := by
  let s := min (1 / (K + 1)) (min (m / (2 * (K ^ 2 + 1))) (1 / (m + 1)))
  have hK1 : 0 < K + 1 := by linarith
  have hK2 : 0 < 2 * (K ^ 2 + 1) := by positivity
  have hm1 : 0 < m + 1 := by linarith
  have hs : 0 < s := lt_min (div_pos zero_lt_one hK1)
    (lt_min (div_pos hm hK2) (div_pos zero_lt_one hm1))
  have h1 : s * (K + 1) ≤ 1 :=
    (le_div_iff₀ hK1).mp (min_le_left _ _)
  have h2 : s * (2 * (K ^ 2 + 1)) ≤ m :=
    (le_div_iff₀ hK2).mp ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : s * (m + 1) ≤ 1 :=
    (le_div_iff₀ hm1).mp ((min_le_right _ _).trans (min_le_right _ _))
  have hs1 : s ≤ 1 := (min_le_left _ _).trans
    ((div_le_iff₀ hK1).mpr (by linarith))
  refine ⟨s, hs, hs1, ?_, ?_, ?_⟩ <;> nlinarith only [hs, h1, h2, h3]

theorem integrable_exp_negative_of_abs_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    (K s : ℝ) (hs : 0 ≤ s) (hbound : ∀ᵐ ω ∂P, |X ω| ≤ K) :
    Integrable (fun ω => Real.exp (-s * X ω)) P := by
  apply (integrable_const (Real.exp (s * K))).mono'
    ((hX.const_mul (-s)).exp.aestronglyMeasurable)
  apply hbound.mono
  intro ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left (abs_le.mp hω).1 hs
  nlinarith only [hmul]

theorem integral_exp_negative_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ)
    (hX : Measurable X) (K m s : ℝ) (hK : 0 ≤ K)
    (hs : 0 < s) (hscale : s * K ≤ 1) (hquad : s * K ^ 2 ≤ m / 2)
    (hbound : ∀ᵐ ω ∂P, |X ω| ≤ K) (hmean : m ≤ ∫ ω, X ω ∂P) :
    (∫ ω, Real.exp (-s * X ω) ∂P) ≤ 1 - s * m / 2 := by
  have hXi : Integrable X P := (integrable_const K).mono' hX.aestronglyMeasurable
    (hbound.mono fun ω hω => by simpa only [Real.norm_eq_abs] using hω)
  have hExpi : Integrable (fun ω => Real.exp (-s * X ω)) P := by
    exact integrable_exp_negative_of_abs_bound P X hX K s hs.le hbound
  have hlinearPoly : Integrable (fun ω => 1 - s * X ω) P :=
    (integrable_const 1).sub (hXi.const_mul s)
  have hpoly : Integrable (fun ω => 1 - s * X ω + s ^ 2 * K ^ 2) P :=
    hlinearPoly.add (integrable_const _)
  have htaylor : ∀ᵐ ω ∂P,
      Real.exp (-s * X ω) ≤ 1 - s * X ω + s ^ 2 * K ^ 2 := by
    apply hbound.mono
    intro ω hω
    have hx : |-s * X ω| ≤ 1 := by
      rw [abs_mul, abs_neg, abs_of_pos hs]
      exact (mul_le_mul_of_nonneg_left hω hs.le).trans hscale
    have ht := (abs_le.mp (Real.abs_exp_sub_one_sub_id_le hx)).2
    have hsq : (X ω) ^ 2 ≤ K ^ 2 := by
      have h := (sq_le_sq₀ (abs_nonneg (X ω)) hK).mpr hω
      simpa only [sq_abs] using h
    have hsqmul := mul_le_mul_of_nonneg_left hsq (sq_nonneg s)
    nlinarith only [ht, hsqmul]
  have hi := integral_mono_ae hExpi hpoly htaylor
  have hp : (∫ ω, 1 - s * X ω + s ^ 2 * K ^ 2 ∂P) =
      1 - s * (∫ ω, X ω ∂P) + s ^ 2 * K ^ 2 := by
    rw [integral_add hlinearPoly (integrable_const _),
      integral_sub (integrable_const 1) (hXi.const_mul s), integral_const_mul]
    simp
  rw [hp] at hi
  have hlinear := mul_le_mul_of_nonneg_left hmean hs.le
  have hquadratic := mul_le_mul_of_nonneg_left hquad hs.le
  nlinarith only [hi, hlinear, hquadratic]

/-- One common scale works for every member of a family, provided the
absolute bound and positive mean are already proved uniformly. -/
theorem exists_uniform_negative_moment {Ω I : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : I → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (K m : ℝ) (hK : 0 ≤ K) (hm : 0 < m)
    (hbound : ∀ i, ∀ᵐ ω ∂P, |X i ω| ≤ K)
    (hmean : ∀ i, m ≤ ∫ ω, X i ω ∂P) :
    ∃ s q : ℝ, 0 < s ∧ s ≤ 1 ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ i, (∫ ω, Real.exp (-s * X i ω) ∂P) ≤ q := by
  obtain ⟨s, hs, hs1, hscale, hquad, hsm⟩ := exists_negative_moment_scale K m hK hm
  refine ⟨s, 1 - s * m / 2, hs, hs1, ?_, ?_, fun i => ?_⟩
  · linarith only [hsm]
  · exact sub_lt_self 1 (half_pos (mul_pos hs hm))
  · exact integral_exp_negative_le P (X i) (hX i) K m s hK hs hscale hquad
      (hbound i) (hmean i)

/-- The small negative moment is proved for the actual iid product and a
common block length, scale, and contraction factor, uniform over both initial
projective lines. It still needs the deterministic determinant-distance
identity to be stated as contraction of projective distance. -/
theorem exists_uniform_product_negative_log_moment (law : PotentialLaw) (E : ℝ)
    (data : QualitativeData law E) :
    ∃ N : ℕ, 0 < N ∧ ∃ s q : ℝ, 0 < s ∧ s ≤ 1 ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ p r : ProjectivePoint,
        (∫ ω, Real.exp (-s *
          (projectiveLogGrowth (transferProduct E ω N) p +
            projectiveLogGrowth (transferProduct E ω N) r)) ∂iidMeasure law) ≤ q := by
  obtain ⟨N, hN, hmean⟩ := exists_uniform_positive_product_log_mean law E data
  obtain ⟨K, hK, hb⟩ := ae_uniform_product_log_bound law E N
  let X : (ProjectivePoint × ProjectivePoint) → PotentialSpace → ℝ := fun z ω =>
    projectiveLogGrowth (transferProduct E ω N) z.1 +
      projectiveLogGrowth (transferProduct E ω N) z.2
  have hXm : ∀ z, Measurable (X z) := fun z =>
    (measurable_projectiveLogGrowth_product E z.1 N).add
      (measurable_projectiveLogGrowth_product E z.2 N)
  have hXb : ∀ z, ∀ᵐ ω ∂iidMeasure law, |X z ω| ≤ 2 * K := by
    intro z
    exact hb.mono fun ω hω => (abs_add_le _ _).trans (by linarith [hω z.1, hω z.2])
  have hm : 0 < (N : ℝ) * stationaryMean law E data.forwardMeasure :=
    mul_pos (by exact_mod_cast hN) data.stationary_mean_pos
  have hXm' : ∀ z, (N : ℝ) * stationaryMean law E data.forwardMeasure ≤
      ∫ ω, X z ω ∂iidMeasure law := by
    intro z
    rw [show X z = (fun ω => projectiveLogGrowth (transferProduct E ω N) z.1 +
      projectiveLogGrowth (transferProduct E ω N) z.2) from rfl,
      integral_add (integrable_projectiveLogGrowth_product law E z.1 N)
        (integrable_projectiveLogGrowth_product law E z.2 N)]
    linarith [hmean z.1, hmean z.2]
  obtain ⟨s, q, hs, hs1, hq0, hq1, hq⟩ := exists_uniform_negative_moment
    (iidMeasure law) X hXm (2 * K)
    ((N : ℝ) * stationaryMean law E data.forwardMeasure)
    (mul_nonneg (by norm_num) hK) hm hXb hXm'
  exact ⟨N, hN, s, q, hs, hs1, hq0, hq1, fun p r => hq (p, r)⟩

end FixedCouplingPoisson.Furstenberg
