import FixedCouplingPoisson.PoissonCloudIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The actual unit-cell cloud has the unit-intensity Poisson Laplace functional
on nonnegative compactly supported continuous tests. No PPP interface is assumed. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter CompactlySupported
open scoped NNReal unitInterval Topology

def poissonLaplaceDefect (f : C_c(ℝ, ℝ)) : C_c(ℝ, ℝ) where
  toFun x := 1 - Real.exp (-f x)
  continuous_toFun := by fun_prop
  hasCompactSupport' := by
    have h0 : (fun y : ℝ => 1 - Real.exp (-y)) 0 = 0 := by simp
    simpa only [Function.comp_def] using
      f.hasCompactSupport.comp_left (g := fun y : ℝ => 1 - Real.exp (-y)) h0

theorem integral_uniformMarks_translate (g : ℝ → ℝ) (z : ℤ) :
    (∫ u : I, g ((z : ℝ) + (u : ℝ))) =
      ∫ x in (0 : ℝ)..(1 : ℝ), g (x + (z : ℝ)) := by
  rw [unitInterval.measurePreserving_coe.integral_comp
    unitInterval.measurableEmbedding_coe (fun x : ℝ => g ((z : ℝ) + x))]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  simp only [add_comm (z : ℝ)]

theorem hasSum_integral_uniformMarks_translate (g : ℝ → ℝ) (hg : Integrable g) :
    HasSum (fun z : ℤ => ∫ u : I, g ((z : ℝ) + (u : ℝ))) (∫ x, g x) := by
  simpa only [integral_uniformMarks_translate] using hg.hasSum_intervalIntegral_comp_add_int

theorem integral_poissonCloud_finite_prod (s : Finset ℤ)
    (g : ℤ → (ℕ × (ℕ → I)) → ℝ) (hg : ∀ z, Measurable (g z)) :
    (∫ ω : PoissonCloud, ∏ z ∈ s, g z (ω z) ∂(poissonCloudLaw : Measure PoissonCloud)) =
      ∏ z ∈ s, ∫ p, g z p ∂(poissonUnitCellLaw 1 : Measure (ℕ × (ℕ → I))) := by
  classical
  have hm : Measurable (fun p : s → (ℕ × (ℕ → I)) => ∏ z : s, g (z : ℤ) (p z)) := by fun_prop
  calc
    (∫ ω : PoissonCloud, ∏ z ∈ s, g z (ω z) ∂(poissonCloudLaw : Measure PoissonCloud)) =
        ∫ ω, ∏ z : s, g z (ω z)
          ∂Measure.infinitePi (fun _ : ℤ => (poissonUnitCellLaw 1 : Measure (ℕ × (ℕ → I)))) := by
      change (∫ ω : PoissonCloud, ∏ z ∈ s, g z (ω z)
        ∂Measure.infinitePi (fun _ : ℤ => (poissonUnitCellLaw 1 : Measure (ℕ × (ℕ → I))))) = _
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => (Finset.prod_coe_sort s (fun z => g z (ω z))).symm)
    _ = ∫ p : s → (ℕ × (ℕ → I)), ∏ z : s, g (z : ℤ) (p z)
          ∂Measure.pi (fun _ : s => (poissonUnitCellLaw 1 : Measure (ℕ × (ℕ → I)))) := by
      simpa only [Finset.restrict, Function.comp_def] using
        (integral_restrict_infinitePi
          (μ := fun _ : ℤ => (poissonUnitCellLaw 1 : Measure (ℕ × (ℕ → I))))
          (s := s) hm.aestronglyMeasurable)
    _ = ∏ z ∈ s, ∫ p, g z p ∂(poissonUnitCellLaw 1 : Measure (ℕ × (ℕ → I))) := by
      rw [integral_fintype_prod_eq_prod
        (μ := fun _ : s => (poissonUnitCellLaw 1 : Measure (ℕ × (ℕ → I))))
        (fun (z : s) (p : ℕ × (ℕ → I)) => g (z : ℤ) p)]
      exact Finset.prod_coe_sort s (fun z => ∫ p, g z p
        ∂(poissonUnitCellLaw 1 : Measure (ℕ × (ℕ → I))))

def poissonCloudLaplaceFunctional (f : C_c(ℝ, ℝ)) (ω : PoissonCloud) : ℝ :=
  Real.exp (-(∫ x, f x ∂poissonCloudMeasure ω))

theorem continuous_poissonCloudLaplaceFunctional (f : C_c(ℝ, ℝ)) :
    Continuous (poissonCloudLaplaceFunctional f) := by
  exact ((continuous_integral_poissonCloudMeasure f).neg).rexp

theorem integrable_poissonCloudLaplaceFunctional (f : C_c(ℝ, ℝ))
    (hf0 : ∀ x, 0 ≤ f x) :
    Integrable (poissonCloudLaplaceFunctional f) (poissonCloudLaw : Measure PoissonCloud) := by
  apply Integrable.of_bound (continuous_poissonCloudLaplaceFunctional f).aestronglyMeasurable 1
  exact ae_of_all _ fun ω => by
    rw [poissonCloudLaplaceFunctional, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (integral_nonneg hf0))

theorem poissonCloudLaplaceFunctional_eq_finite_prod (f : C_c(ℝ, ℝ)) (s : Finset ℤ)
    (hs : ∀ z ∉ s, ∀ u : I, f ((z : ℝ) + (u : ℝ)) = 0) (ω : PoissonCloud) :
    poissonCloudLaplaceFunctional f ω =
      ∏ z ∈ s, poissonUnitCellFunctional (fun u : I => Real.exp (-f ((z : ℝ) + (u : ℝ))))
        (ω z) := by
  classical
  rw [poissonCloudLaplaceFunctional, integral_poissonCloudMeasure_finite f s hs,
    ← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro z hz
  rw [poissonUnitCellFunctional, ← Finset.sum_neg_distrib, Real.exp_sum]

theorem integral_poissonCloudLaplaceFunctional (f : C_c(ℝ, ℝ))
    (hf0 : ∀ x, 0 ≤ f x) :
    (∫ ω, poissonCloudLaplaceFunctional f ω ∂(poissonCloudLaw : Measure PoissonCloud)) =
      Real.exp (-(∫ x, 1 - Real.exp (-f x))) := by
  classical
  obtain ⟨s, hs⟩ := exists_poissonCloud_activeCells f
  have hg : ∀ z : ℤ, Measurable (fun u : I => Real.exp (-f ((z : ℝ) + (u : ℝ)))) := by
    intro z
    fun_prop
  have hg0 : ∀ z : ℤ, ∀ u : I, 0 ≤ Real.exp (-f ((z : ℝ) + (u : ℝ))) :=
    fun z u => (Real.exp_pos _).le
  have hg1 : ∀ z : ℤ, ∀ u : I, Real.exp (-f ((z : ℝ) + (u : ℝ))) ≤ 1 :=
    fun z u => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 _))
  have hgi : ∀ z : ℤ, Integrable (fun u : I => Real.exp (-f ((z : ℝ) + (u : ℝ)))) := by
    intro z
    apply Integrable.of_bound (hg z).aestronglyMeasurable 1
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hg0 z u)]
      exact hg1 z u
  have hdef : ∀ z : ℤ,
      (∫ u : I, 1 - Real.exp (-f ((z : ℝ) + (u : ℝ)))) =
        1 - ∫ u : I, Real.exp (-f ((z : ℝ) + (u : ℝ))) := by
    intro z
    rw [integral_sub (integrable_const 1) (hgi z), integral_const]
    simp
  have hsum : (∑ z ∈ s, ∫ u : I, 1 - Real.exp (-f ((z : ℝ) + (u : ℝ)))) =
      ∫ x, 1 - Real.exp (-f x) := by
    have h := (hasSum_integral_uniformMarks_translate (poissonLaplaceDefect f)
      (poissonLaplaceDefect f).integrable).tsum_eq
    change (∑' z : ℤ, ∫ u : I, 1 - Real.exp (-f ((z : ℝ) + (u : ℝ)))) = _ at h
    rw [tsum_eq_sum (s := s) (fun z hz => by simp [hs z hz])] at h
    exact h
  simp_rw [poissonCloudLaplaceFunctional_eq_finite_prod f s hs]
  rw [integral_poissonCloud_finite_prod s _ (fun z =>
    measurable_poissonUnitCellFunctional _ (hg z))]
  simp_rw [integral_poissonUnitCellFunctional 1 _ (hg _) (hg0 _) (hg1 _)]
  simp only [NNReal.coe_one, one_mul]
  rw [← Real.exp_sum]
  congr 1
  rw [← hsum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rw [hdef]
  ring

end FixedCouplingPoisson
