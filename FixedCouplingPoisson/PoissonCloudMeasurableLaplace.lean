import FixedCouplingPoisson.PoissonCloudLaplace

/-! A measurable bounded-support variant of the genuine cloud Laplace
calculation. Its finite-cell form applies directly to interval step tests. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Filter CompactlySupported
open scoped NNReal unitInterval Topology

def poissonCloudFiniteLaplace (f : ℝ → ℝ) (s : Finset ℤ) (ω : PoissonCloud) : ℝ :=
  Real.exp (-(∑ z ∈ s, ∑ j ∈ Finset.range (ω z).1,
    f ((z : ℝ) + ((ω z).2 j : ℝ))))

theorem poissonCloudFiniteLaplace_eq_prod (f : ℝ → ℝ) (s : Finset ℤ) (ω : PoissonCloud) :
    poissonCloudFiniteLaplace f s ω =
      ∏ z ∈ s, poissonUnitCellFunctional (fun u : I => Real.exp (-f ((z : ℝ) + (u : ℝ))))
        (ω z) := by
  classical
  rw [poissonCloudFiniteLaplace, ← Finset.sum_neg_distrib, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro z hz
  rw [poissonUnitCellFunctional, ← Finset.sum_neg_distrib, Real.exp_sum]

theorem integral_poissonCloudFiniteLaplace (f : ℝ → ℝ) (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (s : Finset ℤ) :
    (∫ ω, poissonCloudFiniteLaplace f s ω ∂(poissonCloudLaw : Measure PoissonCloud)) =
      Real.exp (∑ z ∈ s, ((∫ u : I, Real.exp (-f ((z : ℝ) + (u : ℝ)))) - 1)) := by
  classical
  have hg : ∀ z : ℤ, Measurable (fun u : I => Real.exp (-f ((z : ℝ) + (u : ℝ)))) := by
    intro z
    fun_prop
  have hg0 : ∀ z : ℤ, ∀ u : I, 0 ≤ Real.exp (-f ((z : ℝ) + (u : ℝ))) :=
    fun z u => (Real.exp_pos _).le
  have hg1 : ∀ z : ℤ, ∀ u : I, Real.exp (-f ((z : ℝ) + (u : ℝ))) ≤ 1 :=
    fun z u => Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 _))
  simp_rw [poissonCloudFiniteLaplace_eq_prod]
  rw [integral_poissonCloud_finite_prod s _ (fun z =>
    measurable_poissonUnitCellFunctional _ (hg z))]
  simp_rw [integral_poissonUnitCellFunctional 1 _ (hg _) (hg0 _) (hg1 _)]
  simp only [NNReal.coe_one, one_mul]
  rw [← Real.exp_sum]

theorem integral_poissonCloudFiniteLaplace_full (f : ℝ → ℝ) (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfi : Integrable (fun x => 1 - Real.exp (-f x)))
    (s : Finset ℤ) (hs : ∀ z ∉ s, ∀ u : I, f ((z : ℝ) + (u : ℝ)) = 0) :
    (∫ ω, poissonCloudFiniteLaplace f s ω ∂(poissonCloudLaw : Measure PoissonCloud)) =
      Real.exp (-(∫ x, 1 - Real.exp (-f x))) := by
  classical
  have hg : ∀ z : ℤ, Integrable (fun u : I => Real.exp (-f ((z : ℝ) + (u : ℝ)))) := by
    intro z
    have hgm : Measurable (fun u : I => Real.exp (-f ((z : ℝ) + (u : ℝ)))) := by fun_prop
    apply Integrable.of_bound hgm.aestronglyMeasurable 1
    exact ae_of_all _ fun u => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hf0 _))
  have hdef : ∀ z : ℤ,
      (∫ u : I, 1 - Real.exp (-f ((z : ℝ) + (u : ℝ)))) =
        1 - ∫ u : I, Real.exp (-f ((z : ℝ) + (u : ℝ))) := by
    intro z
    rw [integral_sub (integrable_const 1) (hg z), integral_const]
    simp
  have hsum : (∑ z ∈ s, ∫ u : I, 1 - Real.exp (-f ((z : ℝ) + (u : ℝ)))) =
      ∫ x, 1 - Real.exp (-f x) := by
    have h := (hasSum_integral_uniformMarks_translate _ hfi).tsum_eq
    rw [tsum_eq_sum (s := s) (fun z hz => by simp [hs z hz])] at h
    exact h
  rw [integral_poissonCloudFiniteLaplace f hfm hf0 s]
  congr 1
  rw [← hsum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rw [hdef]
  ring

theorem integral_poissonCloudMeasure_finite_of_integrable (f : ℝ → ℝ) (s : Finset ℤ)
    (hs : ∀ z ∉ s, ∀ u : I, f ((z : ℝ) + (u : ℝ)) = 0) (ω : PoissonCloud)
    (hfi : Integrable f (poissonCloudMeasure ω)) :
    (∫ x, f x ∂poissonCloudMeasure ω) =
      ∑ z ∈ s, ∑ j ∈ Finset.range (ω z).1, f ((z : ℝ) + ((ω z).2 j : ℝ)) := by
  classical
  rw [poissonCloudMeasure, integral_sum_measure hfi]
  rw [tsum_eq_sum (s := s) (fun z hz => by
    rw [integral_poissonCellMeasure]
    exact Finset.sum_eq_zero (fun j hj => hs z hz ((ω z).2 j)))]
  simp_rw [integral_poissonCellMeasure]

theorem integral_poissonCloudLaplace_measurable (f : ℝ → ℝ) (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (hfω : ∀ ω, Integrable f (poissonCloudMeasure ω))
    (hfi : Integrable (fun x => 1 - Real.exp (-f x))) (s : Finset ℤ)
    (hs : ∀ z ∉ s, ∀ u : I, f ((z : ℝ) + (u : ℝ)) = 0) :
    (∫ ω, Real.exp (-(∫ x, f x ∂poissonCloudMeasure ω))
      ∂(poissonCloudLaw : Measure PoissonCloud)) =
        Real.exp (-(∫ x, 1 - Real.exp (-f x))) := by
  have hstep (ω : PoissonCloud) :
      (∫ x, f x ∂poissonCloudMeasure ω) =
        ∑ z ∈ s, ∑ j ∈ Finset.range (ω z).1, f ((z : ℝ) + ((ω z).2 j : ℝ)) :=
    integral_poissonCloudMeasure_finite_of_integrable f s hs ω (hfω ω)
  simp_rw [hstep]
  exact integral_poissonCloudFiniteLaplace_full f hfm hf0 hfi s hs

end FixedCouplingPoisson
