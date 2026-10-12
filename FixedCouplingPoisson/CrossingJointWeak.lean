import FixedCouplingPoisson.CrossingRenewal
import FixedCouplingPoisson.ExponentialProduct

/-! Genuine finite-dimensional weak limits for the actual consecutive
crossing waits. The limit is the actual independent exponential product. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

def scaledCanonicalWaitingVector (law : PotentialLaw) (E δ θ φ : ℝ) (m : ℕ)
    (ω : PotentialSpace) (j : Fin m) : ℝ :=
  (idsCandidate law (E + δ) - idsCandidate law E) *
    canonicalLevelWaitingTime E δ θ φ j ω

theorem measurable_scaledCanonicalWaitingVector (law : PotentialLaw)
    (E δ θ φ : ℝ) (m : ℕ) :
    Measurable (scaledCanonicalWaitingVector law E δ θ φ m) :=
  measurable_pi_lambda _ fun j => measurable_const.mul
    (canonicalLevelWaitingTime_measurable E δ θ φ j)

def scaledCanonicalWaitingLaw (law : PotentialLaw) (E δ θ φ : ℝ) (m : ℕ) :
    ProbabilityMeasure (Fin m → ℝ) :=
  ProbabilityMeasure.map (⟨iidMeasure law, inferInstance⟩ : ProbabilityMeasure PotentialSpace)
    (measurable_scaledCanonicalWaitingVector law E δ θ φ m).aemeasurable

theorem scaledCanonicalWaitingLaw_tendsto_exponentialProduct
    {ι : Type*} {F : Filter ι} [F.IsCountablyGenerated]
    (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (E δ θ φ : ι → ℝ)
    (hE : ∀ i, E i ∈ K) (hE' : ∀ i, E i + δ i ∈ K)
    (hδ : ∀ i, 0 ≤ δ i) (hinit : ∀ i, φ i ≤ θ i)
    (hp : ∀ i, 0 < idsCandidate law (E i + δ i) - idsCandidate law (E i))
    (hδlim : Tendsto δ F (𝓝 0))
    (hgap : Tendsto (fun i => θ i - φ i) F (𝓝 0)) (m : ℕ) :
    Tendsto (fun i => scaledCanonicalWaitingLaw law (E i) (δ i) (θ i) (φ i) m)
      F (𝓝 (exponentialProduct (Fin m))) := by
  classical
  let P : ProbabilityMeasure PotentialSpace := ⟨iidMeasure law, inferInstance⟩
  apply laws_tendsto_of_mixed_integer_laplace P
    (fun i => scaledCanonicalWaitingVector law (E i) (δ i) (θ i) (φ i) m)
    (fun i => measurable_scaledCanonicalWaitingVector law (E i) (δ i) (θ i) (φ i) m)
    (fun i ω j => mul_nonneg (hp i).le (Nat.cast_nonneg _))
    (exponentialProduct (Fin m)) (exponentialProduct_ae_nonneg (Fin m))
  intro a
  let t : ℕ → ℝ := fun j => if h : j < m then (a ⟨j, h⟩ : ℝ) else 0
  have ht (j : ℕ) : 0 ≤ t j := by
    dsimp only [t]
    split_ifs <;> positivity
  have h := canonicalLevelLaplace_product_tendsto law input hK E δ θ φ
    hE hE' hδ hinit hp hδlim hgap t ht m
  have htest (i : ι) (ω : PotentialSpace) :
      prefixProduct (fun j => canonicalLevelLaplaceFactor law
        (E i) (δ i) (θ i) (φ i) (t j) j) m ω =
      realMixedLaplaceTest a
        (scaledCanonicalWaitingVector law (E i) (δ i) (θ i) (φ i) m ω) := by
    rw [prefixProduct, ← Fin.prod_univ_eq_prod_range, realMixedLaplaceTest_eq_prod]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [canonicalLevelLaplaceFactor, scaledCanonicalWaitingVector, t,
      dif_pos j.isLt]
    congr 1
    ring
  have htarget : (∏ j ∈ Finset.range m, (1 + t j)⁻¹) =
      ∫ x, realMixedLaplaceTest a x
        ∂(exponentialProduct (Fin m) : Measure (Fin m → ℝ)) := by
    rw [integral_exponentialProduct_mixedLaplace, ← Fin.prod_univ_eq_prod_range]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [t, dif_pos j.isLt]
  simpa only [htest, htarget, P, ProbabilityMeasure.coe_mk] using h

end FixedCouplingPoisson.Furstenberg
