import FixedCouplingPoisson.ActualColoredBlock

/-! Adapted colored products and the exact deterministic block partition. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set
open scoped BigOperators

theorem canonicalBlockCount_past_measurable (E δ θ φ : ℝ) (j L : ℕ) :
    @Measurable PotentialSpace ℕ (pastMeasurableSpace (j + L)) _
      (canonicalBlockCount E δ θ φ j L) := by
  exact (measurable_of_countable Int.toNat).comp
    ((canonicalCrossingCount_past_measurable E δ θ φ (j + L)).sub
      ((canonicalCrossingCount_past_measurable E δ θ φ j).mono
        (pastMeasurableSpace_mono (by omega)) le_rfl))

theorem canonicalColoredFactor_past_measurable (e : ℕ → ℝ) (s j L : ℕ)
    (t : Fin s → ℝ) :
    @Measurable PotentialSpace ℝ (pastMeasurableSpace (j + L)) _
      (fun ω => coloredLaplaceFactor t (canonicalColoredBlock e s j L ω)) := by
  letI : MeasurableSpace PotentialSpace := pastMeasurableSpace (j + L)
  exact measurable_coloredLaplaceFactor t (fun i =>
    canonicalBlockCount_past_measurable _ _ _ _ _ _)

theorem canonicalColoredFactor_measurable (e : ℕ → ℝ) (s j L : ℕ)
    (t : Fin s → ℝ) :
    Measurable (fun ω => coloredLaplaceFactor t (canonicalColoredBlock e s j L ω)) :=
  (canonicalColoredFactor_past_measurable e s j L t).mono
    (pastMeasurableSpace_le (j + L)) le_rfl

theorem canonicalColoredProduct_past_stronglyMeasurable (e : ℕ → ℝ) (s : ℕ)
    (u : ℕ → ℕ) (hu : Monotone u) (t : Fin s → ℝ) (b : ℕ) :
    StronglyMeasurable[pastMeasurableSpace (u b)]
      (prefixProduct (fun j ω => coloredLaplaceFactor t
        (canonicalColoredBlock e s (u j) (u (j + 1) - u j) ω)) b) := by
  letI : MeasurableSpace PotentialSpace := pastMeasurableSpace (u b)
  apply (Finset.range b).stronglyMeasurable_fun_prod
  intro j hj
  have hm := canonicalColoredFactor_past_measurable e s (u j) (u (j + 1) - u j) t
  rw [Nat.add_sub_of_le (hu (Nat.le_succ j))] at hm
  exact (hm.mono (pastMeasurableSpace_mono
    (hu (by have := Finset.mem_range.mp hj; omega))) le_rfl).stronglyMeasurable

theorem prefixProduct_coloredLaplaceFactor {Ω : Type*} (s : ℕ) (t : Fin s → ℝ)
    (X : ℕ → Ω → Fin s → ℕ) (m : ℕ) (ω : Ω) :
    prefixProduct (fun b z => coloredLaplaceFactor t (X b z)) m ω =
      coloredLaplaceFactor t (fun i => ∑ b ∈ Finset.range m, X b ω i) := by
  unfold prefixProduct coloredLaplaceFactor
  rw [← Real.exp_sum]
  congr 1
  simp only [Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_neg_distrib, Finset.sum_comm]

theorem canonicalColoredProduct_eq_total (e : ℕ → ℝ) (s : ℕ)
    (horder : ∀ i < s, e i ≤ e (i + 1)) (u : ℕ → ℕ) (hu : Monotone u)
    (t : Fin s → ℝ) (m : ℕ) (ω : PotentialSpace) :
    prefixProduct (fun b z => coloredLaplaceFactor t
      (canonicalColoredBlock e s (u b) (u (b + 1) - u b) z)) m ω =
        coloredLaplaceFactor t (canonicalColoredBlock e s (u 0) (u m - u 0) ω) := by
  rw [prefixProduct_coloredLaplaceFactor]
  congr 1
  funext i
  exact canonicalBlockCount_sum_partition (e i.val) (e (i.val + 1) - e i.val) 0 0
    (sub_nonneg.mpr (horder i.val i.isLt)) u hu m ω

theorem canonicalColoredProduct_eq_count (e : ℕ → ℝ) (s : ℕ)
    (horder : ∀ i < s, e i ≤ e (i + 1)) (u : ℕ → ℕ) (hu : Monotone u)
    (hu0 : u 0 = 0) (t : Fin s → ℝ) (m : ℕ) (ω : PotentialSpace) :
    prefixProduct (fun b z => coloredLaplaceFactor t
      (canonicalColoredBlock e s (u b) (u (b + 1) - u b) z)) m ω =
        coloredLaplaceFactor t (fun i => canonicalNaturalCrossingCount
          (e i.val) (e (i.val + 1) - e i.val) 0 0 (u m) ω) := by
  rw [canonicalColoredProduct_eq_total e s horder u hu t m ω, hu0, Nat.sub_zero]
  congr 1
  funext i
  exact canonicalBlockCount_zero_start _ _ _ _ _

/-- Accumulate true conditional model kernels along a deterministic partition.
The conditional bound is an intermediate premise, supplied by the actual
uniform Gamma estimate when this lemma is used in the joint limit. -/
theorem canonicalColoredProduct_conditional_budget (law : PotentialLaw)
    (e : ℕ → ℝ) (s : ℕ) (horder : ∀ i < s, e i ≤ e (i + 1))
    (u : ℕ → ℕ) (hu : Monotone u) (hu0 : u 0 = 0)
    (t : Fin s → ℝ) (ht : ∀ i, 0 ≤ t i) (m : ℕ)
    (a δ r : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hδ : 0 ≤ δ)
    (hkernel : ∀ b < m, ∀ᵐ ω ∂iidMeasure law,
      ω ∈ canonicalColoredGoodStart e s (u b) r →
        |((iidMeasure law)[(fun z => coloredLaplaceFactor t
          (canonicalColoredBlock e s (u b) (u (b + 1) - u b) z)) |
            pastMeasurableSpace (u b)]) ω - a| ≤ δ) :
    |(∫ ω, coloredLaplaceFactor t (fun i => canonicalNaturalCrossingCount
        (e i.val) (e (i.val + 1) - e i.val) 0 0 (u m) ω) ∂iidMeasure law) - a ^ m| ≤
      (m : ℝ) * δ + 2 * ∑ b ∈ Finset.range m,
        (iidMeasure law).real (canonicalColoredGoodStart e s (u b) r)ᶜ := by
  let Ψ : ℕ → PotentialSpace → ℝ := fun b z => coloredLaplaceFactor t
    (canonicalColoredBlock e s (u b) (u (b + 1) - u b) z)
  have h := conditional_backward_uniform_budget (μ := iidMeasure law) Ψ
    (fun b => (canonicalColoredFactor_measurable e s (u b) (u (b + 1) - u b) t).stronglyMeasurable)
    (fun _ ω => coloredLaplaceFactor_bounds t ht _) (fun b => pastMeasurableSpace (u b)) m
    (fun b _ => pastMeasurableSpace_le (u b))
    (fun b _ => canonicalColoredProduct_past_stronglyMeasurable e s u hu t b)
    ha0 ha1 hδ (fun b => canonicalColoredGoodStart e s (u b) r)
    (fun b _ => canonicalColoredGoodStart_measurable e s (u b) r) hkernel
  have heq : (fun ω => prefixProduct Ψ m ω) =
      (fun ω => coloredLaplaceFactor t (fun i => canonicalNaturalCrossingCount
        (e i.val) (e (i.val + 1) - e i.val) 0 0 (u m) ω)) := by
    funext ω
    exact canonicalColoredProduct_eq_count e s horder u hu hu0 t m ω
  rw [heq] at h
  exact h

end FixedCouplingPoisson.Furstenberg
