import FixedCouplingPoisson.ForcedMultiBlockContraction
import FixedCouplingPoisson.IIDMarkov

/-!
# Actual contraction at a stopped-past measurable future horizon

The horizon is part of the stopped-past state, together
with the two projective initial points. Only the fresh potential path is
independent of that state, by the proved actual iid restart theorem.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory

/-- The pair and the number of future steps are both state coordinates. -/
def pairHorizonObservable (E E' s : ℝ) :
    (ProjectivePair × ℕ) × PotentialSpace → ℝ := fun z =>
  (projectiveDistance (projectiveProcess E z.1.1.1 z.1.2 z.2)
    (projectiveProcess E' z.1.1.2 z.1.2 z.2)) ^ s

theorem measurable_pairHorizonObservable (E E' s : ℝ) (hs : 0 ≤ s) :
    Measurable (pairHorizonObservable E E' s) := by
  unfold pairHorizonObservable
  have hm : Measurable (fun z : (ProjectivePair × PotentialSpace) × ℕ =>
      (projectiveDistance (projectiveProcess E z.1.1.1 z.2 z.1.2)
        (projectiveProcess E' z.1.1.2 z.2 z.1.2)) ^ s) :=
    measurable_from_prod_countable_left fun n =>
      measurable_twoEnergy_pairDistance_block E E' s hs n
  have harg : Measurable (fun z : (ProjectivePair × ℕ) × PotentialSpace =>
      ((z.1.1, z.2), z.1.2)) :=
    (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst))
  have hc := hm.comp harg
  exact hc

theorem integrable_pairHorizonObservable (law : PotentialLaw)
    (E E' s : ℝ) (hs : 0 ≤ s) (ν : ProbabilityMeasure (ProjectivePair × ℕ)) :
    Integrable (pairHorizonObservable E E' s)
      ((ν : Measure (ProjectivePair × ℕ)).prod (iidMeasure law)) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_pairHorizonObservable E E' s hs).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    unfold pairHorizonObservable
    rw [Real.norm_eq_abs, abs_of_nonneg
      (Real.rpow_nonneg (projectiveDistance_nonneg _ _) s)]
    exact projectiveDistance_rpow_le_one _ _ s hs

/-- Exact genuine conditional expectation, before imposing any moment estimate. -/
theorem pairHorizonObservable_condExp (law : PotentialLaw)
    (E E' s : ℝ) (hs : 0 ≤ s)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤)
    {X : PotentialSpace → ProjectivePair × ℕ}
    (hX : Measurable[hτ.measurableSpace] X) :
    (iidMeasure law)[(fun ω => pairHorizonObservable E E' s
      (X ω, stoppedPotentialFuture τ ω)) | hτ.measurableSpace] =ᵐ[iidMeasure law]
      (fun ω => twoEnergyPairDistanceMoment law E E' s
        (X ω).1.1 (X ω).1.2 (X ω).2) := by
  have hXm : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  let ν : ProbabilityMeasure (ProjectivePair × ℕ) := ⟨(iidMeasure law).map X,
    Measure.isProbabilityMeasure_map hXm.aemeasurable⟩
  have hi : Integrable (pairHorizonObservable E E' s)
      (((iidMeasure law).map X).prod (iidMeasure law)) :=
    integrable_pairHorizonObservable law E E' s hs ν
  have hc := iidMeasure_condExp_stopped_futureKernel law hτ hfinite hX
    (measurable_pairHorizonObservable E E' s hs) hi
  simpa only [futureKernel, pairHorizonObservable, twoEnergyPairDistanceMoment] using hc

/-- A deterministic-time bound can be applied to a past-measurable random horizon. -/
theorem pairHorizonObservable_condExp_le (law : PotentialLaw)
    (E E' s q η : ℝ) (N : ℕ) (hs : 0 ≤ s)
    (hbound : ∀ n : ℕ, ∀ p r : ProjectivePoint,
      twoEnergyPairDistanceMoment law E E' s p r n ≤ q ^ (n / N) + η)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤)
    {X : PotentialSpace → ProjectivePair × ℕ}
    (hX : Measurable[hτ.measurableSpace] X) :
    ∀ᵐ ω ∂iidMeasure law,
      ((iidMeasure law)[(fun ω => pairHorizonObservable E E' s
        (X ω, stoppedPotentialFuture τ ω)) | hτ.measurableSpace]) ω ≤
          q ^ ((X ω).2 / N) + η := by
  filter_upwards [pairHorizonObservable_condExp law E E' s hs hτ hfinite hX] with ω hω
  rw [hω]
  exact hbound (X ω).2 (X ω).1.1 (X ω).1.2

/-- On a past event where enough future steps remain, the same deterministic
geometric tail applies. The lower-horizon condition is not asserted for free. -/
theorem pairHorizonObservable_condExp_le_of_horizon_ge (law : PotentialLaw)
    (E E' s q η : ℝ) (N m : ℕ) (hs : 0 ≤ s) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hbound : ∀ n : ℕ, ∀ p r : ProjectivePoint,
      twoEnergyPairDistanceMoment law E E' s p r n ≤ q ^ (n / N) + η)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤)
    {X : PotentialSpace → ProjectivePair × ℕ}
    (hX : Measurable[hτ.measurableSpace] X)
    (hm : ∀ᵐ ω ∂iidMeasure law, m ≤ (X ω).2) :
    ∀ᵐ ω ∂iidMeasure law,
      ((iidMeasure law)[(fun ω => pairHorizonObservable E E' s
        (X ω, stoppedPotentialFuture τ ω)) | hτ.measurableSpace]) ω ≤
          q ^ (m / N) + η := by
  filter_upwards [pairHorizonObservable_condExp_le law E E' s q η N hs
    hbound hτ hfinite hX, hm] with ω hω hmω
  exact hω.trans (add_le_add
    (pow_le_pow_of_le_one hq0 hq1 (Nat.div_le_div_right hmω)) le_rfl)

/-- Compact-energy constants also work for every actual stopped-past pair and horizon. -/
theorem exists_uniform_random_horizon_condExp_contraction
    (law : PotentialLaw) (input : Input law)
    (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ N : ℕ, 0 < N ∧ ∃ s q C : ℝ,
      0 < s ∧ s ≤ 1 ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧
      ∀ E ∈ K, ∀ E' : ℝ,
      ∀ {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ),
      (∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤) →
      ∀ {X : PotentialSpace → ProjectivePair × ℕ}, Measurable[hτ.measurableSpace] X →
      ∀ᵐ ω ∂iidMeasure law,
        ((iidMeasure law)[(fun ω => pairHorizonObservable E E' s
          (X ω, stoppedPotentialFuture τ ω)) | hτ.measurableSpace]) ω ≤
            q ^ ((X ω).2 / N) + C * |E - E'| ^ s := by
  obtain ⟨N, hN, s, q, C, hs, hs1, hq0, hq1, hC, hbound⟩ :=
    exists_uniform_forced_multiblock_moment law input K hK hne
  refine ⟨N, hN, s, q, C, hs, hs1, hq0, hq1, hC,
    fun E hE E' τ hτ hfinite X hX => ?_⟩
  exact pairHorizonObservable_condExp_le law E E' s q (C * |E - E'| ^ s) N hs.le
    (hbound E hE E') hτ hfinite hX

end FixedCouplingPoisson.Furstenberg
