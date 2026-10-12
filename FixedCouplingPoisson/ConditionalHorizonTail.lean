import FixedCouplingPoisson.RandomHorizonContraction

/-!
# Conditional distance tails at a stopped-past chosen future horizon

The conditional probability is the actual conditional expectation of an
indicator on the original iid sample space. The whole initial pair and the
future horizon are retained in the stopped-past state.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory

def pairHorizonDistance (E E' : ℝ) :
    (ProjectivePair × ℕ) × PotentialSpace → ℝ := fun z =>
  projectiveDistance (projectiveProcess E z.1.1.1 z.1.2 z.2)
    (projectiveProcess E' z.1.1.2 z.1.2 z.2)

theorem measurable_pairHorizonDistance (E E' : ℝ) :
    Measurable (pairHorizonDistance E E') := by
  unfold pairHorizonDistance
  have hm := measurable_pairHorizonObservable E E' 1 (by norm_num)
  unfold pairHorizonObservable at hm
  simpa only [Real.rpow_one] using hm

def pairHorizonTailObservable (E E' h : ℝ) :
    (ProjectivePair × ℕ) × PotentialSpace → ℝ :=
  {z | h ≤ pairHorizonDistance E E' z}.indicator (fun _ => 1)

theorem measurable_pairHorizonTailObservable (E E' h : ℝ) :
    Measurable (pairHorizonTailObservable E E' h) :=
  measurable_const.indicator
    (measurableSet_le measurable_const (measurable_pairHorizonDistance E E'))

theorem pairHorizonTailObservable_bounds (E E' h : ℝ)
    (z : (ProjectivePair × ℕ) × PotentialSpace) :
    0 ≤ pairHorizonTailObservable E E' h z ∧
      pairHorizonTailObservable E E' h z ≤ 1 := by
  classical
  by_cases hz : h ≤ pairHorizonDistance E E' z
  · simp [pairHorizonTailObservable, hz]
  · simp [pairHorizonTailObservable, hz]

theorem integrable_pairHorizonTailObservable (law : PotentialLaw)
    (E E' h : ℝ) (ν : ProbabilityMeasure (ProjectivePair × ℕ)) :
    Integrable (pairHorizonTailObservable E E' h)
      ((ν : Measure (ProjectivePair × ℕ)).prod (iidMeasure law)) := by
  apply (integrable_const (1 : ℝ)).mono'
    (measurable_pairHorizonTailObservable E E' h).aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pairHorizonTailObservable_bounds E E' h z).1]
    exact (pairHorizonTailObservable_bounds E E' h z).2

theorem futureKernel_pairHorizonTailObservable (law : PotentialLaw)
    (E E' h : ℝ) (x : ProjectivePair × ℕ) :
    futureKernel law (pairHorizonTailObservable E E' h) x =
      (iidMeasure law).real {ω | h ≤ projectiveDistance
        (projectiveProcess E x.1.1 x.2 ω)
        (projectiveProcess E' x.1.2 x.2 ω)} := by
  have hm : Measurable (fun ω => pairHorizonDistance E E' (x, ω)) :=
    (measurable_pairHorizonDistance E E').comp (measurable_const.prodMk measurable_id)
  have hset : MeasurableSet {ω | h ≤ pairHorizonDistance E E' (x, ω)} :=
    measurableSet_le measurable_const hm
  change (∫ ω, pairHorizonTailObservable E E' h (x, ω) ∂iidMeasure law) = _
  have heq : (fun ω => pairHorizonTailObservable E E' h (x, ω)) =
      {ω | h ≤ pairHorizonDistance E E' (x, ω)}.indicator (fun _ => (1 : ℝ)) := by
    classical
    funext ω
    simp only [pairHorizonTailObservable, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq, integral_indicator_const 1 hset]
  simp only [smul_eq_mul, mul_one, pairHorizonDistance]

/-- Exact stopped-past conditional distance-tail probability. -/
theorem pairHorizonTailObservable_condExp (law : PotentialLaw)
    (E E' h : ℝ)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤)
    {X : PotentialSpace → ProjectivePair × ℕ}
    (hX : Measurable[hτ.measurableSpace] X) :
    (iidMeasure law)[(fun ω => pairHorizonTailObservable E E' h
      (X ω, stoppedPotentialFuture τ ω)) | hτ.measurableSpace] =ᵐ[iidMeasure law]
      (fun ω => (iidMeasure law).real {v | h ≤ projectiveDistance
        (projectiveProcess E (X ω).1.1 (X ω).2 v)
        (projectiveProcess E' (X ω).1.2 (X ω).2 v)}) := by
  have hXm : Measurable X := hX.mono hτ.measurableSpace_le le_rfl
  let ν : ProbabilityMeasure (ProjectivePair × ℕ) := ⟨(iidMeasure law).map X,
    Measure.isProbabilityMeasure_map hXm.aemeasurable⟩
  have hi : Integrable (pairHorizonTailObservable E E' h)
      (((iidMeasure law).map X).prod (iidMeasure law)) :=
    integrable_pairHorizonTailObservable law E E' h ν
  have hc := iidMeasure_condExp_stopped_futureKernel law hτ hfinite hX
    (measurable_pairHorizonTailObservable E E' h) hi
  simpa only [futureKernel_pairHorizonTailObservable] using hc

/-- Actual conditional Markov tail with a past-measurable random future length. -/
theorem pairHorizonTailObservable_condExp_le (law : PotentialLaw)
    (E E' s q η h : ℝ) (N : ℕ) (hs : 0 ≤ s) (hh : 0 < h)
    (hbound : ∀ n : ℕ, ∀ p r : ProjectivePoint,
      twoEnergyPairDistanceMoment law E E' s p r n ≤ q ^ (n / N) + η)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤)
    {X : PotentialSpace → ProjectivePair × ℕ}
    (hX : Measurable[hτ.measurableSpace] X) :
    ∀ᵐ ω ∂iidMeasure law,
      ((iidMeasure law)[(fun ω => pairHorizonTailObservable E E' h
        (X ω, stoppedPotentialFuture τ ω)) | hτ.measurableSpace]) ω ≤
          (q ^ ((X ω).2 / N) + η) / h ^ s := by
  filter_upwards [pairHorizonTailObservable_condExp law E E' h hτ hfinite hX] with ω hω
  rw [hω]
  exact twoEnergyPairDistanceMoment_measure_distance_ge_le law E E' s h _ hs hh
    (X ω).1.1 (X ω).1.2 (X ω).2
    (hbound (X ω).2 (X ω).1.1 (X ω).1.2)

/-- A deterministic minimum length may be imposed only on a past event.
No lower bound on the random horizon outside that event is required. -/
theorem pairHorizonTailObservable_condExp_le_on_horizon_ge (law : PotentialLaw)
    (E E' s q η h : ℝ) (N m : ℕ) (hs : 0 ≤ s) (hh : 0 < h)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hbound : ∀ n : ℕ, ∀ p r : ProjectivePoint,
      twoEnergyPairDistanceMoment law E E' s p r n ≤ q ^ (n / N) + η)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤)
    {X : PotentialSpace → ProjectivePair × ℕ}
    (hX : Measurable[hτ.measurableSpace] X) :
    ∀ᵐ ω ∂iidMeasure law, m ≤ (X ω).2 →
      ((iidMeasure law)[(fun ω => pairHorizonTailObservable E E' h
        (X ω, stoppedPotentialFuture τ ω)) | hτ.measurableSpace]) ω ≤
          (q ^ (m / N) + η) / h ^ s := by
  filter_upwards [pairHorizonTailObservable_condExp_le law E E' s q η h N hs hh
    hbound hτ hfinite hX] with ω hω
  intro hm
  exact hω.trans (div_le_div_of_nonneg_right
    (add_le_add (pow_le_pow_of_le_one hq0 hq1 (Nat.div_le_div_right hm)) le_rfl)
    (Real.rpow_nonneg hh.le s))

/-- The genuine Furstenberg-derived tail bound, uniform in stopped states. -/
theorem exists_uniform_random_horizon_condExp_tail
    (law : PotentialLaw) (input : Input law)
    (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ N : ℕ, 0 < N ∧ ∃ s q C : ℝ,
      0 < s ∧ s ≤ 1 ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧
      ∀ E ∈ K, ∀ E' h : ℝ, 0 < h →
      ∀ {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ),
      (∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤) →
      ∀ {X : PotentialSpace → ProjectivePair × ℕ}, Measurable[hτ.measurableSpace] X →
      ∀ᵐ ω ∂iidMeasure law,
        ((iidMeasure law)[(fun ω => pairHorizonTailObservable E E' h
          (X ω, stoppedPotentialFuture τ ω)) | hτ.measurableSpace]) ω ≤
            (q ^ ((X ω).2 / N) + C * |E - E'| ^ s) / h ^ s := by
  obtain ⟨N, hN, s, q, C, hs, hs1, hq0, hq1, hC, hbound⟩ :=
    exists_uniform_forced_multiblock_moment law input K hK hne
  refine ⟨N, hN, s, q, C, hs, hs1, hq0, hq1, hC,
    fun E hE E' h hh τ hτ hfinite X hX => ?_⟩
  exact pairHorizonTailObservable_condExp_le law E E' s q (C * |E - E'| ^ s)
    h N hs.le hh (hbound E hE E') hτ hfinite hX

end FixedCouplingPoisson.Furstenberg
