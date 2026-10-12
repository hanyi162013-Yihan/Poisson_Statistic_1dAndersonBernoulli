import FixedCouplingPoisson.ConditionalHorizonTail
import FixedCouplingPoisson.PhaseDistribution
import FixedCouplingPoisson.PhaseWindow
import FixedCouplingPoisson.CanonicalResidual

/-!
# Conditional exclusion of middle oriented residuals after a stopped restart

This only excludes compact subintervals of `(0, pi)`. It does not exclude
the upper endpoint and therefore does not assert one-sided residual pinning.
The residual is calculated directly from two actual lifted phases.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ProbabilityTheory

def liftedPairResidual (a b : ℝ) : ℝ :=
  terminalWindowResidual (fun i => if i = 0 then a else b) 0

theorem measurable_liftedPairResidual :
    Measurable (fun z : ℝ × ℝ => liftedPairResidual z.1 z.2) := by
  have hk : Measurable (fun z : ℝ × ℝ => (⌊(z.1 - z.2) / Real.pi⌋ : ℝ)) :=
    (measurable_of_countable (fun k : ℤ => (k : ℝ))).comp
      ((measurable_fst.sub measurable_snd).div_const Real.pi).floor
  change Measurable (fun z : ℝ × ℝ =>
    z.1 - z.2 - Real.pi * (⌊(z.1 - z.2) / Real.pi⌋ : ℝ))
  exact (measurable_fst.sub measurable_snd).sub (hk.const_mul Real.pi)

theorem liftedPairResidual_mem (a b : ℝ) :
    liftedPairResidual a b ∈ Set.Ico 0 Real.pi :=
  terminalWindowResidual_mem _ 0

theorem projectiveDistance_eq_sin_liftedPairResidual (a b : ℝ) :
    projectiveDistance (phaseProjective a) (phaseProjective b) =
      Real.sin (liftedPairResidual a b) := by
  let r := liftedPairResidual a b
  let k : ℤ := ⌊(a - b) / Real.pi⌋
  have ha : a = (b + r) + (k : ℝ) * Real.pi := by
    change a = (b + (a - b - Real.pi * (⌊(a - b) / Real.pi⌋ : ℝ))) +
      (⌊(a - b) / Real.pi⌋ : ℝ) * Real.pi
    ring
  have hp : phaseProjective a = phaseProjective (b + r) := by
    rw [ha, phaseProjective_add_int]
  rw [hp, projectiveDistance_phaseProjective]
  have heq : b - (b + r) = -r := by ring
  rw [heq, Real.sin_neg, abs_neg, abs_of_nonneg]
  exact Real.sin_nonneg_of_nonneg_of_le_pi
    (liftedPairResidual_mem a b).1 (liftedPairResidual_mem a b).2.le

/-- A residual away from both endpoints forces a definite determinant distance. -/
theorem liftedPairResidual_middle_distance_lower (a b : ℝ)
    {h : ℝ} (_hh : 0 ≤ h) (hlower : h ≤ liftedPairResidual a b)
    (hupper : liftedPairResidual a b ≤ Real.pi - h) :
    (2 / Real.pi) * h ≤ projectiveDistance (phaseProjective a) (phaseProjective b) := by
  rw [projectiveDistance_eq_sin_liftedPairResidual]
  let r := liftedPairResidual a b
  have hr0 : 0 ≤ r := (liftedPairResidual_mem a b).1
  have hrπ : r ≤ Real.pi := (liftedPairResidual_mem a b).2.le
  have hcoef : 0 ≤ 2 / Real.pi := by positivity
  by_cases hrhalf : r ≤ Real.pi / 2
  · exact (mul_le_mul_of_nonneg_left hlower hcoef).trans
      (Real.mul_le_sin hr0 hrhalf)
  · have hother := Real.mul_le_sin (sub_nonneg.mpr hrπ)
      (show Real.pi - r ≤ Real.pi / 2 by linarith)
    rw [Real.sin_pi_sub] at hother
    exact (mul_le_mul_of_nonneg_left (show h ≤ Real.pi - r by linarith) hcoef).trans hother

def liftedHorizonResidual (E E' : ℝ) :
    ((ℝ × ℝ) × ℕ) × PotentialSpace → ℝ := fun z =>
  liftedPairResidual (canonicalPhaseProcess E z.1.1.1 z.1.2 z.2)
    (canonicalPhaseProcess E' z.1.1.2 z.1.2 z.2)

theorem liftedHorizonResidual_eq_canonicalCrossingResidual
    (E δ θ φ : ℝ) (n : ℕ) (ω : PotentialSpace) :
    liftedHorizonResidual E (E + δ) (((θ, φ), n), ω) =
      canonicalCrossingResidual E δ θ φ n ω := rfl

theorem measurable_liftedHorizonResidual (E E' : ℝ) :
    Measurable (liftedHorizonResidual E E') := by
  unfold liftedHorizonResidual
  have hm : Measurable (fun z : ((ℝ × ℝ) × PotentialSpace) × ℕ =>
      liftedPairResidual (canonicalPhaseProcess E z.1.1.1 z.2 z.1.2)
        (canonicalPhaseProcess E' z.1.1.2 z.2 z.1.2)) :=
    measurable_from_prod_countable_left fun n =>
      measurable_liftedPairResidual.comp
        (((canonicalPhaseProcess_measurable_initial_path E n).comp
          ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).prodMk
        ((canonicalPhaseProcess_measurable_initial_path E' n).comp
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd)))
  exact hm.comp
    (((measurable_fst.comp measurable_fst).prodMk measurable_snd).prodMk
      (measurable_snd.comp measurable_fst))

def liftedHorizonMiddleObservable (E E' h : ℝ) :
    ((ℝ × ℝ) × ℕ) × PotentialSpace → ℝ :=
  {z | h ≤ liftedHorizonResidual E E' z ∧
    liftedHorizonResidual E E' z ≤ Real.pi - h}.indicator (fun _ => 1)

theorem measurable_liftedHorizonMiddleObservable (E E' h : ℝ) :
    Measurable (liftedHorizonMiddleObservable E E' h) :=
  measurable_const.indicator
    ((measurableSet_le measurable_const (measurable_liftedHorizonResidual E E')).inter
      (measurableSet_le (measurable_liftedHorizonResidual E E') measurable_const))

def projectivePairHorizonOfLifted : (ℝ × ℝ) × ℕ → ProjectivePair × ℕ := fun x =>
  ((phaseProjective x.1.1, phaseProjective x.1.2), x.2)

theorem measurable_projectivePairHorizonOfLifted : Measurable projectivePairHorizonOfLifted :=
  (((continuous_phaseProjective.measurable.comp
    (measurable_fst.comp measurable_fst)).prodMk
    (continuous_phaseProjective.measurable.comp
      (measurable_snd.comp measurable_fst))).prodMk measurable_snd)

theorem liftedHorizonMiddleObservable_le_tail (E E' h : ℝ) (hh : 0 ≤ h)
    (z : ((ℝ × ℝ) × ℕ) × PotentialSpace) :
    liftedHorizonMiddleObservable E E' h z ≤
      pairHorizonTailObservable E E' ((2 / Real.pi) * h)
        (projectivePairHorizonOfLifted z.1, z.2) := by
  classical
  by_cases hz : h ≤ liftedHorizonResidual E E' z ∧
      liftedHorizonResidual E E' z ≤ Real.pi - h
  · have hd := liftedPairResidual_middle_distance_lower
      (canonicalPhaseProcess E z.1.1.1 z.1.2 z.2)
      (canonicalPhaseProcess E' z.1.1.2 z.1.2 z.2) hh hz.1 hz.2
    simp only [phaseProjective_canonicalPhaseProcess] at hd
    simpa only [liftedHorizonMiddleObservable, pairHorizonTailObservable,
      projectivePairHorizonOfLifted, pairHorizonDistance, Set.indicator_apply,
      Set.mem_ofPred_eq, hz, hd, true_and, ite_true] using (le_refl (1 : ℝ))
  · have hz0 : liftedHorizonMiddleObservable E E' h z = 0 := by
      simp [liftedHorizonMiddleObservable, hz]
    rw [hz0]
    exact (pairHorizonTailObservable_bounds E E' _ _).1

/-- Conditional middle-residual probability for an actual stopped restart,
with both lifted phases and the future horizon chosen by the stopped past. -/
theorem stoppedHorizon_middleResidual_condExp_le (law : PotentialLaw)
    (E E' s q η h : ℝ) (N : ℕ) (hs : 0 ≤ s) (hh : 0 < h)
    (hbound : ∀ n : ℕ, ∀ p r : ProjectivePoint,
      twoEnergyPairDistanceMoment law E E' s p r n ≤ q ^ (n / N) + η)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤)
    {Θ : PotentialSpace → (ℝ × ℝ) × ℕ}
    (hΘ : Measurable[hτ.measurableSpace] Θ) :
    ∀ᵐ ω ∂iidMeasure law,
      ((iidMeasure law)[(fun ω => liftedHorizonMiddleObservable E E' h
        (Θ ω, stoppedPotentialFuture τ ω)) | hτ.measurableSpace]) ω ≤
          (q ^ ((Θ ω).2 / N) + η) / (((2 / Real.pi) * h) ^ s) := by
  let X : PotentialSpace → ProjectivePair × ℕ :=
    projectivePairHorizonOfLifted ∘ Θ
  have hX : Measurable[hτ.measurableSpace] X :=
    measurable_projectivePairHorizonOfLifted.comp hΘ
  have hΘm : Measurable Θ := hΘ.mono hτ.measurableSpace_le le_rfl
  have harg : Measurable (fun ω => (Θ ω, stoppedPotentialFuture τ ω)) :=
    hΘm.prodMk (measurable_stoppedPotentialFuture hτ)
  have hargX : Measurable (fun ω => (X ω, stoppedPotentialFuture τ ω)) :=
    (hX.mono hτ.measurableSpace_le le_rfl).prodMk (measurable_stoppedPotentialFuture hτ)
  have hmid : Integrable (fun ω => liftedHorizonMiddleObservable E E' h
      (Θ ω, stoppedPotentialFuture τ ω)) (iidMeasure law) := by
    apply (integrable_const (1 : ℝ)).mono'
      ((measurable_liftedHorizonMiddleObservable E E' h).comp harg).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      classical
      by_cases hz : h ≤ liftedHorizonResidual E E' (Θ ω, stoppedPotentialFuture τ ω) ∧
          liftedHorizonResidual E E' (Θ ω, stoppedPotentialFuture τ ω) ≤ Real.pi - h
      · simp [liftedHorizonMiddleObservable, hz]
      · simp [liftedHorizonMiddleObservable, hz]
  have htail : Integrable (fun ω => pairHorizonTailObservable E E' ((2 / Real.pi) * h)
      (X ω, stoppedPotentialFuture τ ω)) (iidMeasure law) := by
    apply (integrable_const (1 : ℝ)).mono'
      ((measurable_pairHorizonTailObservable E E' _).comp hargX).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      change |pairHorizonTailObservable E E' ((2 / Real.pi) * h)
        (X ω, stoppedPotentialFuture τ ω)| ≤ 1
      rw [abs_of_nonneg (pairHorizonTailObservable_bounds E E' _ _).1]
      exact (pairHorizonTailObservable_bounds E E' _ _).2
  have hmono := condExp_mono (m := hτ.measurableSpace) hmid htail
    (Eventually.of_forall fun ω => liftedHorizonMiddleObservable_le_tail E E' h hh.le
      (Θ ω, stoppedPotentialFuture τ ω))
  have hle := pairHorizonTailObservable_condExp_le law E E' s q η
    ((2 / Real.pi) * h) N hs (by positivity) hbound hτ hfinite hX
  filter_upwards [hmono, hle] with ω hω hωle
  exact hω.trans hωle

/-- The same conditional middle bound on any past event where enough steps remain. -/
theorem stoppedHorizon_middleResidual_condExp_le_on_horizon_ge (law : PotentialLaw)
    (E E' s q η h : ℝ) (N m : ℕ) (hs : 0 ≤ s) (hh : 0 < h)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hbound : ∀ n : ℕ, ∀ p r : ProjectivePoint,
      twoEnergyPairDistanceMoment law E E' s p r n ≤ q ^ (n / N) + η)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤)
    {Θ : PotentialSpace → (ℝ × ℝ) × ℕ}
    (hΘ : Measurable[hτ.measurableSpace] Θ) :
    ∀ᵐ ω ∂iidMeasure law, m ≤ (Θ ω).2 →
      ((iidMeasure law)[(fun ω => liftedHorizonMiddleObservable E E' h
        (Θ ω, stoppedPotentialFuture τ ω)) | hτ.measurableSpace]) ω ≤
          (q ^ (m / N) + η) / (((2 / Real.pi) * h) ^ s) := by
  filter_upwards [stoppedHorizon_middleResidual_condExp_le law E E' s q η h N hs hh
    hbound hτ hfinite hΘ] with ω hω
  intro hm
  exact hω.trans (div_le_div_of_nonneg_right
    (add_le_add (pow_le_pow_of_le_one hq0 hq1 (Nat.div_le_div_right hm)) le_rfl)
    (Real.rpow_nonneg (by positivity) s))

/-- Compact-energy constants derived from the genuine block contraction. -/
theorem exists_uniform_random_horizon_condExp_middle_residual
    (law : PotentialLaw) (input : Input law)
    (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ N : ℕ, 0 < N ∧ ∃ s q C : ℝ,
      0 < s ∧ s ≤ 1 ∧ 0 ≤ q ∧ q < 1 ∧ 0 ≤ C ∧
      ∀ E ∈ K, ∀ E' h : ℝ, 0 < h →
      ∀ {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ),
      (∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤) →
      ∀ {Θ : PotentialSpace → (ℝ × ℝ) × ℕ}, Measurable[hτ.measurableSpace] Θ →
      ∀ᵐ ω ∂iidMeasure law,
        ((iidMeasure law)[(fun ω => liftedHorizonMiddleObservable E E' h
          (Θ ω, stoppedPotentialFuture τ ω)) | hτ.measurableSpace]) ω ≤
            (q ^ ((Θ ω).2 / N) + C * |E - E'| ^ s) /
              (((2 / Real.pi) * h) ^ s) := by
  obtain ⟨N, hN, s, q, C, hs, hs1, hq0, hq1, hC, hbound⟩ :=
    exists_uniform_forced_multiblock_moment law input K hK hne
  refine ⟨N, hN, s, q, C, hs, hs1, hq0, hq1, hC,
    fun E hE E' h hh τ hτ hfinite Θ hΘ => ?_⟩
  exact stoppedHorizon_middleResidual_condExp_le law E E' s q (C * |E - E'| ^ s)
    h N hs.le hh (hbound E hE E') hτ hfinite hΘ

/-- The bound is also on the actual original path at `tau + ell`, not just
on an abstract independently restarted evolution. -/
theorem canonicalCrossingResidual_condExp_middle_at_random_future_le (law : PotentialLaw)
    (E δ θ φ s q η h : ℝ) (N : ℕ) (hs : 0 ≤ s) (hh : 0 < h)
    (hbound : ∀ n : ℕ, ∀ p r : ProjectivePoint,
      twoEnergyPairDistanceMoment law E (E + δ) s p r n ≤ q ^ (n / N) + η)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤)
    {ell : PotentialSpace → ℕ} (hell : Measurable[hτ.measurableSpace] ell) :
    ∀ᵐ ω ∂iidMeasure law,
      ((iidMeasure law)[({v | h ≤ canonicalCrossingResidual E δ θ φ
          ((τ v).untopD 0 + ell v) v ∧ canonicalCrossingResidual E δ θ φ
          ((τ v).untopD 0 + ell v) v ≤ Real.pi - h}.indicator (fun _ => (1 : ℝ))) |
          hτ.measurableSpace]) ω ≤
        (q ^ (ell ω / N) + η) / (((2 / Real.pi) * h) ^ s) := by
  let Θ : PotentialSpace → (ℝ × ℝ) × ℕ := fun ω =>
    ((stoppedValue (canonicalPhaseProcess E θ) τ ω,
      stoppedValue (canonicalPhaseProcess (E + δ) φ) τ ω), ell ω)
  have hΘ : Measurable[hτ.measurableSpace] Θ :=
    ((canonicalPhaseProcess_stopped_measurable E θ hτ).prodMk
      (canonicalPhaseProcess_stopped_measurable (E + δ) φ hτ)).prodMk hell
  have hgen := stoppedHorizon_middleResidual_condExp_le law E (E + δ) s q η h N
    hs hh hbound hτ hfinite hΘ
  have hobs : (fun ω => liftedHorizonMiddleObservable E (E + δ) h
      (Θ ω, stoppedPotentialFuture τ ω)) =ᵐ[iidMeasure law]
      ({v | h ≤ canonicalCrossingResidual E δ θ φ ((τ v).untopD 0 + ell v) v ∧
        canonicalCrossingResidual E δ θ φ ((τ v).untopD 0 + ell v) v ≤
          Real.pi - h}.indicator (fun _ => (1 : ℝ))) := by
    filter_upwards [hfinite] with ω hω
    have hr : liftedHorizonResidual E (E + δ) (Θ ω, stoppedPotentialFuture τ ω) =
        canonicalCrossingResidual E δ θ φ ((τ ω).untopD 0 + ell ω) ω := by
      change liftedPairResidual
        (canonicalPhaseProcess E (stoppedValue (canonicalPhaseProcess E θ) τ ω)
          (ell ω) (stoppedPotentialFuture τ ω))
        (canonicalPhaseProcess (E + δ)
          (stoppedValue (canonicalPhaseProcess (E + δ) φ) τ ω)
          (ell ω) (stoppedPotentialFuture τ ω)) = _
      rw [canonicalPhaseProcess_stopped_restart E θ (ell ω) τ ω hω,
        canonicalPhaseProcess_stopped_restart (E + δ) φ (ell ω) τ ω hω]
      rfl
    classical
    simp only [liftedHorizonMiddleObservable, Set.indicator_apply,
      Set.mem_ofPred_eq, hr]
  have hce := condExp_congr_ae (m := hτ.measurableSpace) hobs
  filter_upwards [hce, hgen] with ω hω hωgen
  rw [← hω]
  exact hωgen

end FixedCouplingPoisson.Furstenberg
