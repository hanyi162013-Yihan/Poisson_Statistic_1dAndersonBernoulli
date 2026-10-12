import FixedCouplingPoisson.ActualBlockCounts
import FixedCouplingPoisson.ColoredBlockKernel
import FixedCouplingPoisson.ConditionalColoredKernel

/-! Actual colored increments, enclosing increments and measurable good starts. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set
open scoped BigOperators

def canonicalColoredBlock (e : ℕ → ℝ) (s j L : ℕ)
    (ω : PotentialSpace) (i : Fin s) : ℕ :=
  canonicalBlockCount (e i.val) (e (i.val + 1) - e i.val) 0 0 j L ω

def canonicalEnclosingBlock (e : ℕ → ℝ) (s j L : ℕ) (ω : PotentialSpace) : ℕ :=
  canonicalBlockCount (e 0) (e s - e 0) 0 0 j L ω

def canonicalColoredGoodStart (e : ℕ → ℝ) (s j : ℕ) (r : ℝ) : Set PotentialSpace :=
  {ω | (∀ i : Fin s,
      canonicalCrossingResidual (e i.val) (e (i.val + 1) - e i.val) 0 0 j ω ≤ r) ∧
    canonicalCrossingResidual (e 0) (e s - e 0) 0 0 j ω ≤ r}

theorem canonicalColoredBlock_measurable (e : ℕ → ℝ) (s j L : ℕ) (i : Fin s) :
    Measurable (fun ω => canonicalColoredBlock e s j L ω i) :=
  canonicalBlockCount_measurable _ _ _ _ _ _

theorem canonicalEnclosingBlock_measurable (e : ℕ → ℝ) (s j L : ℕ) :
    Measurable (canonicalEnclosingBlock e s j L) :=
  canonicalBlockCount_measurable _ _ _ _ _ _

theorem canonicalColoredGoodStart_past_measurable (e : ℕ → ℝ) (s j : ℕ) (r : ℝ) :
    MeasurableSet[pastMeasurableSpace j] (canonicalColoredGoodStart e s j r) := by
  letI : MeasurableSpace PotentialSpace := pastMeasurableSpace j
  change MeasurableSet ({ω | ∀ i : Fin s,
      canonicalCrossingResidual (e i.val) (e (i.val + 1) - e i.val) 0 0 j ω ≤ r} ∩
    {ω | canonicalCrossingResidual (e 0) (e s - e 0) 0 0 j ω ≤ r})
  have hadj : MeasurableSet {ω | ∀ i : Fin s,
      canonicalCrossingResidual (e i.val) (e (i.val + 1) - e i.val) 0 0 j ω ≤ r} := by
    simpa only [Set.ofPred_forall] using
      (MeasurableSet.iInter fun i : Fin s => measurableSet_le
        (canonicalCrossingResidual_past_measurable (e i.val)
          (e (i.val + 1) - e i.val) 0 0 j) measurable_const)
  exact hadj.inter (measurableSet_le
    (canonicalCrossingResidual_past_measurable (e 0) (e s - e 0) 0 0 j) measurable_const)

theorem canonicalColoredGoodStart_measurable (e : ℕ → ℝ) (s j : ℕ) (r : ℝ) :
    MeasurableSet (canonicalColoredGoodStart e s j r) :=
  pastMeasurableSpace_le j _ (canonicalColoredGoodStart_past_measurable e s j r)

theorem canonicalColoredBlock_enclosing_domination (e : ℕ → ℝ) (s j L : ℕ)
    (horder : ∀ i < s, e i ≤ e (i + 1)) (houter : e 0 ≤ e s) (r : ℝ)
    (hr : (s : ℝ) * r < Real.pi) (ω : PotentialSpace)
    (hgood : ω ∈ canonicalColoredGoodStart e s j r) :
    (∑ i : Fin s, canonicalColoredBlock e s j L ω i) ≤
      canonicalEnclosingBlock e s j L ω := by
  have hsum : (∑ i ∈ Finset.range s,
      canonicalCrossingResidual (e i) (e (i + 1) - e i) 0 0 j ω) ≤ (s : ℝ) * r := by
    calc
      _ ≤ ∑ _i ∈ Finset.range s, r := Finset.sum_le_sum fun i hi =>
        hgood.1 ⟨i, Finset.mem_range.mp hi⟩
      _ = _ := by simp
  change (∑ i : Fin s,
    canonicalBlockCount (e i.val) (e (i.val + 1) - e i.val) 0 0 j L ω) ≤ _
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ => canonicalBlockCount (e i) (e (i + 1) - e i) 0 0 j L ω) s]
  exact canonicalBlockCount_adjacent_domination e j L s horder houter ω (hsum.trans_lt hr)

theorem canonicalBlockCount_firstArrival_condExp (law : PotentialLaw) (E δ θ φ : ℝ)
    (j L : ℕ) :
    (iidMeasure law)[(fun ω => firstArrivalIndicator
      (canonicalBlockCount E δ θ φ j L ω)) | pastMeasurableSpace j] =ᵐ[iidMeasure law]
        (fun ω => freshCountTailKernel law E δ 1 L (canonicalResidualState E δ θ φ j ω)) := by
  have heq : (fun ω => firstArrivalIndicator (canonicalBlockCount E δ θ φ j L ω)) =
      {ω | 1 ≤ canonicalBlockCount E δ θ φ j L ω}.indicator
        (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [firstArrivalIndicator, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq]
  exact canonicalBlockCount_tail_condExp law E δ θ φ 1 j L

theorem canonicalBlockCount_twoArrival_condExp (law : PotentialLaw) (E δ θ φ : ℝ)
    (j L : ℕ) :
    (iidMeasure law)[(fun ω => twoArrivalIndicator
      (canonicalBlockCount E δ θ φ j L ω)) | pastMeasurableSpace j] =ᵐ[iidMeasure law]
        (fun ω => freshCountTailKernel law E δ 2 L (canonicalResidualState E δ θ φ j ω)) := by
  have heq : (fun ω => twoArrivalIndicator (canonicalBlockCount E δ θ φ j L ω)) =
      {ω | 2 ≤ canonicalBlockCount E δ θ φ j L ω}.indicator
        (fun _ => (1 : ℝ)) := by
    funext ω
    simp only [twoArrivalIndicator, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [heq]
  exact canonicalBlockCount_tail_condExp law E δ θ φ 2 j L

/-- The actual model conditional colored-block budget, with all conditional
arrival terms identified with proved fresh-iid kernels. -/
theorem canonicalColoredBlock_conditional_error_budget (law : PotentialLaw)
    (e : ℕ → ℝ) (s j L : ℕ) (horder : ∀ i < s, e i ≤ e (i + 1))
    (houter : e 0 ≤ e s) (r : ℝ) (hr : (s : ℝ) * r < Real.pi)
    (t q : Fin s → ℝ) (ht : ∀ i, 0 ≤ t i) :
    ∀ᵐ ω ∂iidMeasure law, ω ∈ canonicalColoredGoodStart e s j r →
      |((iidMeasure law)[(fun z => coloredLaplaceFactor t
        (canonicalColoredBlock e s j L z)) | pastMeasurableSpace j]) ω -
          (1 - ∑ i, firstArrivalWeight (t i) * q i)| ≤
        ((s : ℝ) + 1) * freshCountTailKernel law (e 0) (e s - e 0) 2 L
          (canonicalResidualState (e 0) (e s - e 0) 0 0 j ω) +
        ∑ i : Fin s, |freshCountTailKernel law (e i.val) (e (i.val + 1) - e i.val) 1 L
          (canonicalResidualState (e i.val) (e (i.val + 1) - e i.val) 0 0 j ω) - q i| := by
  have hbase := condExp_coloredLaplaceFactor_error_le_on_event_of_arrival_approx
    (μ := iidMeasure law) (pastMeasurableSpace_le j)
    (canonicalColoredGoodStart_past_measurable e s j r) t ht
    (fun i => canonicalColoredBlock_measurable e s j L i)
    (canonicalEnclosingBlock_measurable e s j L)
    (fun ω hω => canonicalColoredBlock_enclosing_domination e s j L
      horder houter r hr ω hω) (fun i _ => q i)
  have hfirst : ∀ᵐ ω ∂iidMeasure law, ∀ i : Fin s,
      ((iidMeasure law)[(fun z => firstArrivalIndicator
        (canonicalColoredBlock e s j L z i)) | pastMeasurableSpace j]) ω =
          freshCountTailKernel law (e i.val) (e (i.val + 1) - e i.val) 1 L
            (canonicalResidualState (e i.val) (e (i.val + 1) - e i.val) 0 0 j ω) := by
    apply ae_all_iff.mpr
    intro i
    exact canonicalBlockCount_firstArrival_condExp law _ _ _ _ _ _
  have htwo := canonicalBlockCount_twoArrival_condExp law (e 0) (e s - e 0) 0 0 j L
  filter_upwards [hbase, hfirst, htwo] with ω hb hf h2 hgood
  have h := hb hgood
  simpa only [canonicalEnclosingBlock, hf, h2] using h

end FixedCouplingPoisson.Furstenberg
