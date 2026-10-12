import FixedCouplingPoisson.ActualColoredBlock
import FixedCouplingPoisson.ResidualPinningEventually

/-! One deterministic cutoff for all actual colored good-start events. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- A single cutoff controls every adjacent and enclosing residual at every
member of a finite block-start family. The tail hypotheses are explicit
intermediate premises, discharged by the model theorem below. -/
theorem canonicalColoredGoodStart_cutoff_of_finite_tails {β : Type*} [Fintype β]
    (law : PotentialLaw) (e : ℕ → ℕ → ℝ) (s : ℕ) (j : β → ℕ → ℕ)
    (hadj : ∀ b (i : Fin s) (h : ℝ), 0 < h → Tendsto (fun n => iidMeasure law {ω |
      h < canonicalCrossingResidual (e n i.val) (e n (i.val + 1) - e n i.val)
        0 0 (j b n) ω}) atTop (𝓝 0))
    (houter : ∀ b (h : ℝ), 0 < h → Tendsto (fun n => iidMeasure law {ω |
      h < canonicalCrossingResidual (e n 0) (e n s - e n 0) 0 0 (j b n) ω})
        atTop (𝓝 0)) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Antitone r ∧ Tendsto r atTop (𝓝 0) ∧
      Tendsto (fun n => iidMeasure law {ω | ∀ b,
        ω ∈ canonicalColoredGoodStart (e n) s (j b n) (r n)}) atTop (𝓝 1) ∧
      ∀ b, Tendsto (fun n => iidMeasure law
        (canonicalColoredGoodStart (e n) s (j b n) (r n))) atTop (𝓝 1) := by
  let R : ℕ → (β × Option (Fin s)) → PotentialSpace → ℝ := fun n z ω =>
    match z.2 with
    | none => canonicalCrossingResidual (e n 0) (e n s - e n 0) 0 0 (j z.1 n) ω
    | some i => canonicalCrossingResidual (e n i.val) (e n (i.val + 1) - e n i.val)
        0 0 (j z.1 n) ω
  have hR : ∀ z (h : ℝ), 0 < h → Tendsto
      (fun n => iidMeasure law {ω | h < R n z ω}) atTop (𝓝 0) := by
    rintro ⟨b, q⟩ h hh
    cases q with
    | none => exact houter b h hh
    | some i => exact hadj b i h hh
  obtain ⟨r, hr, hanti, hlim, hbad⟩ :=
    finite_residual_exists_antitone_cutoff (iidMeasure law) R hR
  have hmeas : ∀ n z, Measurable (R n z) := by
    rintro n ⟨b, q⟩
    cases q with
    | none => exact canonicalCrossingResidual_measurable _ _ _ _ _
    | some i => exact canonicalCrossingResidual_measurable _ _ _ _ _
  have hall := finite_residual_good_tendsto_one_of_bad (iidMeasure law) R hmeas r hbad
  have heq : ∀ n, {ω | ∀ z, R n z ω ≤ r n} = {ω | ∀ b,
      ω ∈ canonicalColoredGoodStart (e n) s (j b n) (r n)} := by
    intro n
    ext ω
    constructor
    · intro h b
      exact ⟨(fun i => h (b, some i)), h (b, none)⟩
    · rintro h ⟨b, q⟩
      cases q with
      | none => exact (h b).2
      | some i => exact (h b).1 i
  have hall' : Tendsto (fun n => iidMeasure law {ω | ∀ b,
      ω ∈ canonicalColoredGoodStart (e n) s (j b n) (r n)}) atTop (𝓝 1) := by
    simpa only [heq] using hall
  refine ⟨r, hr, hanti, hlim, hall', ?_⟩
  intro b
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hall' tendsto_const_nhds
  · intro n
    exact measure_mono (fun _ h => h b)
  · intro n
    exact prob_le_one

private theorem canonical_zero_initial_tail_at_eventually_zero_or_diverging_times
    (law : PotentialLaw) (input : Input law) {K : Set ℝ} (hK : IsCompact K)
    (E δ : ℕ → ℝ)
    (hE : ∀ᶠ n in atTop, E n ∈ K) (hE' : ∀ᶠ n in atTop, E n + δ n ∈ K)
    (hδ0 : ∀ᶠ n in atTop, 0 ≤ δ n)
    (hp : ∀ᶠ n in atTop, 0 < idsCandidate law (E n + δ n) - idsCandidate law (E n))
    (hδ : Tendsto δ atTop (𝓝 0)) (j : ℕ → ℕ)
    (hstart : (∀ᶠ n in atTop, j n = 0) ∨ Tendsto j atTop atTop) {t : ℝ}
    (htime : Tendsto (fun n =>
      (idsCandidate law (E n + δ n) - idsCandidate law (E n)) * (j n : ℝ))
      atTop (𝓝 t)) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => iidMeasure law {ω |
      r < canonicalCrossingResidual (E n) (δ n) 0 0 (j n) ω}) atTop (𝓝 0) := by
  rcases hstart with hzero | hj
  · apply (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ENNReal))
      atTop (𝓝 0)).congr'
    filter_upwards [hzero] with n hn
    simp only [hn, canonicalCrossingResidual, canonicalCrossingCount,
      canonicalGapProcess_zero, sub_self, zero_div, Int.floor_zero, Int.cast_zero,
      mul_zero, not_lt_of_ge hr.le, Set.ofPred_false, measure_empty]
  · exact canonicalCrossingResidual_tails_tendsto_zero_eventually law input hK
      E δ (fun _ => 0) (fun _ => 0) hE hE' hδ0
      (Eventually.of_forall fun _ => le_rfl) hp hδ
      (by simpa only [sub_self] using
        (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 0)))
      j hj htime hr

/-- Actual model pinning supplies all good-start tails. Only eventual
physical endpoint/order/rate conditions are needed, and the block beginning
at time zero is included exactly. -/
theorem canonicalColoredGoodStart_cutoff_from_scales_eventually
    {β : Type*} [Fintype β] (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (e : ℕ → ℕ → ℝ) (s : ℕ) (j : β → ℕ → ℕ)
    (hEnergy : ∀ᶠ n in atTop, ∀ i, i ≤ s → e n i ∈ K)
    (horder : ∀ᶠ n in atTop, ∀ i, i < s → e n i ≤ e n (i + 1))
    (houterOrder : ∀ᶠ n in atTop, e n 0 ≤ e n s)
    (hp : ∀ᶠ n in atTop, ∀ i, i < s →
      0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i))
    (hpOuter : ∀ᶠ n in atTop, 0 < idsCandidate law (e n s) - idsCandidate law (e n 0))
    (hδ : ∀ i < s, Tendsto (fun n => e n (i + 1) - e n i) atTop (𝓝 0))
    (hδOuter : Tendsto (fun n => e n s - e n 0) atTop (𝓝 0))
    (hstart : ∀ b, (∀ᶠ n in atTop, j b n = 0) ∨ Tendsto (j b) atTop atTop)
    (t : β → Fin s → ℝ) (tOuter : β → ℝ)
    (htime : ∀ b (i : Fin s), Tendsto (fun n =>
      (idsCandidate law (e n (i.val + 1)) - idsCandidate law (e n i.val)) * (j b n : ℝ))
      atTop (𝓝 (t b i)))
    (htimeOuter : ∀ b, Tendsto (fun n =>
      (idsCandidate law (e n s) - idsCandidate law (e n 0)) * (j b n : ℝ))
      atTop (𝓝 (tOuter b))) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Antitone r ∧ Tendsto r atTop (𝓝 0) ∧
      Tendsto (fun n => iidMeasure law {ω | ∀ b,
        ω ∈ canonicalColoredGoodStart (e n) s (j b n) (r n)}) atTop (𝓝 1) ∧
      ∀ b, Tendsto (fun n => iidMeasure law
        (canonicalColoredGoodStart (e n) s (j b n) (r n))) atTop (𝓝 1) := by
  have hplus : ∀ a b : ℝ, a + (b - a) = b := by intro a b; ring
  apply canonicalColoredGoodStart_cutoff_of_finite_tails law e s j
  · intro b i r hr
    exact canonical_zero_initial_tail_at_eventually_zero_or_diverging_times law input hK
      (fun n => e n i.val) (fun n => e n (i.val + 1) - e n i.val)
      (hEnergy.mono fun _ hn => hn i.val i.isLt.le)
      (by simpa only [hplus] using
        (hEnergy.mono fun _ hn => hn (i.val + 1) (Nat.succ_le_of_lt i.isLt)))
      (horder.mono fun _ hn => sub_nonneg.mpr (hn i.val i.isLt))
      (by simpa only [hplus] using (hp.mono fun _ hn => hn i.val i.isLt))
      (hδ i.val i.isLt) (j b) (hstart b)
      (by simpa only [hplus] using htime b i) hr
  · intro b r hr
    exact canonical_zero_initial_tail_at_eventually_zero_or_diverging_times law input hK
      (fun n => e n 0) (fun n => e n s - e n 0)
      (hEnergy.mono fun _ hn => hn 0 (Nat.zero_le s))
      (by simpa only [hplus] using (hEnergy.mono fun _ hn => hn s le_rfl))
      (houterOrder.mono fun _ hn => sub_nonneg.mpr hn)
      (by simpa only [hplus] using hpOuter) hδOuter (j b) (hstart b)
      (by simpa only [hplus] using htimeOuter b) hr

end FixedCouplingPoisson.Furstenberg
