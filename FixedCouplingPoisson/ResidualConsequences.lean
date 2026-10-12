import FixedCouplingPoisson.UnstoppedPairCollapse
import FixedCouplingPoisson.ResidualUpper
import FixedCouplingPoisson.ForwardPinning


/-! Elementary assembly of middle-residual and upper-residual estimates. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- A verified middle-residual limit and arbitrary small upper-end bounds
select the zero endpoint. Both inputs are explicit here and must be proved
for the actual model before this lemma can be applied. -/
theorem residual_tails_tendsto_zero_of_middle_upper {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : ℕ → Ω → ℝ)
    (hmiddle : ∀ h : ℝ, 0 < h → Tendsto
      (fun n => μ {ω | h ≤ R n ω ∧ R n ω ≤ Real.pi - h}) atTop (𝓝 0))
    (hupper : ∀ ε : ℝ, 0 < ε → ∃ h : ℝ, 0 < h ∧ ∀ᶠ n in atTop,
      μ {ω | Real.pi - h ≤ R n ω} ≤ ENNReal.ofReal ε)
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => μ {ω | r < R n ω}) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  by_cases htop : ε = ∞
  · exact Eventually.of_forall fun _ => by simp only [htop, le_top]
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨h, hh, hbound⟩ := hupper (ε.toReal / 2) (half_pos hεr)
  let q := min r h
  have hq : 0 < q := lt_min hr hh
  have hsmall := (hmiddle q hq).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.mpr (half_pos hεr)))
  filter_upwards [hbound, hsmall] with n hn hmn
  have hsub : {ω | r < R n ω} ⊆
      {ω | q ≤ R n ω ∧ R n ω ≤ Real.pi - q} ∪
        {ω | Real.pi - h ≤ R n ω} := by
    intro ω hω
    by_cases hu : Real.pi - h ≤ R n ω
    · exact Or.inr hu
    · exact Or.inl ⟨(min_le_left r h).trans hω.le,
        (not_le.mp hu).le.trans (sub_le_sub_left (min_le_right r h) Real.pi)⟩
  calc
    μ {ω | r < R n ω} ≤ μ
        ({ω | q ≤ R n ω ∧ R n ω ≤ Real.pi - q} ∪
          {ω | Real.pi - h ≤ R n ω}) := measure_mono hsub
    _ ≤ μ {ω | q ≤ R n ω ∧ R n ω ≤ Real.pi - q} +
        μ {ω | Real.pi - h ≤ R n ω} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε.toReal / 2) + ENNReal.ofReal (ε.toReal / 2) :=
      add_le_add hmn.le hn
    _ = ε := by
      rw [← ENNReal.ofReal_add (half_pos hεr).le (half_pos hεr).le]
      have heq : ε.toReal / 2 + ε.toReal / 2 = ε.toReal := by ring
      rw [heq, ENNReal.ofReal_toReal htop]

/-- Assembly at actual deterministic observation times. The short-window
claim is an explicit intermediate premise, to be discharged by actual arrival
convergence; this statement alone does not prove the model's pinning result. -/
theorem canonicalCrossingResidual_tails_of_short_windows (law : PotentialLaw)
    (input : Input law) {K : Set ℝ} (hK : IsCompact K) (hne : K.Nonempty)
    (E δ θ φ : ℕ → ℝ) (k : ℕ → ℕ)
    (hE : ∀ᶠ n in atTop, E n ∈ K)
    (hE' : ∀ᶠ n in atTop, E n + δ n ∈ K)
    (hδ0 : ∀ᶠ n in atTop, 0 ≤ δ n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hk : Tendsto k atTop atTop)
    (hp : ∀ᶠ n in atTop, 0 < idsCandidate law (E n + δ n) - idsCandidate law (E n))
    (hshort : ∀ ε : ℝ, 0 < ε → ∃ L : ℕ → ℕ, ∃ a : ℝ, 0 < a ∧
      (∀ᶠ n in atTop, a ≤ (idsCandidate law (E n + δ n) - idsCandidate law (E n)) *
        (L n : ℝ)) ∧
      (∀ᶠ n in atTop, iidMeasure law {ω |
        canonicalCrossingCount (E n) (δ n) (θ n) (φ n) (k n) ω <
          canonicalCrossingCount (E n) (δ n) (θ n) (φ n) (k n + L n) ω} ≤
            ENNReal.ofReal ε))
    {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => iidMeasure law {ω |
      r < canonicalCrossingResidual (E n) (δ n) (θ n) (φ n) (k n) ω})
      atTop (𝓝 0) := by
  apply residual_tails_tendsto_zero_of_middle_upper (iidMeasure law)
    (fun n => canonicalCrossingResidual (E n) (δ n) (θ n) (φ n) (k n))
    (fun h hh => canonicalCrossingResidual_middle_tendsto_zero law input hK hne
      E δ θ φ k hE hδ hk hh) ?_ hr
  intro ε hε
  obtain ⟨L, a, ha, hL, hcross⟩ := hshort (ε / 2) (half_pos hε)
  obtain ⟨d, hd, hupper⟩ := inverse_upper_residual_probability_uniform law input hK
    (half_pos hε) ha
  refine ⟨d / 2, half_pos hd, ?_⟩
  filter_upwards [hE, hE', hδ0, hp, hL, hcross, hδ.eventually (gt_mem_nhds hd)]
    with n hEn hE'n hδn hpn hLn hcrossn hδdn
  calc
    _ ≤ iidMeasure law {ω |
        canonicalCrossingCount (E n) (δ n) (θ n) (φ n) (k n) ω <
          canonicalCrossingCount (E n) (δ n) (θ n) (φ n) (k n + L n) ω} +
        ENNReal.ofReal (ε / 2) :=
      hupper (E n) hEn (δ n) hδn hE'n hδdn (θ n) (φ n) hpn (k n) (L n) hLn
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hcrossn le_rfl
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
      congr 1
      ring

end FixedCouplingPoisson.Furstenberg


/-!
# Fixed-anchor disappearance of actual terminal spectral rounding errors

Actual oriented residual tails and forward nonatomic pinning together make
all actual finite spectral window counts equal their winding integers with
probability tending to one.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter
open scoped Topology BigOperators ENNReal

/-- Once the actual residuals vanish in probability, a fixed exact energy
anchor removes all terminal rounding errors simultaneously. -/
theorem actualWindow_rounding_error_tendsto_zero (law : PotentialLaw) (E : ℝ)
    (data : QualitativeData law E) (e : ℕ → ℕ → ℝ) (s κ : ℕ) (hκ : κ ≤ s)
    (hanchor : ∀ n, e n κ = E)
    (hres : ∀ h : ℝ, 0 < h → Tendsto
      (fun n => iidMeasure law {ω | ∃ i, i < s ∧ h < actualWindowResidual e n i ω})
      atTop (𝓝 0)) :
    Tendsto (fun n => iidMeasure law
      {ω | ∃ i, i < s ∧ actualWindowSpectralCount e n i ω ≠ actualWindowWinding e n i ω})
      atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  by_cases hεtop : ε = ∞
  · exact Eventually.of_forall fun n => by simp only [hεtop, le_top]
  have hεreal : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  let ρ := ε.toReal / 2
  have hρ : 0 < ρ := half_pos hεreal
  obtain ⟨δ, hδ, hpin⟩ := iid_canonicalPhase_anchor_pinning law E 0 data
    (phaseProjective (Real.pi / 2)) ρ hρ
  let c : ℝ := 2 * (s : ℝ) + 1
  have hc : 0 < c := by dsimp only [c]; positivity
  let h := δ / c
  have hh : 0 < h := div_pos hδ hc
  have hch : (2 * (s : ℝ) + 1) * h = δ := by
    change c * (δ / c) = δ
    field_simp [hc.ne']
  have hsmall := (hres h hh).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.mpr hρ))
  filter_upwards [hpin, hsmall] with n hn hsmalln
  have hsubset :
      {ω | ∃ i, i < s ∧ actualWindowSpectralCount e n i ω ≠ actualWindowWinding e n i ω} ⊆
      {ω | ∃ i, i < s ∧ h < actualWindowResidual e n i ω} ∪
        {ω | projectiveDistance (phaseProjective (canonicalPhaseProcess E 0 n ω))
          (phaseProjective (Real.pi / 2)) ≤ δ} := by
    intro ω hω
    by_cases hbad : ∃ i, i < s ∧ h < actualWindowResidual e n i ω
    · exact Or.inl hbad
    · right
      obtain ⟨i, hi, herr⟩ := hω
      have hresbound : ∀ j < s, terminalWindowResidual (actualEndpointPhase e n ω) j ≤ h := by
        intro j hj
        exact le_of_not_gt (fun hlt => hbad ⟨j, hj, hlt⟩)
      rw [actualWindowSpectralCount_eq_terminal] at herr
      have hd := terminalWindow_error_anchor_distance (actualEndpointPhase e n ω)
        (Real.pi / 2) s κ hκ h hh.le hresbound i hi herr
      rw [hch] at hd
      have heq : actualEndpointPhase e n ω κ = canonicalPhaseProcess E 0 n ω := by
        unfold actualEndpointPhase
        rw [hanchor, shootingPhase_eq_process]
      rw [heq] at hd
      exact hd
  calc
    _ ≤ iidMeasure law
        ({ω | ∃ i, i < s ∧ h < actualWindowResidual e n i ω} ∪
          {ω | projectiveDistance (phaseProjective (canonicalPhaseProcess E 0 n ω))
            (phaseProjective (Real.pi / 2)) ≤ δ}) := measure_mono hsubset
    _ ≤ iidMeasure law {ω | ∃ i, i < s ∧ h < actualWindowResidual e n i ω} +
        iidMeasure law {ω | projectiveDistance (phaseProjective (canonicalPhaseProcess E 0 n ω))
          (phaseProjective (Real.pi / 2)) ≤ δ} := measure_union_le _ _
    _ ≤ ENNReal.ofReal ρ + ENNReal.ofReal ρ := add_le_add hsmalln.le hn.le
    _ = ε := by
      rw [← ENNReal.ofReal_add hρ.le hρ.le]
      have hsum : ρ + ρ = ε.toReal := by dsimp only [ρ]; ring
      rw [hsum, ENNReal.ofReal_toReal hεtop]

/-- The actual spectral window counts equal the windings with probability tending to one. -/
theorem actualWindow_rounding_success_tendsto_one (law : PotentialLaw) (E : ℝ)
    (data : QualitativeData law E) (e : ℕ → ℕ → ℝ) (s κ : ℕ) (hκ : κ ≤ s)
    (hanchor : ∀ n, e n κ = E)
    (hres : ∀ h : ℝ, 0 < h → Tendsto
      (fun n => iidMeasure law {ω | ∃ i, i < s ∧ h < actualWindowResidual e n i ω})
      atTop (𝓝 0)) :
    Tendsto (fun n => iidMeasure law
      {ω | ∀ i, i < s → actualWindowSpectralCount e n i ω = actualWindowWinding e n i ω})
      atTop (𝓝 1) := by
  have hbad := actualWindow_rounding_error_tendsto_zero law E data e s κ hκ hanchor hres
  have ht := ENNReal.Tendsto.sub
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ≥0∞)) atTop (𝓝 1)) hbad
    (Or.inl ENNReal.one_ne_top)
  simp only [tsub_zero] at ht
  convert ht using 1
  funext n
  let good := {ω | ∀ i, i < s →
    actualWindowSpectralCount e n i ω = actualWindowWinding e n i ω}
  have hgood : MeasurableSet good := measurableSet_actualWindow_rounding_success e n s
  have hcompl : {ω | ∃ i, i < s ∧
      actualWindowSpectralCount e n i ω ≠ actualWindowWinding e n i ω} = goodᶜ := by
    ext ω
    change (∃ i, i < s ∧ actualWindowSpectralCount e n i ω ≠
      actualWindowWinding e n i ω) ↔
      ¬ (∀ i, i < s → actualWindowSpectralCount e n i ω = actualWindowWinding e n i ω)
    constructor
    · rintro ⟨i, hi, hne⟩ hall
      exact hne (hall i hi)
    · intro hnot
      classical
      by_contra hnone
      apply hnot
      intro i hi
      by_contra hne
      exact hnone ⟨i, hi, hne⟩
  rw [hcompl, measure_compl hgood (measure_ne_top _ _)]
  rw [measure_univ, ENNReal.sub_sub_cancel ENNReal.one_ne_top prob_le_one]

theorem actualWindow_rounding_success_of_individual_residuals (law : PotentialLaw) (E : ℝ)
    (data : QualitativeData law E) (e : ℕ → ℕ → ℝ) (s κ : ℕ) (hκ : κ ≤ s)
    (hanchor : ∀ n, e n κ = E)
    (hres : ∀ i < s, ∀ h : ℝ, 0 < h → Tendsto
      (fun n => iidMeasure law {ω | h < actualWindowResidual e n i ω}) atTop (𝓝 0)) :
    Tendsto (fun n => iidMeasure law
      {ω | ∀ i, i < s → actualWindowSpectralCount e n i ω = actualWindowWinding e n i ω})
      atTop (𝓝 1) :=
  actualWindow_rounding_success_tendsto_one law E data e s κ hκ hanchor
    (actualWindow_residual_union_tendsto_zero law e s hres)

end FixedCouplingPoisson.Furstenberg
