import FixedCouplingPoisson.CanonicalResidualCutoff

/-! Finite-prefix parameter repairs for the actual residual and rounding limits. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology ENNReal

/-- A finite-prefix repair reads one valid index before the eventual valid range.
The selector is eventually the identity, so it preserves full-sequence limits. -/
theorem exists_eventually_id_valid_selector {P : ℕ → Prop}
    (hP : ∀ᶠ n in atTop, P n) :
    ∃ ρ : ℕ → ℕ, (∀ n, P (ρ n)) ∧ ρ =ᶠ[atTop] id := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hP
  refine ⟨fun n => max n N, (fun n => hN _ (le_max_right n N)), ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  exact max_eq_left hn

/-- Eventual model validity suffices for actual residual pinning. Only finitely
many parameter values are repaired inside the proof; the observation times
and the stated random variables remain the original ones. -/
theorem canonicalCrossingResidual_tails_tendsto_zero_eventually (law : PotentialLaw)
    (input : Input law) {K : Set ℝ} (hK : IsCompact K)
    (E δ θ φ : ℕ → ℝ)
    (hE : ∀ᶠ n in atTop, E n ∈ K) (hE' : ∀ᶠ n in atTop, E n + δ n ∈ K)
    (hδ0 : ∀ᶠ n in atTop, 0 ≤ δ n) (hinit : ∀ᶠ n in atTop, φ n ≤ θ n)
    (hp : ∀ᶠ n in atTop,
      0 < idsCandidate law (E n + δ n) - idsCandidate law (E n))
    (hδ : Tendsto δ atTop (𝓝 0))
    (hgap : Tendsto (fun n => θ n - φ n) atTop (𝓝 0))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop) {t : ℝ}
    (htime : Tendsto (fun n =>
      (idsCandidate law (E n + δ n) - idsCandidate law (E n)) * (k n : ℝ))
      atTop (𝓝 t)) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => iidMeasure law {ω |
      r < canonicalCrossingResidual (E n) (δ n) (θ n) (φ n) (k n) ω})
      atTop (𝓝 0) := by
  have hvalid : ∀ᶠ n in atTop,
      E n ∈ K ∧ E n + δ n ∈ K ∧ 0 ≤ δ n ∧ φ n ≤ θ n ∧
        0 < idsCandidate law (E n + δ n) - idsCandidate law (E n) := by
    filter_upwards [hE, hE', hδ0, hinit, hp] with n hn hn' hd hi hpn
    exact ⟨hn, hn', hd, hi, hpn⟩
  obtain ⟨ρ, hρvalid, hρeq⟩ := exists_eventually_id_valid_selector hvalid
  have hρtop : Tendsto ρ atTop atTop := tendsto_id.congr' hρeq.symm
  have hgap' : Tendsto (fun n => θ (ρ n) - φ (ρ n)) atTop (𝓝 0) :=
    hgap.comp hρtop
  have ht : Tendsto (fun n =>
      (idsCandidate law (E (ρ n) + δ (ρ n)) - idsCandidate law (E (ρ n))) *
        (k n : ℝ)) atTop (𝓝 t) := by
    apply htime.congr'
    filter_upwards [hρeq] with n hn
    simp only [hn, id_eq]
  have htail := canonicalCrossingResidual_tails_tendsto_zero law input hK
    (E ∘ ρ) (δ ∘ ρ) (θ ∘ ρ) (φ ∘ ρ)
    (fun n => (hρvalid n).1) (fun n => (hρvalid n).2.1)
    (fun n => (hρvalid n).2.2.1) (fun n => (hρvalid n).2.2.2.1)
    (fun n => (hρvalid n).2.2.2.2)
    (hδ.comp hρtop) hgap' k hk ht hr
  apply htail.congr'
  filter_upwards [hρeq] with n hn
  simp only [Function.comp_apply, hn, id_eq]

/-- The actual terminal residual limit requires valid endpoint and rate
conditions only eventually. -/
theorem actualWindowResidual_tails_tendsto_zero_eventually
    (law : PotentialLaw) (input : Input law) {K : Set ℝ} (hK : IsCompact K)
    (e : ℕ → ℕ → ℝ) (i : ℕ)
    (hE : ∀ᶠ n in atTop, e n i ∈ K) (hE' : ∀ᶠ n in atTop, e n (i + 1) ∈ K)
    (horder : ∀ᶠ n in atTop, e n i ≤ e n (i + 1))
    (hp : ∀ᶠ n in atTop,
      0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i))
    (hδ : Tendsto (fun n => e n (i + 1) - e n i) atTop (𝓝 0)) {t : ℝ}
    (htime : Tendsto (fun n =>
      (idsCandidate law (e n (i + 1)) - idsCandidate law (e n i)) * (n : ℝ))
      atTop (𝓝 t)) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => iidMeasure law {ω | r < actualWindowResidual e n i ω})
      atTop (𝓝 0) := by
  have hplus : ∀ n, e n i + (e n (i + 1) - e n i) = e n (i + 1) := by
    intro n
    ring
  have hg : Tendsto (fun _n : ℕ => (0 : ℝ) - 0) atTop (𝓝 0) := by
    simpa only [sub_self] using (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ℝ))
      atTop (𝓝 0))
  have ht : Tendsto (fun n =>
      (idsCandidate law (e n i + (e n (i + 1) - e n i)) - idsCandidate law (e n i)) *
        (id n : ℝ)) atTop (𝓝 t) := by
    simpa only [hplus, id_eq] using htime
  have htail := canonicalCrossingResidual_tails_tendsto_zero_eventually law input hK
    (fun n => e n i) (fun n => e n (i + 1) - e n i) (fun _ => 0) (fun _ => 0)
    hE (by simpa only [hplus] using hE')
    (horder.mono fun _ hn => sub_nonneg.mpr hn)
    (Eventually.of_forall fun _ => le_rfl)
    (by simpa only [hplus] using hp) hδ hg id tendsto_id ht hr
  simpa only [actualWindowResidual_eq_canonicalCrossingResidual, id_eq] using htail

/-- The exact actual spectral-rounding conclusion is unchanged by failures of
energy/rate conditions on a finite prefix of the observation sequence. -/
theorem actualWindow_rounding_success_from_IDS_scales_eventually
    (law : PotentialLaw) (input : Input law) (E : ℝ) {K : Set ℝ} (hK : IsCompact K)
    (e : ℕ → ℕ → ℝ) (s κ : ℕ) (hκ : κ ≤ s)
    (hanchor : ∀ n, e n κ = E)
    (hEnergy : ∀ᶠ n in atTop, ∀ i, i ≤ s → e n i ∈ K)
    (horder : ∀ᶠ n in atTop, ∀ i, i < s → e n i ≤ e n (i + 1))
    (hp : ∀ᶠ n in atTop, ∀ i, i < s →
      0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i))
    (hδ : ∀ i < s, Tendsto (fun n => e n (i + 1) - e n i) atTop (𝓝 0))
    (w : ℕ → ℝ)
    (htime : ∀ i < s, Tendsto (fun n =>
      (idsCandidate law (e n (i + 1)) - idsCandidate law (e n i)) * (n : ℝ))
      atTop (𝓝 (w i))) :
    Tendsto (fun n => iidMeasure law {ω | ∀ i, i < s →
      actualWindowSpectralCount e n i ω = actualWindowWinding e n i ω})
      atTop (𝓝 1) := by
  apply actualWindow_rounding_success_of_individual_residuals law E (input.atEnergy E)
    e s κ hκ hanchor
  intro i hi r hr
  exact actualWindowResidual_tails_tendsto_zero_eventually law input hK e i
    (hEnergy.mono fun _ hn => hn i hi.le)
    (hEnergy.mono fun _ hn => hn (i + 1) (Nat.succ_le_of_lt hi))
    (horder.mono fun _ hn => hn i hi) (hp.mono fun _ hn => hn i hi)
    (hδ i hi) (htime i hi) hr

/-- One full-sequence cutoff handles finitely many true residuals under
only eventual model conditions. A time-zero member is included without
requiring its observation times to diverge. -/
theorem canonicalCrossingResidual_finite_exists_antitone_cutoff_eventually
    {ι : Type*} [Fintype ι] (law : PotentialLaw) (input : Input law)
    {K : Set ℝ} (hK : IsCompact K) (E δ θ φ : ι → ℕ → ℝ) (k : ι → ℕ → ℕ)
    (hE : ∀ i, ∀ᶠ n in atTop, E i n ∈ K)
    (hE' : ∀ i, ∀ᶠ n in atTop, E i n + δ i n ∈ K)
    (hδ0 : ∀ i, ∀ᶠ n in atTop, 0 ≤ δ i n)
    (hinit : ∀ i, ∀ᶠ n in atTop, φ i n ≤ θ i n)
    (hp : ∀ i, ∀ᶠ n in atTop,
      0 < idsCandidate law (E i n + δ i n) - idsCandidate law (E i n))
    (hδ : ∀ i, Tendsto (δ i) atTop (𝓝 0))
    (hgap : ∀ i, Tendsto (fun n => θ i n - φ i n) atTop (𝓝 0))
    (hstart : ∀ i, (∀ᶠ n in atTop, k i n = 0 ∧ θ i n = φ i n) ∨
      Tendsto (k i) atTop atTop)
    (t : ι → ℝ)
    (htime : ∀ i, Tendsto (fun n =>
      (idsCandidate law (E i n + δ i n) - idsCandidate law (E i n)) * (k i n : ℝ))
      atTop (𝓝 (t i))) :
    ∃ r : ℕ → ℝ, (∀ n, 0 < r n) ∧ Antitone r ∧
      Tendsto r atTop (𝓝 0) ∧ Tendsto (fun n => iidMeasure law {ω |
        ∃ i, r n < canonicalCrossingResidual (E i n) (δ i n) (θ i n) (φ i n)
          (k i n) ω}) atTop (𝓝 0) := by
  apply finite_residual_exists_antitone_cutoff (iidMeasure law)
    (fun n i ω => canonicalCrossingResidual (E i n) (δ i n) (θ i n) (φ i n) (k i n) ω)
  intro i r hr
  rcases hstart i with hzero | hk
  · apply (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ENNReal))
      atTop (𝓝 0)).congr'
    filter_upwards [hzero] with n hn
    have hz : ∀ ω, canonicalCrossingResidual (E i n) (δ i n)
        (θ i n) (φ i n) (k i n) ω = 0 := by
      intro ω
      simp only [canonicalCrossingResidual, canonicalCrossingCount,
        hn.1, canonicalGapProcess_zero, hn.2, sub_self,
        zero_div, Int.floor_zero, Int.cast_zero, mul_zero]
    simp only [hz, not_lt_of_ge hr.le, Set.ofPred_false, measure_empty]
  · exact canonicalCrossingResidual_tails_tendsto_zero_eventually law input hK
      (E i) (δ i) (θ i) (φ i) (hE i) (hE' i) (hδ0 i) (hinit i) (hp i)
      (hδ i) (hgap i) (k i) hk (htime i) hr

end FixedCouplingPoisson.Furstenberg
