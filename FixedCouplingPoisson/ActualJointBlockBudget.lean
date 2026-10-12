import FixedCouplingPoisson.ActualJointScaling
import FixedCouplingPoisson.ActualColoredProduct
import FixedCouplingPoisson.ColoredGoodStarts

/-! The true colored-count block budget, with every kernel and good-event
probability discharged by the phase model. -/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal

theorem canonicalColoredCount_twoStage_budget
    (law : PotentialLaw) (input : Input law) {K : Set ℝ} (hK : IsCompact K)
    (e : ℕ → ℕ → ℝ) (s : ℕ) (E₀ : ℝ)
    (hcompact : ∀ n i, i ≤ s → e n i ∈ K)
    (horder : ∀ n i, i < s → e n i ≤ e n (i + 1))
    (houter : ∀ n, e n 0 ≤ e n s)
    (hp : ∀ n i, i < s → 0 < idsCandidate law (e n (i + 1)) - idsCandidate law (e n i))
    (hpouter : ∀ n, 0 < idsCandidate law (e n s) - idsCandidate law (e n 0))
    (helim : ∀ i, i ≤ s → Tendsto (fun n => e n i) atTop (𝓝 E₀))
    (w : Fin s → ℝ) (W : ℝ) (hw : ∀ i, 0 ≤ w i) (hW : 0 ≤ W)
    (hscale : ∀ i : Fin s, Tendsto (fun n =>
      (idsCandidate law (e n (i.val + 1)) - idsCandidate law (e n i.val)) * (n : ℝ))
      atTop (𝓝 (w i)))
    (houterScale : Tendsto (fun n =>
      (idsCandidate law (e n s) - idsCandidate law (e n 0)) * (n : ℝ)) atTop (𝓝 W))
    (t : Fin s → ℝ) (ht : ∀ i, 0 ≤ t i)
    {m : ℕ} (hm : 0 < m)
    (ha : 0 ≤ 1 - (∑ i, firstArrivalWeight (t i) * w i) / (m : ℝ))
    (η : ℝ) (hη : 0 < η) :
    ∀ᶠ n in atTop,
      |(∫ ω, coloredLaplaceFactor t (fun i => canonicalNaturalCrossingCount
        (e n i.val) (e n (i.val + 1) - e n i.val) 0 0 n ω) ∂iidMeasure law) -
          (1 - (∑ i, firstArrivalWeight (t i) * w i) / (m : ℝ)) ^ m| ≤
        coloredQuadraticBudget s w W / (m : ℝ) + η := by
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have hmass (i : Fin s) := idsCluster_mass_tendsto_zero law e i.val (i.val + 1) E₀
    (helim i.val i.isLt.le) (helim (i.val + 1) (by omega))
  have hmassOuter := idsCluster_mass_tendsto_zero law e 0 s E₀
    (helim 0 (Nat.zero_le s)) (helim s le_rfl)
  let j : Fin m → ℕ → ℕ := fun b n => equalBlockEndpoint m b.val n
  have htime (b : Fin m) (i : Fin s) := equalBlockEndpoint_scaled_tendsto hm b.val
    (N := id) (fun n => (hp n i.val i.isLt).le) (hmass i) (hscale i)
  have htimeOuter (b : Fin m) := equalBlockEndpoint_scaled_tendsto hm b.val
    (N := id) (fun n => (hpouter n).le) hmassOuter houterScale
  have hstart (b : Fin m) : (∀ᶠ n in atTop, j b n = 0) ∨
      Tendsto (j b) atTop atTop := by
    by_cases hb : b.val = 0
    · left
      exact Eventually.of_forall (fun n => by simp [j, hb])
    · right
      exact equalBlockEndpoint_tendsto_atTop hm (Nat.pos_of_ne_zero hb) tendsto_id
  obtain ⟨r, hr, _, hrlim, _, hgood⟩ :=
    canonicalColoredGoodStart_cutoff_from_scales_eventually law input hK e s j
      (Eventually.of_forall hcompact) (Eventually.of_forall horder)
      (Eventually.of_forall houter) (Eventually.of_forall hp) (Eventually.of_forall hpouter)
      (fun i hi => by simpa only [sub_self] using
        (helim (i + 1) (by omega)).sub (helim i hi.le))
      (by simpa only [sub_self] using (helim s le_rfl).sub (helim 0 (Nat.zero_le s)))
      hstart (fun b i => (b.val : ℝ) * w i / (m : ℝ))
      (fun b => (b.val : ℝ) * W / (m : ℝ)) htime htimeOuter
  let ε : ℝ := η / (2 * (m : ℝ) * (2 * (s : ℝ) + 1))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hkernels : ∀ b : Fin m, ∀ᶠ n in atTop, ∀ a : ℕ,
      ∀ᵐ ω ∂iidMeasure law, ω ∈ canonicalColoredGoodStart (e n) s a (r n) →
        |((iidMeasure law)[(fun z => coloredLaplaceFactor t
          (canonicalColoredBlock (e n) s a (equalBlockLength m b.val n) z)) |
            pastMeasurableSpace a]) ω -
          (1 - (∑ i, firstArrivalWeight (t i) * w i) / (m : ℝ))| ≤
        coloredQuadraticBudget s (fun i => w i / (m : ℝ)) (W / (m : ℝ)) +
          (2 * (s : ℝ) + 1) * ε := by
    intro b
    simpa only [coloredArrivalWeight_div] using
      canonicalColoredBlock_conditional_error_uniform law input hK e s E₀
        hcompact horder houter hp hpouter helim r (fun n => (hr n).le) hrlim
        (fun n => equalBlockLength m b.val n) (fun i => w i / (m : ℝ)) (W / (m : ℝ))
        (fun i => div_nonneg (hw i) hmR.le) (div_nonneg hW hmR.le)
        (fun i => equalBlockLength_scaled_tendsto hm b.val (N := id)
          (fun n => (hp n i.val i.isLt).le) (hmass i) (hscale i))
        (equalBlockLength_scaled_tendsto hm b.val (N := id)
          (fun n => (hpouter n).le) hmassOuter houterScale) t ht ε hε
  have hbadFin := finite_good_complement_budget_tendsto_zero (iidMeasure law)
    (fun n b => canonicalColoredGoodStart (e n) s (j b n) (r n))
    (fun n b => canonicalColoredGoodStart_measurable _ _ _ _) hgood
  have hbad : Tendsto (fun n => 2 * ∑ b ∈ Finset.range m,
      (iidMeasure law).real (canonicalColoredGoodStart (e n) s
        (equalBlockEndpoint m b n) (r n))ᶜ) atTop (𝓝 0) := by
    have heq (n : ℕ) : (∑ b : Fin m, (iidMeasure law).real
        (canonicalColoredGoodStart (e n) s (equalBlockEndpoint m b.val n) (r n))ᶜ) =
        ∑ b ∈ Finset.range m, (iidMeasure law).real
          (canonicalColoredGoodStart (e n) s (equalBlockEndpoint m b n) (r n))ᶜ :=
      Fin.sum_univ_eq_sum_range (fun b : ℕ => (iidMeasure law).real
        (canonicalColoredGoodStart (e n) s (equalBlockEndpoint m b n) (r n))ᶜ) m
    simpa only [j, heq] using hbadFin
  have hbadSmall := (tendsto_order.mp hbad).2 (η / 2) (by linarith)
  have hΛ : 0 ≤ ∑ i, firstArrivalWeight (t i) * w i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (firstArrivalWeight_bounds (ht i)).1 (hw i)
  have ha1 : 1 - (∑ i, firstArrivalWeight (t i) * w i) / (m : ℝ) ≤ 1 :=
    sub_le_self _ (div_nonneg hΛ hmR.le)
  filter_upwards [eventually_all.mpr hkernels, hbadSmall] with n hkn hbn
  have hbound := canonicalColoredProduct_conditional_budget law (e n) s (horder n)
    (fun b => equalBlockEndpoint m b n) (equalBlockEndpoint_monotone m n)
    (equalBlockEndpoint_zero m n) t ht m
    (1 - (∑ i, firstArrivalWeight (t i) * w i) / (m : ℝ))
    (coloredQuadraticBudget s (fun i => w i / (m : ℝ)) (W / (m : ℝ)) +
      (2 * (s : ℝ) + 1) * ε) (r n) ha ha1
    (add_nonneg (coloredQuadraticBudget_nonneg _ _ _) (by positivity))
    (fun b hb => hkn ⟨b, hb⟩ (equalBlockEndpoint m b n))
  rw [equalBlockEndpoint_last hm] at hbound
  apply hbound.trans
  rw [mul_add, coloredQuadraticBudget_div s w W hm]
  have heps : (m : ℝ) * ((2 * (s : ℝ) + 1) * ε) = η / 2 := by
    dsimp [ε]
    field_simp
    <;> ring
  rw [heps]
  linarith

end FixedCouplingPoisson.Furstenberg
