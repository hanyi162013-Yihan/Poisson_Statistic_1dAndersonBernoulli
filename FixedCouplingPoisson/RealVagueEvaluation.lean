import FixedCouplingPoisson.RealVagueSpace
import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic.Linarith

/-! Intrinsic Borel interval evaluation on actual locally finite vague measures. -/
noncomputable section
namespace FixedCouplingPoisson.RealVagueMeasure
open MeasureTheory Set Topology
open scoped Topology CompactlySupported ENNReal

private abbrev OpenMeasureTest (U : Set ℝ) :=
  {f : C_c(ℝ, ℝ) // (∀ x, f x ∈ Icc 0 1) ∧ tsupport f ⊆ U}

private theorem openMeasureTest_integral_le (μ : RealVagueMeasure) {U : Set ℝ}
    (hU : IsOpen U) (f : OpenMeasureTest U) :
    ENNReal.ofReal (testIntegral μ f.val) ≤ (μ : Measure ℝ) U := by
  rw [testIntegral, ofReal_integral_eq_lintegral_ofReal f.val.integrable
    (ae_of_all _ fun x => (f.property.1 x).1)]
  calc
    _ ≤ ∫⁻ x, U.indicator (fun _ => (1 : ℝ≥0∞)) x ∂(μ : Measure ℝ) := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ U
      · rw [indicator_of_mem hx]
        exact (ENNReal.ofReal_le_ofReal (f.property.1 x).2).trans_eq ENNReal.ofReal_one
      · have hz : f.val x = 0 :=
          image_eq_zero_of_notMem_tsupport (fun hs => hx (f.property.2 hs))
        simp [hx, hz]
    _ = _ := by rw [lintegral_indicator_const hU.measurableSet, one_mul]

private theorem measure_compact_le_openMeasureTest_integral
    (μ : RealVagueMeasure) {U K : Set ℝ} (f : OpenMeasureTest U)
    (hK : IsCompact K) (hfK : EqOn f.val 1 K) :
    (μ : Measure ℝ) K ≤ ENNReal.ofReal (testIntegral μ f.val) := by
  rw [testIntegral, ofReal_integral_eq_lintegral_ofReal f.val.integrable
    (ae_of_all _ fun x => (f.property.1 x).1)]
  calc
    _ = ∫⁻ x, K.indicator (fun _ => (1 : ℝ≥0∞)) x ∂(μ : Measure ℝ) := by
      rw [lintegral_indicator_const hK.measurableSet, one_mul]
    _ ≤ _ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ K
      · simp [hx, hfK hx]
      · simp [hx]

private theorem measure_open_eq_iSup_testIntegral (μ : RealVagueMeasure)
    {U : Set ℝ} (hU : IsOpen U) :
    (μ : Measure ℝ) U = ⨆ f : OpenMeasureTest U, ENNReal.ofReal (testIntegral μ f.val) := by
  classical
  apply le_antisymm
  · rw [hU.measure_eq_iSup_isCompact (μ : Measure ℝ)]
    refine iSup_le fun K => iSup_le fun hKU => iSup_le fun hK => ?_
    obtain ⟨f, hfK, hfcompact, hfU, hfbounds⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
    let g : OpenMeasureTest U := ⟨⟨f, hfcompact⟩, hfbounds, hfU⟩
    exact le_iSup_of_le g (measure_compact_le_openMeasureTest_integral μ g hK hfK)
  · exact iSup_le fun f => openMeasureTest_integral_le μ hU f

/-- Evaluation on each actual open set is lower semicontinuous for the vague topology. -/
theorem lowerSemicontinuous_measure_open {U : Set ℝ} (hU : IsOpen U) :
    LowerSemicontinuous (fun μ : RealVagueMeasure => (μ : Measure ℝ) U) := by
  have heq : (fun μ : RealVagueMeasure => (μ : Measure ℝ) U) =
      fun μ => ⨆ f : OpenMeasureTest U, ENNReal.ofReal (testIntegral μ f.val) :=
    funext fun μ => measure_open_eq_iSup_testIntegral μ hU
  rw [heq]
  exact lowerSemicontinuous_iSup fun f =>
    (ENNReal.continuous_ofReal.comp (continuous_testIntegral f.val)).lowerSemicontinuous

/-- The intrinsic measure of every open set is a Borel random variable. -/
theorem measurable_measure_open {U : Set ℝ} (hU : IsOpen U) :
    Measurable (fun μ : RealVagueMeasure => (μ : Measure ℝ) U) :=
  (lowerSemicontinuous_measure_open hU).measurable

/-- Genuine half-open interval evaluation is Borel measurable, including reversed endpoints. -/
theorem measurable_measure_Ioc (a b : ℝ) :
    Measurable (fun μ : RealVagueMeasure => (μ : Measure ℝ) (Ioc a b)) := by
  by_cases hab : a ≤ b
  · have hset : Ioo a (b + 1) \ Ioo b (b + 1) = Ioc a b := by
      ext x
      simp only [mem_sdiff, mem_Ioo, mem_Ioc]
      constructor
      · rintro ⟨⟨hax, hxb⟩, hnot⟩
        exact ⟨hax, le_of_not_gt (fun hbx => hnot ⟨hbx, hxb⟩)⟩
      · rintro ⟨hax, hxb⟩
        exact ⟨⟨hax, by linarith⟩, fun h => (not_lt_of_ge hxb) h.1⟩
    have heq (μ : RealVagueMeasure) :
        (μ : Measure ℝ) (Ioc a b) =
          (μ : Measure ℝ) (Ioo a (b + 1)) - (μ : Measure ℝ) (Ioo b (b + 1)) := by
      rw [← hset]
      apply measure_sdiff
      · intro x hx
        exact ⟨lt_of_le_of_lt hab hx.1, hx.2⟩
      · exact measurableSet_Ioo.nullMeasurableSet
      · exact (lt_of_le_of_lt (measure_mono Ioo_subset_Icc_self)
          (isCompact_Icc.measure_lt_top (μ := (μ : Measure ℝ)))).ne
    simp_rw [heq]
    exact (measurable_measure_open isOpen_Ioo).sub (measurable_measure_open isOpen_Ioo)
  · rw [Ioc_eq_empty (not_lt.mpr (le_of_lt (lt_of_not_ge hab)))]
    simpa using (measurable_const : Measurable (fun _ : RealVagueMeasure => (0 : ℝ≥0∞)))

/-- The real-valued intrinsic interval mass is Borel measurable as well. -/
theorem measurable_measureReal_Ioc (a b : ℝ) :
    Measurable (fun μ : RealVagueMeasure => (μ : Measure ℝ).real (Ioc a b)) :=
  ENNReal.measurable_toReal.comp (measurable_measure_Ioc a b)

end FixedCouplingPoisson.RealVagueMeasure
