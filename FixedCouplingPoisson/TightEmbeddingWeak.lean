import FixedCouplingPoisson.WeakProbabilityTransfer
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.TietzeExtension
import Mathlib.Tactic.Linarith

/-! Actual tight-law transfer through continuous injective coordinates.
The target law is explicitly included in the common tight family.
-/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Filter Set Topology
open scoped Topology BoundedContinuousFunction

/-- Agreement on a measurable good set controls arbitrary bounded tests. -/
theorem integral_boundedContinuous_eqOn_error_le
    {S : Type*} [MeasurableSpace S] [TopologicalSpace S] [BorelSpace S]
    (P : ProbabilityMeasure S) (f g : S →ᵇ ℝ) {K : Set S}
    (hK : MeasurableSet K) (heq : EqOn f g K) :
    |(∫ x, f x ∂(P : Measure S)) - (∫ x, g x ∂(P : Measure S))| ≤
      (‖f‖ + ‖g‖) * (P : Measure S).real Kᶜ := by
  have hfi := f.integrable (P : Measure S)
  have hgi := g.integrable (P : Measure S)
  have hbi : Integrable (Kᶜ.indicator (fun _ => ‖f‖ + ‖g‖)) (P : Measure S) :=
    (integrable_const _).indicator hK.compl
  rw [← integral_sub hfi hgi]
  calc
    _ ≤ ∫ x, |f x - g x| ∂(P : Measure S) := abs_integral_le_integral_abs
    _ ≤ ∫ x, Kᶜ.indicator (fun _ => ‖f‖ + ‖g‖) x ∂(P : Measure S) := by
      apply integral_mono_ae (hfi.sub hgi).abs hbi
      filter_upwards with x
      by_cases hx : x ∈ K
      · simp [hx, heq hx]
      · rw [Set.indicator_of_mem hx]
        exact (abs_sub _ _).trans (add_le_add
          (by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x)
          (by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x))
    _ = _ := by rw [integral_indicator_const _ hK.compl, smul_eq_mul, mul_comm]

/-- Common tightness (including the target), true coordinate weak convergence,
and a continuous injection imply ordinary weak convergence of the source laws.
A compact source set embeds closedly in the normal coordinate space; Tietze
extends each bounded test there with its norm preserved. -/
theorem probabilityMeasure_tendsto_of_tight_of_continuous_injective_map
    {S B ι : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [T2Space S]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B] [T2Space B] [NormalSpace B]
    {F : Filter ι} (e : S → B) (he : Continuous e) (hinj : Function.Injective e)
    (μs : ι → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (htight : IsTightMeasureSet (insert (μ : Measure S)
      (Set.range (fun i => (μs i : Measure S)))))
    (hmap : Tendsto (fun i => (μs i).map he.measurable.aemeasurable) F
      (𝓝 (μ.map he.measurable.aemeasurable))) : Tendsto μs F (𝓝 μ) := by
  classical
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / (8 * (‖f‖ + 1))
  have hη : 0 < η := div_pos hε (by positivity)
  obtain ⟨K, hK, htail⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
      (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  have hreal (ν : ProbabilityMeasure S)
      (hν : (ν : Measure S) ∈ insert (μ : Measure S)
        (Set.range (fun i => (μs i : Measure S)))) :
      (ν : Measure S).real Kᶜ ≤ η := by
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top (htail _ hν)).trans_eq
      (ENNReal.toReal_ofReal hη.le)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let eK : K → B := fun x => e x
  have heK : IsClosedEmbedding eK :=
    (he.comp continuous_subtype_val).isClosedEmbedding
      (fun x y hxy => Subtype.ext (hinj hxy))
  let fK : K →ᵇ ℝ := f.domRestrict K
  obtain ⟨g, hgnorm, hgeq⟩ :=
    fK.exists_extension_norm_eq_of_isClosedEmbedding heK
  have hgnormle : ‖g‖ ≤ ‖f‖ := by
    rw [hgnorm]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
    intro x
    exact f.norm_coe_le_norm x
  let G : S →ᵇ ℝ := g.compContinuous ⟨e, he⟩
  have hGnorm : ‖G‖ ≤ ‖f‖ := (BoundedContinuousFunction.norm_compContinuous_le _ _).trans hgnormle
  have heq : EqOn f G K := by
    intro x hx
    exact (congrFun hgeq (⟨x, hx⟩ : K)).symm
  have hsmall : (2 * ‖f‖) * η < ε / 4 := by
    have hden : (8 : ℝ) * (‖f‖ + 1) ≠ 0 := ne_of_gt (by positivity)
    have hηeq : η * (8 * (‖f‖ + 1)) = ε := div_mul_cancel₀ ε hden
    nlinarith [norm_nonneg f]
  have herr (ν : ProbabilityMeasure S)
      (hν : (ν : Measure S) ∈ insert (μ : Measure S)
        (Set.range (fun i => (μs i : Measure S)))) :
      |(∫ x, f x ∂(ν : Measure S)) - (∫ x, G x ∂(ν : Measure S))| < ε / 4 := by
    calc
      _ ≤ (‖f‖ + ‖G‖) * (ν : Measure S).real Kᶜ :=
        integral_boundedContinuous_eqOn_error_le ν f G hK.measurableSet heq
      _ ≤ (2 * ‖f‖) * η := by
        apply mul_le_mul
        · linarith
        · exact hreal ν hν
        · exact measureReal_nonneg
        · positivity
      _ < ε / 4 := hsmall
  have hGlim : Tendsto (fun i => ∫ x, G x ∂(μs i : Measure S)) F
      (𝓝 (∫ x, G x ∂(μ : Measure S))) := by
    have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmap g
    have heqmap (ν : ProbabilityMeasure S) :
        (∫ x, g x ∂(ν.map he.measurable.aemeasurable : Measure B)) =
          ∫ x, G x ∂(ν : Measure S) :=
      integral_probabilityMeasure_map ν he.measurable g
    rw [heqmap μ] at h
    exact h.congr' (Eventually.of_forall fun i => heqmap (μs i))
  filter_upwards [Metric.tendsto_nhds.mp hGlim (ε / 4) (by positivity)] with i hi
  rw [Real.dist_eq] at hi ⊢
  have ha := herr (μs i) (Set.mem_insert_of_mem _ ⟨i, rfl⟩)
  have hb := herr μ (Set.mem_insert _ _)
  have ht1 := abs_sub_le (∫ x, f x ∂(μs i : Measure S))
    (∫ x, G x ∂(μs i : Measure S)) (∫ x, f x ∂(μ : Measure S))
  have ht2 := abs_sub_le (∫ x, G x ∂(μs i : Measure S))
    (∫ x, G x ∂(μ : Measure S)) (∫ x, f x ∂(μ : Measure S))
  rw [abs_sub_comm (∫ x, G x ∂(μ : Measure S)) (∫ x, f x ∂(μ : Measure S))] at ht2
  linarith

end FixedCouplingPoisson
