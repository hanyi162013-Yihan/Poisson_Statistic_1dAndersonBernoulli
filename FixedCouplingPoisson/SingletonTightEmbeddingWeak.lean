import FixedCouplingPoisson.TightEmbeddingWeak
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Separation.CompletelyRegular

/-! Weak convergence reflects through an embedding when the target law alone is tight. -/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Filter Set Topology
open scoped Topology BoundedContinuousFunction ENNReal

private theorem integral_error_le_weight
    {S : Type*} [MeasurableSpace S] [TopologicalSpace S] [BorelSpace S]
    (P : ProbabilityMeasure S) (f g q : S →ᵇ ℝ) (δ C : ℝ)
    (h : ∀ x, |f x - g x| ≤ δ + C * (1 - q x)) :
    |(∫ x, f x ∂(P : Measure S)) - (∫ x, g x ∂(P : Measure S))| ≤
      δ + C * (1 - ∫ x, q x ∂(P : Measure S)) := by
  have hfi := f.integrable (P : Measure S)
  have hgi := g.integrable (P : Measure S)
  have hqi := q.integrable (P : Measure S)
  rw [← integral_sub hfi hgi]
  calc
    _ ≤ ∫ x, |f x - g x| ∂(P : Measure S) := abs_integral_le_integral_abs
    _ ≤ ∫ x, δ + C * (1 - q x) ∂(P : Measure S) :=
      integral_mono_ae (hfi.sub hgi).abs
        ((integrable_const δ).add (((integrable_const 1).sub hqi).const_mul C))
        (ae_of_all _ h)
    _ = _ := by
      have hsub : (∫ x, 1 - q x ∂(P : Measure S)) =
          1 - ∫ x, q x ∂(P : Measure S) := by
        calc
          _ = (∫ _ : S, (1 : ℝ) ∂(P : Measure S)) -
              ∫ x, q x ∂(P : Measure S) := integral_sub (integrable_const 1) hqi
          _ = _ := by simp
      calc
        _ = (∫ _ : S, δ ∂(P : Measure S)) +
            ∫ x, C * (1 - q x) ∂(P : Measure S) :=
          integral_add (integrable_const δ) (((integrable_const 1).sub hqi).const_mul C)
        _ = _ := by rw [integral_const_mul, hsub]; simp

/-- Compact Hausdorff ambient version: no tightness assumption is imposed on the source family. -/
theorem probabilityMeasure_tendsto_of_target_tight_of_isEmbedding_compact
    {S B ι : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [T2Space S]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B] [T2Space B] [CompactSpace B]
    {F : Filter ι} (e : S → B) (he : IsEmbedding e)
    (μs : ι → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (htight : IsTightMeasureSet {(μ : Measure S)})
    (hmap : Tendsto (fun i => (μs i).map he.continuous.measurable.aemeasurable) F
      (𝓝 (μ.map he.continuous.measurable.aemeasurable))) : Tendsto μs F (𝓝 μ) := by
  classical
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / (32 * (‖f‖ + 1))
  let δ : ℝ := ε / 8
  have hη : 0 < η := div_pos hε (by positivity)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, hK, htail⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
      (ENNReal.ofReal η) (ENNReal.ofReal_pos.mpr hη)
  have hreal : (μ : Measure S).real Kᶜ ≤ η :=
    (ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (htail _ (Set.mem_singleton _))).trans_eq (ENNReal.toReal_ofReal hη.le)
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let eK : K → B := fun x => e x
  have heK : IsClosedEmbedding eK :=
    (he.continuous.comp continuous_subtype_val).isClosedEmbedding
      (fun x y hxy => Subtype.ext (he.injective hxy))
  obtain ⟨g, hgnorm, hgeq⟩ :=
    (f.domRestrict K).exists_extension_norm_eq_of_isClosedEmbedding heK
  have hgnormle : ‖g‖ ≤ ‖f‖ := by
    rw [hgnorm]
    exact (BoundedContinuousFunction.norm_le (norm_nonneg f)).mpr
      (fun x => f.norm_coe_le_norm x)
  let G : S →ᵇ ℝ := g.compContinuous ⟨e, he.continuous⟩
  have hGnorm : ‖G‖ ≤ ‖f‖ :=
    (BoundedContinuousFunction.norm_compContinuous_le _ _).trans hgnormle
  have heq : EqOn f G K := by
    intro x hx
    exact (congrFun hgeq (⟨x, hx⟩ : K)).symm
  let U : Set S := {x | |f x - G x| < δ}
  have hU : IsOpen U := isOpen_lt (f.continuous.sub G.continuous).abs continuous_const
  have hKU : K ⊆ U := by intro x hx; simp [U, heq hx, hδ]
  obtain ⟨V, hV, hpre⟩ := he.isInducing.isOpen_iff.mp hU
  have heKV : e '' K ⊆ V := by
    rintro _ ⟨x, hx, rfl⟩
    change x ∈ e ⁻¹' V
    rw [hpre]
    exact hKU hx
  obtain ⟨q₀, hqK, hqzero, _, hqbounds⟩ :=
    exists_continuous_one_zero_of_isCompact (hK.image he.continuous) hV.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr heKV)
  let q : B →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact q₀
  let Q : S →ᵇ ℝ := q.compContinuous ⟨e, he.continuous⟩
  have hQbounds (x : S) : Q x ∈ Icc (0 : ℝ) 1 := hqbounds (e x)
  have hQK : EqOn Q 1 K := by intro x hx; exact hqK ⟨x, hx, rfl⟩
  have hpoint (x : S) : |f x - G x| ≤ δ + (2 * ‖f‖) * (1 - Q x) := by
    by_cases hx : x ∈ U
    · exact (le_of_lt hx).trans (le_add_of_nonneg_right
        (mul_nonneg (by positivity) (sub_nonneg.mpr (hQbounds x).2)))
    · have heV : e x ∉ V := by
        intro hex
        apply hx
        rw [← hpre]
        exact hex
      have hQzero : Q x = 0 := hqzero heV
      rw [hQzero, sub_zero, mul_one]
      have hbound : |f x - G x| ≤ 2 * ‖f‖ := by
        have hf := f.norm_coe_le_norm x
        have hg := G.norm_coe_le_norm x
        rw [Real.norm_eq_abs] at hf hg
        calc
          _ ≤ |f x| + |G x| := abs_sub _ _
          _ ≤ 2 * ‖f‖ := by linarith
      linarith
  have htarget : 1 - ∫ x, Q x ∂(μ : Measure S) ≤ η := by
    have hmono : (∫ x, 1 - Q x ∂(μ : Measure S)) ≤
        ∫ x, Kᶜ.indicator (fun _ => (1 : ℝ)) x ∂(μ : Measure S) := by
      apply integral_mono_ae ((integrable_const 1).sub (Q.integrable _))
        ((integrable_const 1).indicator hK.measurableSet.compl)
      filter_upwards with x
      by_cases hx : x ∈ K
      · simp [hx, hQK hx]
      · simp only [mem_compl_iff, hx, not_false_eq_true, indicator_of_mem]
        change 1 - Q x ≤ 1
        exact sub_le_self 1 (hQbounds x).1
    rw [integral_sub (integrable_const 1) (Q.integrable _)] at hmono
    simp only [integral_const, probReal_univ, one_smul, integral_indicator_const _ hK.measurableSet.compl,
      smul_eq_mul, mul_one] at hmono
    exact hmono.trans hreal
  have hlim (b : B →ᵇ ℝ) : Tendsto
      (fun i => ∫ x, b (e x) ∂(μs i : Measure S)) F
      (𝓝 (∫ x, b (e x) ∂(μ : Measure S))) := by
    have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmap b
    rw [integral_probabilityMeasure_map μ he.continuous.measurable b] at h
    exact h.congr' (Eventually.of_forall fun i =>
      integral_probabilityMeasure_map (μs i) he.continuous.measurable b)
  have hGlim : Tendsto (fun i => ∫ x, G x ∂(μs i : Measure S)) F
      (𝓝 (∫ x, G x ∂(μ : Measure S))) := hlim g
  have hQlim : Tendsto (fun i => ∫ x, Q x ∂(μs i : Measure S)) F
      (𝓝 (∫ x, Q x ∂(μ : Measure S))) := hlim q
  have hsmall : δ + (2 * ‖f‖) * (2 * η) < ε / 4 := by
    have hden : (32 : ℝ) * (‖f‖ + 1) ≠ 0 := ne_of_gt (by positivity)
    have hηeq : η * (32 * (‖f‖ + 1)) = ε := div_mul_cancel₀ ε hden
    dsimp [δ]
    nlinarith only [hηeq, hη, norm_nonneg f]
  have herr (ν : ProbabilityMeasure S)
      (hν : 1 - ∫ x, Q x ∂(ν : Measure S) ≤ 2 * η) :
      |(∫ x, f x ∂(ν : Measure S)) - (∫ x, G x ∂(ν : Measure S))| < ε / 4 := by
    calc
      _ ≤ δ + (2 * ‖f‖) * (1 - ∫ x, Q x ∂(ν : Measure S)) :=
        integral_error_le_weight ν f G Q δ (2 * ‖f‖) hpoint
      _ ≤ δ + (2 * ‖f‖) * (2 * η) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hν (by positivity))
      _ < ε / 4 := hsmall
  filter_upwards [Metric.tendsto_nhds.mp hGlim (ε / 4) (by positivity),
      Metric.tendsto_nhds.mp hQlim η hη] with i hi hqi
  rw [Real.dist_eq] at hi hqi ⊢
  have hν : 1 - ∫ x, Q x ∂(μs i : Measure S) ≤ 2 * η := by
    have := (abs_lt.mp hqi).1
    linarith
  have ha := herr (μs i) hν
  have hb := herr μ (htarget.trans (by linarith))
  have ht1 := abs_sub_le (∫ x, f x ∂(μs i : Measure S))
    (∫ x, G x ∂(μs i : Measure S)) (∫ x, f x ∂(μ : Measure S))
  have ht2 := abs_sub_le (∫ x, G x ∂(μs i : Measure S))
    (∫ x, G x ∂(μ : Measure S)) (∫ x, f x ∂(μ : Measure S))
  rw [abs_sub_comm (∫ x, G x ∂(μ : Measure S)) (∫ x, f x ∂(μ : Measure S))] at ht2
  linarith

/-- A topological embedding into any Tychonoff space reflects weak convergence
at every tight target probability measure, with no common source tightness premise. -/
theorem probabilityMeasure_tendsto_of_target_tight_of_isEmbedding
    {S B ι : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [T2Space S]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B] [T35Space B]
    {F : Filter ι} (e : S → B) (he : IsEmbedding e)
    (μs : ι → ProbabilityMeasure S) (μ : ProbabilityMeasure S)
    (htight : IsTightMeasureSet {(μ : Measure S)})
    (hmap : Tendsto (fun i => (μs i).map he.continuous.measurable.aemeasurable) F
      (𝓝 (μ.map he.continuous.measurable.aemeasurable))) : Tendsto μs F (𝓝 μ) := by
  letI : MeasurableSpace (StoneCech B) := borel (StoneCech B)
  letI : BorelSpace (StoneCech B) := ⟨rfl⟩
  let k : B → StoneCech B := stoneCechUnit
  have hk : IsEmbedding k := isEmbedding_stoneCechUnit
  have hke : IsEmbedding (k ∘ e) := hk.comp he
  apply probabilityMeasure_tendsto_of_target_tight_of_isEmbedding_compact
    (k ∘ e) hke μs μ htight
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro g
  let gB : B →ᵇ ℝ := g.compContinuous ⟨k, hk.continuous⟩
  have h := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hmap gB
  have heq (ν : ProbabilityMeasure S) :
      (∫ x, g x ∂(ν.map hke.continuous.measurable.aemeasurable : Measure (StoneCech B))) =
        ∫ x, gB x ∂(ν.map he.continuous.measurable.aemeasurable : Measure B) := by
    rw [integral_probabilityMeasure_map ν hke.continuous.measurable g,
      integral_probabilityMeasure_map ν he.continuous.measurable gB]
    rfl
  rw [← heq μ] at h
  exact h.congr' (Eventually.of_forall fun i => (heq (μs i)).symm)

end FixedCouplingPoisson
