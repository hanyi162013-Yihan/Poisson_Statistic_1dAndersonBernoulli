import FixedCouplingPoisson.Model
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Process.Stopping

/-!
The actual infinite iid sample space, deterministic future laws and discrete
stopped fresh-future laws. The past at time `n` contains precisely the sites
with indices less than `n`, as appropriate after `n` transfer steps.
-/
namespace FixedCouplingPoisson
open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal

abbrev PotentialSpace := ℕ → ℝ

noncomputable def iidMeasure (law : PotentialLaw) : Measure PotentialSpace :=
  Measure.infinitePi (fun _ : ℕ => law.measure)

instance (law : PotentialLaw) : IsProbabilityMeasure (iidMeasure law) := by
  unfold iidMeasure
  infer_instance

theorem measurable_site (j : ℕ) : Measurable (fun ω : PotentialSpace => ω j) :=
  measurable_pi_apply j

theorem iidMeasure_site_map (law : PotentialLaw) (j : ℕ) :
    (iidMeasure law).map (fun ω => ω j) = law.measure := by
  exact Measure.infinitePi_map_eval (fun _ : ℕ => law.measure) j

theorem iidMeasure_independent (law : PotentialLaw) :
    iIndepFun (fun j (ω : PotentialSpace) => ω j) (iidMeasure law) := by
  exact iIndepFun_infinitePi (X := fun _ (v : ℝ) => v) (fun _ => measurable_id)

noncomputable def canonicalIIDPotential (law : PotentialLaw) :
    IIDPotential (iidMeasure law) law where
  potential := fun j ω => ω j
  measurable := measurable_site
  independent := iidMeasure_independent law
  identical := iidMeasure_site_map law

def potentialShift (n : ℕ) (ω : PotentialSpace) : PotentialSpace :=
  fun j => ω (n + j)

theorem measurable_potentialShift (n : ℕ) : Measurable (potentialShift n) := by
  exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

@[simp] theorem potentialShift_zero (ω : PotentialSpace) : potentialShift 0 ω = ω := by
  ext j
  simp [potentialShift]

theorem potentialShift_add (n m : ℕ) (ω : PotentialSpace) :
    potentialShift m (potentialShift n ω) = potentialShift (n + m) ω := by
  ext j
  simp [potentialShift, Nat.add_assoc]

theorem iidMeasure_shift_map (law : PotentialLaw) (n : ℕ) :
    (iidMeasure law).map (potentialShift n) = iidMeasure law := by
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => law.measure)
    (f := fun j => n + j) (fun _ _ h => Nat.add_left_cancel h)

def potentialBlock (k n : ℕ) (ω : PotentialSpace) : Fin n → ℝ :=
  fun j => ω (k + j.val)

theorem measurable_potentialBlock (k n : ℕ) : Measurable (potentialBlock k n) := by
  exact measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

theorem iidMeasure_block_map (law : PotentialLaw) (k n : ℕ) :
    (iidMeasure law).map (potentialBlock k n) = finitePotentialMeasure law n := by
  change (Measure.infinitePi (fun _ : ℕ => law.measure)).map
    (fun ω (j : Fin n) => ω (k + j.val)) = Measure.pi (fun _ : Fin n => law.measure)
  simpa only [Measure.infinitePi_eq_pi] using
    Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => law.measure)
    (f := fun j : Fin n => k + j.val)
    (fun _ _ h => Fin.ext (Nat.add_left_cancel h))

@[instance_reducible]
def siteMeasurableSpace (j : ℕ) : MeasurableSpace PotentialSpace :=
  MeasurableSpace.comap (fun ω => ω j) inferInstance

@[instance_reducible]
def pastMeasurableSpace (n : ℕ) : MeasurableSpace PotentialSpace :=
  ⨆ j : ℕ, ⨆ (_ : j < n), siteMeasurableSpace j

@[instance_reducible]
def futureMeasurableSpace (n : ℕ) : MeasurableSpace PotentialSpace :=
  ⨆ j : ℕ, ⨆ (_ : n ≤ j), siteMeasurableSpace j

theorem siteMeasurableSpace_le (j : ℕ) :
    siteMeasurableSpace j ≤ (inferInstance : MeasurableSpace PotentialSpace) :=
  (measurable_site j).comap_le

theorem pastMeasurableSpace_le (n : ℕ) :
    pastMeasurableSpace n ≤ (inferInstance : MeasurableSpace PotentialSpace) :=
  iSup_le fun j => iSup_le fun _ => siteMeasurableSpace_le j

theorem futureMeasurableSpace_le (n : ℕ) :
    futureMeasurableSpace n ≤ (inferInstance : MeasurableSpace PotentialSpace) :=
  iSup_le fun j => iSup_le fun _ => siteMeasurableSpace_le j

theorem pastMeasurableSpace_mono : Monotone pastMeasurableSpace := by
  intro n m hnm
  exact iSup_le fun j => iSup_le fun hj =>
    le_iSup_of_le j (le_iSup_of_le (lt_of_lt_of_le hj hnm) le_rfl)

def potentialFiltration : Filtration ℕ (inferInstance : MeasurableSpace PotentialSpace) where
  seq := pastMeasurableSpace
  mono' := pastMeasurableSpace_mono
  le' := pastMeasurableSpace_le

theorem iidMeasure_past_future_independent (law : PotentialLaw) (n : ℕ) :
    Indep (pastMeasurableSpace n) (futureMeasurableSpace n) (iidMeasure law) := by
  have hd : Disjoint {j : ℕ | j < n} {j : ℕ | n ≤ j} :=
    Set.disjoint_left.2 fun _ hj hk => (Nat.not_lt_of_ge hk) hj
  exact indep_iSup_of_disjoint (m := siteMeasurableSpace) siteMeasurableSpace_le
    (iidMeasure_independent law).iIndep hd

theorem measurable_potentialShift_future (n : ℕ) :
    @Measurable PotentialSpace PotentialSpace (futureMeasurableSpace n) inferInstance
      (potentialShift n) := by
  refine (@measurable_pi_iff PotentialSpace ℕ (fun _ => ℝ)
    (futureMeasurableSpace n) (fun _ => inferInstance) (potentialShift n)).mpr fun j => ?_
  apply Measurable.of_comap_le
  change siteMeasurableSpace (n + j) ≤ futureMeasurableSpace n
  exact le_iSup_of_le (n + j) (le_iSup_of_le (Nat.le_add_right n j) le_rfl)

theorem iidMeasure_past_inter_shift (law : PotentialLaw) (n : ℕ)
    {s : Set PotentialSpace} (hs : MeasurableSet[pastMeasurableSpace n] s)
    {A : Set PotentialSpace} (hA : MeasurableSet A) :
    iidMeasure law (s ∩ potentialShift n ⁻¹' A) =
      iidMeasure law s * iidMeasure law A := by
  rw [(Indep_iff _ _ _).1 (iidMeasure_past_future_independent law n) _ _ hs
    ((measurable_potentialShift_future n) hA)]
  rw [← Measure.map_apply (measurable_potentialShift n) hA, iidMeasure_shift_map]

def stoppedPotentialShift (τ : PotentialSpace → ℕ) (ω : PotentialSpace) : PotentialSpace :=
  potentialShift (τ ω) ω

theorem stoppedPast_fiber_measurable {τ : PotentialSpace → ℕ}
    (hτ : IsStoppingTime potentialFiltration (fun ω => (τ ω : WithTop ℕ)))
    {s : Set PotentialSpace} (hs : MeasurableSet[hτ.measurableSpace] s) (n : ℕ) :
    MeasurableSet[pastMeasurableSpace n] (s ∩ {ω | τ ω = n}) := by
  have heq : MeasurableSet[hτ.measurableSpace] {ω | (τ ω : WithTop ℕ) = n} :=
    hτ.measurableSet_eq' n
  have hset : {ω | (τ ω : WithTop ℕ) = n} = {ω | τ ω = n} := by
    ext ω
    exact WithTop.coe_inj
  rw [← hset]
  exact (hτ.measurableSet_inter_eq_iff s n).1 (hs.inter heq)

theorem measurable_potentialStoppingTime {τ : PotentialSpace → ℕ}
    (hτ : IsStoppingTime potentialFiltration (fun ω => (τ ω : WithTop ℕ))) :
    Measurable τ := by
  apply measurable_to_countable'
  intro n
  have hset : {ω | (τ ω : WithTop ℕ) = n} = τ ⁻¹' {n} := by
    ext ω
    exact WithTop.coe_inj
  rw [← hset]
  exact pastMeasurableSpace_le n _ (hτ.measurableSet_eq n)

theorem measurable_stoppedPotentialShift {τ : PotentialSpace → ℕ}
    (hτ : IsStoppingTime potentialFiltration (fun ω => (τ ω : WithTop ℕ))) :
    Measurable (stoppedPotentialShift τ) := by
  exact (measurable_from_prod_countable_right
    (f := fun p : ℕ × PotentialSpace => potentialShift p.1 p.2)
    (fun n => measurable_potentialShift n)).comp
    ((measurable_potentialStoppingTime hτ).prodMk measurable_id)

/-- Freshness at a finite discrete stopping time, proved by its countable fibers. -/
theorem iidMeasure_stopped_inter_shift (law : PotentialLaw) {τ : PotentialSpace → ℕ}
    (hτ : IsStoppingTime potentialFiltration (fun ω => (τ ω : WithTop ℕ)))
    {s : Set PotentialSpace} (hs : MeasurableSet[hτ.measurableSpace] s)
    {A : Set PotentialSpace} (hA : MeasurableSet A) :
    iidMeasure law (s ∩ stoppedPotentialShift τ ⁻¹' A) =
      iidMeasure law s * iidMeasure law A := by
  let pieces : ℕ → Set PotentialSpace := fun n => s ∩ {ω | τ ω = n}
  have hp : ∀ n, MeasurableSet (pieces n) := fun n =>
    pastMeasurableSpace_le n _ (stoppedPast_fiber_measurable hτ hs n)
  have hd : Pairwise (Disjoint on pieces) := by
    intro i j hij
    apply Set.disjoint_left.2
    rintro ω ⟨_, hi⟩ ⟨_, hj⟩
    exact hij (hi.symm.trans hj)
  have hdu : Pairwise (Disjoint on fun n => pieces n ∩ potentialShift n ⁻¹' A) := by
    intro i j hij
    exact (hd hij).mono Set.inter_subset_left Set.inter_subset_left
  have hu : (⋃ n, pieces n) = s := by
    ext ω
    simp [pieces]
  have hsplit : s ∩ stoppedPotentialShift τ ⁻¹' A =
      ⋃ n, pieces n ∩ potentialShift n ⁻¹' A := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ⟨hωs, hωA⟩
      exact ⟨τ ω, ⟨hωs, rfl⟩, hωA⟩
    · rintro ⟨n, ⟨hωs, hn⟩, hωA⟩
      change τ ω = n at hn
      exact ⟨hωs, by simpa only [stoppedPotentialShift, hn] using hωA⟩
  rw [hsplit, measure_iUnion hdu
    (fun n => (hp n).inter ((measurable_potentialShift n) hA))]
  have hi (n : ℕ) : iidMeasure law (pieces n ∩ potentialShift n ⁻¹' A) =
      iidMeasure law (pieces n) * iidMeasure law A :=
    iidMeasure_past_inter_shift law n (stoppedPast_fiber_measurable hτ hs n) hA
  simp_rw [hi]
  rw [ENNReal.tsum_mul_right, ← measure_iUnion hd hp, hu]

theorem iidMeasure_stopped_shift_map (law : PotentialLaw) {τ : PotentialSpace → ℕ}
    (hτ : IsStoppingTime potentialFiltration (fun ω => (τ ω : WithTop ℕ))) :
    (iidMeasure law).map (stoppedPotentialShift τ) = iidMeasure law := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_stoppedPotentialShift hτ) hA]
  simpa using iidMeasure_stopped_inter_shift law hτ
    (s := Set.univ) MeasurableSet.univ hA

/-- The whole future, not merely one next coordinate, is independent of the stopped past. -/
theorem iidMeasure_stopped_future_independent (law : PotentialLaw) {τ : PotentialSpace → ℕ}
    (hτ : IsStoppingTime potentialFiltration (fun ω => (τ ω : WithTop ℕ))) :
    Indep hτ.measurableSpace
      (MeasurableSpace.comap (stoppedPotentialShift τ) inferInstance) (iidMeasure law) := by
  rw [Indep_iff]
  intro s t hs ht
  obtain ⟨A, hA, rfl⟩ := ht
  rw [iidMeasure_stopped_inter_shift law hτ hs hA]
  rw [← Measure.map_apply (measurable_stoppedPotentialShift hτ) hA,
    iidMeasure_stopped_shift_map law hτ]

theorem iidMeasure_bounded_all_sites (law : PotentialLaw) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ ω ∂iidMeasure law, ∀ j : ℕ, |ω j| ≤ M := by
  obtain ⟨M, hM, hb⟩ := law.bounded
  refine ⟨M, hM, ae_all_iff.mpr fun j => ?_⟩
  have hj : ∀ᵐ v ∂(iidMeasure law).map (fun ω => ω j), |v| ≤ M := by
    rw [iidMeasure_site_map]
    exact hb
  exact ae_of_ae_map (measurable_site j).aemeasurable hj

def stoppedPotentialFuture (τ : PotentialSpace → WithTop ℕ)
    (ω : PotentialSpace) : PotentialSpace := potentialShift ((τ ω).untopD 0) ω

theorem measurable_stoppedPotentialFuture {τ : PotentialSpace → WithTop ℕ}
    (hτ : IsStoppingTime potentialFiltration τ) :
    Measurable (stoppedPotentialFuture τ) := by
  have ht : Measurable (fun ω => (τ ω).untopD 0) :=
    (measurable_of_countable (fun t : WithTop ℕ => t.untopD 0)).comp hτ.measurable'
  exact (measurable_from_prod_countable_right
    (f := fun p : ℕ × PotentialSpace => potentialShift p.1 p.2)
    (fun n => measurable_potentialShift n)).comp (ht.prodMk measurable_id)

/-- Freshness on the finite part of an arbitrary discrete stopping time. -/
theorem iidMeasure_finite_stopped_inter_future (law : PotentialLaw)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    {s : Set PotentialSpace} (hs : MeasurableSet[hτ.measurableSpace] s)
    {A : Set PotentialSpace} (hA : MeasurableSet A) :
    iidMeasure law ((s ∩ {ω | τ ω ≠ ⊤}) ∩ stoppedPotentialFuture τ ⁻¹' A) =
      iidMeasure law (s ∩ {ω | τ ω ≠ ⊤}) * iidMeasure law A := by
  let pieces : ℕ → Set PotentialSpace := fun n => s ∩ {ω | τ ω = (n : WithTop ℕ)}
  have hpast : ∀ n, MeasurableSet[pastMeasurableSpace n] (pieces n) := by
    intro n
    exact (hτ.measurableSet_inter_eq_iff s n).1 (hs.inter (hτ.measurableSet_eq' n))
  have hp : ∀ n, MeasurableSet (pieces n) := fun n => pastMeasurableSpace_le n _ (hpast n)
  have hd : Pairwise (Disjoint on pieces) := by
    intro i j hij
    apply Set.disjoint_left.2
    rintro ω ⟨_, hi⟩ ⟨_, hj⟩
    exact hij (WithTop.coe_injective (hi.symm.trans hj))
  have hdu : Pairwise (Disjoint on fun n => pieces n ∩ potentialShift n ⁻¹' A) := by
    intro i j hij
    exact (hd hij).mono Set.inter_subset_left Set.inter_subset_left
  have hu : (⋃ n, pieces n) = s ∩ {ω | τ ω ≠ ⊤} := by
    ext ω
    cases h : τ ω with
    | top => simp [pieces, h]
    | coe n => simp [pieces, h]
  have hsplit : (s ∩ {ω | τ ω ≠ ⊤}) ∩ stoppedPotentialFuture τ ⁻¹' A =
      ⋃ n, pieces n ∩ potentialShift n ⁻¹' A := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion]
    constructor
    · rintro ⟨⟨hωs, hfinite⟩, hωA⟩
      cases h : τ ω with
      | top => exact False.elim (hfinite h)
      | coe n => exact ⟨n, ⟨hωs, h⟩,
          by simpa only [stoppedPotentialFuture, h, WithTop.untopD_coe] using hωA⟩
    · rintro ⟨n, ⟨hωs, hn⟩, hωA⟩
      change τ ω = (n : WithTop ℕ) at hn
      refine ⟨⟨hωs, by simp [hn]⟩, ?_⟩
      change potentialShift ((τ ω).untopD 0) ω ∈ A
      rw [hn]
      exact hωA
  rw [hsplit, measure_iUnion hdu
    (fun n => (hp n).inter ((measurable_potentialShift n) hA))]
  have hi (n : ℕ) : iidMeasure law (pieces n ∩ potentialShift n ⁻¹' A) =
      iidMeasure law (pieces n) * iidMeasure law A :=
    iidMeasure_past_inter_shift law n (hpast n) hA
  simp_rw [hi]
  rw [ENNReal.tsum_mul_right, ← measure_iUnion hd hp, hu]

theorem iidMeasure_ae_finite_stopped_inter_future (law : PotentialLaw)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤)
    {s : Set PotentialSpace} (hs : MeasurableSet[hτ.measurableSpace] s)
    {A : Set PotentialSpace} (hA : MeasurableSet A) :
    iidMeasure law (s ∩ stoppedPotentialFuture τ ⁻¹' A) =
      iidMeasure law s * iidMeasure law A := by
  have hleft : iidMeasure law (s ∩ stoppedPotentialFuture τ ⁻¹' A) =
      iidMeasure law ((s ∩ {ω | τ ω ≠ ⊤}) ∩ stoppedPotentialFuture τ ⁻¹' A) := by
    apply measure_congr
    filter_upwards [hfinite] with ω hω
    apply propext
    change (ω ∈ s ∧ stoppedPotentialFuture τ ω ∈ A) ↔
      ((ω ∈ s ∧ τ ω ≠ ⊤) ∧ stoppedPotentialFuture τ ω ∈ A)
    simp [hω]
  have hright : iidMeasure law (s ∩ {ω | τ ω ≠ ⊤}) = iidMeasure law s := by
    apply measure_congr
    filter_upwards [hfinite] with ω hω
    apply propext
    change (ω ∈ s ∧ τ ω ≠ ⊤) ↔ ω ∈ s
    simp [hω]
  rw [hleft, iidMeasure_finite_stopped_inter_future law hτ hs hA, hright]

theorem iidMeasure_ae_finite_stopped_future_map (law : PotentialLaw)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤) :
    (iidMeasure law).map (stoppedPotentialFuture τ) = iidMeasure law := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply (measurable_stoppedPotentialFuture hτ) hA]
  simpa using iidMeasure_ae_finite_stopped_inter_future law hτ hfinite
    (s := Set.univ) MeasurableSet.univ hA

theorem iidMeasure_ae_finite_stopped_future_independent (law : PotentialLaw)
    {τ : PotentialSpace → WithTop ℕ} (hτ : IsStoppingTime potentialFiltration τ)
    (hfinite : ∀ᵐ ω ∂iidMeasure law, τ ω ≠ ⊤) :
    Indep hτ.measurableSpace
      (MeasurableSpace.comap (stoppedPotentialFuture τ) inferInstance) (iidMeasure law) := by
  rw [Indep_iff]
  intro s t hs ht
  obtain ⟨A, hA, rfl⟩ := ht
  rw [iidMeasure_ae_finite_stopped_inter_future law hτ hfinite hs hA]
  rw [← Measure.map_apply (measurable_stoppedPotentialFuture hτ) hA,
    iidMeasure_ae_finite_stopped_future_map law hτ hfinite]

end FixedCouplingPoisson
