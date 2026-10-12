import FixedCouplingPoisson.ProductCocycle

/-!
# Deterministic-time restart for the actual iid projective process

The past-state/future joint law is derived from the
already proved independent coordinate sigma algebras. The actual process
composition uses the actual shifted potential sequence.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory ProbabilityTheory Matrix Filter

theorem iidMeasure_past_state_future_map {S : Type*} [MeasurableSpace S]
    (law : PotentialLaw) (n : ℕ) {X : PotentialSpace → S}
    (hX : @Measurable PotentialSpace S (pastMeasurableSpace n) inferInstance X) :
    (iidMeasure law).map (fun ω => (X ω, potentialShift n ω)) =
      ((iidMeasure law).map X).prod (iidMeasure law) := by
  have hXm : Measurable X := hX.mono (pastMeasurableSpace_le n) le_rfl
  have hi : IndepFun X (potentialShift n) (iidMeasure law) := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right
      (indep_of_indep_of_le_left (iidMeasure_past_future_independent law n) hX.comap_le)
      (measurable_potentialShift_future n).comap_le
  rw [hi.map_prod_eq_prod_map_map hXm.aemeasurable
    (measurable_potentialShift n).aemeasurable, iidMeasure_shift_map]

theorem iidMeasure_integral_past_state_future {S : Type*} [MeasurableSpace S]
    (law : PotentialLaw) (n : ℕ) {X : PotentialSpace → S}
    (hX : @Measurable PotentialSpace S (pastMeasurableSpace n) inferInstance X)
    {f : S × PotentialSpace → ℝ} (hfm : Measurable f)
    (hf : Integrable f (((iidMeasure law).map X).prod (iidMeasure law))) :
    (∫ ω, f (X ω, potentialShift n ω) ∂iidMeasure law) =
      ∫ x, (∫ ξ, f (x, ξ) ∂iidMeasure law) ∂(iidMeasure law).map X := by
  have hXm : Measurable X := hX.mono (pastMeasurableSpace_le n) le_rfl
  calc
    (∫ ω, f (X ω, potentialShift n ω) ∂iidMeasure law) =
        ∫ z, f z ∂(iidMeasure law).map (fun ω => (X ω, potentialShift n ω)) :=
      (integral_map (hXm.prodMk (measurable_potentialShift n)).aemeasurable
        hfm.aestronglyMeasurable).symm
    _ = ∫ z, f z ∂(((iidMeasure law).map X).prod (iidMeasure law)) := by
      rw [iidMeasure_past_state_future_map law n hX]
    _ = _ := integral_prod f hf

theorem projectiveProcess_add (E : ℝ) (p : ProjectivePoint)
    (n m : ℕ) (ω : PotentialSpace) :
    projectiveProcess E p (n + m) ω =
      projectiveProcess E (projectiveProcess E p n ω) m (potentialShift n ω) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_succ, projectiveProcess_succ, ih, projectiveProcess_succ]
    rfl

theorem measurable_projectiveProcess_joint (E : ℝ) (n : ℕ) :
    Measurable (fun z : ProjectivePoint × PotentialSpace => projectiveProcess E z.1 n z.2) := by
  induction n with
  | zero => exact measurable_fst
  | succ n ih =>
    have hm := (measurable_forwardStep E).comp
      (((measurable_site n).comp measurable_snd).prodMk ih)
    have hfun : (fun z : ProjectivePoint × PotentialSpace =>
        projectiveProcess E z.1 (n + 1) z.2) =
        forwardStep E ∘ (fun z => (z.2 n, projectiveProcess E z.1 n z.2)) := by
      funext z
      rfl
    rw [hfun]
    exact hm

end FixedCouplingPoisson.Furstenberg
