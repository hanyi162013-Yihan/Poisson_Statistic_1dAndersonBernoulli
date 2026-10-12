import FixedCouplingPoisson.EnergyCesaro
import FixedCouplingPoisson.BlockContraction

/-!
# One common contraction block on a compact energy set

A compact energy set supplies one common finite block,
positive log-mean lower bound, bounded-log constant, negative moment scale,
and contraction factor. All uniformity is derived from the actual bounded
iid model and the preceding compactness arguments. The external input only
contains the pointwise qualitative stationary probabilities and positive
stationary log means. The final result concerns same-energy pairs; a
two-energy perturbation estimate and stopping occupation are separate steps.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Matrix Filter

theorem ae_uniform_product_log_bound_on_compact (law : PotentialLaw)
    (K : Set ℝ) (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ ω ∂iidMeasure law, ∀ E ∈ K, ∀ p : ProjectivePoint,
      |projectiveLogGrowth (transferProduct E ω n) p| ≤ C := by
  obtain ⟨B, hB⟩ := hK.bddAbove_image continuous_abs.continuousOn
  let A : ℝ := max B 0
  have hA : 0 ≤ A := le_max_right _ _
  have hEA : ∀ E ∈ K, |E| ≤ A := fun E hE =>
    (hB ⟨E, hE, rfl⟩).trans (le_max_left _ _)
  obtain ⟨M, hM, hb⟩ := iidMeasure_bounded_all_sites law
  have hC : 0 ≤ Real.log (A + M + 2) := Real.log_nonneg (by linarith)
  refine ⟨(n : ℝ) * Real.log (A + M + 2), mul_nonneg (Nat.cast_nonneg _) hC, ?_⟩
  filter_upwards [hb] with ω hω E hE p
  rw [projectiveLogGrowth_product_sum]
  calc
    _ ≤ ∑ k ∈ Finset.range n,
        |transferLogCocycle E (ω k) (projectiveProcess E p k ω)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, Real.log (A + M + 2) := by
      apply Finset.sum_le_sum
      intro k _
      exact (abs_transferLogCocycle_le E (ω k) M hM (hω k) _).trans
        (Real.log_le_log (by positivity) (by linarith [hEA E hE]))
    _ = _ := by simp

theorem exists_uniform_product_negative_log_moment_on_compact (law : PotentialLaw)
    (input : Input law) (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ N : ℕ, 0 < N ∧ ∃ s q : ℝ, 0 < s ∧ s ≤ 1 ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ E ∈ K, ∀ p r : ProjectivePoint,
        (∫ ω, Real.exp (-s *
          (projectiveLogGrowth (transferProduct E ω N) p +
            projectiveLogGrowth (transferProduct E ω N) r)) ∂iidMeasure law) ≤ q := by
  obtain ⟨m, hm, N, hN, hmean⟩ :=
    exists_uniform_positive_product_log_mean_on_compact law input K hK hne
  obtain ⟨C, hC, hb⟩ := ae_uniform_product_log_bound_on_compact law K hK N
  let X : (K × (ProjectivePoint × ProjectivePoint)) → PotentialSpace → ℝ := fun z ω =>
    projectiveLogGrowth (transferProduct z.1 ω N) z.2.1 +
      projectiveLogGrowth (transferProduct z.1 ω N) z.2.2
  have hXm : ∀ z, Measurable (X z) := fun z =>
    (measurable_projectiveLogGrowth_product z.1 z.2.1 N).add
      (measurable_projectiveLogGrowth_product z.1 z.2.2 N)
  have hXb : ∀ z, ∀ᵐ ω ∂iidMeasure law, |X z ω| ≤ 2 * C := by
    intro z
    exact hb.mono fun ω hω => (abs_add_le _ _).trans (by
      linarith [hω z.1 z.1.2 z.2.1, hω z.1 z.1.2 z.2.2])
  have hNm : 0 < (N : ℝ) * m := mul_pos (by exact_mod_cast hN) hm
  have hXm' : ∀ z, (N : ℝ) * m ≤ ∫ ω, X z ω ∂iidMeasure law := by
    intro z
    rw [show X z = (fun ω => projectiveLogGrowth (transferProduct z.1 ω N) z.2.1 +
      projectiveLogGrowth (transferProduct z.1 ω N) z.2.2) from rfl,
      integral_add (integrable_projectiveLogGrowth_product law z.1 z.2.1 N)
        (integrable_projectiveLogGrowth_product law z.1 z.2.2 N)]
    linarith [hmean z.1 z.1.2 z.2.1, hmean z.1 z.1.2 z.2.2]
  obtain ⟨s, q, hs, hs1, hq0, hq1, hq⟩ := exists_uniform_negative_moment
    (iidMeasure law) X hXm (2 * C) ((N : ℝ) * m)
    (mul_nonneg (by norm_num) hC) hNm hXb hXm'
  exact ⟨N, hN, s, q, hs, hs1, hq0, hq1, fun E hE p r => hq (⟨E, hE⟩, (p, r))⟩

/-- One common block length, exponent and contraction factor work for all
energies in the compact set and all two starting lines. The two evolving
directions share the same actual iid potential sequence. -/
theorem exists_uniform_projective_block_contraction_on_compact (law : PotentialLaw)
    (input : Input law) (K : Set ℝ) (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ N : ℕ, 0 < N ∧ ∃ s q : ℝ, 0 < s ∧ s ≤ 1 ∧ 0 ≤ q ∧ q < 1 ∧
      ∀ E ∈ K, ∀ p r : ProjectivePoint,
        (∫ ω, (projectiveDistance (projectiveProcess E p N ω)
          (projectiveProcess E r N ω)) ^ s ∂iidMeasure law) ≤
            q * (projectiveDistance p r) ^ s := by
  obtain ⟨N, hN, s, q, hs, hs1, hq0, hq1, hq⟩ :=
    exists_uniform_product_negative_log_moment_on_compact law input K hK hne
  refine ⟨N, hN, s, q, hs, hs1, hq0, hq1, fun E hE p r => ?_⟩
  have heq : (fun ω => (projectiveDistance (projectiveProcess E p N ω)
      (projectiveProcess E r N ω)) ^ s) =
      (fun ω => (projectiveDistance p r) ^ s * Real.exp (-s *
        (projectiveLogGrowth (transferProduct E ω N) p +
          projectiveLogGrowth (transferProduct E ω N) r))) :=
    funext fun ω => projectiveDistance_product_rpow_identity E ω N p r s
  rw [heq, integral_const_mul]
  calc
    _ ≤ (projectiveDistance p r) ^ s * q :=
      mul_le_mul_of_nonneg_left (hq E hE p r)
        (Real.rpow_nonneg (projectiveDistance_nonneg p r) s)
    _ = _ := mul_comm _ _

end FixedCouplingPoisson.Furstenberg
