import FixedCouplingPoisson.IDS
import FixedCouplingPoisson.IIDModel
import Mathlib.Analysis.Subadditive
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.LiminfLimsup

/-!
# The actual iid Dirichlet IDS and finite-volume errors

Cutting the edge between adjacent chains changes the explicit matrix by rank
at most two. The actual iid block laws transfer this pointwise spectral bound
to mean counts. Fekete's lemma then proves existence of the canonical IDS at
every energy, with error at most `2/n`; strict counts have the same limit.

No spectral perturbation bound, count measurability, or IDS limit is assumed.
-/

namespace FixedCouplingPoisson
open Matrix Filter MeasureTheory Set
open scoped Topology

def blockDirichletMatrix (n m : ℕ) (v : Fin (n + m) → ℝ) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ :=
  Matrix.fromBlocks
    (dirichletMatrix n (fun i => v (Fin.castAdd m i))) 0 0
    (dirichletMatrix m (fun i => v (Fin.natAdd n i)))

def sumDirichletMatrix (n m : ℕ) (v : Fin (n + m) → ℝ) :
    Matrix (Fin n ⊕ Fin m) (Fin n ⊕ Fin m) ℝ :=
  Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (dirichletMatrix (n + m) v)

theorem blockDirichletMatrix_isHermitian (n m : ℕ) (v : Fin (n + m) → ℝ) :
    (blockDirichletMatrix n m v).IsHermitian :=
  (dirichletMatrix_isHermitian n _).fromBlocks (by simp) (dirichletMatrix_isHermitian m _)

theorem sumDirichletMatrix_isHermitian (n m : ℕ) (v : Fin (n + m) → ℝ) :
    (sumDirichletMatrix n m v).IsHermitian :=
  (dirichletMatrix_isHermitian (n + m) v).reindex finSumFinEquiv.symm

theorem dirichlet_cut_rank_succ (n m : ℕ) (v : Fin ((n + 1) + (m + 1)) → ℝ) :
    (sumDirichletMatrix (n + 1) (m + 1) v - blockDirichletMatrix (n + 1) (m + 1) v).rank ≤ 2 := by
  classical
  let s : Finset (Fin (n + 1) ⊕ Fin (m + 1)) := {Sum.inl (Fin.last n), Sum.inr 0}
  have hcard : s.card = 2 := by simp [s]
  apply (Matrix.rank_le_card_of_support_subset _ s ?_).trans (le_of_eq hcard)
  rw [Function.support_subset_iff']
  intro i hi
  ext j
  cases i with
  | inl i =>
      have hiLast : i ≠ Fin.last n := by simpa [s] using hi
      have hiLt : i.val < n := by
        have hiVal : i.val ≠ n := fun h => hiLast (Fin.ext h)
        omega
      cases j with
      | inl j =>
          simp [sumDirichletMatrix, blockDirichletMatrix, Matrix.reindex_apply,
            dirichletMatrix, Fin.ext_iff]
          exact sub_self _
      | inr j =>
          have hne : i.val ≠ n + 1 + j.val := by omega
          have hdist : ¬(i.val + 1 = n + 1 + j.val ∨ n + 1 + j.val + 1 = i.val) := by omega
          simp [sumDirichletMatrix, blockDirichletMatrix, Matrix.reindex_apply,
            dirichletMatrix, Fin.ext_iff, hne, hdist]
  | inr i =>
      have hiZero : i ≠ 0 := by simpa [s] using hi
      have hiPos : 0 < i.val := by
        have hiVal : i.val ≠ 0 := fun h => hiZero (Fin.ext h)
        omega
      cases j with
      | inl j =>
          have hne : n + 1 + i.val ≠ j.val := by omega
          have hdist : ¬(n + 1 + i.val + 1 = j.val ∨ j.val + 1 = n + 1 + i.val) := by omega
          simp [sumDirichletMatrix, blockDirichletMatrix, Matrix.reindex_apply,
            dirichletMatrix, Fin.ext_iff, hne, hdist]
      | inr j =>
          simp [sumDirichletMatrix, blockDirichletMatrix, Matrix.reindex_apply,
            dirichletMatrix, Fin.ext_iff, Nat.add_assoc]

theorem dirichlet_cut_rank (n m : ℕ) (v : Fin (n + m) → ℝ) :
    (sumDirichletMatrix n m v - blockDirichletMatrix n m v).rank ≤ 2 := by
  classical
  cases n with
  | zero =>
      have hz : sumDirichletMatrix 0 m v - blockDirichletMatrix 0 m v = 0 := by
        ext i j
        cases i with
        | inl i => exact Fin.elim0 i
        | inr i =>
            cases j with
            | inl j => exact Fin.elim0 j
            | inr j =>
                simp [sumDirichletMatrix, blockDirichletMatrix, Matrix.reindex_apply,
                  dirichletMatrix, Fin.ext_iff]
      rw [hz, Matrix.rank_zero]
      omega
  | succ n =>
      cases m with
      | zero =>
          have hz : sumDirichletMatrix (n + 1) 0 v - blockDirichletMatrix (n + 1) 0 v = 0 := by
            ext i j
            cases i with
            | inr i => exact Fin.elim0 i
            | inl i =>
                cases j with
                | inr j => exact Fin.elim0 j
                | inl j =>
                    simp [sumDirichletMatrix, blockDirichletMatrix, Matrix.reindex_apply,
                      dirichletMatrix, Fin.ext_iff]
                    exact sub_self _
          rw [hz, Matrix.rank_zero]
          omega
      | succ m => exact dirichlet_cut_rank_succ n m v

theorem sumDirichletMatrix_count (n m : ℕ) (v : Fin (n + m) → ℝ) (E : ℝ) :
    hermitianNonstrictCount (sumDirichletMatrix_isHermitian n m v) E =
      nonstrictSpectralCount (n + m) v E := by
  exact hermitianNonstrictCount_reindex (dirichletMatrix_isHermitian (n + m) v)
    finSumFinEquiv.symm E

theorem blockDirichletMatrix_count (n m : ℕ) (v : Fin (n + m) → ℝ) (E : ℝ) :
    hermitianNonstrictCount (blockDirichletMatrix_isHermitian n m v) E =
      nonstrictSpectralCount n (fun i => v (Fin.castAdd m i)) E +
      nonstrictSpectralCount m (fun i => v (Fin.natAdd n i)) E := by
  exact hermitianNonstrictCount_fromBlocks (dirichletMatrix_isHermitian n _)
    (dirichletMatrix_isHermitian m _) E

theorem nonstrictSpectralCount_concat_le (n m : ℕ) (v : Fin (n + m) → ℝ) (E : ℝ) :
    nonstrictSpectralCount (n + m) v E ≤
      nonstrictSpectralCount n (fun i => v (Fin.castAdd m i)) E +
      nonstrictSpectralCount m (fun i => v (Fin.natAdd n i)) E + 2 := by
  have h := hermitianNonstrictCount_le_add_rank
    (sumDirichletMatrix_isHermitian n m v) (blockDirichletMatrix_isHermitian n m v) E
  rw [sumDirichletMatrix_count, blockDirichletMatrix_count] at h
  exact h.trans (Nat.add_le_add_left (dirichlet_cut_rank n m v) _)

theorem nonstrictSpectralCount_concat_abs (n m : ℕ) (v : Fin (n + m) → ℝ) (E : ℝ) :
    |(nonstrictSpectralCount (n + m) v E : ℝ) -
      ((nonstrictSpectralCount n (fun i => v (Fin.castAdd m i)) E : ℝ) +
       (nonstrictSpectralCount m (fun i => v (Fin.natAdd n i)) E : ℝ))| ≤ 2 := by
  have h := hermitianNonstrictCount_rank_abs
    (sumDirichletMatrix_isHermitian n m v) (blockDirichletMatrix_isHermitian n m v) E
  rw [sumDirichletMatrix_count, blockDirichletMatrix_count, Nat.cast_add] at h
  exact h.trans (by exact_mod_cast dirichlet_cut_rank n m v)

theorem iidBlock_count_integrable (law : PotentialLaw) (k n : ℕ) (E : ℝ) :
    Integrable (fun ω => (nonstrictSpectralCount n (potentialBlock k n ω) E : ℝ))
      (iidMeasure law) := by
  have h := integrable_nonstrictSpectralCount n E (finitePotentialMeasure law n)
  rw [← iidMeasure_block_map law k n] at h
  exact h.comp_measurable (measurable_potentialBlock k n)

theorem iidBlock_count_integral (law : PotentialLaw) (k n : ℕ) (E : ℝ) :
    (∫ ω, (nonstrictSpectralCount n (potentialBlock k n ω) E : ℝ) ∂iidMeasure law) =
      meanSpectralCount law n E := by
  unfold meanSpectralCount
  rw [← iidMeasure_block_map law k n]
  exact (integral_map (measurable_potentialBlock k n).aemeasurable
    (measurable_nonstrictSpectralCount_real n E).aestronglyMeasurable).symm

theorem potentialBlock_concat_left (n m : ℕ) (ω : PotentialSpace) :
    (fun i => potentialBlock 0 (n + m) ω (Fin.castAdd m i)) = potentialBlock 0 n ω := rfl

theorem potentialBlock_concat_right (n m : ℕ) (ω : PotentialSpace) :
    (fun i => potentialBlock 0 (n + m) ω (Fin.natAdd n i)) = potentialBlock n m ω := by
  ext i
  simp only [potentialBlock, Fin.val_natAdd, zero_add]

theorem meanSpectralCount_almost_subadditive (law : PotentialLaw) (E : ℝ) (n m : ℕ) :
    meanSpectralCount law (n + m) E ≤
      meanSpectralCount law n E + meanSpectralCount law m E + 2 := by
  have hpoint : ∀ ω : PotentialSpace,
      (nonstrictSpectralCount (n + m) (potentialBlock 0 (n + m) ω) E : ℝ) ≤
        (nonstrictSpectralCount n (potentialBlock 0 n ω) E : ℝ) +
        (nonstrictSpectralCount m (potentialBlock n m ω) E : ℝ) + 2 := by
    intro ω
    have hnat := nonstrictSpectralCount_concat_le n m (potentialBlock 0 (n + m) ω) E
    rw [potentialBlock_concat_left, potentialBlock_concat_right] at hnat
    exact_mod_cast hnat
  have hn := iidBlock_count_integrable law 0 n E
  have hm := iidBlock_count_integrable law n m E
  have hsum : Integrable (fun ω : PotentialSpace =>
      (nonstrictSpectralCount n (potentialBlock 0 n ω) E : ℝ) +
      (nonstrictSpectralCount m (potentialBlock n m ω) E : ℝ)) (iidMeasure law) := hn.add hm
  have h := integral_mono (iidBlock_count_integrable law 0 (n + m) E)
    (hsum.add (integrable_const (2 : ℝ))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hsum (integrable_const (2 : ℝ)), integral_add hn hm] at h
  simpa only [iidBlock_count_integral, integral_const, probReal_univ,
    one_smul] using h

theorem meanSpectralCount_almost_superadditive (law : PotentialLaw) (E : ℝ) (n m : ℕ) :
    meanSpectralCount law n E + meanSpectralCount law m E ≤
      meanSpectralCount law (n + m) E + 2 := by
  have hpoint : ∀ ω : PotentialSpace,
      (nonstrictSpectralCount n (potentialBlock 0 n ω) E : ℝ) +
        (nonstrictSpectralCount m (potentialBlock n m ω) E : ℝ) ≤
      (nonstrictSpectralCount (n + m) (potentialBlock 0 (n + m) ω) E : ℝ) + 2 := by
    intro ω
    have h := nonstrictSpectralCount_concat_abs n m (potentialBlock 0 (n + m) ω) E
    rw [potentialBlock_concat_left, potentialBlock_concat_right] at h
    linarith [(abs_le.mp h).1]
  have hn := iidBlock_count_integrable law 0 n E
  have hm := iidBlock_count_integrable law n m E
  have hnm := iidBlock_count_integrable law 0 (n + m) E
  have h := integral_mono (hn.add hm) (hnm.add (integrable_const (2 : ℝ))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hn hm, integral_add hnm (integrable_const (2 : ℝ))] at h
  simpa only [iidBlock_count_integral, integral_const, probReal_univ, one_smul] using h

theorem almostSubadditive_tendsto_limsup (a : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, 0 ≤ a n) (hsub : ∀ n m, a (n + m) ≤ a n + a m + C) :
    Tendsto (fun n => a n / (n : ℝ)) atTop
      (nhds (limsup (fun n => a n / (n : ℝ)) atTop)) := by
  let u := fun n => a n + C
  have hu : Subadditive u := by
    intro n m
    dsimp [u]
    linarith [hsub n m]
  have hbdd : BddBelow (range (fun n => u n / (n : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact div_nonneg (add_nonneg (ha n) hC) (Nat.cast_nonneg _)
  have hlim := hu.tendsto_lim hbdd
  have hshift := hlim.sub (tendsto_const_div_atTop_nhds_zero_nat C)
  have hfinal : Tendsto (fun n => a n / (n : ℝ)) atTop (nhds hu.lim) := by
    simpa only [u, add_div, add_sub_cancel_right, sub_zero] using hshift
  simpa only [hfinal.limsup_eq] using hfinal

theorem hasIDS_idsCandidate (law : PotentialLaw) : HasIDS law (idsCandidate law) := by
  intro E
  exact almostSubadditive_tendsto_limsup (fun n => meanSpectralCount law n E) 2 (by norm_num)
    (fun n => (meanSpectralCount_bounds law n E).1)
    (meanSpectralCount_almost_subadditive law E)

theorem idsCandidate_bounds (law : PotentialLaw) (E : ℝ) :
    0 ≤ idsCandidate law E ∧ idsCandidate law E ≤ 1 := by
  have ht := hasIDS_idsCandidate law E
  exact ⟨ge_of_tendsto ht (Filter.Eventually.of_forall fun n =>
    (normalizedMeanCount_bounds law E n).1),
    le_of_tendsto ht (Filter.Eventually.of_forall fun n =>
    (normalizedMeanCount_bounds law E n).2)⟩

theorem monotone_idsCandidate (law : PotentialLaw) : Monotone (idsCandidate law) := by
  intro E F hEF
  exact le_of_tendsto_of_tendsto (hasIDS_idsCandidate law E) (hasIDS_idsCandidate law F)
    (Filter.Eventually.of_forall fun n => monotone_normalizedMeanCount law n hEF)

theorem almostAdditive_limit_error (a : ℕ → ℝ) (C N : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n, 0 ≤ a n ∧ a n ≤ n)
    (hsub : ∀ n m, a (n + m) ≤ a n + a m + C)
    (hsup : ∀ n m, a n + a m ≤ a (n + m) + C)
    (hN : Tendsto (fun n => a n / (n : ℝ)) atTop (nhds N)) (n : ℕ) (hn : n ≠ 0) :
    |a n / (n : ℝ) - N| ≤ C / (n : ℝ) := by
  let u := fun k => a k + C
  let v := fun k => C - a k
  have hu : Subadditive u := by
    intro k l
    dsimp [u]
    linarith [hsub k l]
  have hv : Subadditive v := by
    intro k l
    dsimp [v]
    linarith [hsup k l]
  have hbu : BddBelow (range (fun k => u k / (k : ℝ))) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact div_nonneg (add_nonneg (ha k).1 hC) (Nat.cast_nonneg _)
  have hbv : BddBelow (range (fun k => v k / (k : ℝ))) := by
    refine ⟨-1, ?_⟩
    rintro _ ⟨k, rfl⟩
    by_cases hk : k = 0
    · simp [hk]
    · have hp : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
      apply (le_div_iff₀ hp).mpr
      dsimp [v]
      linarith [(ha k).2]
  have hlu : hu.lim = N := by
    apply tendsto_nhds_unique (hu.tendsto_lim hbu)
    simpa only [u, add_div, add_zero] using
      hN.add (tendsto_const_div_atTop_nhds_zero_nat C)
  have hlv : hv.lim = -N := by
    apply tendsto_nhds_unique (hv.tendsto_lim hbv)
    simpa only [v, sub_div, zero_sub] using
      (tendsto_const_div_atTop_nhds_zero_nat C).sub hN
  have hou := hu.lim_le_div hbu hn
  have hov := hv.lim_le_div hbv hn
  rw [hlu] at hou
  rw [hlv] at hov
  dsimp [u, v] at hou hov
  rw [add_div] at hou
  rw [sub_div] at hov
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem normalizedMeanCount_error (law : PotentialLaw) (E : ℝ) (n : ℕ) (hn : n ≠ 0) :
    |normalizedMeanCount law E n - idsCandidate law E| ≤ 2 / (n : ℝ) := by
  exact almostAdditive_limit_error (fun k => meanSpectralCount law k E) 2 (idsCandidate law E)
    (by norm_num) (fun k => meanSpectralCount_bounds law k E)
    (meanSpectralCount_almost_subadditive law E)
    (meanSpectralCount_almost_superadditive law E) (hasIDS_idsCandidate law E) n hn

theorem measurable_idsCandidate (law : PotentialLaw) : Measurable (idsCandidate law) :=
  (monotone_idsCandidate law).measurable

theorem strictMeanCount_tendsto_idsCandidate (law : PotentialLaw) (E : ℝ) :
    Tendsto (fun n =>
      (∫ v, (strictSpectralCount n v E : ℝ) ∂finitePotentialMeasure law n) / (n : ℝ))
      atTop (nhds (idsCandidate law E)) := by
  let s := fun n => ∫ v, (strictSpectralCount n v E : ℝ) ∂finitePotentialMeasure law n
  have hb : ∀ n, 0 ≤ (meanSpectralCount law n E - s n) / (n : ℝ) ∧
      (meanSpectralCount law n E - s n) / (n : ℝ) ≤ 1 / (n : ℝ) := by
    intro n
    have h := integral_spectralCount_endpoint_bounds n E (finitePotentialMeasure law n)
    change s n ≤ meanSpectralCount law n E ∧ meanSpectralCount law n E ≤ s n + 1 at h
    exact ⟨div_nonneg (sub_nonneg.mpr h.1) (Nat.cast_nonneg _),
      div_le_div_of_nonneg_right (by linarith [h.2]) (Nat.cast_nonneg _)⟩
  have hd := squeeze_zero (fun n => (hb n).1) (fun n => (hb n).2)
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  have ht := (hasIDS_idsCandidate law E).sub hd
  simpa only [normalizedMeanCount, sub_div, sub_sub_cancel, sub_zero, s] using ht

theorem strictMeanCount_error (law : PotentialLaw) (E : ℝ) (n : ℕ) (hn : n ≠ 0) :
    |(∫ v, (strictSpectralCount n v E : ℝ) ∂finitePotentialMeasure law n) / (n : ℝ) -
      idsCandidate law E| ≤ 3 / (n : ℝ) := by
  have hb := integral_spectralCount_endpoint_bounds n E (finitePotentialMeasure law n)
  change (∫ v, (strictSpectralCount n v E : ℝ) ∂finitePotentialMeasure law n) ≤
    meanSpectralCount law n E ∧ meanSpectralCount law n E ≤
      (∫ v, (strictSpectralCount n v E : ℝ) ∂finitePotentialMeasure law n) + 1 at hb
  have hl := div_le_div_of_nonneg_right hb.1 (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
  have hr := div_le_div_of_nonneg_right hb.2 (Nat.cast_nonneg n : 0 ≤ (n : ℝ))
  rw [add_div] at hr
  have he := abs_le.mp (normalizedMeanCount_error law E n hn)
  change -(2 / (n : ℝ)) ≤ meanSpectralCount law n E / (n : ℝ) - idsCandidate law E ∧
    meanSpectralCount law n E / (n : ℝ) - idsCandidate law E ≤ 2 / (n : ℝ) at he
  have hpos : 0 ≤ 1 / (n : ℝ) := div_nonneg zero_le_one (Nat.cast_nonneg _)
  have hthree : (3 : ℝ) / (n : ℝ) = 2 / (n : ℝ) + 1 / (n : ℝ) := by ring
  rw [hthree, abs_le]
  constructor <;> linarith

end FixedCouplingPoisson
