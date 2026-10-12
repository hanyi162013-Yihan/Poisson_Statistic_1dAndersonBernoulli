import FixedCouplingPoisson.PhaseProcess
import FixedCouplingPoisson.Spectral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Order.Interval.Finset.Nat

/-!
# Finite Dirichlet Sturm counting from the actual canonical phase

The shooting phase starts at the actual Dirichlet vector `(1,0)`. Strict
energy order and the finite spectral theorem identify all its half-integer
levels, so no energy-asymptotic assumption is needed for the count formula.
-/
namespace FixedCouplingPoisson
open Real Set Matrix Finset

noncomputable def shootingPhase (E : ℝ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  orbit (canonicalPhaseLift E) v 0 n

theorem shootingPhase_eq_process (E : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    shootingPhase E v n = canonicalPhaseProcess E 0 n v := rfl

@[simp] theorem shootingPhase_zero (E : ℝ) (v : ℕ → ℝ) : shootingPhase E v 0 = 0 := rfl

@[simp] theorem shootingPhase_succ (E : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    shootingPhase E v (n + 1) = canonicalPhase E (v n) (shootingPhase E v n) := rfl

theorem canonicalPhase_zero_eq_chart (E v : ℝ) :
    canonicalPhase E v 0 = chartPhase E v 0 := by
  apply canonicalPhase_eq_chartPhase
  constructor <;> linarith [Real.pi_pos]

theorem canonicalPhase_zero_mem (E v : ℝ) : canonicalPhase E v 0 ∈ Set.Ioo 0 Real.pi := by
  rw [canonicalPhase_zero_eq_chart]
  exact chartPhase_mem E v 0

theorem canonicalPhase_zero_strictAnti (v : ℝ) : StrictAnti (fun E => canonicalPhase E v 0) := by
  intro E E' h
  change canonicalPhase E' v 0 < canonicalPhase E v 0
  rw [canonicalPhase_zero_eq_chart, canonicalPhase_zero_eq_chart]
  exact chartPhase_strictAnti_energy v 0 h

/-- Strict energy order for the actual Dirichlet shooting phase at every positive time. -/
theorem shootingPhase_strictAnti_energy (v : ℕ → ℝ) (n : ℕ) :
    StrictAnti (fun E => shootingPhase E v (n + 1)) := by
  induction n with
  | zero => exact canonicalPhase_zero_strictAnti (v 0)
  | succ n ih =>
    intro E E' h
    change canonicalPhase E' (v (n + 1)) (shootingPhase E' v (n + 1)) <
      canonicalPhase E (v (n + 1)) (shootingPhase E v (n + 1))
    exact lt_of_le_of_lt
      ((canonicalPhase_antitone_energy (v (n + 1)) (shootingPhase E' v (n + 1))) h.le)
      ((canonicalPhase_strictMono E (v (n + 1))) (ih h))

/-- All positive-time Dirichlet shooting phases lie between 0 and nπ. -/
theorem shootingPhase_mem (E : ℝ) (v : ℕ → ℝ) (n : ℕ) :
    shootingPhase E v (n + 1) ∈ Set.Ioo 0 ((n + 1 : ℕ) * Real.pi) := by
  induction n with
  | zero =>
    rw [shootingPhase_succ, shootingPhase_zero]
    simpa only [Nat.zero_add, Nat.cast_one, one_mul] using canonicalPhase_zero_mem E (v 0)
  | succ n ih =>
    have hzero := canonicalPhase_zero_mem E (v (n + 1))
    have hlower := (canonicalPhase_strictMono E (v (n + 1))) ih.1
    have hupper := (canonicalPhase_strictMono E (v (n + 1))) ih.2
    have hperiod : canonicalPhase E (v (n + 1)) ((n + 1 : ℕ) * Real.pi) =
        canonicalPhase E (v (n + 1)) 0 + (n + 1 : ℕ) * Real.pi := by
      simpa only [zero_add, Int.cast_natCast] using
        canonicalPhase_add_int E (v (n + 1)) 0 ((n + 1 : ℕ) : ℤ)
    rw [hperiod] at hupper
    constructor
    · exact lt_trans hzero.1 hlower
    · change canonicalPhase E (v (n + 1)) (shootingPhase E v (n + 1)) <
        (↑(n + 1 + 1) : ℝ) * Real.pi
      push_cast
      push_cast at hupper
      linarith [hzero.2]

/-- A finite vector extended by zero to the right. -/
def paddedFinite {n : ℕ} (x : Fin n → ℝ) (j : ℕ) : ℝ :=
  if h : j < n then x ⟨j, h⟩ else 0

@[simp] theorem paddedFinite_in {n : ℕ} (x : Fin n → ℝ) (j : ℕ) (hj : j < n) :
    paddedFinite x j = x ⟨j, hj⟩ := by simp [paddedFinite, hj]

@[simp] theorem paddedFinite_out {n : ℕ} (x : Fin n → ℝ) (j : ℕ) (hj : n ≤ j) :
    paddedFinite x j = 0 := by simp [paddedFinite, Nat.not_lt.mpr hj]

theorem dirichletMatrix_entry_three {n : ℕ} (v : Fin n → ℝ) (i j : Fin n) :
    dirichletMatrix n v i j =
      (if i = j then v i else 0) + (if j.val + 1 = i.val then 1 else 0) +
        (if i.val + 1 = j.val then 1 else 0) := by
  by_cases hij : i = j
  · subst j
    simp [dirichletMatrix]
  · by_cases hprev : j.val + 1 = i.val
    · have hnext : i.val + 1 ≠ j.val := by omega
      simp [dirichletMatrix, hij, hprev, hnext]
    · by_cases hnext : i.val + 1 = j.val
      · simp [dirichletMatrix, hij, hprev, hnext]
      · simp [dirichletMatrix, hij, hprev, hnext]

theorem dirichletMatrix_prev_sum {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (∑ j : Fin n, (if j.val + 1 = i.val then (1 : ℝ) else 0) * x j) =
      if i.val = 0 then 0 else paddedFinite x (i.val - 1) := by
  by_cases hi : i.val = 0
  · simp [hi]
  · let prev : Fin n := ⟨i.val - 1, by omega⟩
    have hiff : ∀ j : Fin n, j.val + 1 = i.val ↔ j = prev := by
      intro j
      constructor
      · intro hj
        apply Fin.ext
        dsimp [prev]
        omega
      · intro hj
        subst j
        dsimp [prev]
        omega
    simp_rw [hiff]
    simp [hi, paddedFinite, prev, show i.val - 1 < n by omega]

theorem dirichletMatrix_next_sum {n : ℕ} (x : Fin n → ℝ) (i : Fin n) :
    (∑ j : Fin n, (if i.val + 1 = j.val then (1 : ℝ) else 0) * x j) =
      paddedFinite x (i.val + 1) := by
  by_cases hi : i.val + 1 < n
  · let next : Fin n := ⟨i.val + 1, hi⟩
    have hiff : ∀ j : Fin n, i.val + 1 = j.val ↔ j = next := by
      intro j
      constructor
      · intro hj
        exact Fin.ext hj.symm
      · intro hj
        subst j
        rfl
    simp_rw [hiff]
    simp [paddedFinite, next, hi]
  · have hnone : ∀ j : Fin n, ¬ i.val + 1 = j.val := by intro j; omega
    simp [hnone, paddedFinite, hi]

/-- The actual Jacobi equation with its two padded boundary values. -/
theorem dirichletMatrix_mulVec_row {n : ℕ} (v x : Fin n → ℝ) (i : Fin n) :
    (dirichletMatrix n v *ᵥ x) i = v i * x i +
      (if i.val = 0 then 0 else paddedFinite x (i.val - 1)) +
      paddedFinite x (i.val + 1) := by
  change (∑ j : Fin n, dirichletMatrix n v i j * x j) = _
  simp_rw [dirichletMatrix_entry_three, add_mul]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    dirichletMatrix_prev_sum, dirichletMatrix_next_sum]
  simp only [ite_mul, zero_mul]
  simp

/-- A finite eigenvector, with both Dirichlet boundary values padded by zero. -/
def eigenvectorSequence {n : ℕ} (x : Fin n → ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => paddedFinite x j

@[simp] theorem eigenvectorSequence_zero {n : ℕ} (x : Fin n → ℝ) :
    eigenvectorSequence x 0 = 0 := rfl

@[simp] theorem eigenvectorSequence_succ {n : ℕ} (x : Fin n → ℝ) (j : ℕ) :
    eigenvectorSequence x (j + 1) = paddedFinite x j := rfl

theorem eigenvectorSequence_recurrence {n : ℕ} (w : ℕ → ℝ) (x : Fin n → ℝ) (E : ℝ)
    (heig : dirichletMatrix n (fun i => w i.val) *ᵥ x = E • x)
    (j : ℕ) (hj : j < n) :
    eigenvectorSequence x (j + 2) =
      (E - w j) * eigenvectorSequence x (j + 1) - eigenvectorSequence x j := by
  have hrow := congrFun heig (⟨j, hj⟩ : Fin n)
  rw [dirichletMatrix_mulVec_row] at hrow
  simp only [Pi.smul_apply, smul_eq_mul] at hrow
  have hp : (if j = 0 then 0 else paddedFinite x (j - 1)) = eigenvectorSequence x j := by
    cases j with
    | zero => simp
    | succ j => simp
  rw [hp] at hrow
  simp only [eigenvectorSequence_succ, paddedFinite_in x j hj]
  linarith

/-- Uniqueness of the finite part of the actual second-order Dirichlet recursion. -/
theorem finite_recurrence_scale (E : ℝ) (w u : ℕ → ℝ) (m : ℕ) (hu0 : u 0 = 0)
    (hrec : ∀ j < m, u (j + 2) = (E - w j) * u (j + 1) - u j) :
    ∀ j ≤ m, u (j + 1) = u 1 * dirichletSolution E w (j + 1) ∧
      u j = u 1 * dirichletSolution E w j := by
  intro j
  induction j with
  | zero => intro _; simp [hu0]
  | succ j ih =>
    intro hj
    have hp := ih (by omega)
    refine ⟨?_, hp.1⟩
    rw [hrec j (by omega), hp.1, hp.2, dirichletSolution_recurrence]
    ring

/-- Only the eigenvalue-to-shooting direction is needed for finite Sturm counting. -/
theorem dirichlet_eigenvector_shooting_zero {n : ℕ} (w : ℕ → ℝ)
    (x : Fin (n + 1) → ℝ) (E : ℝ)
    (heig : dirichletMatrix (n + 1) (fun i => w i.val) *ᵥ x = E • x) (hx : x ≠ 0) :
    dirichletSolution E w (n + 2) = 0 := by
  have hx0 : x 0 ≠ 0 := dirichlet_eigenvector_first_ne_zero _ x E heig hx
  have hscale := finite_recurrence_scale E w (eigenvectorSequence x) (n + 1) rfl
    (fun j hj => eigenvectorSequence_recurrence w x E heig j hj) (n + 1) le_rfl
  have hfirst : eigenvectorSequence x 1 = x 0 := by simp [paddedFinite]
  have hend : eigenvectorSequence x (n + 2) = 0 := by
    change paddedFinite x (n + 1) = 0
    exact paddedFinite_out x (n + 1) le_rfl
  rw [hfirst, hend] at hscale
  exact (mul_eq_zero.mp hscale.1.symm).resolve_left hx0

/-- A Dirichlet shooting zero gives an actual vertical transfer direction. -/
theorem canonicalPhaseProcess_cos_zero_of_dirichlet_zero (E : ℝ) (w : PotentialSpace)
    (n : ℕ) (hzero : dirichletSolution E w (n + 1) = 0) :
    cos (canonicalPhaseProcess E 0 n w) = 0 := by
  have hunit : angleVector 0 = (![1, 0] : Vector2) := by simp [angleVector]
  have hrep := canonicalPhaseProcess_actual_vector E 0 n w
  rw [hunit, transferProduct_dirichlet] at hrep
  have hcoord := congrFun hrep 0
  simp only [Matrix.cons_val_zero, Pi.smul_apply, smul_eq_mul, angleVector] at hcoord
  have hnorm : euclideanNorm
      (![dirichletSolution E w (n + 1), dirichletSolution E w n] : Vector2) ≠ 0 :=
    ne_of_gt (euclideanNorm_pos _ (dirichletSolution_pair_ne_zero E w n))
  have hmul : euclideanNorm
      (![dirichletSolution E w (n + 1), dirichletSolution E w n] : Vector2) *
        cos (canonicalPhaseProcess E 0 n w) = 0 := hcoord.symm.trans hzero
  exact (mul_eq_zero.mp hmul).resolve_left hnorm

/-- There are exactly n possible vertical levels inside the actual phase range. -/
theorem halfIntegerPhaseLevel_exists (n : ℕ) (θ : ℝ) (hcos : cos θ = 0)
    (hbound : θ ∈ Set.Ioo 0 ((n : ℝ) * Real.pi)) :
    ∃ k : Fin n, θ = Real.pi / 2 + (k.val : ℝ) * Real.pi := by
  obtain ⟨z, hz⟩ := Real.cos_eq_zero_iff.mp hcos
  have hform : θ = ((z : ℝ) + 1 / 2) * Real.pi := by rw [hz]; ring
  have hzlower : 0 < (z : ℝ) + 1 / 2 := by
    apply (mul_pos_iff_of_pos_right Real.pi_pos).mp
    simpa only [← hform] using hbound.1
  have hzupper : (z : ℝ) + 1 / 2 < (n : ℝ) := by
    apply (mul_lt_mul_iff_left₀ Real.pi_pos).mp
    simpa only [← hform] using hbound.2
  have hzlower' : (-1 : ℤ) < z := by
    have h : (-1 : ℝ) < (z : ℝ) := by linarith
    exact_mod_cast h
  have hz0 : 0 ≤ z := by omega
  have hzupper' : z < (n : ℤ) := by
    have h : (z : ℝ) < (n : ℝ) := by linarith
    exact_mod_cast h
  refine ⟨⟨z.toNat, by omega⟩, ?_⟩
  have hzcast : (z.toNat : ℝ) = (z : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hz0
  simp only [hzcast]
  rw [hform]
  ring

theorem fin_ge_card (n m : ℕ) :
    (univ.filter (fun k : Fin n => m ≤ k.val)).card = n - m := by
  classical
  let s := univ.filter (fun k : Fin n => m ≤ k.val)
  have himage : s.image Fin.val = Finset.Ico m n := by
    ext j
    simp only [s, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨hk, k.isLt⟩
    · rintro ⟨hmj, hjn⟩
      exact ⟨⟨j, hjn⟩, hmj, rfl⟩
  calc
    s.card = (s.image Fin.val).card := (card_image_of_injective s Fin.val_injective).symm
    _ = (Finset.Ico m n).card := congrArg Finset.card himage
    _ = n - m := Nat.card_Ico m n

noncomputable def halfIntegerPhaseLevel (k : ℕ) : ℝ := Real.pi / 2 + k * Real.pi

theorem phase_lt_halfIntegerLevel_iff_floor (θ : ℝ) (k : ℕ) :
    θ < halfIntegerPhaseLevel k ↔ Int.floor (θ / Real.pi + 1 / 2) ≤ (k : ℤ) := by
  have hfloor : Int.floor (θ / Real.pi + 1 / 2) ≤ (k : ℤ) ↔
      θ / Real.pi + 1 / 2 < (k : ℝ) + 1 := by
    simpa only [Int.cast_natCast] using
      (Int.floor_le_iff (a := θ / Real.pi + 1 / 2) (z := (k : ℤ)))
  rw [hfloor]
  have hlevel : halfIntegerPhaseLevel k = ((k : ℝ) + 1 / 2) * Real.pi := by
    unfold halfIntegerPhaseLevel
    ring
  rw [hlevel, ← div_lt_iff₀ Real.pi_pos]
  constructor <;> intro h <;> linarith


/-- Every actual finite-volume eigenvalue is a zero of the Dirichlet shooting solution. -/
theorem dirichletEigenvalue_shooting_zero (w : ℕ → ℝ) (n : ℕ) (i : Fin (n + 1)) :
    dirichletSolution (dirichletEigenvalues (n + 1) (fun j => w j.val) i) w (n + 2) = 0 := by
  let hA := dirichletMatrix_isHermitian (n + 1) (fun j => w j.val)
  let b := hA.eigenvectorBasis
  have hx : (⇑(b i) : Fin (n + 1) → ℝ) ≠ 0 := by
    intro h
    apply b.orthonormal.ne_zero i
    ext j
    exact congrFun h j
  exact dirichlet_eigenvector_shooting_zero w (⇑(b i)) _
    (hA.mulVec_eigenvectorBasis i) hx

/-- The actual n simple eigenvalues reach the n possible vertical phase levels. -/
theorem dirichletEigenvalue_phase_level (w : ℕ → ℝ) (n : ℕ) (i : Fin (n + 1)) :
    ∃ k : Fin (n + 1),
      shootingPhase (dirichletEigenvalues (n + 1) (fun j => w j.val) i) w (n + 1) =
        halfIntegerPhaseLevel k.val := by
  apply halfIntegerPhaseLevel_exists
  · exact canonicalPhaseProcess_cos_zero_of_dirichlet_zero _ w (n + 1)
      (dirichletEigenvalue_shooting_zero w n i)
  · exact shootingPhase_mem _ w n

/-- The vertical level belonging to an actual spectral-theorem eigenvalue. -/
noncomputable def spectralPhaseLevel (w : ℕ → ℝ) (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) :=
  Classical.choose (dirichletEigenvalue_phase_level w n i)

theorem spectralPhaseLevel_spec (w : ℕ → ℝ) (n : ℕ) (i : Fin (n + 1)) :
    shootingPhase (dirichletEigenvalues (n + 1) (fun j => w j.val) i) w (n + 1) =
      halfIntegerPhaseLevel (spectralPhaseLevel w n i).val :=
  Classical.choose_spec (dirichletEigenvalue_phase_level w n i)

theorem spectralPhaseLevel_injective (w : ℕ → ℝ) (n : ℕ) :
    Function.Injective (spectralPhaseLevel w n) := by
  intro i j hij
  apply dirichletEigenvalues_injective (n + 1) (fun j => w j.val)
  apply (shootingPhase_strictAnti_energy w n).injective
  change shootingPhase (dirichletEigenvalues (n + 1) (fun j => w j.val) i) w (n + 1) =
    shootingPhase (dirichletEigenvalues (n + 1) (fun j => w j.val) j) w (n + 1)
  rw [spectralPhaseLevel_spec, spectralPhaseLevel_spec, hij]

theorem spectralPhaseLevel_bijective (w : ℕ → ℝ) (n : ℕ) :
    Function.Bijective (spectralPhaseLevel w n) :=
  ⟨spectralPhaseLevel_injective w n,
    Finite.surjective_of_injective (spectralPhaseLevel_injective w n)⟩

/-- Strict eigenvalue counting is the reverse strict phase-level counting. -/
theorem strictSpectralCount_eq_halfLevels (w : ℕ → ℝ) (n : ℕ) (E : ℝ) :
    strictSpectralCount (n + 1) (fun j => w j.val) E =
      (univ.filter (fun k : Fin (n + 1) =>
        shootingPhase E w (n + 1) < halfIntegerPhaseLevel k.val)).card := by
  classical
  unfold strictSpectralCount
  apply Finset.card_bijective (spectralPhaseLevel w n) (spectralPhaseLevel_bijective w n)
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← spectralPhaseLevel_spec]
  exact (shootingPhase_strictAnti_energy w n).lt_iff_gt.symm

/-- Non-strict eigenvalue counting preserves the equality endpoint in phase coordinates. -/
theorem nonstrictSpectralCount_eq_halfLevels (w : ℕ → ℝ) (n : ℕ) (E : ℝ) :
    nonstrictSpectralCount (n + 1) (fun j => w j.val) E =
      (univ.filter (fun k : Fin (n + 1) =>
        shootingPhase E w (n + 1) ≤ halfIntegerPhaseLevel k.val)).card := by
  classical
  unfold nonstrictSpectralCount
  apply Finset.card_bijective (spectralPhaseLevel w n) (spectralPhaseLevel_bijective w n)
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← spectralPhaseLevel_spec]
  exact (shootingPhase_strictAnti_energy w n).le_iff_ge.symm

theorem phase_le_halfIntegerLevel_iff_ceil (θ : ℝ) (k : ℕ) :
    θ ≤ halfIntegerPhaseLevel k ↔ Int.ceil (θ / Real.pi - 1 / 2) ≤ (k : ℤ) := by
  have hceil : Int.ceil (θ / Real.pi - 1 / 2) ≤ (k : ℤ) ↔
      θ / Real.pi - 1 / 2 ≤ (k : ℝ) := by
    simpa only [Int.cast_natCast] using
      (Int.ceil_le (a := θ / Real.pi - 1 / 2) (z := (k : ℤ)))
  rw [hceil]
  have hlevel : halfIntegerPhaseLevel k = ((k : ℝ) + 1 / 2) * Real.pi := by
    unfold halfIntegerPhaseLevel
    ring
  rw [hlevel, ← div_le_iff₀ Real.pi_pos]
  constructor <;> intro h <;> linarith

/-- Counting half-integer levels strictly above an actual nonnegative angle. -/
theorem halfLevel_count_floor (n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    (univ.filter (fun k : Fin n => θ < halfIntegerPhaseLevel k.val)).card =
      n - (Int.floor (θ / Real.pi + 1 / 2)).toNat := by
  classical
  have hfloor0 : 0 ≤ Int.floor (θ / Real.pi + 1 / 2) := by
    apply Int.floor_nonneg.mpr
    have hdiv := div_nonneg hθ Real.pi_pos.le
    linarith
  have hcast : ((Int.floor (θ / Real.pi + 1 / 2)).toNat : ℤ) =
      Int.floor (θ / Real.pi + 1 / 2) := Int.toNat_of_nonneg hfloor0
  have hfilter : univ.filter (fun k : Fin n => θ < halfIntegerPhaseLevel k.val) =
      univ.filter (fun k : Fin n => (Int.floor (θ / Real.pi + 1 / 2)).toNat ≤ k.val) := by
    apply Finset.filter_congr
    intro k _
    rw [phase_lt_halfIntegerLevel_iff_floor, ← hcast]
    norm_cast
  rw [hfilter, fin_ge_card]

/-- Counting half-integer levels at or above a nonnegative angle. -/
theorem halfLevel_count_ceil (n : ℕ) (θ : ℝ) (hθ : 0 ≤ θ) :
    (univ.filter (fun k : Fin n => θ ≤ halfIntegerPhaseLevel k.val)).card =
      n - (Int.ceil (θ / Real.pi - 1 / 2)).toNat := by
  classical
  have hceil0 : 0 ≤ Int.ceil (θ / Real.pi - 1 / 2) := by
    have hdiv := div_nonneg hθ Real.pi_pos.le
    have h : (-1 : ℤ) < Int.ceil (θ / Real.pi - 1 / 2) := by
      apply Int.lt_ceil.mpr
      norm_num only [Int.cast_neg, Int.cast_one]
      linarith
    omega
  have hcast : ((Int.ceil (θ / Real.pi - 1 / 2)).toNat : ℤ) =
      Int.ceil (θ / Real.pi - 1 / 2) := Int.toNat_of_nonneg hceil0
  have hfilter : univ.filter (fun k : Fin n => θ ≤ halfIntegerPhaseLevel k.val) =
      univ.filter (fun k : Fin n => (Int.ceil (θ / Real.pi - 1 / 2)).toNat ≤ k.val) := by
    apply Finset.filter_congr
    intro k _
    rw [phase_le_halfIntegerLevel_iff_ceil, ← hcast]
    norm_cast
  rw [hfilter, fin_ge_card]

/-- Exact finite Sturm formula with the strict eigenvalue endpoint. -/
theorem strictSpectralCount_shooting (w : ℕ → ℝ) (n : ℕ) (E : ℝ) :
    strictSpectralCount n (fun j => w j.val) E =
      n - (Int.floor (shootingPhase E w n / Real.pi + 1 / 2)).toNat := by
  cases n with
  | zero => norm_num [strictSpectralCount, shootingPhase, orbit]
  | succ n =>
    rw [strictSpectralCount_eq_halfLevels]
    exact halfLevel_count_floor (n + 1) _ (shootingPhase_mem E w n).1.le

/-- Exact finite Sturm formula with the non-strict eigenvalue endpoint. -/
theorem nonstrictSpectralCount_shooting (w : ℕ → ℝ) (n : ℕ) (E : ℝ) :
    nonstrictSpectralCount n (fun j => w j.val) E =
      n - (Int.ceil (shootingPhase E w n / Real.pi - 1 / 2)).toNat := by
  cases n with
  | zero => norm_num [nonstrictSpectralCount, shootingPhase, orbit]
  | succ n =>
    rw [nonstrictSpectralCount_eq_halfLevels]
    exact halfLevel_count_ceil (n + 1) _ (shootingPhase_mem E w n).1.le

theorem shootingPhase_mem_closed (E : ℝ) (w : ℕ → ℝ) (n : ℕ) :
    shootingPhase E w n ∈ Set.Icc 0 ((n : ℝ) * Real.pi) := by
  cases n with
  | zero => simp only [shootingPhase_zero, Nat.cast_zero, zero_mul, Set.mem_Icc, le_refl, and_self]
  | succ n => exact ⟨(shootingPhase_mem E w n).1.le, (shootingPhase_mem E w n).2.le⟩

/-- The floor index of an angle in the actual shooting range is a finite-volume index. -/
theorem halfLevel_floorIndex_bounds (n : ℕ) (θ : ℝ)
    (hθ : θ ∈ Set.Icc 0 ((n : ℝ) * Real.pi)) :
    0 ≤ Int.floor (θ / Real.pi + 1 / 2) ∧
      Int.floor (θ / Real.pi + 1 / 2) ≤ (n : ℤ) := by
  have hdiv0 : 0 ≤ θ / Real.pi := div_nonneg hθ.1 Real.pi_pos.le
  have hdivn : θ / Real.pi ≤ (n : ℝ) := (div_le_iff₀ Real.pi_pos).mpr hθ.2
  constructor
  · apply Int.floor_nonneg.mpr
    linarith
  · apply Int.floor_le_iff.mpr
    simp only [Int.cast_natCast]
    linarith

/-- The ceiling index of an angle in the actual shooting range is a finite-volume index. -/
theorem halfLevel_ceilIndex_bounds (n : ℕ) (θ : ℝ)
    (hθ : θ ∈ Set.Icc 0 ((n : ℝ) * Real.pi)) :
    0 ≤ Int.ceil (θ / Real.pi - 1 / 2) ∧
      Int.ceil (θ / Real.pi - 1 / 2) ≤ (n : ℤ) := by
  have hdiv0 : 0 ≤ θ / Real.pi := div_nonneg hθ.1 Real.pi_pos.le
  have hdivn : θ / Real.pi ≤ (n : ℝ) := (div_le_iff₀ Real.pi_pos).mpr hθ.2
  constructor
  · have h : (-1 : ℤ) < Int.ceil (θ / Real.pi - 1 / 2) := by
      apply Int.lt_ceil.mpr
      norm_num only [Int.cast_neg, Int.cast_one]
      linarith
    omega
  · apply Int.ceil_le.mpr
    simp only [Int.cast_natCast]
    linarith

/-- The exact strict Sturm formula as a real-valued count identity. -/
theorem strictSpectralCount_shooting_real (w : ℕ → ℝ) (n : ℕ) (E : ℝ) :
    (strictSpectralCount n (fun j => w j.val) E : ℝ) = (n : ℝ) -
      (Int.floor (shootingPhase E w n / Real.pi + 1 / 2) : ℝ) := by
  have hb := halfLevel_floorIndex_bounds n _ (shootingPhase_mem_closed E w n)
  have hcast : ((Int.floor (shootingPhase E w n / Real.pi + 1 / 2)).toNat : ℤ) =
      Int.floor (shootingPhase E w n / Real.pi + 1 / 2) := Int.toNat_of_nonneg hb.1
  have hle : (Int.floor (shootingPhase E w n / Real.pi + 1 / 2)).toNat ≤ n := by omega
  rw [strictSpectralCount_shooting, Nat.cast_sub hle]
  congr 1
  exact_mod_cast hcast

/-- The exact non-strict Sturm formula as a real-valued count identity. -/
theorem nonstrictSpectralCount_shooting_real (w : ℕ → ℝ) (n : ℕ) (E : ℝ) :
    (nonstrictSpectralCount n (fun j => w j.val) E : ℝ) = (n : ℝ) -
      (Int.ceil (shootingPhase E w n / Real.pi - 1 / 2) : ℝ) := by
  have hb := halfLevel_ceilIndex_bounds n _ (shootingPhase_mem_closed E w n)
  have hcast : ((Int.ceil (shootingPhase E w n / Real.pi - 1 / 2)).toNat : ℤ) =
      Int.ceil (shootingPhase E w n / Real.pi - 1 / 2) := Int.toNat_of_nonneg hb.1
  have hle : (Int.ceil (shootingPhase E w n / Real.pi - 1 / 2)).toNat ≤ n := by omega
  rw [nonstrictSpectralCount_shooting, Nat.cast_sub hle]
  congr 1
  exact_mod_cast hcast

/-- Strict eigenvalue counting differs from the reversed normalized phase by at most a half. -/
theorem strictSpectralCount_phase_error (w : ℕ → ℝ) (n : ℕ) (E : ℝ) :
    |(strictSpectralCount n (fun j => w j.val) E : ℝ) +
      shootingPhase E w n / Real.pi - (n : ℝ)| ≤ 1 / 2 := by
  rw [strictSpectralCount_shooting_real, abs_le]
  have hlo := Int.floor_le (shootingPhase E w n / Real.pi + 1 / 2)
  have hhi := Int.lt_floor_add_one (shootingPhase E w n / Real.pi + 1 / 2)
  constructor <;> linarith

/-- Non-strict eigenvalue counting has the same half-unit deterministic phase error. -/
theorem nonstrictSpectralCount_phase_error (w : ℕ → ℝ) (n : ℕ) (E : ℝ) :
    |(nonstrictSpectralCount n (fun j => w j.val) E : ℝ) +
      shootingPhase E w n / Real.pi - (n : ℝ)| ≤ 1 / 2 := by
  rw [nonstrictSpectralCount_shooting_real, abs_le]
  have hlo := Int.le_ceil (shootingPhase E w n / Real.pi - 1 / 2)
  have hhi := Int.ceil_lt_add_one (shootingPhase E w n / Real.pi - 1 / 2)
  constructor <;> linarith

/-- A spectral window count has at most one unit of deterministic phase-gap error. -/
theorem strictSpectralCount_phase_gap_error (w : ℕ → ℝ) (n : ℕ) (E E' : ℝ) :
    |((strictSpectralCount n (fun j => w j.val) E' : ℝ) -
        (strictSpectralCount n (fun j => w j.val) E : ℝ)) -
      (shootingPhase E w n - shootingPhase E' w n) / Real.pi| ≤ 1 := by
  have hE := abs_le.mp (strictSpectralCount_phase_error w n E)
  have hE' := abs_le.mp (strictSpectralCount_phase_error w n E')
  rw [sub_div, abs_le]
  constructor <;> linarith

/-- The actual iid phase gap controls the actual strict finite spectral window count. -/
theorem strictSpectralCount_canonicalGap_error (w : PotentialSpace) (n : ℕ) (E δ : ℝ) :
    |((strictSpectralCount n (fun j => w j.val) (E + δ) : ℝ) -
        (strictSpectralCount n (fun j => w j.val) E : ℝ)) -
      canonicalGapProcess E δ 0 0 n w / Real.pi| ≤ 1 := by
  simpa only [canonicalGapProcess, ← shootingPhase_eq_process] using
    strictSpectralCount_phase_gap_error w n E (E + δ)

end FixedCouplingPoisson
