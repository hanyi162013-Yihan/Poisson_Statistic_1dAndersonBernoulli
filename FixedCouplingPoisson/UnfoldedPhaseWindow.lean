import FixedCouplingPoisson.Normalization
import FixedCouplingPoisson.PhaseWindow
import FixedCouplingPoisson.IDSExistence

/-!
# Actual unfolded finite Dirichlet windows

The coordinate is evaluated on the spectral-theorem eigenvalues of the actual
Dirichlet matrix. Local strict increase at the two physical cuts identifies
the unfolded half-open window globally, including eigenvalues outside the
local normalization neighborhood. The same count is therefore the actual
shooting-phase ceiling count and its winding plus a zero-or-one carry.
-/
noncomputable section
namespace FixedCouplingPoisson.Furstenberg
open MeasureTheory Set Filter
open scoped Topology

/-- The unfolded coordinate of an actual finite Dirichlet eigenvalue. -/
def dirichletUnfoldedCoordinate (N : ℝ → ℝ) (E : ℝ) (n : ℕ)
    (v : Fin n → ℝ) (j : Fin n) : ℝ :=
  (n : ℝ) * (N (dirichletEigenvalues n v j) - N E)

/-- The actual cardinality in the unfolded half-open window `(a,b]`. -/
def dirichletUnfoldedWindowCount (N : ℝ → ℝ) (E : ℝ) (n : ℕ)
    (v : Fin n → ℝ) (a b : ℝ) : ℕ := by
  classical
  exact (Finset.univ.filter fun j => a < dirichletUnfoldedCoordinate N E n v j ∧
    dirichletUnfoldedCoordinate N E n v j ≤ b).card

theorem unfolded_physical_endpoint_le {N : ℝ → ℝ} {J : Set ℝ}
    {E a b ea eb : ℝ} {n : ℕ} (hstrict : StrictMonoOn N J)
    (hea : J ∈ 𝓝 ea) (heb : J ∈ 𝓝 eb) (hn : 0 < n) (hab : a ≤ b)
    (ha : N ea = N E + a / (n : ℝ)) (hb : N eb = N E + b / (n : ℝ)) :
    ea ≤ eb := by
  rcases lt_or_eq_of_le hab with hab | rfl
  · exact (unfolded_endpoint_lt hstrict (mem_of_mem_nhds hea)
      (mem_of_mem_nhds heb) hn hab ha hb).le
  · exact (hstrict.injOn (mem_of_mem_nhds hea) (mem_of_mem_nhds heb)
      (ha.trans hb.symm)).le

/-- The membership identity applies to every actual eigenvalue, without a
hypothesis that the spectrum lies in the normalization neighborhood. -/
theorem dirichletUnfoldedWindowCount_eq_energyWindowCount
    {N : ℝ → ℝ} {J : Set ℝ} {E a b ea eb : ℝ} {n : ℕ}
    (hmono : Monotone N) (hstrict : StrictMonoOn N J)
    (hea : J ∈ 𝓝 ea) (heb : J ∈ 𝓝 eb) (hn : 0 < n)
    (ha : N ea = N E + a / (n : ℝ)) (hb : N eb = N E + b / (n : ℝ))
    (v : Fin n → ℝ) :
    dirichletUnfoldedWindowCount N E n v a b = dirichletEnergyWindowCount n v ea eb := by
  classical
  unfold dirichletUnfoldedWindowCount dirichletEnergyWindowCount
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j _
  exact unfolded_window_iff hmono hstrict hea heb hn ha hb

/-- Exact shooting-phase formula for the actual unfolded finite window. -/
theorem dirichletUnfoldedWindowCount_eq_phase_ceil
    {N : ℝ → ℝ} {J : Set ℝ} {E a b ea eb : ℝ} {n : ℕ}
    (hmono : Monotone N) (hstrict : StrictMonoOn N J)
    (hea : J ∈ 𝓝 ea) (heb : J ∈ 𝓝 eb) (hn : 0 < n) (hab : a ≤ b)
    (ha : N ea = N E + a / (n : ℝ)) (hb : N eb = N E + b / (n : ℝ))
    (ω : PotentialSpace) :
    (dirichletUnfoldedWindowCount N E n (fun j => ω j.val) a b : ℤ) =
      ⌈(shootingPhase ea ω n - Real.pi / 2) / Real.pi⌉ -
        ⌈(shootingPhase eb ω n - Real.pi / 2) / Real.pi⌉ := by
  rw [dirichletUnfoldedWindowCount_eq_energyWindowCount hmono hstrict hea heb hn ha hb,
    dirichletEnergyWindowCount_eq_nonstrict_difference n (fun j => ω j.val) ea eb
      (unfolded_physical_endpoint_le hstrict hea heb hn hab ha hb)]
  exact nonstrictSpectralWindow_eq_phase_ceil ω n ea eb

/-- Specialization to the actual IDS constructed from the iid Dirichlet matrices. -/
def idsUnfoldedWindowCount (law : PotentialLaw) (E : ℝ) (n : ℕ)
    (v : Fin n → ℝ) (a b : ℝ) : ℕ :=
  dirichletUnfoldedWindowCount (idsCandidate law) E n v a b

theorem idsUnfoldedWindowCount_eq_energyWindowCount (law : PotentialLaw)
    {J : Set ℝ} {E a b ea eb : ℝ} {n : ℕ}
    (hstrict : StrictMonoOn (idsCandidate law) J)
    (hea : J ∈ 𝓝 ea) (heb : J ∈ 𝓝 eb) (hn : 0 < n)
    (ha : idsCandidate law ea = idsCandidate law E + a / (n : ℝ))
    (hb : idsCandidate law eb = idsCandidate law E + b / (n : ℝ)) (v : Fin n → ℝ) :
    idsUnfoldedWindowCount law E n v a b = dirichletEnergyWindowCount n v ea eb :=
  dirichletUnfoldedWindowCount_eq_energyWindowCount
    (monotone_idsCandidate law) hstrict hea heb hn ha hb v

/-- On the original iid sample space, the actual unfolded count is exactly
the already proved adjacent physical-window spectral count. -/
theorem idsUnfoldedWindowCount_eq_actualWindowSpectralCount (law : PotentialLaw)
    {J : Set ℝ} {E : ℝ} (x : ℕ → ℝ) (e : ℕ → ℕ → ℝ) (n i : ℕ)
    (hstrict : StrictMonoOn (idsCandidate law) J)
    (hea : J ∈ 𝓝 (e n i)) (heb : J ∈ 𝓝 (e n (i + 1))) (hn : 0 < n)
    (hab : x i ≤ x (i + 1))
    (ha : idsCandidate law (e n i) = idsCandidate law E + x i / (n : ℝ))
    (hb : idsCandidate law (e n (i + 1)) =
      idsCandidate law E + x (i + 1) / (n : ℝ)) (ω : PotentialSpace) :
    (idsUnfoldedWindowCount law E n (fun j => ω j.val) (x i) (x (i + 1)) : ℤ) =
      actualWindowSpectralCount e n i ω := by
  rw [idsUnfoldedWindowCount_eq_energyWindowCount law hstrict hea heb hn ha hb]
  exact (actualWindowSpectralCount_eq_card e n i ω
    (unfolded_physical_endpoint_le hstrict hea heb hn hab ha hb)).symm

/-- The only difference between the actual unfolded count and its integer
winding is the deterministic carry at the terminal Dirichlet cut. -/
theorem idsUnfoldedWindowCount_winding_error_zero_or_one (law : PotentialLaw)
    {J : Set ℝ} {E : ℝ} (x : ℕ → ℝ) (e : ℕ → ℕ → ℝ) (n i : ℕ)
    (hstrict : StrictMonoOn (idsCandidate law) J)
    (hea : J ∈ 𝓝 (e n i)) (heb : J ∈ 𝓝 (e n (i + 1))) (hn : 0 < n)
    (hab : x i ≤ x (i + 1))
    (ha : idsCandidate law (e n i) = idsCandidate law E + x i / (n : ℝ))
    (hb : idsCandidate law (e n (i + 1)) =
      idsCandidate law E + x (i + 1) / (n : ℝ)) (ω : PotentialSpace) :
    (idsUnfoldedWindowCount law E n (fun j => ω j.val) (x i) (x (i + 1)) : ℤ) -
        actualWindowWinding e n i ω = 0 ∨
      (idsUnfoldedWindowCount law E n (fun j => ω j.val) (x i) (x (i + 1)) : ℤ) -
        actualWindowWinding e n i ω = 1 := by
  rw [idsUnfoldedWindowCount_eq_actualWindowSpectralCount law x e n i
    hstrict hea heb hn hab ha hb ω, actualWindowSpectralCount_eq_terminal]
  exact terminalWindowCount_error_zero_or_one (actualEndpointPhase e n ω) (Real.pi / 2) i

/-- Actual unfolded counts are measurable via the proved phase formula;
no measurable eigenvalue enumeration is assumed. -/
theorem measurable_idsUnfoldedWindowCount (law : PotentialLaw)
    {J : Set ℝ} {E : ℝ} (x : ℕ → ℝ) (e : ℕ → ℕ → ℝ) (n i : ℕ)
    (hstrict : StrictMonoOn (idsCandidate law) J)
    (hea : J ∈ 𝓝 (e n i)) (heb : J ∈ 𝓝 (e n (i + 1))) (hn : 0 < n)
    (hab : x i ≤ x (i + 1))
    (ha : idsCandidate law (e n i) = idsCandidate law E + x i / (n : ℝ))
    (hb : idsCandidate law (e n (i + 1)) =
      idsCandidate law E + x (i + 1) / (n : ℝ)) :
    Measurable (fun ω : PotentialSpace =>
      idsUnfoldedWindowCount law E n (fun j => ω j.val) (x i) (x (i + 1))) := by
  have heq : (fun ω : PotentialSpace =>
      idsUnfoldedWindowCount law E n (fun j => ω j.val) (x i) (x (i + 1))) =
      (fun ω => (actualWindowSpectralCount e n i ω).toNat) := by
    funext ω
    rw [← idsUnfoldedWindowCount_eq_actualWindowSpectralCount law x e n i
      hstrict hea heb hn hab ha hb ω]
    exact (Int.toNat_natCast _).symm
  rw [heq]
  exact (measurable_of_countable Int.toNat).comp (measurable_actualWindowSpectralCount e n i)

end FixedCouplingPoisson.Furstenberg
