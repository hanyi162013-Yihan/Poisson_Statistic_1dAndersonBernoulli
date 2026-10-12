import FixedCouplingPoisson.IDSExistence
import Mathlib.Tactic

/-!
# Selective constant-block extraction

Only the two endpoints of each selected good block are cut. Each cut uses
an actual rank-two Dirichlet perturbation already proved in `IDSExistence`;
the two-energy window therefore loses at most eight per selected block.
The intervening arbitrary pieces are discarded using nonnegative counts.
No cut is charged for a bad slot which is not selected.
-/
noncomputable section
namespace FixedCouplingPoisson
open MeasureTheory Set

/-- The actual number of eigenvalues in `(E,F]`, written as a real number. -/
def iidWindowCount (k n : ℕ) (ω : PotentialSpace) (E F : ℝ) : ℝ :=
  (nonstrictSpectralCount n (potentialBlock k n ω) F : ℝ) -
    (nonstrictSpectralCount n (potentialBlock k n ω) E : ℝ)

theorem iidWindowCount_nonneg (k n : ℕ) (ω : PotentialSpace) {E F : ℝ}
    (hEF : E ≤ F) : 0 ≤ iidWindowCount k n ω E F := by
  unfold iidWindowCount
  exact sub_nonneg.mpr (Nat.cast_le.mpr (monotone_nonstrictSpectralCount n _ hEF))

theorem potentialBlock_concat_left_at (k n m : ℕ) (ω : PotentialSpace) :
    (fun i => potentialBlock k (n + m) ω (Fin.castAdd m i)) = potentialBlock k n ω := rfl

theorem potentialBlock_concat_right_at (k n m : ℕ) (ω : PotentialSpace) :
    (fun i => potentialBlock k (n + m) ω (Fin.natAdd n i)) =
      potentialBlock (k + n) m ω := by
  ext i
  simp [potentialBlock, Nat.add_assoc]

/-- One rank-two cut costs at most four in a two-energy window. -/
theorem iidWindowCount_concat_lower (k n m : ℕ) (ω : PotentialSpace) (E F : ℝ) :
    iidWindowCount k n ω E F + iidWindowCount (k + n) m ω E F - 4 ≤
      iidWindowCount k (n + m) ω E F := by
  have hE := nonstrictSpectralCount_concat_abs n m (potentialBlock k (n + m) ω) E
  have hF := nonstrictSpectralCount_concat_abs n m (potentialBlock k (n + m) ω) F
  rw [potentialBlock_concat_left_at, potentialBlock_concat_right_at] at hE hF
  unfold iidWindowCount
  obtain ⟨hE₀, hE₁⟩ := abs_le.mp hE
  obtain ⟨hF₀, hF₁⟩ := abs_le.mp hF
  linarith

/-- Isolating one good block uses exactly two possible boundary cuts. -/
theorem iidWindowCount_extract_lower (k n a L : ℕ) (ω : PotentialSpace)
    {E F : ℝ} (hEF : E ≤ F) (hka : k ≤ a) (han : a + L ≤ k + n) :
    iidWindowCount a L ω E F + iidWindowCount (a + L) (k + n - (a + L)) ω E F - 8 ≤
      iidWindowCount k n ω E F := by
  have h₁ := iidWindowCount_concat_lower k (a - k) (k + n - a) ω E F
  have h₂ := iidWindowCount_concat_lower a L (k + n - (a + L)) ω E F
  have hprefix := iidWindowCount_nonneg k (a - k) ω hEF
  have hs : k + (a - k) = a := by omega
  have hn : a - k + (k + n - a) = n := by omega
  have hr : L + (k + n - (a + L)) = k + n - a := by omega
  rw [hs, hn] at h₁
  rw [hr] at h₂
  linarith

/-- A constant chain with at least nine eigenvalues in the window pays for
both boundary cuts and leaves at least one eigenvalue per selected block.
The selected starts may be separated by arbitrary unselected potential. -/
theorem selectedConstantBlocks_windowCount_lower (E F : ℝ) (hEF : E ≤ F)
    (c : ℝ) (L : ℕ)
    (hconstant : 9 ≤ (nonstrictSpectralCount L (fun _ => c) F : ℝ) -
      (nonstrictSpectralCount L (fun _ => c) E : ℝ))
    (g k n : ℕ) (ω : PotentialSpace) (starts : Fin g → ℕ)
    (hstart : ∀ i, k ≤ starts i)
    (hend : ∀ i, starts i + L ≤ k + n)
    (hsep : ∀ i j, i < j → starts i + L ≤ starts j)
    (hgood : ∀ i, potentialBlock (starts i) L ω = fun _ => c) :
    (g : ℝ) ≤ iidWindowCount k n ω E F := by
  induction g generalizing k n with
  | zero => simpa using iidWindowCount_nonneg k n ω hEF
  | succ g ih =>
    let a := starts 0
    have htail := ih (a + L) (k + n - (a + L)) (fun i => starts i.succ)
      (fun i => hsep 0 i.succ (by simp))
      (fun i => by have hh := hend i.succ; have ha := hend 0; dsimp [a] at *; omega)
      (fun i j hij => hsep i.succ j.succ (by simpa using hij))
      (fun i => hgood i.succ)
    have hc : 9 ≤ iidWindowCount a L ω E F := by
      unfold iidWindowCount
      rw [show potentialBlock a L ω = fun _ => c from hgood 0]
      exact hconstant
    have he := iidWindowCount_extract_lower k n a L ω hEF (hstart 0) (hend 0)
    push_cast
    linarith

end FixedCouplingPoisson
