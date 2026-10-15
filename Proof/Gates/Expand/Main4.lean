import Proof.Gates.Expand.Main3
import Proof.Gates.Interfaces.CounterFormats

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Expand.Layout

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Expand

def cleanup : WMX NS NR := .seq (clrR (RF 8)) (.seq (clrR (RF 10)) (clrR (Y 0)))

def mainP : WMX NS NR := .seq stageA (.seq stageB (.seq core cleanup))

def cleanupCost (r : FormulaReq) : ℕ :=
  (r.2.degree * (1 + 2) + 1) + 1 + ((r.1 * (1 + 2) + 1) + 1 + ((2 * Lw r + 1) * (1 + 2) + 1))

/-- The step budget of the expansion engine. -/
def budget (r : FormulaReq) : ℕ :=
  stageACost r + 1 + (stageBCost r + 1 + (coreCost r (Wt r) (Wb2 r) + 1 + cleanupCost r))

/-- The register cap of the run (a semantic parameter only). -/
def capOf (r : FormulaReq) : ℕ :=
  2 ^ (Lw r + 4) + 2 ^ (natBitLength r.1 + 1) + 4 * Wb2 r + 4 * Wb1 r + 4 * Lw r + 4 * Wt r + 4 * r.2.degree +
    4 * r.1 + ((fam r.1 r.2.degree).length + 2) * (2 * Wb2 r + 1) + (termsWord (expandM r.2)).length +
    8 * Wb2 r + 1000

theorem succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self

theorem widths (r : FormulaReq) : Widths r (Wt r) (Wb2 r) (capOf r) := by
  have eW2 : Wb2 r = (Wt r + Lw r + 2) * (Lw r + 2) + r.1 * (r.2.degree + 1) + r.2.degree + 4 := rfl
  have hN := toks_le_word r
  have eL : Lw r = (formulaWord r).length := rfl
  have hWt : Wt r = r.2.weight + 2 := rfl
  have hA : Wt r + Lw r + 2 ≤ (Wt r + Lw r + 2) * (Lw r + 2) := Nat.le_mul_of_pos_right _ (by omega)
  have hVD : r.1 ≤ r.1 * (r.2.degree + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hVD2 : r.1 * r.2.degree + 2 ≤ Wb2 r := by rw [eW2]; nlinarith
  refine ⟨by omega, by omega, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h1 : r.2.degree + 3 ≤ 2 ^ (r.2.degree + 2) := by have := succ_le_two_pow (r.2.degree + 2); omega
    calc (r.2.degree + 3) * 2 ^ r.1 * 2 ^ Wt r ≤ 2 ^ (r.2.degree + 2) * 2 ^ r.1 * 2 ^ Wt r := by gcongr
      _ = 2 ^ (r.2.degree + 2 + r.1 + Wt r) := by ring
      _ ≤ 2 ^ Wb2 r := Nat.pow_le_pow_right (by norm_num) (by rw [eW2]; omega)
  · rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by rw [eW2]; unfold Lw at *; nlinarith)
  · rw [famRecs_length]
    have h1 : (fam r.1 r.2.degree).length ≤ 2 ^ (r.1 * r.2.degree) := by
      calc (fam r.1 r.2.degree).length ≤ (r.1 + 1) ^ r.2.degree := fam_length_le _ _
        _ ≤ (2 ^ r.1) ^ r.2.degree := Nat.pow_le_pow_left (succ_le_two_pow _) _
        _ = 2 ^ (r.1 * r.2.degree) := by rw [← pow_mul]
    have h2 : 2 ^ (r.1 * r.2.degree + 2) ≤ 2 ^ Wb2 r := Nat.pow_le_pow_right (by norm_num) hVD2
    have h3 : 2 ^ (r.1 * r.2.degree + 2) = 4 * 2 ^ (r.1 * r.2.degree) := by ring
    have h4 := @Nat.one_le_two_pow (r.1 * r.2.degree)
    omega
  all_goals
    have c1 := Nat.two_pow_pos (natBitLength r.1 + 1)
    have c2 := Nat.two_pow_pos (Lw r + 4)
    have c3 : capOf r = 2 ^ (Lw r + 4) + 2 ^ (natBitLength r.1 + 1) + 4 * Wb2 r + 4 * Wb1 r + 4 * Lw r + 4 * Wt r +
      4 * r.2.degree + 4 * r.1 + ((fam r.1 r.2.degree).length + 2) * (2 * Wb2 r + 1) +
      (termsWord (expandM r.2)).length + 8 * Wb2 r + 1000 := rfl
    rw [c3]
  · omega
  · omega
  · omega
  · omega
  · rw [← eL]; omega
  · omega

theorem capOf_eq (r : FormulaReq) : capOf r = 2 ^ (Lw r + 4) + 2 ^ (natBitLength r.1 + 1) + 4 * Wb2 r + 4 * Wb1 r +
    4 * Lw r + 4 * Wt r + 4 * r.2.degree + 4 * r.1 + ((fam r.1 r.2.degree).length + 2) * (2 * Wb2 r + 1) +
    (termsWord (expandM r.2)).length + 8 * Wb2 r + 1000 := rfl

/-- **The expansion engine's run.** -/
theorem main_spec (r : FormulaReq) :
    Runs (capOf r) mainP (Interfaces.startState NS NR (formulaWord r)) (budget r)
      (fun τ => τ.st O = termsWord (expandM r.2) ∧ (∀ i, τ.sh i = 0) ∧ ∀ q, τ.val q = 0) := by
  have hc := capOf_eq r
  have hw := widths r
  have hTW : 2 * 2 ^ r.1 * 2 ^ Wt r ≤ 2 ^ Wb2 r :=
    le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))) hw.dw
  have c1 := Nat.two_pow_pos (natBitLength r.1 + 1)
  have c2 := Nat.two_pow_pos (Lw r + 4)
  refine Runs.seq (stageA_spec r (capOf r) (by unfold CapA; omega)) (fun τ1 h1 => ?_)
  refine Runs.seq (stageB_spec r (capOf r) τ1 h1 (by unfold CapB; omega) hTW (wb1_le_wb2 r)) (fun τ2 h2 => ?_)
  refine Runs.seq (core_spec r (Wt r) (Wb2 r) (capOf r) τ2 h2 hw) (fun τ3 ⟨hO, hsh, hk, h8, h10, hy⟩ => ?_)
  refine Runs.seq ((rClrR (capOf r) (RF 8) τ3 (by rw [h8]; omega)).cost (le_of_eq (by rw [h8])))
    (fun τ4 ⟨f4, z4⟩ => ?_)
  refine Runs.seq ((rClrR (capOf r) (RF 10) τ4 (by rw [f4.val (by lay_ne), h10]; omega)).cost
    (le_of_eq (by rw [f4.val (by lay_ne), h10]))) (fun τ5 ⟨f5, z5⟩ => ?_)
  refine ((rClrR (capOf r) (Y 0) τ5 (by rw [f5.val (by lay_ne), f4.val (by lay_ne), hy]; have : Lw r = (formulaWord r).length := rfl; omega)).cost
    (le_of_eq (by rw [f5.val (by lay_ne), f4.val (by lay_ne), hy]; rfl))).post (fun τ6 ⟨f6, z6⟩ => ⟨?_, ?_, ?_⟩)
  · rw [f6.st (by simp), f5.st (by simp), f4.st (by simp)]; exact hO
  · intro i; rw [f6.sh (by simp), f5.sh (by simp), f4.sh (by simp)]; exact hsh i
  · intro q
    by_cases e8 : q = RF 8
    · subst e8; rw [f6.val (by lay_ne), f5.val (by lay_ne), z4]
    · by_cases e10 : q = RF 10
      · subst e10; rw [f6.val (by lay_ne), z5]
      · by_cases ey : q = Y 0
        · subst ey; exact z6
        · rw [f6.val (by simp [ey]), f5.val (by simp [e10]), f4.val (by simp [e8])]; exact hk q ⟨e8, e10, ey⟩

noncomputable def expansionMachineWF :
    WordFunction FormulaReq formulaWord (fun r => termsWord (expandM r.2)) budget :=
  Interfaces.wordFunction_of_wmx mainP O (by simp [O]) capOf (fun r => main_spec r)

end NearCubicGates.Close.Expand.Layout
