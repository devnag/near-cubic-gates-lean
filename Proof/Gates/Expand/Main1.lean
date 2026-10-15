import Proof.Gates.Expand.Setup9

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

theorem toks_le_word (r : FormulaReq) : (toks r.2).length ≤ (formulaWord r).length := by
  have h1 : (toks r.2).length ≤ tokBits r.2 := by
    unfold tokBits
    rw [List.length_flatMap]
    have : ∀ t ∈ toks r.2, 1 ≤ (tokWord t).length := by
      intro t _; cases t <;> simp [tokWord, Interfaces.intWord, natWord_len] <;> omega
    calc (toks r.2).length = ((toks r.2).map fun _ => 1).sum := by simp
      _ ≤ ((toks r.2).map fun t => (tokWord t).length).sum := List.sum_le_sum (fun t ht => this t ht)
  exact h1.trans (tokBits_le r)

def stageA : WMX NS NR :=
  .seq meas (.seq regA (.seq stageA1 (.seq (passA (degH U R) (RF 8)) (.seq (passA (wtH U R) (GR 1))
    (.seq readV (.seq regB1 regB2))))))

/-- The quantities of a request. -/
def Lw (r : FormulaReq) : ℕ := (formulaWord r).length
def Wb1 (r : FormulaReq) : ℕ := (Lw r + 2) * (Lw r + 2)
def KA (r : FormulaReq) : ℕ := 2 ^ (Lw r + 1)
def Wt (r : FormulaReq) : ℕ := r.2.weight + 2
def Wb2 (r : FormulaReq) : ℕ := wb2 (Wt r) (Lw r) r.1 r.2.degree

def stageACost (r : FormulaReq) : ℕ :=
  measCost (Lw r) + 1 + (regACost (Lw r) + 1 + (stageA1Cost (Wb1 r) (Lw r) + 1 +
    ((evalCost (Wb1 r) (hcost (Wb1 r) (tokBits r.2) (maxExp r.2) r.1) r.1 (toks r.2).length (Lw r) + 1 +
      toRegCost (Wb1 r) r.2.degree) + 1 +
    ((evalCost (Wb1 r) (hcost (Wb1 r) (tokBits r.2) (maxExp r.2) r.1) r.1 (toks r.2).length (Lw r) + 1 +
      toRegCost (Wb1 r) r.2.weight) + 1 +
    (readVCost r.1 (Lw r) + 1 + (regB1Cost r.2.weight (Lw r) + 1 + regB2Cost r.2.weight (Lw r) r.1 r.2.degree))))))

/-- The registers that may be nonzero after stage A. -/
def KeepA : List (Fin NR) := [GR 0, GR 1, GR 2, GR 3, GR 4, RF 8, RF 10, Y 0]

/-- The state after stage A. -/
structure AState (r : FormulaReq) (τ : WState NS NR) : Prop where
  mv : ∃ w, MV NB (Wb1 r) w τ
  inp : τ.st (U 0) = frame (formulaWord r)
  others : ∀ x, x ∉ nbList → x ≠ U 0 → τ.st x = [] ∧ τ.sh x = 0
  hd : τ.sh (U 0) = 0
  regs : ∀ q, q ∉ KeepA → τ.val q = 0
  g1 : τ.val (GR 1) = Wt r
  g2 : τ.val (GR 2) = Wb2 r
  g3 : τ.val (GR 3) = r.2.degree + 1
  d : τ.val (RF 8) = r.2.degree
  v : τ.val (RF 10) = r.1
  y0 : τ.val (Y 0) = 2 * Lw r + 1
  g0 : τ.val (GR 0) = Lw r
  g4 : τ.val (GR 4) = Lw r + 2

/-- The cap stage A needs. -/
def CapA (r : FormulaReq) (cap : ℕ) : Prop :=
  2 ^ (Lw r + 4) + 2 ^ (natBitLength r.1 + 1) + 4 * Wb2 r + 4 * (Wb1 r) + 4 * Lw r + 4 * Wt r + 4 * r.2.degree + 100
    ≤ cap

end NearCubicGates.Close.Expand.Layout
