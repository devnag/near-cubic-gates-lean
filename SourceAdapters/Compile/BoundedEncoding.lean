import SourceAdapters.Compile.BoundedMachine
import SourceAdapters.Compile.BoundedExpression
import Proof.Gates.Succinct.Points

/-!
proof of `lem:multitape-refuter`, Step 3: explicit finite configuration bits and local read
expressions. Control and heads use one-hot encodings; tape cells remain bits.
-/

namespace NearCubicGates.Adapters.Compile

open NearCubicWires NearCubicWires.LocalBitMultitape
  NearCubicWires.FinitePredicateCircuit
set_option autoImplicit false

def windowBits (t s width : ℕ) : ℕ := s + (t * width + t * width)

def controlIndex {t s width : ℕ} (q : Fin s) : Fin (windowBits t s width) :=
  q.castAdd _

def headIndex {t s width : ℕ} (tape : Fin t) (position : Fin width) :
    Fin (windowBits t s width) :=
  ((finProdFinEquiv (tape, position)).castAdd (t * width)).natAdd s

def cellIndex {t s width : ℕ} (tape : Fin t) (position : Fin width) :
    Fin (windowBits t s width) :=
  ((finProdFinEquiv (tape, position)).natAdd (t * width)).natAdd s

def MachineWindow.encode {t s width : ℕ} (a : MachineWindow t s width) :
    BitInput (windowBits t s width) :=
  Fin.addCases (fun q => decide (a.control = q))
    (Fin.addCases
      (fun index => let pair := finProdFinEquiv.symm index
                    decide (a.heads pair.1 = pair.2))
      (fun index => let pair := finProdFinEquiv.symm index
                    a.cells pair.1 pair.2))

@[simp] theorem MachineWindow.encode_control {t s width : ℕ}
    (a : MachineWindow t s width) (q : Fin s) :
    a.encode (controlIndex q) = decide (a.control = q) := by
  simp [MachineWindow.encode, controlIndex]

@[simp] theorem MachineWindow.encode_head {t s width : ℕ}
    (a : MachineWindow t s width) (tape : Fin t) (position : Fin width) :
    a.encode (headIndex tape position) = decide (a.heads tape = position) := by
  simp only [MachineWindow.encode, headIndex, Fin.addCases_left, Fin.addCases_right,
    Equiv.symm_apply_apply]

@[simp] theorem MachineWindow.encode_cell {t s width : ℕ}
    (a : MachineWindow t s width) (tape : Fin t) (position : Fin width) :
    a.encode (cellIndex tape position) = a.cells tape position := by
  simp only [MachineWindow.encode, cellIndex, Fin.addCases_right, Equiv.symm_apply_apply]

def anyExpression {n : ℕ} : List (BoolExpr n) → BoolExpr n
  | [] => .const false
  | e :: rest => .or e (anyExpression rest)

def allExpression {n : ℕ} : List (BoolExpr n) → BoolExpr n
  | [] => .const true
  | e :: rest => .and e (allExpression rest)

@[simp] theorem anyExpression_true {n : ℕ} (expressions : List (BoolExpr n))
    (input : BitInput n) :
    (anyExpression expressions).eval input = true ↔
      ∃ expression ∈ expressions, expression.eval input = true := by
  induction expressions with
  | nil => simp [anyExpression, BoolExpr.eval]
  | cons expression rest ih => simp [anyExpression, BoolExpr.eval, ih]

@[simp] theorem allExpression_true {n : ℕ} (expressions : List (BoolExpr n))
    (input : BitInput n) :
    (allExpression expressions).eval input = true ↔
      ∀ expression ∈ expressions, expression.eval input = true := by
  induction expressions with
  | nil => simp [allExpression, BoolExpr.eval]
  | cons expression rest ih => simp [allExpression, BoolExpr.eval, ih]

/-- An actual head-selected tape bit, using only the configuration wires. -/
def scannedExpression {t s width : ℕ} (tape : Fin t) : BoolExpr (windowBits t s width) :=
  anyExpression (List.ofFn (fun position : Fin width =>
    .and (.input (headIndex tape position)) (.input (cellIndex tape position))))

@[simp] theorem scannedExpression_eval {t s width : ℕ} (a : MachineWindow t s width)
    (tape : Fin t) : (scannedExpression tape).eval a.encode = a.scanned tape := by
  apply Bool.eq_iff_iff.mpr
  simp only [scannedExpression, anyExpression_true, List.mem_ofFn, BoolExpr.eval,
    MachineWindow.encode_head, MachineWindow.encode_cell, Bool.and_eq_true,
    decide_eq_true_eq, exists_exists_eq_and]
  simp [MachineWindow.scanned]

/-- Test the literal scanned-bit row of the machine transition table. -/
def scanPatternExpression {t s width : ℕ} (scans : Fin t → Bool) :
    BoolExpr (windowBits t s width) :=
  allExpression (List.ofFn (fun tape : Fin t =>
    if scans tape then scannedExpression tape else .not (scannedExpression tape)))

theorem scanPatternExpression_eval {t s width : ℕ} (a : MachineWindow t s width)
    (scans : Fin t → Bool) :
    (scanPatternExpression scans).eval a.encode = true ↔ scans = a.scanned := by
  simp only [scanPatternExpression, allExpression_true, List.mem_ofFn]
  constructor
  · intro h
    funext tape
    have ht := h _ ⟨tape, rfl⟩
    cases hs : scans tape <;> simp [hs, BoolExpr.eval] at ht ⊢ <;> exact ht
  · rintro rfl expression ⟨tape, rfl⟩
    cases hs : a.scanned tape <;> simp [hs, BoolExpr.eval]

/-- A transition-table row, with the exact current state and read symbols. -/
def rowExpression {t s width : ℕ} (state : Fin s) (scans : Fin t → Bool) :
    BoolExpr (windowBits t s width) :=
  .and (.input (controlIndex state)) (scanPatternExpression scans)

@[simp] theorem rowExpression_eval {t s width : ℕ} (a : MachineWindow t s width)
    (state : Fin s) (scans : Fin t → Bool) :
    (rowExpression state scans).eval a.encode = true ↔
      a.control = state ∧ scans = a.scanned := by
  simp [rowExpression, BoolExpr.eval, scanPatternExpression_eval]

end NearCubicGates.Adapters.Compile
