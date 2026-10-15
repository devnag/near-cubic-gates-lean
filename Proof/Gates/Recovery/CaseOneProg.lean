import Proof.Gates.Recovery.CaseOneLoop
import Proof.Gates.Recovery.HTParts2
import Proof.Gates.CheckedPCPP.ClauseFront
import Proof.Gates.WordPrograms.RegArith

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Recovery.CaseOneMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Recovery.HTParts
open NearCubicGates.Close.CheckedPCPP.ClauseFront (named dblW dblW_exec)

/-! ## Streams and registers -/

section Streams
variable (tA : ℕ)

/-- The number of streams minus one: `W, A, Q, X`, the amplifier block (`tA`), the evaluator block (`46`). -/
def NS : ℕ := 49 + tA

def W : Fin (NS tA + 1) := ⟨0, by unfold NS; omega⟩
def A : Fin (NS tA + 1) := ⟨1, by unfold NS; omega⟩
def Q : Fin (NS tA + 1) := ⟨2, by unfold NS; omega⟩
def X : Fin (NS tA + 1) := ⟨3, by unfold NS; omega⟩
def bA (j : Fin tA) : Fin (NS tA + 1) := ⟨4 + j.val, by have := j.isLt; unfold NS; omega⟩
def bV (j : Fin 46) : Fin (NS tA + 1) := ⟨4 + tA + j.val, by have := j.isLt; unfold NS; omega⟩

@[simp] theorem W_val : (W tA).val = 0 := rfl
@[simp] theorem A_val : (A tA).val = 1 := rfl
@[simp] theorem Q_val : (Q tA).val = 2 := rfl
@[simp] theorem X_val : (X tA).val = 3 := rfl
@[simp] theorem bA_val (j : Fin tA) : (bA tA j).val = 4 + j.val := rfl
@[simp] theorem bV_val (j : Fin 46) : (bV tA j).val = 4 + tA + j.val := rfl

end Streams

theorem fin_ne' {n : ℕ} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

/-- Distinct streams of the layout. -/
macro "cdst" : tactic => `(tactic| (apply fin_ne'; simp only [W_val, A_val, Q_val, X_val, bA_val, bV_val]; omega))

abbrev rQ : Fin 16 := 0
abbrev rT1 : Fin 16 := 1
abbrev rT : Fin 16 := 2
abbrev rK : Fin 16 := 3
abbrev rE : Fin 16 := 4
abbrev rB0 : Fin 16 := 5
abbrev rH : Fin 16 := 6
abbrev rB : Fin 16 := 7
abbrev SC : Fin 16 := 8
abbrev opX : Fin 16 := 9
abbrev rQd : Fin 16 := 10
abbrev rTd : Fin 16 := 11

/-! ## The program -/

section Program
variable (tA : ℕ)

/-- Read `q`, compute `2^q`, write `marks (frame q.bits)` on `X`. -/
def headW : WMX (NS tA) 16 :=
  .seq (.wm (oneLoop (Q tA) rQ (fun _ => WM.skip)))
  (.seq (addR rQ rT1 rT)
  (.seq (.wm (WM.rewind (Q tA) rT1))
  (.seq (WMX.inc rK)
  (.seq (addR rQ rE rT)
  (.seq (dblW rK rE rQd rTd)
  (.seq (addR rQ rB0 rT)
  (.seq (bitsQ rB0 rH rB (X tA) opX)
    (.wm (Codec.emitMarks (X tA) opX [false])))))))))

/-- The frame end of `X`; `X` and `W` back to head `0`. -/
def tailW : WMX (NS tA) 16 :=
  .seq (.wm (emitC (X tA) opX false)) (.seq (.wm (WM.rewind (X tA) opX)) (.wm (WM.rewind (W tA) SC)))

/-- The amplifier's input word on `X`. -/
def buildW : WMX (NS tA) 16 :=
  .seq (headW tA) (.seq (.wm (cycW (W tA) (X tA) opX SC rK)) (tailW tA))

end Program

/-- The entry state: the three ports, every other stream empty, heads and registers `0`. -/
def initCaseOne (tA : ℕ) (word addr : List Bool) (q : ℕ) : WState (NS tA) 16 :=
  ⟨fun _ => 0, fun i => if h : i.val < 3 then threeWords word addr q ⟨i.val, h⟩ else [], fun _ => 0, false⟩

theorem marks_append (l l' : List Bool) : marks (l ++ l') = marks l ++ marks l' := by simp [marks]

theorem marks_marks (l : List Bool) : marks (marks l) = l.flatMap fun b => marks [true, b] := by
  induction l with
  | nil => simp [marks]
  | cons b l ih => rw [marks_cons, marks_cons, marks_cons, ih]; simp [marks]

/-- The amplifier's input word as `buildW` writes it. -/
theorem xWord_eq (q : ℕ) (T : List Bool) :
    frame (frame q.bits ++ T) =
      (q.bits.flatMap fun b => marks [true, b]) ++ marks [false] ++ marks T ++ [false] := by
  rw [frame_eq_marks, marks_append, frame_eq_marks, marks_append, marks_marks]

end NearCubicGates.Close.Recovery.CaseOneMachine
