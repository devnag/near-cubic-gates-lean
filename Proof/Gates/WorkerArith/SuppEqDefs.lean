import Proof.Gates.WorkerArith.RowTest
import Proof.Gates.Worker.Classify
import Proof.Gates.Worker.Dock

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.RepairOrdinary.Streaming NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Interfaces (listWord)

variable {ns nr : ℕ}

/-- The canonical parity list of systematic coordinate `u` (`q` outer coordinates, then the code rows). -/
def sysList (q : ℕ) (rows : ℕ → List ℕ) (u : ℕ) : List ℕ := if u < q then [u] else rows (u - q)

/-- Write the list of the coordinate in `U` to `o` (output position `Rw 7`), then save its length in `OPx`.
`Q 2 = q`, `Q 3 = LS`; scratch `Q 5 … Q 8` (`D F T X`). -/
def writeListW (S o : Fin (ns + 1)) (Rw : Fin 16 ↪ Fin nr) (Q : Fin 12 ↪ Fin nr) (U OPx : Fin nr) : WM ns nr :=
  .seq (Worker.ltSubW U (Q 2) (Q 5) (Q 6) (Q 7) (Q 8))
    (.seq (.ifr (Q 6)
      (.seq (WM.clear (Q 6)) (.seq (Codec.dupR U (Rw 14) (Q 8)) (.seq (Codec.parSys o Rw) (WM.clear (Rw 14)))))
      (.seq (WM.move (Q 5) (Rw 14)) (.seq (Codec.parRow S o Rw (Q 3)) (WM.clear (Rw 14)))))
    (WM.move (Rw 7) OPx))

/-- One comparison step on two marked words (both heads on a marker cell of `A`). -/
def cmpBody (A B : Fin (ns + 1)) (NEQ CNT : Fin nr) : WM ns nr :=
  .seq (.ifs B .skip (WM.setF NEQ))
    (.seq (.fwd A) (.seq (.fwd B)
    (.seq (.ifs A (.ifs B .skip (WM.setF NEQ)) (.ifs B (WM.setF NEQ) .skip))
    (.seq (.fwd A) (.seq (.fwd B) (.inc CNT))))))

/-- Compare two marked words from heads `0`: `NEQ := [they differ]`, heads back at `0`. -/
def cmpW (A B : Fin (ns + 1)) (NEQ CNT : Fin nr) : WM ns nr :=
  .seq (.whs A (cmpBody A B NEQ CNT))
    (.seq (.ifs B (WM.setF NEQ) .skip)
    (.whr CNT (.seq (.dec CNT) (.seq (.bwd A) (.seq (.bwd A) (.seq (.bwd B) (.bwd B)))))))

def blankW (o : Fin (ns + 1)) (C T2 : Fin nr) : WM ns nr :=
  .seq (.whr C (.seq (.dec C) (.seq (.wr o false) (.seq (.fwd o) (.inc T2))))) (WM.rewind o T2)

/-- **The support-equality test.** `Q 0 = u`, `Q 1 = v`, `Q 2 = q`, `Q 3 = LS` (kept), `Q 4 := [S_u = S_v]`;
`Q 5 … Q 11` scratch; `Rw` the writers' register file with `Rw 7` a scratch output position. -/
def suppEqW (S A B : Fin (ns + 1)) (Rw : Fin 16 ↪ Fin nr) (Q : Fin 12 ↪ Fin nr) : WM ns nr :=
  .seq (writeListW S A Rw Q (Q 0) (Q 9))
  (.seq (writeListW S B Rw Q (Q 1) (Q 10))
  (.seq (Codec.dupR (Q 9) (Q 5) (Q 8)) (.seq (WM.rewind A (Q 5))
  (.seq (Codec.dupR (Q 10) (Q 5) (Q 8)) (.seq (WM.rewind B (Q 5))
  (.seq (cmpW A B (Q 11) (Q 7))
  (.seq (blankW A (Q 9) (Q 8)) (.seq (blankW B (Q 10) (Q 8))
  (.seq (.ifr (Q 11) (WM.clear (Q 11)) (.inc (Q 4)))
  (Codec.rewindCW S (Q 3) (Q 7) (Q 8)))))))))))

/-- The ideal end state: the record rewound, the scratch streams empty, the flag set. -/
def suppIdeal (σ : WState ns nr) (S A B : Fin (ns + 1)) (EQ : Fin nr) (b : Bool) : WState ns nr :=
  ((((σ.seth S 0).sets A []).seth A 0).sets B [] |>.seth B 0).setv EQ b.toNat

/-- The cost class. -/
def suppCost (Z rb : ℕ) : ℕ := 20000 * (Z + 1) ^ 2 * (rb + 1)

def SuppEqSpec (cap : ℕ) (S A B : Fin (ns + 1)) (Rw : Fin 16 ↪ Fin nr) (Q : Fin 12 ↪ Fin nr) (rows : ℕ → List ℕ)
    (R q u v rb Lb : ℕ) (rest : List Bool) (σ : WState ns nr) : Prop :=
  [S, A, B].Nodup → (∀ i k, Q i ≠ Rw k) → u < q + R → v < q + R →
  (∀ j < R, Codec.rowCost (rows j) ≤ rb) →
  (∀ j < R, 2 ^ (natBitLength (rows j).length + 1) ≤ cap ∧ (rows j).length ≤ cap ∧
    ∀ x ∈ rows j, natBitLength x + 1 ≤ cap) →
  20 * (Lb + q + u + v + 10) ≤ cap →
  σ.st S = Codec.rowPrefix rows R ++ rest → σ.sh S ≤ Lb → (Codec.rowPrefix rows R).length ≤ Lb →
  Worker.Blank (σ.st A) → σ.sh A = 0 → Worker.Blank (σ.st B) → σ.sh B = 0 →
  (∀ k : Fin 16, k ≠ 12 → k ≠ 13 → k ≠ 15 → σ.val (Rw k) = 0) → (∀ i : Fin 12, 4 ≤ i.val → σ.val (Q i) = 0) →
  σ.val (Q 0) = u → σ.val (Q 1) = v → σ.val (Q 2) = q → σ.val (Q 3) = Lb →
  ∃ τ, WXExec cap (.wm (suppEqW S A B Rw Q)) σ τ (suppCost (Lb + q + u + v) rb) ∧
    SimW (suppIdeal σ S A B (Q 4) (decide (sysList q rows u = sysList q rows v))) τ

end NearCubicGates.Close.WorkerArith
