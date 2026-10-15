import Proof.MachineModel.NativeMaster
import Proof.MachineModel.NativeFanout
import Proof.MachineModel.BankCountOptional

/-! The fifteen measured source words are exactly the static native inputs.
Only the table and counted last-index fields remain for incidence to fill. -/
namespace NearCubicWires.ExtIncidence.NativeTemplate
open LocalBitMultitape RepairOrdinary RepairRepresentation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def select (i : Fin 113) : Option (Fin 15):=match i.val with
  | 0 => some 0
  | 9 => some 1
  | 13 => some 2
  | 18 => some 3
  | 21 => some 4
  | 29 => some 5
  | 33 => some 6
  | 35 => some 7
  | 38 => some 8
  | 39 => some 9
  | 40 => some 9
  | 45 => some 10
  | 46 => some 11
  | 51 => some 10
  | 61 => some 11
  | 66 => some 12
  | 90 => some 13
  | 106 => some 10
  | 108 => some 11
  | 109 => some 12
  | 111 => some 13
  | 112 => some 14
  | _ => none

def payload {n : ℕ} (gs : List (ExactThresholdGate n)) (Q w : ℕ) (i : Fin 113):=
  NativeFanout.word select (NativeMaster.words gs Q w) i

private theorem read_false (z k : ℕ) : readTapeBit (List.replicate z false) k=false:=by
  simp [readTapeBit,List.getD]
private theorem read_empty (k : ℕ) : readTapeBit [] k=false:=rfl

theorem entry_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w C : ℕ)
    (out : List Bool) :
    (CloseoutRowsBankPolynomial.entry gs p F Q w C [] out).tapes=
      fun i=>ZeroPadding.pad (CloseoutRowsBankCapacity.capacities C i)
        (Fin.addCases (m:=112) (n:=1) (motive:=fun _=>List Bool)
          (CloseoutRowsLoopLayout.inputTapes gs p F w 0 C [] out) (fun _=>CompareMachine.word Q) i):=rfl

theorem core_read {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w C : ℕ)
    (out : List Bool) (i : Fin 48) (pos : ℕ) :
    readTapeBit ((CloseoutRowsBankPolynomial.entry gs p F Q w C [] out).tapes (i.castAdd 65)) pos=
      readTapeBit (RowTupleCursorLayout.data gs 0 p F w 0 1 [] [] out 0 [] i) pos:=by
  change readTapeBit ((CloseoutRowsBankPolynomial.entry gs p F Q w C [] out).tapes
    (((i.castAdd 55).castAdd 9).castAdd 1)) pos=_
  simp only [entry_tapes,Fin.addCases_left]
  simp only [CloseoutRowsLoopLayout.inputTapes,Fin.addCases_left]
  change readTapeBit (ZeroPadding.pad (CloseoutRowsBankCapacity.capacities C (i.castAdd 65))
    (ZeroPadding.pad (CloseoutRowsDegreeReset.caps C (i.castAdd 55))
      ((CloseoutRowsLoopLayout.rawInput gs p F w 0 [] out).tapes ((i.castAdd 41).castAdd 14)))) pos=_
  simp only [CloseoutRowsLoopLayout.rawInput,CloseoutRowsComputedCuts.input,Fin.addCases_left]
  change readTapeBit (ZeroPadding.pad (CloseoutRowsBankCapacity.capacities C (i.castAdd 65))
    (ZeroPadding.pad (CloseoutRowsDegreeReset.caps C (i.castAdd 55))
      (Function.update (CloseoutRowsComputedCuts.body (0 : Fin 1) gs p F w 0 [] out).tapes 48 []
        (i.castAdd 41)))) pos=_
  have hn : (i.castAdd 41 : Fin 89)≠48:=by
    intro h;have hv:=congrArg (fun x : Fin 89=>x.val) h;have hi:=i.isLt
    simp only [Fin.val_castAdd] at hv;omega
  rw [ZeroPadding.read_pad,ZeroPadding.read_pad,Function.update_of_ne hn]
  change readTapeBit ((CloseoutRowsComputedCuts.body (0 : Fin 1) gs p F w 0 [] out).tapes
    ((i.castAdd 1).castAdd 40)) pos=_
  simp only [CloseoutRowsComputedCuts.body,CloseoutRowsEnumeratedCuts.input,
    TapeEmbedding.config,Fin.addCases_left,CloseoutRowsEnumeratedCuts.core]
  change readTapeBit (ZeroPadding.pad (RowTupleCursorBody.padding F i)
    (RowTupleCursorLayout.data gs 0 p F w 0 1 [] [] out 0 [] i)) pos=_
  exact ZeroPadding.read_pad _ _ _

end NearCubicWires.ExtIncidence.NativeTemplate
