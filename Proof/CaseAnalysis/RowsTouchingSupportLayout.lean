import Proof.CaseAnalysis.RowsTouchingSupportCounterStep
import Proof.MachineModel.Layout
import Proof.Circuits.DecompositionCountPosition

/-! The same support pass returns its three coordinate-mask heads and
produces the exact lookup count word directly, eliminating a raw-count
conversion. Only the original support stream cursor advances. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportReady
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SupportScan
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def directions : Fin 7→HeadMove:=![.stay,.stay,.stay,.stay,.right,.stay,.stay]
def move:=DecompositionCountPosition.move directions
noncomputable abbrev core:=Composition.machine move SupportScan.machine
def selected (i : Fin 7):Bool:=decide (i≠0)
noncomputable abbrev machine:=MaskedReset.machine core selected
def heads (pos : ℕ) : Fin 8→ℕ:=![pos,0,0,0,0,0,0,0]
def raw (P : ℕ) (source : List Bool) (xs : List Cell) (n : ℕ) (hit cur : Bool):Fin 7→List Bool:=
  ![source,(masks xs) 0,(masks xs) 1,(masks xs) 2,ZeroPadding.pad P (CompareMachine.word n),
    ZeroPadding.pad P [hit],ZeroPadding.pad P [cur]]
def data (P C : ℕ) (source : List Bool) (xs : List Cell) (n : ℕ) (hit cur : Bool):Fin 8→List Bool:=
  ![source,(masks xs) 0,(masks xs) 1,(masks xs) 2,ZeroPadding.pad P (CompareMachine.word n),
    ZeroPadding.pad P [hit],ZeroPadding.pad P [cur],List.replicate C false]

theorem data_eq (P C : ℕ) (source : List Bool) (xs : List Cell) (n : ℕ) (hit cur : Bool):
    (fun i=>Fin.addCases (raw P source xs n hit cur) (fun _ : Fin 1=>List.replicate C false) i)=
      data P C source xs n hit cur:=by
  funext i;fin_cases i <;> rfl

theorem heads_in (pos : ℕ):
    (fun i=>Fin.addCases (![pos,0,0,0,0,0,0] : Fin 7→ℕ) (fun _ : Fin 1=>0) i)=heads pos:=by
  funext i;fin_cases i <;> rfl

theorem heads_out (pos n c : ℕ):
    (fun i=>Fin.addCases (fun j=>if selected j then 0 else (![pos,n,n,n,c,0,0] : Fin 7→ℕ) j)
      (fun _ : Fin 1=>0) i)=heads pos:=by
  funext i;fin_cases i <;> rfl

def pads (P : ℕ):Fin 7→ℕ:=![0,0,0,0,P,P,P]
theorem raw_eq (P : ℕ) (source : List Bool) (xs : List Cell) (n : ℕ) (hit cur : Bool):
    (fun i=>ZeroPadding.pad (pads P i)
      ((![source,(masks xs) 0,(masks xs) 1,(masks xs) 2,CompareMachine.word n,[hit],[cur]] : Fin 7→List Bool) i))=
      raw P source xs n hit cur:=by
  funext i
  fin_cases i
  · exact ZeroPadding.pad_zero source
  · exact ZeroPadding.pad_zero ((masks xs) 0)
  · exact ZeroPadding.pad_zero ((masks xs) 1)
  · exact ZeroPadding.pad_zero ((masks xs) 2)
  · rfl
  · rfl
  · rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportReady
