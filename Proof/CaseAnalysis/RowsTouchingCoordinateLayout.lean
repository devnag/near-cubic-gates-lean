import Proof.CaseAnalysis.RowsTouchingGateFoldTyped
import Proof.CaseAnalysis.RowsTouchingChoiceRun
import Proof.CaseAnalysis.RowsTouchingCounterUpdate
import Proof.CaseAnalysis.RowsTouchingMaskShiftTyped

/-! One coordinate consumes the original support stream and retains the
same three masks, Pascal table, q/K drivers and scalar workspace. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Store where
  gate : Gate.Store
  left : List Bool
  right : List Bool
  flag : Bool
  carry : Bool

def supportCells (mask : List MaskShift.Cell):List SupportScan.Cell:=mask.map (fun x=>(false,x))
def choiceStore (st : Store):Choice.Store:=⟨st.left,st.right,st.gate.scratch,st.flag⟩
def chosen (w k h : ℕ) (st : Store):Store:=
  let picked:=Choice.after w st.gate.excluded st.gate.included k h (choiceStore st)
  {st with gate:={st.gate with scratch:=picked.scratch},left:=picked.left,right:=picked.right,flag:=picked.flag}
def extra (q K h w P E : ℕ) (st : Store):Fin 9→List Bool:=
  ![ZeroPadding.pad P (CompareMachine.word h),st.left,st.right,[st.flag],frame (binary w 0),
    CompareMachine.word q,[st.carry],List.replicate E false,ZeroPadding.pad P (CompareMachine.word K)]
def extraHeads:Fin 9→ℕ:=![0,0,0,0,0,1,0,0,0]
def heads (i : Fin 35):ℕ:=
  Fin.addCases (m:=26) (n:=9) (motive:=fun _=>ℕ) GateFoldReady.heads extraHeads i
def data (q G K k h w P C D E : ℕ) (source : List Bool) (mask : List MaskShift.Cell)
    (st : Store) (i : Fin 35):List Bool:=
  Fin.addCases (m:=26) (n:=9) (motive:=fun _=>List Bool)
    (GateFoldReady.data q k w P C D G source (supportCells mask) st.gate) (extra q K h w P E st) i

def choiceSlots:Fin 12→Fin 35:=![18,19,11,26,27,28,20,21,22,29,30,17]
def maskSlots:Fin 7→Fin 35:=![1,2,3,29,32,31,33]
def counterSlots:Fin 4→Fin 35:=![11,26,23,29]
def zeroSlots (right : Bool):Fin 4→Fin 35:=![30,if right then 19 else 18,17,21]
noncomputable def fold:=TapeEmbedding.machine 9 GateFoldReady.machine
noncomputable def choose:=RecoveryFocus.machine choiceSlots Choice.machine
noncomputable def shift:=RecoveryFocus.machine maskSlots MaskShift.machine
noncomputable def counters:=RecoveryFocus.machine counterSlots CounterUpdate.machine
noncomputable def zero (right : Bool):=RecoveryFocus.machine (zeroSlots right) RecoveryBoundedTapeCopy.machine
noncomputable def machine:=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine fold choose) shift) counters)
    (zero false)) (zero true)

def nextK (k : ℕ) (picked : Bool):ℕ:=if picked then k-1 else k
def nextH (h : ℕ) (picked : Bool):ℕ:=if picked then h else h-1
def zeroed (st : Store):Store:={st with gate:={st.gate with excluded:=0,included:=0}}
def cleared (st : Store) (right : Bool):Store:=
  let gate : Gate.Store := { st.gate with
    excluded := if right then st.gate.excluded else 0
    included := if right then 0 else st.gate.included }
  { st with gate := gate }

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Coordinate
