import Proof.CaseAnalysis.RecoveryGrammarPreparedStep

/-! Exact retained scalar values for the original fixed-count grammar.
The run theorems read these physical words; setup and row updates pay for them. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
open LocalBitMultitape RecoveryRootRound BoundedOracleStructuralCircuit OuterPCPRecovery
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rowIndex (q bound row : ℕ) : Fin 4→ℕ:=
  ![row*rowWidth q bound,row*rowWidth q bound+6,
    row*rowWidth q bound+6+boundedCircuitFieldLimit q bound,0]
def rowLimit (q bound : ℕ) : Fin 6→ℕ:=![6,boundedCircuitFieldLimit q bound,2,3,5,bound+1]
def rowUpper (q row : ℕ) : Fin 3→ℕ:=![0,q,row]
def selectedFields (p : Selection) (q bound row C : ℕ):=
  RecoveryBoundedGrammarPrototype.fields C (rowIndex q bound row p.index) p.value.val
    (rowLimit q bound p.limit) (rowUpper q row p.upper)
def selectedWord (p : Selection) (q bound row C : ℕ):=
  RecoveryBoundedRowReload.word (selectedFields p q bound row C)
def numbers (q bound row C : ℕ) : Fin 21→ℕ:=
  ![row*rowWidth q bound,row*rowWidth q bound+6,
    row*rowWidth q bound+6+boundedCircuitFieldLimit q bound,0,
    6,boundedCircuitFieldLimit q bound,2,3,5,bound+1,0,1,2,3,4,5,6,0,q,row,C]
def metadata (q bound row C B : ℕ) (extra : Fin 12→List Bool) : Fin 33→List Bool:=
  Fin.addCases (m:=21) (n:=12) (fun j=>ZeroPadding.pad B (List.replicate (numbers q bound row C j) true)) extra

theorem metadata_scalar (p : Selection) (q bound row C B P node : ℕ)
    (fields : Fin 78→List Bool) (out stack packet source : List Bool) (extra : Fin 12→List Bool) (j : Fin 5) :
    data fields node B P out stack packet source (metadata q bound row C B extra) (scalarPorts p j)=
      ZeroPadding.pad B (RecoveryBoundedGrammarPrototype.scalarValues C
        (rowIndex q bound row p.index) p.value.val (rowLimit q bound p.limit) (rowUpper q row p.upper) j) := by
  rcases p with ⟨pi,pl,pv,pu⟩
  fin_cases j
  · fin_cases pi <;> rfl
  · fin_cases pl <;> rfl
  · fin_cases pv <;> rfl
  · fin_cases pu <;> rfl
  · rfl

def tag (value : Fin 7) : Selection:=⟨0,0,value,0⟩
def first (value : Fin 7) : Selection:=⟨1,1,value,0⟩
def second (value : Fin 7) : Selection:=⟨2,1,value,0⟩
def firstLess (upper : Fin 3) : Selection:=⟨1,1,0,upper⟩
def secondLess (upper : Fin 3) : Selection:=⟨2,1,0,upper⟩
def foldTwo : Selection:=⟨3,2,0,0⟩
def foldThree : Selection:=⟨3,3,0,0⟩
def foldFive : Selection:=⟨3,4,0,0⟩
def foldRows : Selection:=⟨3,5,0,0⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarCold
