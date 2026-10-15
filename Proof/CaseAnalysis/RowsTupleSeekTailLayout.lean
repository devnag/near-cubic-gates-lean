import Proof.CaseAnalysis.RowsTupleSeekPairsUnary

/-! Three original input streams and four append outputs share one parsed
bottom-count driver. Port updates preserve every other live cursor. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tailHeads (pos : Fin 3→ℕ) (out : Fin 4→List Bool) (dh : ℕ) : Fin 8→ℕ :=
  ![pos 0,(out 0).length,pos 1,(out 1).length,pos 2,(out 2).length,(out 3).length,dh]
def tailData (source : Fin 3→List Bool) (out : Fin 4→List Bool) (n : ℕ) : Fin 8→List Bool :=
  ![source 0,out 0,source 1,out 1,source 2,out 2,out 3,UnaryTemplate.tape n]
def streamSlots (j : Fin 3) : Fin 2→Fin 8 := ![⟨2*j.val,by omega⟩,⟨2*j.val+1,by omega⟩]
def bottomSlots : Fin 5→Fin 8 := ![0,1,2,3,7]
def countSlots : Fin 2→Fin 8 := ![7,6]
def outSlot (j : Fin 3) : Fin 4 := j.castAdd 1

theorem field_dock {s cost : ℕ} (p : Machine 2 s) (j : Fin 3)
    (source : Fin 3→List Bool) (pos : Fin 3→ℕ) (out : Fin 4→List Bool) (n dh endpoint : ℕ)
    (emitted : List Bool)
    (run : Step p cost (fieldHeads (pos j) (out (outSlot j))) (fieldData (source j) (out (outSlot j)))
      (fieldHeads endpoint emitted) (fieldData (source j) emitted)) :
    Step (RecoveryFocus.machine (streamSlots j) p) cost (tailHeads pos out dh) (tailData source out n)
      (tailHeads (Function.update pos j endpoint) (Function.update out (outSlot j) emitted) dh)
      (tailData source (Function.update out (outSlot j) emitted) n) := by
  apply dock_exact run (streamSlots j) (by fin_cases j <;> decide)
  · intro i;fin_cases j <;> fin_cases i <;> rfl
  · intro i;fin_cases j <;> fin_cases i <;> rfl
  · intro i;fin_cases j <;> fin_cases i <;> rfl
  · intro i;fin_cases j <;> fin_cases i <;> rfl
  · intro i hi
    fin_cases j <;> fin_cases i
    all_goals first | exact ⟨rfl,rfl⟩ | exact False.elim (hi 0 rfl) | exact False.elim (hi 1 rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
