import Proof.CaseAnalysis.RowsTupleSeekTailRun

/-! These slices describe the existing four stream fields of one original
family term. They introduce no alternate circuit or coefficient encoding. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure TermSlices where
  top : List Bool
  coefficient : Fin 3→List Bool
  gates : List GatePair

def TermSlices.words (t : TermSlices) : Fin 4→List Bool :=
  ![natWord t.gates.length++frame t.top++nativeWord t.gates,supportWord t.gates,
    record (t.coefficient 0) (t.coefficient 1) (t.coefficient 2),countWord t.gates.length]
def TermSlices.cost (t : TermSlices) := headerCost t.gates.length+1+
  tailCost t.top (t.coefficient 0) (t.coefficient 1) (t.coefficient 2) t.gates
def appended (keep : Bool) (t : TermSlices) (out : Fin 4→List Bool) := fun i=>out i++selected keep (t.words i)
def withHeader (keep : Bool) (n : ℕ) (out : Fin 4→List Bool) :=
  Function.update out 0 (out 0++selected keep (natWord n))

theorem tail_appended (keep : Bool) (t : TermSlices) (out : Fin 4→List Bool) :
    tailOutput keep t.top (t.coefficient 0) (t.coefficient 1) (t.coefficient 2) t.gates
      (withHeader keep t.gates.length out)=appended keep t out := by
  cases keep <;> funext i <;> fin_cases i <;>
    simp [tailOutput,withHeader,appended,TermSlices.words,selected,List.append_assoc]

def rawSlots : Fin 8→Fin 20 := ![0,14,15,16,17,18,19,10]
def rawSourceSlots : Fin 3→Fin 20 := ![0,15,17]
def rawOutputSlots : Fin 4→Fin 20 := ![14,16,18,19]
def rawExtraHeads (pos : Fin 3→ℕ) (out : Fin 4→List Bool) : Fin 5→ℕ :=
  ![pos 1,(out 1).length,pos 2,(out 2).length,(out 3).length]
def rawExtraData (source : Fin 3→List Bool) (out : Fin 4→List Bool) : Fin 5→List Bool :=
  ![source 1,out 1,source 2,out 2,out 3]
noncomputable def rawFirst (keep : Bool) := TapeEmbedding.machine 5 (headerMachine keep)
noncomputable def rawLast (keep : Bool) := RecoveryFocus.machine rawSlots (tailMachine keep)
noncomputable def rawMachine (keep : Bool) := Composition.machine (rawFirst keep) (rawLast keep)
noncomputable def rawInput (keep : Bool) (source : Fin 3→List Bool) (pos : Fin 3→ℕ) (out : Fin 4→List Bool) :=
  TapeEmbedding.config (rawExtraHeads pos out) (rawExtraData source out) (headerEntry keep (source 0) (pos 0) (out 0))
noncomputable def rawEntry (keep : Bool) (source : Fin 3→List Bool) (pos : Fin 3→ℕ) (out : Fin 4→List Bool) :=
  (⟨(rawMachine keep).start,(rawInput keep source pos out).heads,(rawInput keep source pos out).tapes⟩ : Configuration 20 _)

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
