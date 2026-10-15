import Proof.CaseAnalysis.RowsTupleSeekFrame
import Proof.MachineModel.Layout

/-! Each retained native bottom gate travels with exactly its declared
support frame. The same gate-count loop will execute this paired worker. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape RecoveryRootRound ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pairHeads (np sp : ℕ) (native support : List Bool) : Fin 4→ℕ :=
  Fin.addCases (m:=2) (n:=2) (motive:=fun _=>ℕ) (fieldHeads np native) (fieldHeads sp support)
def pairData (ns ss native support : List Bool) : Fin 4→List Bool :=
  Fin.addCases (m:=2) (n:=2) (motive:=fun _=>List Bool) (fieldData ns native) (fieldData ss support)
def supportSlots : Fin 2→Fin 4 := ![2,3]
def pairFirst (keep : Bool) := TapeEmbedding.machine 2 (frameMachine keep)
noncomputable def pairLast (keep : Bool) := RecoveryFocus.machine supportSlots (frameMachine keep)
noncomputable def pairMachine (keep : Bool) := Composition.machine (pairFirst keep) (pairLast keep)

theorem pair_run (keep : Bool) (np n nt sp s st native support : List Bool) :
    Step (pairMachine keep) (2*n.length+2*s.length+3)
      (pairHeads np.length sp.length native support)
      (pairData (np++frame n++nt) (sp++frame s++st) native support)
      (pairHeads (np.length+(frame n).length) (sp.length+(frame s).length)
        (native++selected keep (frame n)) (support++selected keep (frame s)))
      (pairData (np++frame n++nt) (sp++frame s++st)
        (native++selected keep (frame n)) (support++selected keep (frame s))) := by
  have first := (frame_run keep np n nt native).embed
    (fieldHeads sp.length support) (fieldData (sp++frame s++st) support)
  have last := (frame_run keep sp s st support).dock supportSlots (by decide)
    (pairHeads (np.length+(frame n).length) sp.length (native++selected keep (frame n)) support)
    (pairData (np++frame n++nt) (sp++frame s++st) (native++selected keep (frame n)) support)
    (by intro i;fin_cases i <;> rfl) (by intro i;fin_cases i <;> rfl)
  have last' := last.congr
    (show _=pairHeads (np.length+(frame n).length) (sp.length+(frame s).length)
      (native++selected keep (frame n)) (support++selected keep (frame s)) by
      funext i;fin_cases i
      · exact dockH_other supportSlots _ _ 0 (by decide)
      · exact dockH_other supportSlots _ _ 1 (by decide)
      · exact dockH_slot supportSlots (by decide) _ _ 0
      · exact dockH_slot supportSlots (by decide) _ _ 1)
    (show _=pairData (np++frame n++nt) (sp++frame s++st)
      (native++selected keep (frame n)) (support++selected keep (frame s)) by
      funext i;fin_cases i
      · exact install_other supportSlots _ _ 0 (by decide)
      · exact install_other supportSlots _ _ 1 (by decide)
      · exact install_slot supportSlots (by decide) _ _ 0
      · exact install_slot supportSlots (by decide) _ _ 1)
  have all := first.seq last'
  have time : (2*n.length+1)+1+(2*s.length+1)=2*n.length+2*s.length+3 := by omega
  rw [time] at all
  exact all

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
