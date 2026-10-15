import Proof.CaseAnalysis.RowsTupleSeekIndexed

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tupleWord {n : ℕ} (js : List (Fin n)) := js.flatMap (fun j=>ExtIncidence.block j.val)
def tupleOutput (ts : List TermSlices) (js : List (Fin ts.length)) (out : Fin 4 → List Bool) :=
  fun i=>out i++js.flatMap (fun j=>(ts[j]).words i)
noncomputable def tupleEntry (ts : List TermSlices) (C D ip : ℕ) (index : List Bool) (out : Fin 4 → List Bool) :=
  (⟨indexedMachine.start,RawLoop.heads (familyHeads (fun _=>0) out) ip,
    RawLoop.data (familyData C D (familyWords ts) out) index⟩ : Configuration 26 _)
noncomputable def tupleMachine := RepeatMachine.machine indexedMachine (fun _ _=>true)
def tupleBudget (C D terms count : ℕ) := count*(indexedCost C D terms+3)+3

theorem indexed_family_run (ts : List TermSlices) (j : Fin ts.length) (C D : ℕ)
    (hC : ∀ t∈ts,t.cost+1 ≤ C) (hD : ∀ i,(familyWords ts i).length ≤ D)
    (pre tail : List Bool) (out : Fin 4 → List Bool) :
    Step indexedMachine (indexedCost C D ts.length)
      (tupleEntry ts C D pre.length (pre++ExtIncidence.block j.val++tail) out).heads
      (tupleEntry ts C D pre.length (pre++ExtIncidence.block j.val++tail) out).tapes
      (tupleEntry ts C D (pre.length+(ExtIncidence.block j.val).length)
        (pre++ExtIncidence.block j.val++tail) (appended true ts[j] out)).heads
      (tupleEntry ts C D (pre.length+(ExtIncidence.block j.val).length)
        (pre++ExtIncidence.block j.val++tail) (appended true ts[j] out)).tapes := by
  have split : ts.take j.val++ts[j]::ts.drop (j.val+1)=ts := by
    simp only [Fin.getElem_fin]
    rw [←List.singleton_append,←List.append_assoc,←List.take_succ_eq_append_getElem j.isLt,List.take_append_drop]
  have bound : ∀ a∈ts.take j.val++[ts[j]],a.cost+1 ≤ C := by
    intro a ha
    rcases List.mem_append.mp ha with ha|ha
    · exact hC a (List.mem_of_mem_take ha)
    · simp only [List.mem_singleton] at ha;subst a;exact hC _ (List.getElem_mem j.isLt)
  have run := indexed_run (ts.take j.val) (ts.drop (j.val+1)) ts[j] out C D bound
    (by rw [split];exact hD) pre tail
  rw [split,List.length_take,Nat.min_eq_left j.isLt.le] at run
  exact run.enlarge (by unfold indexedCost;gcongr;exact j.isLt.le)

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
