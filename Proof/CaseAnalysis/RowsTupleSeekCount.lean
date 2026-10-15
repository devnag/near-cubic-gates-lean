import Proof.CaseAnalysis.RowsTupleSeekHeader

/-! Retain the already-read bottom count in the mask consumer's unary
stream. The count driver's false terminator is copied even when n is zero. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countWord (n : ℕ) := List.replicate n true++[false]
def countMachine (keep : Bool) : Machine 2 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q bits=>if q=0 then
    some ⟨if bits 0 then 0 else 1,![none,if keep then some (bits 0) else none],
      ![.right,if keep then .right else .stay]⟩ else none
def countCfg (q : Fin 2) (source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 2 2 :=
  ⟨q,fieldHeads pos out,fieldData source out⟩

theorem count_step (keep b : Bool) (pre tail out : List Bool) :
    step (countMachine keep) (countCfg 0 (pre++b::tail) pre.length out)=
      some (countCfg (if b then 0 else 1) (pre++b::tail) (pre.length+1)
        (out++selected keep [b])) := by
  simp only [step,countMachine,countCfg,Configuration.scanned,fieldHeads,fieldData,
    Matrix.cons_val_zero,Streaming.read_append,↓reduceIte,Option.map_some]
  apply congrArg some
  apply configuration_ext
  · rfl
  · cases keep <;> funext i <;> fin_cases i <;>
      simp [applyAction,HeadMove.apply,selected]
  · cases keep <;> funext i <;> fin_cases i <;>
      simp [applyAction,selected,Streaming.write_append]

theorem count_timed (keep : Bool) (pre tail out : List Bool) (n : ℕ) :
    Timed (countMachine keep) (n+1)
      (countCfg 0 (pre++countWord n++tail) pre.length out)
      (countCfg 1 (pre++countWord n++tail) (pre.length+n+1) (out++selected keep (countWord n))) := by
  induction n generalizing pre out with
  | zero=>simpa [countWord] using
      Timed.single (by rfl : (countMachine keep).halted 0=false) (count_step keep false pre tail out)
  | succ n ih=>
    have first := Timed.single (by rfl : (countMachine keep).halted 0=false)
      (count_step keep true pre (countWord n++tail) out)
    have last := ih (pre++[true]) (out++selected keep [true])
    simp only [List.length_append,List.length_singleton,List.append_assoc,List.cons_append,
      List.nil_append,↓reduceIte] at first last
    have all := first.trans last
    cases keep <;> simpa only [countWord,List.replicate_succ,List.cons_append,List.append_assoc,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,selected,Bool.false_eq_true,↓reduceIte,List.append_nil,List.nil_append] using all

theorem count_run (keep : Bool) (pre tail out : List Bool) (n : ℕ) :
    Step (countMachine keep) (n+1) (fieldHeads pre.length out) (fieldData (pre++countWord n++tail) out)
      (fieldHeads (pre.length+n+1) (out++selected keep (countWord n)))
      (fieldData (pre++countWord n++tail) (out++selected keep (countWord n))) := by
  obtain ⟨r,hr,rf,_⟩ := (count_timed keep pre tail out n).run (by rfl)
  exact Step.of_run hr (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
