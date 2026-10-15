import Proof.CaseAnalysis.CaseTwoXorBody

/-! The fixed-copy accumulator begins with one paid write of false. The
three original words are untouched. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.XorInit
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 4 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then
    some ⟨1,fun i=>if i=3 then some false else none,fun _=>.stay⟩ else none
def input (words : Fin 3→List Bool) : Fin 4→List Bool:=![words 0,words 1,words 2,[]]
def output (words : Fin 3→List Bool) : Fin 4→List Bool:=![words 0,words 1,words 2,[false]]
def final (words : Fin 3→List Bool) : Configuration 4 2:=⟨1,fun _=>0,output words⟩
theorem init_step (words : Fin 3→List Bool) :
    step machine (initialConfiguration machine (input words))=some (final words):=by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i <;>
      simp [applyAction,machine,initialConfiguration,input,final,output,writeTapeBit]
theorem ready (words : Fin 3→List Bool) : ClockJoin.ReadyRun machine 1 (input words) (output words):=by
  have h:=Timed.single (by rfl) (init_step words)
  obtain ⟨r,hr,hf,hs⟩:=h.run (by rfl)
  exact ⟨r,hr,congrArg Configuration.tapes hf,by intro i;rw [hf];rfl,hs.le⟩

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.XorInit
