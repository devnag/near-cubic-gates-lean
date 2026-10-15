import Proof.CaseAnalysis.CaseTwoWholeBlockReset

/-! One actual local XOR transition. The returned block bit is read once;
the accumulator is overwritten at its current zero head. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.XorStep
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q bits=>if q.val=0 then
    some ⟨1,![some (xor (bits 0) (bits 1)),none],fun _=>.stay⟩ else none
def input (parity bit : Bool) : Fin 2→List Bool:=![[parity],[bit]]
def output (parity bit : Bool) : Fin 2→List Bool:=![[xor parity bit],[bit]]
def final (parity bit : Bool) : Configuration 2 2:=⟨1,fun _=>0,output parity bit⟩
theorem bit_step (parity bit : Bool) :
    step machine (initialConfiguration machine (input parity bit))=some (final parity bit):=by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i;fin_cases i <;>rfl
  · funext i;fin_cases i <;>
      simp [applyAction,machine,initialConfiguration,input,final,output,Configuration.scanned,
        readTapeBit,writeTapeBit,List.getD]
theorem ready (parity bit : Bool) : ClockJoin.ReadyRun machine 1 (input parity bit) (output parity bit):=by
  have h:=Timed.single (by rfl) (bit_step parity bit)
  obtain ⟨r,hr,hf,hs⟩:=h.run (by rfl)
  exact ⟨r,hr,congrArg Configuration.tapes hf,by intro i;rw [hf];rfl,hs.le⟩

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.XorStep
