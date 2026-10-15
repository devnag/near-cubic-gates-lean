import Proof.PCP.VerifierDecodingTagScan

/-! The final literal code-length test. The parser reaches this transition
only after consuming the required fields; the retained frame delimiter then
certifies exact exhaustion without computing a separate length expression. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.DelimiterMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val ≠ 0
  rule := fun q bits => if q.val = 0 then
    some ⟨if bits 0 then 2 else 1,fun _ => none,fun _ => .stay⟩ else none

def cfg (state : Fin 3) (pre rest : List Bool) : Configuration 1 3 :=
  ⟨state,fun _ => pre.length,fun _ => pre++frame rest⟩

theorem delimiter_step (pre rest : List Bool) :
    step machine (cfg 0 pre rest) = some (cfg (if rest=[] then 1 else 2) pre rest) := by
  cases rest with
  | nil =>
    simp [step,machine,cfg,Configuration.scanned,RepairOrdinary.frame,Streaming.read_append]
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction,HeadMove.apply]
    · rfl
  | cons bit rest =>
    simp [step,machine,cfg,Configuration.scanned,RepairOrdinary.frame,Streaming.read_append]
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction,HeadMove.apply]
    · rfl

theorem delimiter_run (pre rest : List Bool) :
    ∃ receipt, runFrom machine 1 (cfg 0 pre rest) = some receipt ∧
      receipt.final = cfg (if rest=[] then 1 else 2) pre rest ∧ receipt.steps = 1 := by
  exact (Timed.single (by rfl : machine.halted (0 : Fin 3) = false) (delimiter_step pre rest)).run
    (by cases rest <;> rfl)

end NearCubicWires.RepairSource.VerifierDecoding.DelimiterMachine
