import Proof.Amplification.RecoveryCaseOneArchive
import Proof.Amplification.RecoveryCaseOnePayloadFrame

/-! Consumer-first Case-1 graph: retain the original dimension, recover the
same canonical table, then physically assemble its amplifier input. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneInput
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def archiveSlots : Fin 4→Fin 1193 := ![0,1184,1185,1186]
def proofSlots (i : Fin 1184) : Fin 1193 := i.castAdd 9
def payloadSlots (i : Fin 8) : Fin 1193 :=
  if i=0 then 1184 else if i=1 then 1181 else ⟨1185+i.val,by have hi:=i.isLt; omega⟩
theorem archive_injective : Function.Injective archiveSlots := by decide
theorem proof_injective : Function.Injective proofSlots := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin 1193=>i.val) h)
theorem payload_injective : Function.Injective payloadSlots := by
  intro i j h
  have hv:=congrArg (fun i : Fin 1193=>i.val) h
  apply Fin.ext
  dsimp [payloadSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega
def ports : Ports 1193 := ⟨by decide,1191,by decide,1139,by decide⟩
noncomputable def archiveMachine := RecoveryFocus.machine archiveSlots RecoveryCaseOneArchive.machine
noncomputable def payloadMachine := RecoveryFocus.machine payloadSlots RecoveryCaseOnePayload.framedMachine
noncomputable def pieces : Fin 3→Piece 1193 :=
  ![ordinary archiveMachine,focused RecoveryPCPFormulaResumeProof.program proofSlots,ordinary payloadMachine]
def next (j : Fin 3) (_ : Fin (pieces j).states) (_ : Fin 1193→Bool) : Option (Fin 3) :=
  if j=0 then some 1 else if j=1 then some 2 else none
noncomputable def program := ports.program (graph pieces 0 next)
noncomputable def input (p : RawProjectionPCP) (R Q : Nat) : Fin 1193→List Bool :=
  Fin.addCases (m:=1184) (n:=9) (motive:=fun _=>List Bool)
    (RecoveryPCPFormulaResumeProof.input p R Q) (fun _=>[])
def budget (R Q count : Nat) (words : List (List Bool)) (payload : Nat) (table : List Bool) :=
  RecoveryCaseOneArchive.budget R.bits+
    RecoveryPCPFormulaResumeProof.budget R Q count words payload+
    RecoveryCaseOnePayload.framedBudget R.bits table+3

end NearCubicWires.RepairSource.RecoveryCaseOneInput
