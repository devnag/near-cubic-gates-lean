import Proof.Amplification.RecoveryPCPFormulaResumeSearchRequest

/-! One ordinary-oracle graph executes the source-field constructor then
its actual framed request through the fixed canonical-prefix search. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProof
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage BalancedCNFSATEncoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def requestSlots (i : Fin 796) : Fin 1184 := i.castAdd 388
def prefixSlots (i : Fin 389) : Fin 1184 :=
  if i=0 then 794 else ⟨795+i.val,by have hi:=i.isLt; omega⟩
theorem request_injective : Function.Injective requestSlots := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin 1184=>i.val) h)
theorem prefix_injective : Function.Injective prefixSlots := by
  intro i j h
  have hv:=congrArg (fun i : Fin 1184=>i.val) h
  apply Fin.ext
  dsimp [prefixSlots] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

def ports : Ports 1184 := ⟨by decide,1181,by decide,1139,by decide⟩
noncomputable def requestMachine := RecoveryFocus.machine requestSlots RecoveryPCPFormulaResumeSearchRequest.machine
noncomputable def pieces : Fin 2→Piece 1184 :=
  ![ordinary requestMachine,focused (RecoveryPrefixCold.program 1073741824 true) prefixSlots]
def next (j : Fin 2) (_ : Fin (pieces j).states) (_ : Fin 1184→Bool) : Option (Fin 2) :=
  if j=0 then some 1 else none
noncomputable def program := ports.program (graph pieces 0 next)
noncomputable def input (p : RawProjectionPCP) (R Q : Nat) : Fin 1184→List Bool :=
  Fin.addCases (m:=796) (n:=388) (motive:=fun _=>List Bool)
    (RecoveryPCPFormulaResumeSearchRequest.input p R Q) (fun _=>[])
def budget (R Q count : Nat) (words : List (List Bool)) (payload : Nat) :=
  RecoveryPCPFormulaResumeSearchRequest.budget R Q count words payload+2+
    RecoveryPrefixCold.budget 1073741824 payload (2^R)

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProof
