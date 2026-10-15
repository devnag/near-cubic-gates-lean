import Proof.Amplification.RecoveryCaseOneInputRun
import Proof.Amplification.RecoveryCaseOneRequest

/-! The actual recovered input is wired directly into the selected ordinary
schedule amplifier, in the same charged oracle graph. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneConstruct
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def tapes (p : OrdinaryProgram) := 1193+RecoveryCaseOneAmplifier.tapes p
def inputSlots (p : OrdinaryProgram) (i : Fin 1193) : Fin (tapes p) :=
  i.castAdd (RecoveryCaseOneAmplifier.tapes p)
def amplifierSlots (p : OrdinaryProgram) (i : Fin (RecoveryCaseOneAmplifier.tapes p)) : Fin (tapes p) :=
  if i.val=0 then inputSlots p 1191 else i.natAdd 1193
theorem input_injective (p : OrdinaryProgram) : Function.Injective (inputSlots p) := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin (tapes p)=>i.val) h)
theorem amplifier_injective (p : OrdinaryProgram) : Function.Injective (amplifierSlots p) := by
  intro i j he
  have hv:=congrArg (fun i : Fin (tapes p)=>i.val) he
  apply Fin.ext
  dsimp [amplifierSlots,inputSlots] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd] at hv <;> omega
def ports (p : OrdinaryProgram) : Ports (tapes p) :=
  ⟨by dsimp [tapes]; omega,(RecoveryCaseOneAmplifier.output p).natAdd 1193,by simp,
    inputSlots p 1139,by change (1139 : Nat)≠0; decide⟩
def last (p : OrdinaryProgram) := RecoveryFocus.machine (amplifierSlots p) (RecoveryCaseOneAmplifier.machine p)
def pieces (p : OrdinaryProgram) : Fin 2→Piece (tapes p) :=
  ![focused RecoveryCaseOneInput.program (inputSlots p),ordinary (last p)]
def next (p : OrdinaryProgram) (j : Fin 2) (_ : Fin (pieces p j).states) (_ : Fin (tapes p)→Bool) : Option (Fin 2) :=
  if j=0 then some 1 else none
def program (p : OrdinaryProgram) := (ports p).program (graph (pieces p) 0 (next p))
def input (program : OrdinaryProgram) (p : RawProjectionPCP) (R Q : Nat) : Fin (tapes program)→List Bool :=
  Fin.addCases (m:=1193) (n:=RecoveryCaseOneAmplifier.tapes program) (motive:=fun _=>List Bool)
    (RecoveryCaseOneInput.input p R Q) (fun _=>[])

theorem input_tapes (program : OrdinaryProgram) (p : RawProjectionPCP) (R Q : Nat) (i : Fin 1193) :
    input program p R Q (inputSlots program i)=RecoveryCaseOneInput.input p R Q i := by
  simp only [input,inputSlots,Fin.addCases_left]

theorem amplifier_input (program : OrdinaryProgram) (p : RawProjectionPCP) (R Q : Nat)
    (out : Fin 1193→List Bool) (word : List Bool) (hout : out 1191=frame word)
    (i : Fin (RecoveryCaseOneAmplifier.tapes program)) :
    install (inputSlots program) (input program p R Q) out (amplifierSlots program i)=
      RecoveryCaseOneAmplifier.input program word i := by
  rw [RecoveryCaseOneAmplifier.input_lookup]
  by_cases hi : i.val=0
  · simp only [amplifierSlots,hi,ite_true]
    exact (install_slot (inputSlots program) (input_injective program) _ out 1191).trans hout
  · simp only [amplifierSlots,hi,ite_false]
    rw [install_other _ _ _ _ (by
      intro j h
      have hv:=congrArg (fun i : Fin (tapes program)=>i.val) h
      have hj:=j.isLt
      change j.val=1193+i.val at hv
      omega)]
    simp only [input,Fin.addCases_right]

end
end NearCubicWires.RepairSource.RecoveryCaseOneConstruct
