import Proof.Amplification.RecoveryCaseOneConstructFields

/-! Static wiring joins the actual selected hierarchy source prefix and
its fixed canonical-proof recovery and actual amplifier program in one ordinary-oracle graph. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOneHierarchy
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (amp : OrdinaryProgram)

def base (k : Nat) := RecoveryPCPFormulaResumeProofSource.tapes source k
def tapes (k : Nat) := base source k+RecoveryCaseOneConstruct.tapes amp
def sourceSlots (k : Nat) (i : Fin (base source k)) : Fin (tapes source amp k) := i.castAdd (RecoveryCaseOneConstruct.tapes amp)
def constructSlots (k : Nat) (i : Fin (RecoveryCaseOneConstruct.tapes amp)) : Fin (tapes source amp k) :=
  if i.val=0 then (RecoveryPCPFormulaResumeProofSource.port source k 0).castAdd (RecoveryCaseOneConstruct.tapes amp) else
  if i.val=28 then (RecoveryPCPFormulaResumeProofSource.port source k 1).castAdd (RecoveryCaseOneConstruct.tapes amp) else
  if i.val=66 then (RecoveryPCPFormulaResumeProofSource.port source k 2).castAdd (RecoveryCaseOneConstruct.tapes amp) else
  if i.val=67 then (RecoveryPCPFormulaResumeProofSource.port source k 3).castAdd (RecoveryCaseOneConstruct.tapes amp) else
  if i.val=68 then (RecoveryPCPFormulaResumeProofSource.port source k 4).castAdd (RecoveryCaseOneConstruct.tapes amp) else i.natAdd (base source k)
theorem source_injective (k : Nat) : Function.Injective (sourceSlots source amp k) := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin (tapes source amp k)=>i.val) h)
theorem port_injective (k : Nat) : Function.Injective (RecoveryPCPFormulaResumeProofSource.port source k) := by
  intro i j h
  apply RecoveryPCPFormulaResumeHierarchy.port_injective source k
  exact Fin.ext (congrArg (fun z : Fin (RecoveryPCPFormulaResumeProofSource.tapes source k)=>z.val) h)
theorem construct_injective (k : Nat) : Function.Injective (constructSlots source amp k) := by
  intro i j he
  have hv:=congrArg Fin.val he
  have p0 : (RecoveryPCPFormulaResumeProofSource.port source k 0).val<base source k :=
    (RecoveryPCPFormulaResumeProofSource.port source k 0).isLt
  have p1 : (RecoveryPCPFormulaResumeProofSource.port source k 1).val<base source k :=
    (RecoveryPCPFormulaResumeProofSource.port source k 1).isLt
  have p2 : (RecoveryPCPFormulaResumeProofSource.port source k 2).val<base source k :=
    (RecoveryPCPFormulaResumeProofSource.port source k 2).isLt
  have p3 : (RecoveryPCPFormulaResumeProofSource.port source k 3).val<base source k :=
    (RecoveryPCPFormulaResumeProofSource.port source k 3).isLt
  have p4 : (RecoveryPCPFormulaResumeProofSource.port source k 4).val<base source k :=
    (RecoveryPCPFormulaResumeProofSource.port source k 4).isLt
  apply Fin.ext
  dsimp only [constructSlots] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  all_goals first
    | omega
    | have hbad:=congrArg Fin.val (port_injective source k (Fin.ext hv)); norm_num at hbad

def ports (k : Nat) : Ports (tapes source amp k) :=
  ⟨by dsimp [tapes,RecoveryCaseOneConstruct.tapes]; omega,
    ((RecoveryCaseOneAmplifier.output amp).natAdd 1193).natAdd (base source k),
    by change base source k+(1193+(amp.tapeCount+1+26))≠0; omega,
    ((1139 : Fin 1193).castAdd (RecoveryCaseOneAmplifier.tapes amp)).natAdd (base source k),
    by change base source k+1139≠0; omega⟩
def sourceMachine (k CH Cpad : Nat) (code : List Bool) := RecoveryFocus.machine (sourceSlots source amp k)
  (RecoveryPCPFormulaResumeProofSource.machine source k CH Cpad code)
def pieces (k CH Cpad : Nat) (code : List Bool) : Fin 2→Piece (tapes source amp k) :=
  ![ordinary (sourceMachine source amp k CH Cpad code),focused (RecoveryCaseOneConstruct.program amp) (constructSlots source amp k)]
def next (k CH Cpad : Nat) (code : List Bool) (j : Fin 2)
    (_ : Fin (pieces source amp k CH Cpad code j).states) (_ : Fin (tapes source amp k)→Bool) : Option (Fin 2) :=
  if j=0 then some 1 else none
def program (k CH Cpad : Nat) (code : List Bool) :=
  (ports source amp k).program (graph (pieces source amp k CH Cpad code) 0 (next source amp k CH Cpad code))

end
end NearCubicWires.RepairSource.RecoveryCaseOneHierarchy
