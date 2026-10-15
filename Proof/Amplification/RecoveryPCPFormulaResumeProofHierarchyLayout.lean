import Proof.Amplification.RecoveryPCPFormulaResumeProofSource

/-! Static wiring joins the actual selected hierarchy source prefix and
its fixed canonical-proof recovery program in one ordinary-oracle graph. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProofHierarchy
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

def base (k : Nat) := RecoveryPCPFormulaResumeProofSource.tapes source k
def tapes (k : Nat) := base source k+1184
def sourceSlots (k : Nat) (i : Fin (base source k)) : Fin (tapes source k) := i.castAdd 1184
def proofSlots (k : Nat) (i : Fin 1184) : Fin (tapes source k) :=
  if i.val=0 then (RecoveryPCPFormulaResumeProofSource.port source k 0).castAdd 1184 else
  if i.val=28 then (RecoveryPCPFormulaResumeProofSource.port source k 1).castAdd 1184 else
  if i.val=66 then (RecoveryPCPFormulaResumeProofSource.port source k 2).castAdd 1184 else
  if i.val=67 then (RecoveryPCPFormulaResumeProofSource.port source k 3).castAdd 1184 else
  if i.val=68 then (RecoveryPCPFormulaResumeProofSource.port source k 4).castAdd 1184 else i.natAdd (base source k)
theorem source_injective (k : Nat) : Function.Injective (sourceSlots source k) := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin (tapes source k)=>i.val) h)
theorem port_injective (k : Nat) : Function.Injective (RecoveryPCPFormulaResumeProofSource.port source k) := by
  intro i j h
  apply RecoveryPCPFormulaResumeHierarchy.port_injective source k
  exact Fin.ext (congrArg (fun z : Fin (RecoveryPCPFormulaResumeProofSource.tapes source k)=>z.val) h)
theorem proof_injective (k : Nat) : Function.Injective (proofSlots source k) := by
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
  dsimp only [proofSlots] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd,Fin.val_natAdd] at hv
  all_goals first
    | omega
    | have hbad:=congrArg Fin.val (port_injective source k (Fin.ext hv)); norm_num at hbad

def ports (k : Nat) : Ports (tapes source k) :=
  ⟨by dsimp [tapes]; omega,(1181 : Fin 1184).natAdd (base source k),by simp,
    (1139 : Fin 1184).natAdd (base source k),by simp⟩
def sourceMachine (k CH Cpad : Nat) (code : List Bool) := RecoveryFocus.machine (sourceSlots source k)
  (RecoveryPCPFormulaResumeProofSource.machine source k CH Cpad code)
def pieces (k CH Cpad : Nat) (code : List Bool) : Fin 2→Piece (tapes source k) :=
  ![ordinary (sourceMachine source k CH Cpad code),focused RecoveryPCPFormulaResumeProof.program (proofSlots source k)]
def next (k CH Cpad : Nat) (code : List Bool) (j : Fin 2)
    (_ : Fin (pieces source k CH Cpad code j).states) (_ : Fin (tapes source k)→Bool) : Option (Fin 2) :=
  if j=0 then some 1 else none
def program (k CH Cpad : Nat) (code : List Bool) :=
  (ports source k).program (graph (pieces source k CH Cpad code) 0 (next source k CH Cpad code))

end
end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeProofHierarchy
