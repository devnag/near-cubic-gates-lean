import Proof.Amplification.RecoveryCaseOnePaddedEvaluationRun

/-! The actual hierarchy constructor preserves a target address on its
fresh bank, then executes the generated-arity crop and padded evaluation. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOnePaddedBit
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound OrdinaryOracleCompose
open SourceInterfaces VerifierDecoding ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (amp : OrdinaryProgram)

def base (k : Nat) := RecoveryCaseOneHierarchy.tapes source amp k
def tapes (k : Nat) := base source amp k+45
def sourceSlots (k : Nat) (i : Fin (base source amp k)) : Fin (tapes source amp k) := i.castAdd 45
def evalSlots (k : Nat) (i : Fin 46) : Fin (tapes source amp k) :=
  if i.val=0 then (RecoveryCaseOneHierarchy.ports source amp k).outputTape.castAdd 45 else
    ⟨base source amp k+i.val-1,by have hi:=i.isLt; dsimp [tapes]; omega⟩
theorem source_injective (k : Nat) : Function.Injective (sourceSlots source amp k) := by
  intro i j h; exact Fin.ext (congrArg (fun i : Fin (tapes source amp k)=>i.val) h)
theorem eval_injective (k : Nat) : Function.Injective (evalSlots source amp k) := by
  intro i j h
  have hv:=congrArg (fun i : Fin (tapes source amp k)=>i.val) h
  have hb : (RecoveryCaseOneHierarchy.ports source amp k).outputTape.val<base source amp k :=
    (RecoveryCaseOneHierarchy.ports source amp k).outputTape.isLt
  apply Fin.ext
  dsimp only [evalSlots] at hv
  split_ifs at hv <;> simp only [Fin.val_castAdd] at hv <;> omega
def ports (k : Nat) : Ports (tapes source amp k) :=
  ⟨by dsimp [tapes]; omega,(43 : Fin 45).natAdd (base source amp k),by simp,
    (RecoveryCaseOneHierarchy.ports source amp k).queryTape.castAdd 45,
    (RecoveryCaseOneHierarchy.ports source amp k).queryFresh⟩
def last (k : Nat) := RecoveryFocus.machine (evalSlots source amp k) RecoveryCaseOnePaddedEvaluation.machine
def pieces (k CH Cpad : Nat) (code : List Bool) : Fin 2→Piece (tapes source amp k) :=
  ![focused (RecoveryCaseOneHierarchy.program source amp k CH Cpad code) (sourceSlots source amp k),
    ordinary (last source amp k)]
def next (k CH Cpad : Nat) (code : List Bool) (j : Fin 2)
    (_ : Fin (pieces source amp k CH Cpad code j).states) (_ : Fin (tapes source amp k)→Bool) : Option (Fin 2) :=
  if j=0 then some 1 else none
def program (k CH Cpad : Nat) (code : List Bool) :=
  (ports source amp k).program (graph (pieces source amp k CH Cpad code) 0 (next source amp k CH Cpad code))
def input (k : Nat) (word address : List Bool) : Fin (tapes source amp k)→List Bool :=
  Fin.addCases (m:=base source amp k) (n:=45) (motive:=fun _=>List Bool)
    (SourceHandoff.sourceTapes word) (fun j=>if j.val=16 then frame address else [])

theorem source_input (k : Nat) (word address : List Bool) (i : Fin (base source amp k)) :
    input source amp k word address (sourceSlots source amp k i)=SourceHandoff.sourceTapes word i := by
  simp only [input,sourceSlots,Fin.addCases_left]

theorem eval_output (k : Nat) : evalSlots source amp k 44=(43 : Fin 45).natAdd (base source amp k) := by
  apply Fin.ext
  change base source amp k+44-1=base source amp k+43
  omega

end
end NearCubicWires.RepairSource.RecoveryCaseOnePaddedBit
