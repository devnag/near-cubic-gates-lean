import Proof.CaseAnalysis.RowsCircuitBodySupport
import Proof.CaseAnalysis.RowsCircuitBottomLoop

/-! The physical published bank facts shared by the original circuit body
and its support-retaining extension. These facts describe the same tapes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBody
open LocalBitMultitape RecoveryRootRound RepairRepresentation
open CloseoutRowsCircuitBottomLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Fields (threshold : Bool) (C core retained : ℕ) (words : List (List Bool))
    (top out members bits : List Bool) (initial L W : ℕ) (A : Fin 1703 → List Bool) : Prop where
  input : ∀ b∈words,2*b.length+1 ≤ C
  capacity : ∀ b∈words,2*CloseoutRowsGateMeasured.budget b+4 ≤ C
  positive : threshold=true → 1 ≤ initial
  resource : 32*(descriptions core words initial words.length+words.length+
    wires threshold core 1 members words 0 words.length+3) ≤ C
  source : (words.flatMap frame).length ≤ C ∧ 1+2*words.length ≤ C
  retainedFits : retained ≤ C
  header : EquationHeaderAppend.budget retained+1 ≤ C
  topFits : 2*top.length+1 ≤ C
  gate : ∀ j,(A (CloseoutRowsCircuitAllocate.gate j)).length ≤ C
  driver : A 1694=List.replicate C true
  log : A 1695=List.replicate (C+1) false
  retained : A 1702=ZeroPadding.pad C (List.replicate retained true)
  topWord : A 1701=ZeroPadding.pad C (frame top)
  stream : A 1688=out
  scratch : A 1696=List.replicate C false
  count : A 624=UnaryTemplate.tape words.length
  ports : ∀ i : Fin 7,A (![1689,1690,297,1692,1693,1697,1674] i)=
    (![List.replicate initial true,[],words.flatMap frame,members,[true],ZeroPadding.pad C [true],UnaryTemplate.tape core] : Fin 7 → List Bool) i
  rawCount : A 622=List.replicate words.length true
  capL : A 1699=List.replicate L true
  capW : A 1698=List.replicate W true
  flag : A 1700=[]
  membersFits : members.length ≤ C+1
  privateSupport : ∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (A i).length ≤ C+1
  raw : A 1=frame bits

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBody
