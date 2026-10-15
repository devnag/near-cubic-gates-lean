import Proof.CaseAnalysis.RecoveryUniversalNodeMeaning

/-! Literal original node bank plus its packet, retained row/tag index and
two fixed tag counters. The complete bank is retained at each call boundary. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalNodeBank
open LocalBitMultitape RepairRepresentation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraHeads : Fin 4→ℕ:=![0,0,1,1]
def extraData (C tag : ℕ) (packet : List Bool) : Fin 4→List Bool:=
  ![ZeroPadding.pad C packet,List.replicate tag true,CompareMachine.word 6,CompareMachine.word 5]
def heads (out : List Bool) : Fin 55→ℕ:=
  Fin.addCases (m:=51) (n:=4) (motive:=fun _=>ℕ) (RecoveryBoundedNodeAddress.heads out) extraHeads
def data (index base C D value limit total L : ℕ) (out source : List Bool)
    (secondIndex tag left right constant : ℕ) (address : List Bool) (count : ℕ) (packet : List Bool) : Fin 55→List Bool:=
  Fin.addCases (m:=51) (n:=4) (motive:=fun _=>List Bool)
    (RecoveryBoundedNodeAddress.data index base C D value limit total L out source secondIndex
      (ZeroPadding.pad C (List.replicate left true)) (ZeroPadding.pad C (List.replicate right true))
      (ZeroPadding.pad C (List.replicate constant true)) address count) (extraData C tag packet)
def prepared (A : Fin 55→List Bool) (constant current tag C : ℕ):=
  RecoveryBoundedNodeTagPrepare.output (RecoveryBoundedNodeTagPacket.output A constant current C) tag C

theorem packet_heads (out : List Bool) (j : Fin 9) :
    heads out (RecoveryBoundedNodeTagPacket.slots j)=0 := by fin_cases j <;> rfl
theorem prepare_heads (out : List Bool) (j : Fin 7) :
    heads out (RecoveryBoundedNodeTagPrepare.slots j)=0 := by fin_cases j <;> rfl
theorem selector_heads (out : List Bool) (j : Fin 44) :
    heads out (RecoveryBoundedNodeTagSelect.slots j)=RecoveryBoundedSelectorReuse.finalHeads out j := by
  fin_cases j <;> rfl

theorem packet_tapes (index base C D value limit total L : ℕ) (out source : List Bool)
    (secondIndex tag left right constant : ℕ) (address : List Bool) (count : ℕ) (j : Fin 9) :
    data index base C D value limit total L out source secondIndex tag left right constant address count []
      (RecoveryBoundedNodeTagPacket.slots j)=RecoveryBoundedNodeTagPacket.input constant base C D j := by
  fin_cases j <;> rfl

theorem prepare_tapes (index base C D value limit total L : ℕ) (out source : List Bool)
    (secondIndex tag left right constant : ℕ) (address : List Bool) (count : ℕ) (j : Fin 7) :
    RecoveryBoundedNodeTagPacket.output
      (data index base C D value limit total L out source secondIndex tag left right constant address count []) constant base C
      (RecoveryBoundedNodeTagPrepare.slots j)=RecoveryBoundedTagPrepare.data tag index value C 0 j := by
  rw [RecoveryBoundedNodeTagPrepare.packet_unchanged]
  fin_cases j <;> rfl

theorem selector_tapes (index base C D value limit total L : ℕ) (out source : List Bool)
    (secondIndex tag left right constant : ℕ) (address : List Bool) (count : ℕ) (j : Fin 44) :
    prepared (data index base C D value limit total L out source secondIndex tag left right constant address count [])
      constant base tag C (RecoveryBoundedNodeTagSelect.slots j)=
        RecoveryBoundedSelectorReuse.finalData tag (base+4) C D 0 6 5 L out
          (ZeroPadding.pad C (RecoveryBoundedTagPacket.word constant base)) j := by
  rw [RecoveryBoundedNodeTagSelect.local_data]
  fin_cases j <;> rfl

theorem selected_heads (out result : List Bool) :
    RecoveryBoundedNodeTagSelect.outputHeads (heads out) result=heads result := by
  funext i
  fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedUniversalNodeBank
