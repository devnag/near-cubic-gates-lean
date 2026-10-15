import Proof.CaseAnalysis.RecoveryRowPacketPaddedFocus

/-! The fixed physical print sequence equals the exact original fifteen
row fields. In particular, the native-width template keeps its final zero. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
open LocalBitMultitape RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def values (C F R count Q clauses : ℕ) : Fin 10→ℕ:=
  ![C,F,R,count,Q,clauses,6,6+F,0,R+1]
def scalarPort (i : Fin 10) : Fin 88:=⟨78+i.val,by omega⟩
def emitted (C F R count Q clauses : ℕ) : Fin 15→List Bool:=
  ![frame (ZeroPadding.pad C (List.replicate 6 true)),field false C,field true F,
    frame (ZeroPadding.pad C (List.replicate 6 true)),frame (ZeroPadding.pad C []),
    frame (ZeroPadding.pad C (List.replicate (6+F) true)),
    frame (ZeroPadding.pad C (List.replicate 6 true)),
    header true++frame (ZeroPadding.pad (R+1) (List.replicate R true)),
    frame (CompareMachine.word 6),frame (CompareMachine.word 5),field true count,
    frame (List.replicate 6 true),field false (6+F),field true Q,field true clauses]
def packet (C F R count Q clauses : ℕ):=
  (List.finRange 15).flatMap (emitted C F R count Q clauses)

theorem emitted_original (C F R count Q clauses : ℕ) (hC : 1≤C) (j : Fin 15) :
    emitted C F R count Q clauses j=frame (RecoveryBoundedRowPacket.fields C F R count Q clauses j) := by
  fin_cases j
  all_goals try rfl
  · change frame (ZeroPadding.pad C [])=frame (ZeroPadding.pad C (CompareMachine.word 0))
    apply congrArg frame
    obtain ⟨c,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega : C≠0)
    simp [ZeroPadding.pad,CompareMachine.word,List.replicate_succ]
  · change header true++frame (ZeroPadding.pad (R+1) (List.replicate R true))=
      frame (UnaryTemplate.tape R)
    simp only [ZeroPadding.pad,List.length_replicate,Nat.add_sub_cancel_left,List.replicate_one]
    rfl

theorem packet_original (C D F L R count Q clauses : ℕ) (hC : 1≤C) :
    packet C F R count Q clauses=
      RecoveryBoundedRowReload.word (RecoveryBoundedRowPrototype.fields C D F L R count Q clauses) := by
  have hp : RecoveryBoundedRowReload.ports=(List.finRange 15).map RecoveryBoundedRowPacket.port:=by decide
  rw [packet,RecoveryBoundedRowReload.word,CloseoutRowsPacketLoad.stream,hp,List.flatMap_map]
  apply congrArg (fun f : Fin 15→List Bool=>(List.finRange 15).flatMap f)
  funext j
  rw [emitted_original C F R count Q clauses hC j,RecoveryBoundedRowPacket.original]

theorem packet_order (C F R count Q clauses : ℕ) :
    packet C F R count Q clauses=
      emitted C F R count Q clauses 0++emitted C F R count Q clauses 1++
      emitted C F R count Q clauses 2++emitted C F R count Q clauses 3++
      emitted C F R count Q clauses 4++emitted C F R count Q clauses 5++
      emitted C F R count Q clauses 6++emitted C F R count Q clauses 7++
      emitted C F R count Q clauses 8++emitted C F R count Q clauses 9++
      emitted C F R count Q clauses 10++emitted C F R count Q clauses 11++
      emitted C F R count Q clauses 12++emitted C F R count Q clauses 13++
      emitted C F R count Q clauses 14 := by
  have hp : List.finRange 15=([0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] : List (Fin 15)):=by decide
  rw [packet,hp]
  simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
