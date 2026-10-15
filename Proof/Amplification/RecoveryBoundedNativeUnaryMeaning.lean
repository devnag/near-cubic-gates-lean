import Proof.Amplification.RecoveryBoundedNativeUnaryLoop

/-! The checked runtime loop emits the original unary guard's forward
literal schedule and saves precisely its compiler references, in order. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryLoop
open SourceInterfaces RepairRepresentation RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def items {n : ℕ} (index offset value : ℕ) : (count : ℕ)→index+count ≤ n→List (Item n)
  | 0,_=>[]
  | count+1,h=>(⟨index,by omega⟩,RecoveryBoundedNativeUnaryFlag.negative value offset)::
      items (index+1) (offset+1) value count (by omega)
def stackWords (refs : List ℕ) := refs.flatMap fun ref=>(frame (List.replicate ref true)).reverse

theorem items_ofFn {n : ℕ} (count index offset value : ℕ) (h : index+count ≤ n) :
    items index offset value count h=List.ofFn (fun i : Fin count=>
      (⟨index+i.val,by omega⟩,RecoveryBoundedNativeUnaryFlag.negative value (offset+i.val)) : Fin count→Item n) := by
  induction count generalizing index offset with
  | zero=>rfl
  | succ count ih=>
    rw [items,List.ofFn_succ]
    congr 1
    rw [ih]
    congr 1
    funext i
    simp only [Fin.val_succ,Nat.add_comm,Nat.add_left_comm]

theorem iterate_indices (count value : ℕ) (a : State) :
    (a.iterate value count).index=a.index+count ∧ (a.iterate value count).offset=a.offset+count := by
  induction count generalizing a with
  | zero=>exact ⟨rfl,rfl⟩
  | succ count ih=>
    have h:=ih (a.next value)
    simpa only [State.iterate,State.next,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem iterate_schedule {n : ℕ} (count value : ℕ) (a : State) (h : a.index+count ≤ n) :
    let selected:=items a.index a.offset value count h
    (a.iterate value count).position=a.position+prefixCount selected ∧
      (a.iterate value count).out=a.out++(literalPrefix a.position selected).flatMap PCPPRequestNodeSchema.native ∧
      (a.iterate value count).stack=a.stack++stackWords (literalReferences a.position selected) := by
  induction count generalizing a with
  | zero=>simp [State.iterate,items,prefixCount,literalPrefix,literalReferences,stackWords]
  | succ count ih=>
    have nextBound : (a.next value).index+count ≤ n := by dsimp only [State.next]; omega
    have hs:=ih (a.next value) nextBound
    let negative:=RecoveryBoundedNativeUnaryFlag.negative value a.offset
    let i : Fin n:=⟨a.index,by omega⟩
    have hbytes := RecoveryBoundedNativeLiteral.emitted_expr i a.position negative
    have hpos : a.position+negative.toNat+1=a.position+(1+negative.toNat) := by omega
    dsimp only at hs ⊢
    simp only [State.iterate,items,prefixCount,literalPrefix,literalReferences,literalCount]
    change (State.iterate value count (a.next value)).position=_ ∧ _
    rw [hs.1,hs.2.1,hs.2.2]
    simp only [State.next]
    change a.position+negative.toNat+1+prefixCount (items (a.index+1) (a.offset+1) value count _)=_ ∧ _
    rw [hpos]
    constructor
    · dsimp only [negative]
      omega
    constructor
    · rw [List.flatMap_append,←List.append_assoc]
      congr 1
      exact congrArg (fun bits=>a.out++bits) hbytes
    · simp only [stackWords,List.flatMap_cons,RecoveryBoundedNativeLiteralStack.stackWord,List.append_assoc]
      rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryLoop
