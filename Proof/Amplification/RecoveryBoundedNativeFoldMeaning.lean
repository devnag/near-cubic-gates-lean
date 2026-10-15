import Proof.Amplification.RecoveryBoundedNativeFoldNode

/-! The physical reverse stack order is exactly the original compiler's fold. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNative
open SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def foldNodes {n : ℕ} (conjunction : Bool) (base : ℕ) : List ℕ→List (BooleanNode n)
  | []=>[]
  | ref::refs=>(if conjunction then BooleanNode.and ref base else BooleanNode.or ref base)::
      foldNodes conjunction (base+1) refs

theorem foldNodes_append {n : ℕ} (conjunction : Bool) (base : ℕ) (xs ys : List ℕ) :
    foldNodes (n:=n) conjunction base (xs++ys)=
      foldNodes conjunction base xs++foldNodes conjunction (base+xs.length) ys := by
  induction xs generalizing base with
  | nil=>simp [foldNodes]
  | cons x xs ih=>
    simp only [List.cons_append,foldNodes,ih,List.cons_append,List.length_cons]
    have he : base+1+xs.length=base+(xs.length+1) := by omega
    rw [he]

theorem allSuffix_reverse {n : ℕ} (base : ℕ) (refs : List ℕ) :
    allSuffix (n:=n) base refs=[BooleanNode.const true]++foldNodes true base refs.reverse := by
  induction refs with
  | nil=>rfl
  | cons ref refs ih=>
    rw [allSuffix,ih,List.reverse_cons,foldNodes_append]
    simp [foldNodes]

end NearCubicWires.RepairOrdinary.RecoveryBoundedNative
