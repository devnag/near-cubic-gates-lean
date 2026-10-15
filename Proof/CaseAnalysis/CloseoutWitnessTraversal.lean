import Proof.PCP.PCPPNativeCanonicalWalkControl
import Proof.PCP.PCPPNativeCanonicalTreeMeaning

namespace NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
open CanonicalBinaryProgram PCPPNativeCanonicalTree
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def nodeBudget (w : ℕ) := 262144*(w+1)^2+8*w+32
def atomStream (w : ℕ) (values : List ℕ) :=
  values.flatMap (fun a=>frame (SignedSortKey.binary w a))

structure Visit (t : BalancedTraversalTree) (x y : State) : Prop where
  path : Path 0 5 (t.nodeCount*nodeBudget x.core.bits.length) x y
  valid : y.Valid
  width : y.core.bits.length=x.core.bits.length
  capacity : y.capacity=x.capacity
  stack : y.stack=x.stack
  out : y.out=x.out++atomStream x.core.bits.length t.atoms
  count : y.count=x.count+t.atoms.length

theorem tree_empty_fields (code : ℕ) (h:tree code=.empty) :
    (Nat.unpair code).1≠1 ∧ (Nat.unpair code).1≠2 := by
  rw [tree] at h
  split_ifs at h with hb hl
  simp_all

theorem tree_leaf_fields (code a : ℕ) (h:tree code=.leaf a) :
    (Nat.unpair code).1=1 ∧ (Nat.unpair code).2=a := by
  rw [tree] at h
  split_ifs at h with hb hl
  simp_all

theorem tree_branch_fields (code : ℕ) (l r : BalancedTraversalTree)
    (h:tree code=.branch l r) :
    (Nat.unpair code).1=2 ∧
      tree (Nat.unpair (Nat.unpair code).2).1=l ∧
      tree (Nat.unpair (Nat.unpair code).2).2=r := by
  rw [tree] at h
  split_ifs at h with hb hl
  simp_all

theorem rightChild_width (d : Data) : (rightChild d).length=d.bits.length := by
  exact (RecoveryFixedUnpair.word_lengths (classified d).bits).2.trans
    (RecoveryChildSelection.word_length false d.bits)

theorem visit (t : BalancedTraversalTree) (x : State) (hx:x.Valid)
    (ht:tree (value x.core.bits)=t)
    (hspace:x.stack.length+t.nodeCount*(2*x.core.bits.length+2)≤x.capacity) :
    ∃ y,Visit t x y := by
  induction t generalizing x with
  | empty=>
    obtain ⟨h1,h2⟩:=tree_empty_fields _ ht
    refine ⟨afterCore x,?_,core_valid x hx,stepped_width x.core,rfl,rfl,?_,?_⟩
    · exact (core_empty x hx.1 h1 h2).mono (by
        have hb:=step_bound x.core
        simp only [BalancedTraversalTree.nodeCount,one_mul,nodeBudget]
        omega)
    · simp [afterCore,State.withCore,BalancedTraversalTree.atoms,atomStream]
    · rfl
  | leaf a=>
    obtain ⟨h1,ha⟩:=tree_leaf_fields _ _ ht
    have h2:(Nat.unpair (value x.core.bits)).1≠2:=by omega
    have hv:value (stepped x.core).bits=a:=by
      rw [stepped,if_neg (show ¬branch x.core from h2)]
      exact (classified_payload x.core).trans ha
    have hw:=stepped_width x.core
    have hb:(stepped x.core).bits=SignedSortKey.binary x.core.bits.length a:=by
      rw [←hv,←hw]
      exact (BoundedCounter.binary_of_value _).symm
    let y:=counted (leaf (afterCore x))
    have hy:y.Valid:=counted_valid _ (leaf_valid _ (core_valid x hx))
    refine ⟨y,?_,hy,hw,rfl,rfl,?_,?_⟩
    · exact ((core_leaf x hx.1 h1).trans
        ((copy_path (afterCore x) (core_valid x hx)).trans (count_path _))).mono (by
          have hs:=step_bound x.core
          simp only [afterCore,State.withCore,hw,BalancedTraversalTree.nodeCount,one_mul,nodeBudget]
          omega)
    · simp [y,counted,leaf,afterCore,State.withCore,BalancedTraversalTree.atoms,atomStream,hb]
    · rfl
  | branch l r il ir=>
    obtain ⟨hbranch,hl,hr⟩:=tree_branch_fields _ _ _ ht
    have hb:branch x.core:=hbranch
    have hw:=stepped_width x.core
    have hrw:=rightChild_width x.core
    have hvals:=branch_values x.core hb
    let leftEntry:=marked (pushed (afterCore x) (rightChild x.core))
    have hspace':x.stack.length+(2*x.core.bits.length+2)+
        l.nodeCount*(2*x.core.bits.length+2)+r.nodeCount*(2*x.core.bits.length+2)≤x.capacity:=by
      simpa only [BalancedTraversalTree.nodeCount,add_mul,one_mul,Nat.add_assoc] using hspace
    have hpush:(pushed (afterCore x) (rightChild x.core)).Valid:=
      pushed_valid _ _ (core_valid x hx) (by
        dsimp only [afterCore,State.withCore]
        rw [hrw]
        omega)
    have hleft:leftEntry.Valid:=marked_valid _ hpush (by
      dsimp only [pushed,afterCore,State.withCore]
      simp only [List.length_append,List.length_reverse,frame_length,hrw]
      omega)
    have hleftSpace:leftEntry.stack.length+l.nodeCount*(2*leftEntry.core.bits.length+2)≤leftEntry.capacity:=by
      dsimp only [leftEntry,marked,pushed,afterCore,State.withCore]
      simp only [List.length_append,List.length_singleton,List.length_reverse,frame_length,hw,hrw]
      omega
    obtain ⟨leftExit,hleftExit⟩:=il leftEntry hleft (by
      change tree (value (stepped x.core).bits)=l
      rw [hvals.1]
      exact hl) hleftSpace
    have hleftWidth:leftExit.core.bits.length=x.core.bits.length:=hleftExit.width.trans hw
    have hleftCap:leftExit.capacity=x.capacity:=hleftExit.capacity
    have hleftStack:leftExit.stack=(x.stack++(frame (rightChild x.core)).reverse)++[true]:=hleftExit.stack
    let pre:=x.stack++(frame (rightChild x.core)).reverse
    let popped:=restacked leftExit pre
    have hpre:pre.length≤leftExit.capacity:=by
      have hs:=hleftExit.valid.2.2.2
      rw [hleftStack,List.length_append,List.length_singleton] at hs
      exact (Nat.le_add_right _ _).trans hs
    have hpopped:popped.Valid:=restacked_valid _ _ hleftExit.valid hpre
    let rightEntry:=restored popped (rightChild x.core) x.stack
    have hright:rightEntry.Valid:=restored_valid _ _ _ hpopped
      (hrw.trans hleftWidth.symm) (by change x.stack.length≤leftExit.capacity;rw [hleftCap];exact hx.2.2.2)
    have hrightSpace:rightEntry.stack.length+r.nodeCount*(2*rightEntry.core.bits.length+2)≤rightEntry.capacity:=by
      dsimp only [rightEntry,restored,popped,restacked]
      rw [hrw,hleftCap]
      omega
    obtain ⟨rightExit,hrightExit⟩:=ir rightEntry hright (by
      change tree (value (rightChild x.core))=r
      rw [hvals.2]
      exact hr) hrightSpace
    have hp1:=push_path (afterCore x) (rightChild x.core) (core_valid x hx) (hrw.trans hw.symm) (by
      change (stepped x.core).tapes 18=ZeroPadding.pad x.capacity (frame (rightChild x.core))
      rw [hx.2.1]
      exact branch_right x.core hb)
    have hp2:=peek_path leftExit pre hleftStack hleftExit.valid.2.2.2
    have hp3:=pop_path popped (rightChild x.core) x.stack hpopped (hrw.trans hleftWidth.symm) rfl
    refine ⟨rightExit,?_,hrightExit.valid,hrightExit.width.trans hrw,
      hrightExit.capacity.trans hleftCap,hrightExit.stack,?_,?_⟩
    · exact ((core_branch x hx.1 hbranch).trans (hp1.trans ((mark_path _).trans
        (hleftExit.path.trans (hp2.trans (hp3.trans hrightExit.path)))))).mono (by
          have hs:=step_bound x.core
          dsimp only [leftEntry,marked,pushed,afterCore,State.withCore,rightEntry,restored]
          simp only [hw,hrw,BalancedTraversalTree.nodeCount,add_mul,one_mul,nodeBudget]
          omega)
    · rw [hrightExit.out]
      change leftExit.out++atomStream (rightChild x.core).length r.atoms=_
      rw [hleftExit.out,hrw]
      dsimp only [leftEntry,marked,pushed,afterCore,State.withCore]
      simp only [hw,BalancedTraversalTree.atoms,atomStream,List.flatMap_append,List.append_assoc]
    · rw [hrightExit.count]
      change leftExit.count+r.atoms.length=_
      rw [hleftExit.count]
      simp only [leftEntry,marked,pushed,afterCore,State.withCore,BalancedTraversalTree.atoms,
        List.length_append,Nat.add_assoc]

end NearCubicWires.RepairOrdinary.PCPPNativeCanonicalWalk
