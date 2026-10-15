import Proof.Supplier.RowTupleCursorBody

/-! Consume the exact checked enumerator grammar. Each selected tuple has
its ordinary digit blocks followed by the extra zero bit and terminator;
the three corresponding physical cells are passed by paid transitions. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFrame
open LocalBitMultitape RecoveryExecution SignedSortKey RowTupleDigits
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def trailer : List Bool := [true,false,false]

theorem encoded_word (w : ℕ) (ds : List ℕ) (hd : ∀ d∈ds,d<2^w) :
    frame (binary (w*ds.length+1) (encode w ds))=RowTupleFilterLoop.word w ds++trailer := by
  have hv := congrArg RadixSemantics.value (binary_encode w ds hd)
  rw [binary_value (w*ds.length) (encode w ds) (encode_bound w ds hd)] at hv
  have h:=BoundedCounter.binary_of_value ((ds.flatMap (binary w))++[false])
  simp only [List.length_append,blocks_length,List.length_cons,List.length_nil,Nat.zero_add,
    RadixSemantics.value_append,RadixSemantics.value,Bool.toNat,Nat.mul_zero,Nat.add_zero,←hv] at h
  simp only [Bool.cond_false,Nat.mul_zero,Nat.add_zero] at h
  rw [h]
  rw [Streaming.frame_append]
  simp [frame,Streaming.marks,RowTupleFilterLoop.word,trailer,List.flatMap_assoc]

def skip : Machine 48 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==3
  rule:=fun q _=>if h:q.val<3 then some
    ⟨⟨q.val+1,by omega⟩,fun _=>none,fun i=>if i=44 then .right else .stay⟩ else none

def cfg (q : Fin 4) (heads : Fin 48→ℕ) (src : Fin 48→List Bool) : Configuration 48 4 :=
  ⟨q,Function.update heads 44 (heads 44+q.val),src⟩

theorem skip_step (q : Fin 4) (hq:q.val<3) (heads : Fin 48→ℕ) (src : Fin 48→List Bool) :
    step skip (cfg q heads src)=some (cfg ⟨q.val+1,by omega⟩ heads src) := by
  simp only [step,skip,cfg,hq,↓reduceDIte,Option.map_some,Option.some.injEq]
  apply configuration_ext
  · rfl
  · funext i
    by_cases hi:i=44
    · subst i; simp [applyAction,HeadMove.apply,Nat.add_assoc]
    · simp [applyAction,HeadMove.apply,hi]
  · rfl

theorem skip_run (heads : Fin 48→ℕ) (src : Fin 48→List Bool) :
    ∃ r,runFrom skip 3 ⟨0,heads,src⟩=some r ∧
      r.final.heads=Function.update heads 44 (heads 44+3) ∧ r.final.tapes=src ∧ r.steps=3 := by
  have a:=Timed.single (show skip.halted (cfg 0 heads src).control=false by rfl) (skip_step 0 (by decide) heads src)
  have b:=Timed.single (show skip.halted (cfg 1 heads src).control=false by rfl) (skip_step 1 (by decide) heads src)
  have c:=Timed.single (show skip.halted (cfg 2 heads src).control=false by rfl) (skip_step 2 (by decide) heads src)
  obtain ⟨r,hr,rf,rs⟩:=(a.trans b |>.trans c).run (by rfl)
  have hi : cfg 0 heads src=(⟨0,heads,src⟩ : Configuration 48 4) := by
    apply configuration_ext
    · rfl
    · simp [cfg]
    · rfl
  rw [hi] at hr
  exact ⟨r,hr,by rw [rf]; rfl,by rw [rf]; rfl,rs⟩

end NearCubicWires.RepairOrdinary.RowTupleFrame
