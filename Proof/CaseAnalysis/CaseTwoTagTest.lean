import Proof.CaseAnalysis.CaseTwoFieldReady

/-! The original tags are in 0..5. Read the fifth bit of the recovered raw
unary tag: it is true exactly at the output sentinel. This finite scan keeps
the private native tag buffer separate from the eventual node stream. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.TagTest
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 10 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==9
  rule:=fun q bits=>if h:q.val<9 then
    some ⟨⟨q.val+1,by omega⟩,
      if q.val=4 then ![none,some (bits 0)] else fun _=>none,
      if q.val<4 then ![.right,.stay] else if q.val=4 then fun _=>.stay else ![.left,.stay]⟩
    else none

theorem raw_ready (tag : Fin 6) (old : Bool) :
    ReadyRun machine 9 ![List.replicate tag.val true,[old]]
      ![List.replicate tag.val true,[decide (tag.val=5)]] := by
  letI : DecidableEq (Configuration 2 10):=fun a b=>decidable_of_iff
    (a.control=b.control ∧ a.heads=b.heads ∧ a.tapes=b.tapes)
    (by cases a;cases b;simp only [Configuration.mk.injEq])
  letI : DecidableEq (ExecutionReceipt 2 10):=fun a b=>decidable_of_iff
    (a.final=b.final ∧ a.steps=b.steps ∧ a.peakTapeCells=b.peakTapeCells)
    (by cases a;cases b;simp only [ExecutionReceipt.mk.injEq])
  refine ⟨⟨⟨9,fun _=>0,_⟩,9,tag.val+1⟩,?_,rfl,fun _=>rfl,rfl⟩
  fin_cases tag <;> cases old <;> decide

theorem ready (tag : Fin 6) (old : Bool) (C : ℕ) :
    ReadyRun machine 9
      ![ZeroPadding.pad C (List.replicate tag.val true),ZeroPadding.pad C [old]]
      ![ZeroPadding.pad C (List.replicate tag.val true),ZeroPadding.pad C [decide (tag.val=5)]] := by
  obtain ⟨base,hr,ht,hh,hs⟩:=raw_ready tag old
  obtain ⟨r,rr,rf,rs,_⟩:=ZeroPadding.run_config machine (fun _=>C) _ _ base hr
  have hi : ZeroPadding.config (fun _ : Fin 2=>C)
      (initialConfiguration machine ![List.replicate tag.val true,[old]])=
      initialConfiguration machine
        ![ZeroPadding.pad C (List.replicate tag.val true),ZeroPadding.pad C [old]] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i;fin_cases i <;> rfl
  rw [hi] at rr
  refine ⟨r,rr,?_,?_,rs.trans hs⟩
  · rw [rf]
    change (fun i=>ZeroPadding.pad C (base.final.tapes i))=_
    rw [ht]
    funext i;fin_cases i <;> rfl
  · intro i;rw [rf];exact hh i

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.TagTest
