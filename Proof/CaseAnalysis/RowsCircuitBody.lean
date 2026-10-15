import Proof.CaseAnalysis.RowsCircuitPreparedRun
import Proof.CaseAnalysis.RowsCircuitTraversalCaps

/-! The complete post-top circuit body publishes the native count and top,
traverses the actual bottom list, returns its private cursors, and decides
both original resource bounds. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBody
open LocalBitMultitape RecoveryRootRound RepairRepresentation
open CloseoutRowsCircuit CloseoutRowsCircuitBottomDock CloseoutRowsCircuitBottomLoop
open CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (threshold : Bool):=CloseoutRowsGateColdPair.machine
  (CloseoutRowsCircuitPreparedRun.machine threshold) (CloseoutRowsCircuitTraversalCaps.machine threshold) (fun _=>true)
def budget (threshold : Bool) (C retained : ℕ) (top : List Bool) (D n wire L W : ℕ):=
  CloseoutRowsCircuitPreparedRun.budget C retained top+1+
    CloseoutRowsCircuitTraversalCaps.budget threshold C D n wire L W+1

private theorem joined (threshold : Bool) (fp fq : ℕ) (H : Fin 1703 → ℕ) (A : Fin 1703 → List Bool)
    (first : ExecutionReceipt 1703 (show ℕ from (show Σ s,Machine 1703 s from ⟨_,CloseoutRowsCircuitPreparedRun.machine threshold⟩).1))
    (last : ExecutionReceipt 1703 (show ℕ from (show Σ s,Machine 1703 s from ⟨_,CloseoutRowsCircuitTraversalCaps.machine threshold⟩).1))
    (hp : runFrom (CloseoutRowsCircuitPreparedRun.machine threshold) fp
      (RecoveryCalls.restarted (CloseoutRowsCircuitPreparedRun.machine threshold) H A)=some first)
    (hq : runFrom (CloseoutRowsCircuitTraversalCaps.machine threshold) fq
      (RecoveryCalls.restarted (CloseoutRowsCircuitTraversalCaps.machine threshold) first.final.heads first.final.tapes)=some last) :
    ∃ r,runFrom (machine threshold) (fp+1+fq+1) (RecoveryCalls.restarted (machine threshold) H A)=some r ∧
      r.steps ≤ fp+1+fq+1 ∧ r.final.heads=last.final.heads ∧ r.final.tapes=last.final.tapes:=
  CloseoutRowsCircuitGuarded.accepted (CloseoutRowsCircuitPreparedRun.machine threshold)
    (CloseoutRowsCircuitTraversalCaps.machine threshold) (fun _=>true) fp fq H A first last hp hq rfl

theorem outside_heads (threshold : Bool) (out : List Bool) (D W : ℕ) (i : Fin 1703)
    (outside : ∀ j,bottomSlots j≠i) :
    CloseoutRowsCircuitBottomPosition.output (CloseoutRowsCircuitBottomEntry.heads threshold out D W) i=0:=by
  have ncore:i≠1674:=Ne.symm (outside 1035)
  have nnative:i≠1688:=Ne.symm (outside 1049)
  have ndesc:i≠1689:=Ne.symm (outside 1050)
  have nwire:i≠1690:=Ne.symm (outside 1051)
  have nmember:i≠1692:=Ne.symm (outside 1053)
  have ncount:i≠624:=Ne.symm (outside 1059)
  simp only [CloseoutRowsCircuitBottomPosition.output,Function.update_of_ne ncount,
    Function.update_of_ne nmember,CloseoutRowsCircuitBottomEntry.heads,if_neg ncore,
    if_neg nnative,if_neg ndesc,if_neg nwire,if_neg ncount]

theorem outside_keep (A B : Fin 1703 → List Bool)
    (keep : ∀ i,(i.val<639 ∨ 1687 < i.val ∨ i.val=1674) → i≠1694 → i≠1695 → i≠1688 → i≠1696 → B i=A i)
    (i : Fin 1703) (outside : ∀ j,bottomSlots j≠i) : B i=A i:=by
  apply keep i _ (Ne.symm (outside 1055)) (Ne.symm (outside 1056))
    (Ne.symm (outside 1049)) (Ne.symm (outside 1057))
  by_cases lo:i.val<639
  · exact Or.inl lo
  by_cases hi:1687 < i.val
  · exact Or.inr (Or.inl hi)
  have bad:=outside ⟨i.val-639,by omega⟩
  apply False.elim
  apply bad
  apply Fin.ext
  rw [bottom_val]
  dsimp only
  split_ifs <;> omega

private theorem from_tail (threshold : Bool) (C core retained : ℕ) (words : List (List Bool))
    (top out members : List Bool) (initial L W : ℕ) (A B : Fin 1703 → List Bool)
    (first : ExecutionReceipt 1703 (show ℕ from (show Σ s,Machine 1703 s from ⟨_,CloseoutRowsCircuitPreparedRun.machine threshold⟩).1))
    (hfirst : runFrom (CloseoutRowsCircuitPreparedRun.machine threshold) (CloseoutRowsCircuitPreparedRun.budget C retained top)
      ⟨(CloseoutRowsCircuitPreparedRun.machine threshold).start,CloseoutRowsCircuitBottomEntry.heads threshold out initial 0,A⟩=some first)
    (fh : first.final.heads=CloseoutRowsCircuitBottomPosition.output
      (CloseoutRowsCircuitBottomEntry.heads threshold (out++natWord retained++frame top) initial 0))
    (ft : first.final.tapes=B)
    (keep : ∀ i,(i.val<639 ∨ 1687 < i.val ∨ i.val=1674) → i≠1694 → i≠1695 → i≠1688 → i≠1696 → B i=A i)
    (tail : ∃ r,
    runFrom (CloseoutRowsCircuitTraversalCaps.machine threshold) (CloseoutRowsCircuitTraversalCaps.budget threshold C (descriptions core words initial words.length)
      words.length (wires threshold core 1 members words 0 words.length) L W) ⟨(CloseoutRowsCircuitTraversalCaps.machine threshold).start,(CloseoutRowsCircuitBottomPosition.output (CloseoutRowsCircuitBottomEntry.heads threshold (out++natWord retained++frame top) initial 0)),B⟩=some r ∧
      r.steps ≤ CloseoutRowsCircuitTraversalCaps.budget threshold C (descriptions core words initial words.length)
        words.length (wires threshold core 1 members words 0 words.length) L W ∧
      r.final.heads=CloseoutRowsCircuitColdEntry.heads
        ((out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words)) ∧
      (readTapeBit (r.final.tapes 1700) 0=true ↔ validity core true words words.length=true ∧
        CloseoutRowsCircuitArithmeticDock.amount threshold (descriptions core words initial words.length) words.length ≤ L ∧
        wires threshold core 1 members words 0 words.length ≤ W) ∧
      r.final.tapes 1688=(out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words) ∧
      r.final.tapes 1674=UnaryTemplate.tape core ∧ r.final.tapes 1694=List.replicate C true ∧
      r.final.tapes 1698=B 1698 ∧ r.final.tapes 1699=B 1699 ∧ r.final.tapes 1=B 1 ∧
      ∃ mid : Fin 1703 → List Bool,
        (∀ i,mid (bottomSlots i)=localTapes C core words.length
          ((out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words))
          (words.flatMap frame) members (descriptions core words initial words.length)
          (wires threshold core 1 members words 0 words.length) (validity core true words words.length) i) ∧
        (∀ i,(∀ j,bottomSlots j≠i) → mid i=B i) ∧
        (∀ i,(i.val<639 ∨ 665 ≤ i.val) → i≠1700 → r.final.tapes i=mid i) ∧
        (∀ i,CloseoutRowsCircuitColdEntry.heads
          ((out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words)) i=0 →
          (mid i).length ≤ C → (r.final.tapes i).length ≤ C)) : ∃ r,
    runFrom (machine threshold) (budget threshold C retained top (descriptions core words initial words.length)
      words.length (wires threshold core 1 members words 0 words.length) L W)
      ⟨(machine threshold).start,CloseoutRowsCircuitBottomEntry.heads threshold out initial 0,A⟩=some r ∧
    r.steps ≤ budget threshold C retained top (descriptions core words initial words.length)
      words.length (wires threshold core 1 members words 0 words.length) L W ∧
    r.final.heads=CloseoutRowsCircuitColdEntry.heads
      ((out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words)) ∧
    (readTapeBit (r.final.tapes 1700) 0=true ↔ validity core true words words.length=true ∧
      CloseoutRowsCircuitArithmeticDock.amount threshold (descriptions core words initial words.length) words.length ≤ L ∧
      wires threshold core 1 members words 0 words.length ≤ W) ∧
    r.final.tapes 1688=(out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words) ∧
    r.final.tapes 1674=UnaryTemplate.tape core ∧ r.final.tapes 1694=List.replicate C true ∧
    r.final.tapes 1698=A 1698 ∧ r.final.tapes 1699=A 1699 ∧ r.final.tapes 1=A 1 ∧
    ∃ mid : Fin 1703 → List Bool,
      (∀ i,mid (bottomSlots i)=localTapes C core words.length
        ((out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words))
        (words.flatMap frame) members (descriptions core words initial words.length)
        (wires threshold core 1 members words 0 words.length) (validity core true words words.length) i) ∧
      (∀ i,(∀ j,bottomSlots j≠i) → mid i=A i) ∧
      (∀ i,(i.val<639 ∨ 665 ≤ i.val) → i≠1700 → r.final.tapes i=mid i) ∧
      (∀ i,CloseoutRowsCircuitColdEntry.heads
        ((out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words)) i=0 →
        (mid i).length ≤ C → (r.final.tapes i).length ≤ C):=by
  let nativePrefix:=out++natWord retained++frame top
  let H:=CloseoutRowsCircuitBottomPosition.output (CloseoutRowsCircuitBottomEntry.heads threshold nativePrefix initial 0)
  obtain ⟨last,hl,_ls,lh,verdict,native,domain,driver,capW,capL,raw,mid,mt,mkeep,kept,msmall⟩:=tail
  have lastRun:runFrom (CloseoutRowsCircuitTraversalCaps.machine threshold)
      (CloseoutRowsCircuitTraversalCaps.budget threshold C (descriptions core words initial words.length)
        words.length (wires threshold core 1 members words 0 words.length) L W)
      (RecoveryCalls.restarted (CloseoutRowsCircuitTraversalCaps.machine threshold) first.final.heads first.final.tapes)=some last:=by
    rw [fh,ft];exact hl
  obtain ⟨r,hr,rs,rh,rt⟩:=joined threshold _ _
    (CloseoutRowsCircuitBottomEntry.heads threshold out initial 0) A first last hfirst lastRun
  have rtape (i : Fin 1703) : r.final.tapes i=last.final.tapes i:=congrFun rt i
  refine ⟨r,hr,rs,rh.trans lh,?_,?_,?_,?_,?_,?_,?_,mid,mt,?_,?_,?_⟩
  · rw [rtape 1700];exact verdict
  · exact (rtape 1688).trans native
  · exact (rtape 1674).trans domain
  · exact (rtape 1694).trans driver
  · exact ((rtape 1698).trans capW).trans (keep 1698 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact ((rtape 1699).trans capL).trans (keep 1699 (by decide) (by decide) (by decide) (by decide) (by decide))
  · exact ((rtape 1).trans raw).trans (keep 1 (by decide) (by decide) (by decide) (by decide) (by decide))
  · intro i hi;rw [mkeep i hi];exact outside_keep A B keep i hi
  · intro i hi hn;exact (rtape i).trans (kept i hi hn)
  · intro i hi hs;exact (congrArg List.length (rtape i)).trans_le (msmall i hi hs)

theorem from_prepared (threshold : Bool) (C core retained : ℕ) (words : List (List Bool))
    (top out members : List Bool) (initial L W : ℕ) (A : Fin 1703 → List Bool)
    (hin : ∀ bits∈words,2*bits.length+1 ≤ C)
    (hcap : ∀ bits∈words,2*CloseoutRowsGateMeasured.budget bits+4 ≤ C)
    (hinit : threshold=true → 1 ≤ initial)
    (hc : 32*(descriptions core words initial words.length+words.length+
      wires threshold core 1 members words 0 words.length+3) ≤ C)
    (hsource : (words.flatMap frame).length ≤ C ∧ 1+2*words.length ≤ C)
    (hnraw : A 622=List.replicate words.length true)
    (hL : A 1699=List.replicate L true) (hW : A 1698=List.replicate W true) (hflag : A 1700=[])
    (prepared : ∃ B first,
      runFrom (CloseoutRowsCircuitPreparedRun.machine threshold) (CloseoutRowsCircuitPreparedRun.budget C retained top)
        ⟨(CloseoutRowsCircuitPreparedRun.machine threshold).start,CloseoutRowsCircuitBottomEntry.heads threshold out initial 0,A⟩=some first ∧
      first.steps ≤ CloseoutRowsCircuitPreparedRun.budget C retained top ∧
      first.final.heads=CloseoutRowsCircuitBottomPosition.output
        (CloseoutRowsCircuitBottomEntry.heads threshold (out++natWord retained++frame top) initial 0) ∧
      first.final.tapes=B ∧
      (∀ i,B (bottomSlots i)=localTapes C core words.length (out++natWord retained++frame top)
        (words.flatMap frame) members initial 0 true i) ∧
      (∀ i,(i.val<639 ∨ 1687 < i.val ∨ i.val=1674) → i≠1694 → i≠1695 → i≠1688 → i≠1696 → B i=A i)) : ∃ r,
    runFrom (machine threshold) (budget threshold C retained top (descriptions core words initial words.length)
      words.length (wires threshold core 1 members words 0 words.length) L W)
      ⟨(machine threshold).start,CloseoutRowsCircuitBottomEntry.heads threshold out initial 0,A⟩=some r ∧
    r.steps ≤ budget threshold C retained top (descriptions core words initial words.length)
      words.length (wires threshold core 1 members words 0 words.length) L W ∧
    r.final.heads=CloseoutRowsCircuitColdEntry.heads
      ((out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words)) ∧
    (readTapeBit (r.final.tapes 1700) 0=true ↔ validity core true words words.length=true ∧
      CloseoutRowsCircuitArithmeticDock.amount threshold (descriptions core words initial words.length) words.length ≤ L ∧
      wires threshold core 1 members words 0 words.length ≤ W) ∧
    r.final.tapes 1688=(out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words) ∧
    r.final.tapes 1674=UnaryTemplate.tape core ∧ r.final.tapes 1694=List.replicate C true ∧
    r.final.tapes 1698=A 1698 ∧ r.final.tapes 1699=A 1699 ∧ r.final.tapes 1=A 1 ∧
    ∃ mid : Fin 1703 → List Bool,
      (∀ i,mid (bottomSlots i)=localTapes C core words.length
        ((out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words))
        (words.flatMap frame) members (descriptions core words initial words.length)
        (wires threshold core 1 members words 0 words.length) (validity core true words words.length) i) ∧
      (∀ i,(∀ j,bottomSlots j≠i) → mid i=A i) ∧
      (∀ i,(i.val<639 ∨ 665 ≤ i.val) → i≠1700 → r.final.tapes i=mid i) ∧
      (∀ i,CloseoutRowsCircuitColdEntry.heads
        ((out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words)) i=0 →
        (mid i).length ≤ C → (r.final.tapes i).length ≤ C) :=by
  let nativePrefix:=out++natWord retained++frame top
  let H:=CloseoutRowsCircuitBottomPosition.output (CloseoutRowsCircuitBottomEntry.heads threshold nativePrefix initial 0)
  obtain ⟨B,first,hfirst,_fs,fh,ft,bt,keep⟩:=prepared
  apply from_tail threshold C core retained words top out members initial L W A B first hfirst fh ft keep
  exact
    CloseoutRowsCircuitTraversalCaps.tail_run threshold C core words nativePrefix members initial L W H B hin hcap hinit hc hsource
      (CloseoutRowsCircuitBottomEntry.heads_ready threshold nativePrefix initial 0) bt
      (outside_heads threshold nativePrefix initial 0)
      ((keep 622 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hnraw)
      ((keep 1699 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL)
      ((keep 1698 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hW)
      ((keep 1700 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hflag)

theorem body_run (threshold : Bool) (C core retained : ℕ) (words : List (List Bool))
    (top out members : List Bool) (initial L W : ℕ) (A : Fin 1703 → List Bool)
    (hin : ∀ bits∈words,2*bits.length+1 ≤ C)
    (hcap : ∀ bits∈words,2*CloseoutRowsGateMeasured.budget bits+4 ≤ C)
    (hinit : threshold=true → 1 ≤ initial)
    (hc : 32*(descriptions core words initial words.length+words.length+
      wires threshold core 1 members words 0 words.length+3) ≤ C)
    (hsource : (words.flatMap frame).length ≤ C ∧ 1+2*words.length ≤ C)
    (hn : retained ≤ C) (hheader : EquationHeaderAppend.budget retained+1 ≤ C)
    (hbits : 2*top.length+1 ≤ C)
    (small : ∀ j,(A (CloseoutRowsCircuitAllocate.gate j)).length ≤ C)
    (hdriver : A 1694=List.replicate C true) (hlog : A 1695=List.replicate (C+1) false)
    (hretained : A 1702=ZeroPadding.pad C (List.replicate retained true))
    (htop : A 1701=ZeroPadding.pad C (frame top)) (hnative : A 1688=out)
    (hscratch : A 1696=List.replicate C false) (hcount : A 624=UnaryTemplate.tape words.length)
    (fields : ∀ i : Fin 7,A (![1689,1690,297,1692,1693,1697,1674] i)=
      (![List.replicate initial true,[],words.flatMap frame,members,[true],ZeroPadding.pad C [true],UnaryTemplate.tape core] : Fin 7 → List Bool) i)
    (hnraw : A 622=List.replicate words.length true)
    (hL : A 1699=List.replicate L true) (hW : A 1698=List.replicate W true) (hflag : A 1700=[]) : ∃ r,
    runFrom (machine threshold) (budget threshold C retained top (descriptions core words initial words.length)
      words.length (wires threshold core 1 members words 0 words.length) L W)
      ⟨(machine threshold).start,CloseoutRowsCircuitBottomEntry.heads threshold out initial 0,A⟩=some r ∧
    r.steps ≤ budget threshold C retained top (descriptions core words initial words.length)
      words.length (wires threshold core 1 members words 0 words.length) L W ∧
    r.final.heads=CloseoutRowsCircuitColdEntry.heads
      ((out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words)) ∧
    (readTapeBit (r.final.tapes 1700) 0=true ↔ validity core true words words.length=true ∧
      CloseoutRowsCircuitArithmeticDock.amount threshold (descriptions core words initial words.length) words.length ≤ L ∧
      wires threshold core 1 members words 0 words.length ≤ W) ∧
    r.final.tapes 1688=(out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words) ∧
    r.final.tapes 1674=UnaryTemplate.tape core ∧ r.final.tapes 1694=List.replicate C true ∧
    r.final.tapes 1698=A 1698 ∧ r.final.tapes 1699=A 1699 ∧ r.final.tapes 1=A 1 ∧
    ∃ mid : Fin 1703 → List Bool,
      (∀ i,mid (bottomSlots i)=localTapes C core words.length
        ((out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words))
        (words.flatMap frame) members (descriptions core words initial words.length)
        (wires threshold core 1 members words 0 words.length) (validity core true words words.length) i) ∧
      (∀ i,(∀ j,bottomSlots j≠i) → mid i=A i) ∧
      (∀ i,(i.val<639 ∨ 665 ≤ i.val) → i≠1700 → r.final.tapes i=mid i) ∧
      (∀ i,CloseoutRowsCircuitColdEntry.heads
        ((out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words)) i=0 →
        (mid i).length ≤ C → (r.final.tapes i).length ≤ C) :=by
  apply from_prepared threshold C core retained words top out members initial L W A
    hin hcap hinit hc hsource hnraw hL hW hflag
  exact CloseoutRowsCircuitPreparedRun.prepared_run threshold C core words.length retained initial
    top out (words.flatMap frame) members A (by omega) hn hheader hbits small hdriver hlog
    hretained htop hnative hscratch hcount fields

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBody
