import Proof.CaseAnalysis.RowsSupportBodyEntry
import Proof.CaseAnalysis.RowsSupportTail

/-! The complete post-top circuit body now retains declared support in a
parallel stream. Count/top/native publication and both resource decisions
remain the original physical workers and original bytes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
open LocalBitMultitape RadixSemantics RepairRepresentation ExtDecompositionBatch
open CloseoutRowsCircuitBottomLoop CloseoutRowsCircuitBottomDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def body (threshold : Bool):=Composition.machine
  (TapeEmbedding.machine 1 (CloseoutRowsCircuitPreparedRun.machine threshold)) (tail threshold)
def bodyBudget (threshold : Bool) (C q retained : ℕ) (top : List Bool) (D n wire L W : ℕ):=
  CloseoutRowsCircuitPreparedRun.budget C retained top+1+tailBudget threshold C q D n wire L W

theorem body_run (threshold : Bool) (C core retained : ℕ) (words : List (List Bool))
    (top native supports members : List Bool) (initial L W : ℕ) (A : Fin 1703 → List Bool)
    (hin : ∀ bits∈words,2*bits.length+1≤C)
    (hcap : ∀ bits∈words,2*CloseoutRowsGateMeasured.budget bits+4≤C)
    (hinit : threshold=true → 1 ≤ initial)
    (hc : 32*(descriptions core words initial words.length+words.length+
      wires threshold core 1 members words 0 words.length+3)≤C)
    (hsource : (words.flatMap frame).length≤C ∧ 1+2*words.length≤C)
    (hn : retained≤C) (hheader : EquationHeaderAppend.budget retained+1≤C)
    (hbits : 2*top.length+1≤C)
    (small : ∀ j,(A (CloseoutRowsCircuitAllocate.gate j)).length≤C)
    (hdriver : A 1694=List.replicate C true) (hlog : A 1695=List.replicate (C+1) false)
    (hretained : A 1702=ZeroPadding.pad C (List.replicate retained true))
    (htop : A 1701=ZeroPadding.pad C (frame top)) (hnative : A 1688=native)
    (hscratch : A 1696=List.replicate C false) (hcount : A 624=UnaryTemplate.tape words.length)
    (fields : ∀ i : Fin 7,A (![1689,1690,297,1692,1693,1697,1674] i)=
      (![List.replicate initial true,[],words.flatMap frame,members,[true],ZeroPadding.pad C [true],UnaryTemplate.tape core] : Fin 7 → List Bool) i)
    (hnraw : A 622=List.replicate words.length true)
    (hL : A 1699=List.replicate L true) (hW : A 1698=List.replicate W true) (hflag : A 1700=[]) :
    ∃ B,Step (body threshold)
      (bodyBudget threshold C core retained top (descriptions core words initial words.length) words.length
        (wires threshold core 1 members words 0 words.length) L W)
      (Fin.addCases (m:=1703) (n:=1) (CloseoutRowsCircuitBottomEntry.heads threshold native initial 0) (fun _=>supports.length))
      (Fin.addCases (m:=1703) (n:=1) A (fun _=>supports))
      (Fin.addCases (m:=1703) (n:=1)
        (CloseoutRowsCircuitColdEntry.heads
          ((native++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words)))
        (fun _=>(supportPrefix threshold core 1 members words supports words.length).length))
      (Fin.addCases (m:=1703) (n:=1) B (fun _=>supportPrefix threshold core 1 members words supports words.length)) ∧
      TailResult threshold C core words (native++natWord retained++frame top) members initial L W A B := by
  let initialHeads:=CloseoutRowsCircuitBottomEntry.heads threshold native initial 0
  let next:=native++natWord retained++frame top
  let H:=CloseoutRowsCircuitBottomPosition.output (CloseoutRowsCircuitBottomEntry.heads threshold next initial 0)
  obtain ⟨prepared,r,hr,_rs,rh,rt,ports,keep⟩:=CloseoutRowsCircuitPreparedRun.prepared_run threshold C core
    words.length retained initial top native (words.flatMap frame) members A (by omega) hn hheader hbits small
    hdriver hlog hretained htop hnative hscratch hcount fields
  have first:Step (TapeEmbedding.machine 1 (CloseoutRowsCircuitPreparedRun.machine threshold))
      (CloseoutRowsCircuitPreparedRun.budget C retained top)
      (Fin.addCases (m:=1703) (n:=1) initialHeads (fun _=>supports.length))
      (Fin.addCases (m:=1703) (n:=1) A (fun _=>supports))
      (Fin.addCases (m:=1703) (n:=1) H (fun _=>supports.length))
      (Fin.addCases (m:=1703) (n:=1) prepared (fun _=>supports)):=
    (Step.of_run hr rh rt).embed (fun _ : Fin 1=>supports.length) (fun _ : Fin 1=>supports)
  obtain ⟨B,last,result⟩:=tail_run threshold C core words next supports members initial L W
    (Fin.addCases (m:=1703) (n:=1) (motive:=fun _=>ℕ) H (fun _=>supports.length))
    (Fin.addCases (m:=1703) (n:=1) (motive:=fun _=>List Bool) prepared (fun _=>supports))
    hin hcap hinit hc hsource
    (Dock.lift_heads 0 1 next supports initial 0 H (CloseoutRowsCircuitBottomEntry.heads_ready threshold next initial 0))
    (Dock.lift_tapes C core words.length next supports (words.flatMap frame) members initial 0 true prepared ports)
    (by intro i hi
        simp only [Fin.addCases_left]
        exact CloseoutRowsCircuitBody.outside_heads threshold next initial 0 i hi)
    ((keep 622 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hnraw)
    ((keep 1699 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hL)
    ((keep 1698 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hW)
    ((keep 1700 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hflag)
  have actualResult:TailResult threshold C core words next members initial L W prepared B:=by
    convert result using 1
    funext i
    simp only [Fin.addCases_left]
  refine ⟨B,first.seq last,actualResult.flag,actualResult.stream,actualResult.domain,actualResult.driver,
    actualResult.capW.trans (keep 1698 (by decide) (by decide) (by decide) (by decide) (by decide)),
    actualResult.capL.trans (keep 1699 (by decide) (by decide) (by decide) (by decide) (by decide)),
    actualResult.raw.trans (keep 1 (by decide) (by decide) (by decide) (by decide) (by decide)),?_⟩
  obtain ⟨mid,mt,mkeep,retained,msmall⟩:=actualResult.bounds
  exact ⟨mid,mt,fun i hi=>(mkeep i hi).trans (CloseoutRowsCircuitBody.outside_keep A prepared keep i hi),
    retained,msmall⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
