import Proof.CaseAnalysis.RowsSupportReturned
import Proof.CaseAnalysis.RowsCircuitTraversalCaps

/-! The support-retaining traversal feeds the original resource verdict.
Its additional stream stays outside every resource worker and private clear. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
open LocalBitMultitape RadixSemantics ExtDecompositionBatch
open CloseoutRowsCircuitBottomLoop CloseoutRowsCircuitBottomDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure TailResult (threshold : Bool) (C core : ℕ) (words : List (List Bool))
    (native members : List Bool) (initial L W : ℕ) (A B : Fin 1703 → List Bool) : Prop where
  flag : readTapeBit (B 1700) 0=true ↔ validity core true words words.length=true ∧
    CloseoutRowsCircuitArithmeticDock.amount threshold (descriptions core words initial words.length) words.length≤L ∧
    wires threshold core 1 members words 0 words.length≤W
  stream : B 1688=native++(List.range words.length).flatMap (outputs threshold core 1 members words)
  domain : B 1674=UnaryTemplate.tape core
  driver : B 1694=List.replicate C true
  capW : B 1698=A 1698
  capL : B 1699=A 1699
  raw : B 1=A 1
  bounds : ∃ mid : Fin 1703 → List Bool,
    (∀ i,mid (CloseoutRowsCircuit.bottomSlots i)=localTapes C core words.length
      (native++(List.range words.length).flatMap (outputs threshold core 1 members words))
      (words.flatMap frame) members (descriptions core words initial words.length)
      (wires threshold core 1 members words 0 words.length) (validity core true words words.length) i) ∧
    (∀ i,(∀ j,CloseoutRowsCircuit.bottomSlots j≠i) → mid i=A i) ∧
    (∀ i,(i.val<639 ∨ 665 ≤ i.val) → i≠1700 → B i=mid i) ∧
    (∀ i,CloseoutRowsCircuitColdEntry.heads
      (native++(List.range words.length).flatMap (outputs threshold core 1 members words)) i=0 →
      (mid i).length≤C → (B i).length≤C)

noncomputable def tail (threshold : Bool):=CloseoutRowsGateColdPair.machine (Dock.returned threshold)
  (TapeEmbedding.machine 1 (CloseoutRowsCircuitResourceRun.machine threshold)) (fun bits=>bits 1693)
def tailBudget (threshold : Bool) (C q D n wire L W : ℕ):=
  Dock.returnBudget C q n+1+CloseoutRowsCircuitResourceRun.budget threshold C D n wire L W+1

theorem tail_run (threshold : Bool) (C core : ℕ) (words : List (List Bool))
    (native supports members : List Bool) (initial L W : ℕ)
    (H : Fin 1704 → ℕ) (A : Fin 1704 → List Bool)
    (hin : ∀ bits∈words,2*bits.length+1≤C)
    (hcap : ∀ bits∈words,2*CloseoutRowsGateMeasured.budget bits+4≤C)
    (hinit : threshold=true → 1 ≤ initial)
    (hc : 32*(descriptions core words initial words.length+words.length+
      wires threshold core 1 members words 0 words.length+3)≤C)
    (hsource : (words.flatMap frame).length≤C ∧ 1+2*words.length≤C)
    (hh : ∀ i,H (Dock.slots i)=Dock.localHeads 0 1 native supports initial 0 i)
    (ht : ∀ i,A (Dock.slots i)=Dock.localTapes C core words.length native supports (words.flatMap frame) members initial 0 true i)
    (hz : ∀ i,(∀ j,CloseoutRowsCircuit.bottomSlots j≠i) → H (i.castAdd 1)=0)
    (hn : A 622=List.replicate words.length true)
    (hL : A 1699=List.replicate L true) (hW : A 1698=List.replicate W true) (hflag : A 1700=[]) :
    ∃ B,Step (tail threshold)
      (tailBudget threshold C core (descriptions core words initial words.length) words.length
        (wires threshold core 1 members words 0 words.length) L W) H A
      (Fin.addCases (m:=1703) (n:=1)
        (CloseoutRowsCircuitColdEntry.heads (native++(List.range words.length).flatMap (outputs threshold core 1 members words)))
        (fun _=>(supportPrefix threshold core 1 members words supports words.length).length))
      (Fin.addCases (m:=1703) (n:=1) B (fun _=>supportPrefix threshold core 1 members words supports words.length)) ∧
      TailResult threshold C core words native members initial L W (fun i=>A (i.castAdd 1)) B := by
  let D:=descriptions core words initial words.length
  let wire:=wires threshold core 1 members words 0 words.length
  let output:=native++(List.range words.length).flatMap (outputs threshold core 1 members words)
  obtain ⟨base,hbase,_bs,bh,bt,bout,keep⟩:=Dock.returned_run threshold C core words native supports members
    initial 0 true H A hin hcap (by omega) ⟨by omega,by omega,hsource⟩ hh ht hz
  let pH:=fun i : Fin 1703=>base.final.heads (i.castAdd 1)
  let pA:=fun i : Fin 1703=>base.final.tapes (i.castAdd 1)
  have head:pH=CloseoutRowsCircuitColdEntry.heads output:=by
    funext i
    simp only [pH,bh,Fin.addCases_left,output]
  have supportHead:base.final.heads 1703=
      (supportPrefix threshold core 1 members words supports words.length).length:=by rw [bh];rfl
  have outside (i : Fin 1703) (hi : i.val<639 ∧ i≠297 ∧ i≠624 ∨ 1698 ≤ i.val) :
      ∀ j,CloseoutRowsCircuit.bottomSlots j≠i:=by
    intro j h
    have hv:=congrArg Fin.val h
    rw [CloseoutRowsCircuit.bottom_val] at hv
    split_ifs at hv <;> omega
  have rawcount:pA 622=List.replicate words.length true:=(keep 622 (outside 622 (by decide))).trans hn
  have capL:pA 1699=List.replicate L true:=(keep 1699 (outside 1699 (by decide))).trans hL
  have capW:pA 1698=List.replicate W true:=(keep 1698 (outside 1698 (by decide))).trans hW
  have noflag:pA 1700=[]:=(keep 1700 (outside 1700 (by decide))).trans hflag
  have fields (i : Fin 1060) : pA (CloseoutRowsCircuit.bottomSlots i)=localTapes C core words.length
      output (words.flatMap frame) members D wire (validity core true words words.length) i:=bt i
  have coreTape:pA 1674=UnaryTemplate.tape core:=by
    have h:=fields 1035
    change pA 1674=ZeroPadding.pad 0 (UnaryTemplate.tape core) at h
    simpa only [ZeroPadding.pad_zero] using h
  have flag:readTapeBit (pA 1693) 0=validity core true words words.length:=by
    change readTapeBit (pA (CloseoutRowsCircuit.bottomSlots 1054)) 0=_
    rw [fields];rfl
  have scan:base.final.scanned 1693=validity core true words words.length:=by
    change readTapeBit (pA 1693) (pH 1693)=_
    rw [head];exact flag
  by_cases good:validity core true words words.length=true
  · obtain ⟨B,run,verdict,small,retained⟩:=CloseoutRowsCircuitResourceRun.resource_run threshold C D words.length wire L W
      (CloseoutRowsCircuitColdEntry.heads output) pA hc
      (by intro yes;have low:=CloseoutRowsCircuitTraversalCaps.description_lower core initial words good
          have pos:=hinit yes;dsimp only [D];omega)
      (by intro i hi;simp only [CloseoutRowsCircuitColdEntry.heads,CloseoutRowsCircuit.heads]
          split_ifs <;> first | rfl | omega)
      (CloseoutRowsCircuitTraversalCaps.blank C core words.length output (words.flatMap frame) members D wire _ pA
        (by omega) fields)
      (fields 1050) rawcount (fields 1051) capL capW (fields 1055) (fields 1056)
    obtain ⟨last,hl,lt,lh,_ls⟩:=run
    have localStep:Step (CloseoutRowsCircuitResourceRun.machine threshold)
        (CloseoutRowsCircuitResourceRun.budget threshold C D words.length wire L W) pH pA pH B:=by
      rw [head]
      exact Step.of_run hl lh lt
    obtain ⟨actual,ar,ah,atapes,_as⟩:=(localStep.embed (fun _ : Fin 1=>base.final.heads 1703)
      (fun _ : Fin 1=>base.final.tapes 1703)).congr_in (Dock.full_eta base.final.heads) (Dock.full_eta base.final.tapes)
    obtain ⟨r,hr,rs,rh,rt⟩:=CloseoutRowsCircuitGuarded.accepted (Dock.returned threshold)
      (TapeEmbedding.machine 1 (CloseoutRowsCircuitResourceRun.machine threshold)) (fun bits=>bits 1693)
      _ _ H A base actual hbase ar (scan.trans good)
    refine ⟨B,⟨r,hr,?_,?_,rs⟩,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [rh,ah,head,supportHead]
    · rw [rt,atapes,bout]
    · rw [verdict]
      exact ⟨fun h=>⟨good,h⟩,fun h=>h.2⟩
    · rw [retained 1688 (by decide) (by decide)];exact fields 1049
    · rw [retained 1674 (by decide) (by decide)];exact coreTape
    · rw [retained 1694 (by decide) (by decide)];exact fields 1055
    · rw [retained 1698 (by decide) (by decide)];exact keep 1698 (outside 1698 (by decide))
    · rw [retained 1699 (by decide) (by decide)];exact keep 1699 (outside 1699 (by decide))
    · rw [retained 1 (by decide) (by decide)];exact keep 1 (outside 1 (by decide))
    · exact ⟨pA,fields,keep,retained,small⟩
  · obtain ⟨r,hr,rs,rh,rt⟩:=CloseoutRowsCircuitGuarded.rejected (Dock.returned threshold)
      (TapeEmbedding.machine 1 (CloseoutRowsCircuitResourceRun.machine threshold)) (fun bits=>bits 1693)
      _ H A base hbase (by rw [scan];exact Bool.eq_false_iff.mpr good)
    have sh:Step (tail threshold) (Dock.returnBudget C core words.length+1) H A
        base.final.heads base.final.tapes:=⟨r,hr,rh,rt,rs⟩
    have data:base.final.tapes=Fin.addCases (m:=1703) (n:=1) pA
        (fun _=>supportPrefix threshold core 1 members words supports words.length):=by
      rw [←bout]
      exact (Dock.full_eta base.final.tapes).symm
    refine ⟨pA,(sh.congr bh data).enlarge (by unfold tailBudget;omega),?_,fields 1049,coreTape,
      fields 1055,keep 1698 (outside 1698 (by decide)),keep 1699 (outside 1699 (by decide)),
      keep 1 (outside 1 (by decide)),?_⟩
    · rw [noflag]
      simp [readTapeBit,good]
    · exact ⟨pA,fields,keep,fun _ _ _=>rfl,fun _ _ h=>h⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
