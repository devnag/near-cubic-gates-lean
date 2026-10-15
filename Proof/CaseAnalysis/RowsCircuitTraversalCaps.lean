import Proof.CaseAnalysis.RowsCircuitGuarded
import Proof.CaseAnalysis.RowsCircuitBottomReturned
import Proof.CaseAnalysis.RowsCircuitResourceRun

/-! The actual complete bottom loop is followed by the original resource
verdict only when every supported gate passed. Malformed bottoms stop with
the still-false circuit flag, before threshold subtraction. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTraversalCaps
open LocalBitMultitape RecoveryRootRound CanonicalWitnessCodec RadixSemantics
open CloseoutRowsCircuit CloseoutRowsCircuitBottomDock CloseoutRowsCircuitBottomLoop
open CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (threshold : Bool):=CloseoutRowsGateColdPair.machine
  (CloseoutRowsCircuitBottomReturned.machine threshold) (CloseoutRowsCircuitResourceRun.machine threshold) (fun b=>b 1693)
def budget (threshold : Bool) (C D n wire L W : ℕ):=CloseoutRowsCircuitBottomReturned.budget C n+1+
  CloseoutRowsCircuitResourceRun.budget threshold C D n wire L W+1

theorem description_lower (core D : ℕ) (words : List (List Bool))
    (good : validity core true words words.length=true) : words.length+D ≤ descriptions core words D words.length:=by
  have every:=(validity_true core words).mp good
  have each (i : Fin words.length) : 1 ≤ descriptionCost core (words.getD i.val []):=by
    have mem:words.getD i.val []∈words:=by
      rw [List.getD_eq_getElem words [] i.isLt]
      exact List.getElem_mem i.isLt
    obtain ⟨g,hg⟩:=Option.isSome_iff_exists.mp (every _ mem)
    rw [descriptionCost,hg]
    change 1 ≤ descriptionBytes g
    unfold descriptionBytes
    rw [CloseoutRowsGateWeightLength.gate_description g]
    omega
  have sum:words.length ≤ ∑ i : Fin words.length,descriptionCost core (words.getD i.val []):=by
    have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun i _=>each i)
    simpa using hs
  rw [descriptions,total_fin]
  omega

theorem blank (C core n : ℕ) (out source members : List Bool) (D W : ℕ) (flag : Bool)
    (A : Fin 1703 → List Bool) (hc : 1 ≤ C)
    (ht : ∀ j,A (bottomSlots j)=localTapes C core n out source members D W flag j)
    (i : Fin 1703) (hi : 639 ≤ i.val ∧ i.val ≤ 664) : A i=List.replicate C false:=by
  let j:Fin 1049:=⟨i.val-639,by omega⟩
  have he:bottomSlots (j.castAdd 11)=i:=by
    apply Fin.ext
    rw [bottom_val]
    dsimp only [j,Fin.val_castAdd]
    split_ifs <;> omega
  rw [←he,ht]
  have cast: j.castAdd 11=(j.castAdd 10).castAdd 1:=Fin.ext rfl
  rw [cast]
  simp only [localTapes,Fin.addCases_left,CloseoutRowsCircuitBottom.data,CloseoutRowsGateBank.input,
    CloseoutRowsGateBank.padded,CloseoutRowsGateBank.input_eq,CloseoutRowsGateBank.pads]
  have notCore:j.val≠1035:=by dsimp only [j];omega
  rw [if_neg notCore,if_neg notCore]
  by_cases h1:j.val=1
  · rw [if_pos h1]
    change ZeroPadding.pad C [false]=List.replicate C false
    cases C
    · omega
    · simp [ZeroPadding.pad,List.replicate_succ]
  · rw [if_neg h1];simp [ZeroPadding.pad]

theorem tail_run (threshold : Bool) (C core : ℕ) (words : List (List Bool))
    (out members : List Bool) (initial L W : ℕ) (H : Fin 1703 → ℕ) (A : Fin 1703 → List Bool)
    (hin : ∀ bits∈words,2*bits.length+1 ≤ C)
    (hcap : ∀ bits∈words,2*CloseoutRowsGateMeasured.budget bits+4 ≤ C)
    (hinit : threshold=true → 1 ≤ initial)
    (hc : 32*(descriptions core words initial words.length+words.length+
      wires threshold core 1 members words 0 words.length+3) ≤ C)
    (hsource : (words.flatMap frame).length ≤ C ∧ 1+2*words.length ≤ C)
    (hh : ∀ i,H (bottomSlots i)=localHeads 0 1 out initial 0 i)
    (ht : ∀ i,A (bottomSlots i)=localTapes C core words.length out (words.flatMap frame) members initial 0 true i)
    (hz : ∀ i,(∀ j,bottomSlots j≠i) → H i=0)
    (hn : A 622=List.replicate words.length true)
    (hL : A 1699=List.replicate L true) (hW : A 1698=List.replicate W true) (hflag : A 1700=[]) : ∃ r,
    runFrom (machine threshold) (budget threshold C (descriptions core words initial words.length)
      words.length (wires threshold core 1 members words 0 words.length) L W) ⟨(machine threshold).start,H,A⟩=some r ∧
      r.steps ≤ budget threshold C (descriptions core words initial words.length)
        words.length (wires threshold core 1 members words 0 words.length) L W ∧
      r.final.heads=CloseoutRowsCircuitColdEntry.heads
        (out++(List.range words.length).flatMap (outputs threshold core 1 members words)) ∧
      (readTapeBit (r.final.tapes 1700) 0=true ↔ validity core true words words.length=true ∧
        CloseoutRowsCircuitArithmeticDock.amount threshold (descriptions core words initial words.length) words.length ≤ L ∧
        wires threshold core 1 members words 0 words.length ≤ W) ∧
      r.final.tapes 1688=out++(List.range words.length).flatMap (outputs threshold core 1 members words) ∧
      r.final.tapes 1674=UnaryTemplate.tape core ∧ r.final.tapes 1694=List.replicate C true ∧
      r.final.tapes 1698=A 1698 ∧ r.final.tapes 1699=A 1699 ∧ r.final.tapes 1=A 1 ∧
      ∃ mid : Fin 1703 → List Bool,
        (∀ i,mid (bottomSlots i)=localTapes C core words.length
          (out++(List.range words.length).flatMap (outputs threshold core 1 members words))
          (words.flatMap frame) members (descriptions core words initial words.length)
          (wires threshold core 1 members words 0 words.length) (validity core true words words.length) i) ∧
        (∀ i,(∀ j,bottomSlots j≠i) → mid i=A i) ∧
        (∀ i,(i.val<639 ∨ 665 ≤ i.val) → i≠1700 → r.final.tapes i=mid i) ∧
        (∀ i,CloseoutRowsCircuitColdEntry.heads
          (out++(List.range words.length).flatMap (outputs threshold core 1 members words)) i=0 →
          (mid i).length ≤ C → (r.final.tapes i).length ≤ C):=by
  let D:=descriptions core words initial words.length
  let wire:=wires threshold core 1 members words 0 words.length
  let native:=out++(List.range words.length).flatMap (outputs threshold core 1 members words)
  obtain ⟨base,hbase,bs,bh,bt,keep⟩:=CloseoutRowsCircuitBottomReturned.traversal_run threshold C core words out members initial 0 true H A
    hin hcap (by omega) (by exact ⟨by omega,by omega,hsource⟩) hh ht hz
  have outside (i : Fin 1703) (hi : i.val<639 ∧ i≠297 ∧ i≠624 ∨ 1698 ≤ i.val) : ∀ j,bottomSlots j≠i:=by
    intro j h
    have hv:=congrArg Fin.val h
    rw [bottom_val] at hv
    split_ifs at hv <;> omega
  have rawcount:base.final.tapes 622=List.replicate words.length true:=
    (keep 622 (outside 622 (by decide))).trans hn
  have capL:base.final.tapes 1699=List.replicate L true:=
    (keep 1699 (outside 1699 (by decide))).trans hL
  have capW:base.final.tapes 1698=List.replicate W true:=
    (keep 1698 (outside 1698 (by decide))).trans hW
  have noflag:base.final.tapes 1700=[]:=
    (keep 1700 (outside 1700 (by decide))).trans hflag
  have coreTape:base.final.tapes 1674=UnaryTemplate.tape core:=by
    have h:=bt 1035
    change base.final.tapes 1674=ZeroPadding.pad 0 (UnaryTemplate.tape core) at h
    simpa only [ZeroPadding.pad_zero] using h
  have flag:readTapeBit (base.final.tapes 1693) 0=validity core true words words.length:=by
    change readTapeBit (base.final.tapes (bottomSlots 1054)) 0=_
    rw [bt];rfl
  have scan:base.final.scanned 1693=validity core true words words.length:=by
    change readTapeBit (base.final.tapes 1693) (base.final.heads 1693)=_
    rw [bh];exact flag
  by_cases good:validity core true words words.length=true
  · obtain ⟨result,run,verdict,small,retained⟩:=CloseoutRowsCircuitResourceRun.resource_run threshold C D words.length wire L W
      (CloseoutRowsCircuitColdEntry.heads native) base.final.tapes hc
      (by intro yes;have low:=description_lower core initial words good;have pos:=hinit yes;dsimp only [D];omega)
      (by
        intro i hi
        simp only [CloseoutRowsCircuitColdEntry.heads,CloseoutRowsCircuit.heads]
        split_ifs <;> first | rfl | omega)
      (blank C core words.length native (words.flatMap frame) members D wire _ base.final.tapes (by omega) bt)
      (bt 1050) rawcount (bt 1051) capL capW (bt 1055) (bt 1056)
    obtain ⟨last,hl,lt,lh,_ls⟩:=run
    have lastRun:runFrom (CloseoutRowsCircuitResourceRun.machine threshold)
        (CloseoutRowsCircuitResourceRun.budget threshold C D words.length wire L W)
        (RecoveryCalls.restarted (CloseoutRowsCircuitResourceRun.machine threshold) base.final.heads base.final.tapes)=some last:=by
      rw [bh];exact hl
    obtain ⟨r,hr,rs,rh,rt⟩:=CloseoutRowsCircuitGuarded.accepted (CloseoutRowsCircuitBottomReturned.machine threshold)
      (CloseoutRowsCircuitResourceRun.machine threshold) (fun b=>b 1693) _ _ H A base last hbase lastRun (scan.trans good)
    have ro (i : Fin 1703) (hi : i.val<639 ∨ 665 ≤ i.val) (hne : i≠1700) :
        r.final.tapes i=base.final.tapes i:=by rw [rt,lt];exact retained i hi hne
    refine ⟨r,hr,rs,rh.trans lh,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [rt,lt,verdict]
      exact ⟨fun h=>⟨good,h⟩,fun h=>h.2⟩
    · rw [ro 1688 (by decide) (by decide)];exact bt 1049
    · rw [ro 1674 (by decide) (by decide)];exact coreTape
    · rw [ro 1694 (by decide) (by decide)];exact bt 1055
    · rw [ro 1698 (by decide) (by decide)];exact keep 1698 (outside 1698 (by decide))
    · rw [ro 1699 (by decide) (by decide)];exact keep 1699 (outside 1699 (by decide))
    · rw [ro 1 (by decide) (by decide)];exact keep 1 (outside 1 (by decide))
    · refine ⟨base.final.tapes,bt,keep,ro,?_⟩
      intro i hi hb
      rw [rt,lt]
      exact small i hi hb
  · obtain ⟨r,hr,rs,rh,rt⟩:=CloseoutRowsCircuitGuarded.rejected (CloseoutRowsCircuitBottomReturned.machine threshold)
      (CloseoutRowsCircuitResourceRun.machine threshold) (fun b=>b 1693) _ H A base hbase
      (by rw [scan];exact Bool.eq_false_iff.mpr good)
    have bound:CloseoutRowsCircuitBottomReturned.budget C words.length+1 ≤ budget threshold C D words.length wire L W:=by
      unfold budget;omega
    have more:=runFrom_moreFuel (machine threshold) _
      (budget threshold C D words.length wire L W-(CloseoutRowsCircuitBottomReturned.budget C words.length+1)) _ r hr
    rw [Nat.add_sub_of_le bound] at more
    refine ⟨r,more,rs.trans bound,rh.trans bh,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [rt,noflag]
      simp [readTapeBit,good]
    · rw [rt];exact bt 1049
    · rw [rt];exact coreTape
    · rw [rt];exact bt 1055
    · rw [rt];exact keep 1698 (outside 1698 (by decide))
    · rw [rt];exact keep 1699 (outside 1699 (by decide))
    · rw [rt];exact keep 1 (outside 1 (by decide))
    · refine ⟨base.final.tapes,bt,keep,?_,?_⟩
      · intro i _hi _hne;exact congrFun rt i
      · intro i _hi hb;rw [rt];exact hb

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitTraversalCaps
