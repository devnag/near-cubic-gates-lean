import Proof.CaseAnalysis.RowsCircuitBottomEntry

/-! The complete counted bottom traversal returns every private cursor
with the paid C driver. Only the source-domain and exact native append
positions remain nonzero. Tape contents and original counters are retained. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomReturned
open LocalBitMultitape RecoveryRootRound CloseoutRowsCircuit CloseoutRowsCircuitBottomDock
open CloseoutRowsCircuitBottomLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (threshold : Bool):=Composition.machine
  (CloseoutRowsCircuitBottomDock.machine threshold) CloseoutRowsCircuitReturnHeads.machine
def budget (C count : ℕ):=CloseoutRowsCircuitBottomLoop.budget C count+1+(10*C+14)

theorem local_heads (p m : ℕ) (out : List Bool) (D W : ℕ) (i : Fin 1060) :
    localHeads p m out D W i=
      if i.val=1059 then 1 else if i.val=1035 then 1 else if i.val=1049 then out.length else
      if i.val=1050 then D else if i.val=1051 then W else if i.val=1052 then p else if i.val=1053 then m else 0:=by
  refine Fin.addCases (m:=1059) (n:=1) ?_ ?_ i
  · intro j
    simp only [localHeads,Fin.addCases_left,Fin.val_castAdd,if_neg (show j.val≠1059 by omega)]
    rfl
  · intro j;have hj:j=0:=Fin.eq_zero j;subst j;rfl

theorem returned_heads (H : Fin 1703 → ℕ) (p m : ℕ) (out : List Bool) (D W : ℕ)
    (rh : ∀ i,H (bottomSlots i)=localHeads p m out D W i)
    (outside : ∀ i,(∀ j,bottomSlots j≠i) → H i=0) :
    CloseoutRowsCircuitReturnHeads.output H=CloseoutRowsCircuitColdEntry.heads out:=by
  funext i
  by_cases h624:i=624
  · subst i;simp [CloseoutRowsCircuitReturnHeads.output,CloseoutRowsCircuitColdEntry.heads,CloseoutRowsCircuit.heads]
  by_cases h1692:i=1692
  · subst i;simp [CloseoutRowsCircuitReturnHeads.output,CloseoutRowsCircuitReturnHeads.h4,
      CloseoutRowsCircuitColdEntry.heads,CloseoutRowsCircuit.heads]
  by_cases h297:i=297
  · subst i;simp [CloseoutRowsCircuitReturnHeads.output,CloseoutRowsCircuitReturnHeads.h4,
      CloseoutRowsCircuitReturnHeads.h3,CloseoutRowsCircuitColdEntry.heads,CloseoutRowsCircuit.heads]
  by_cases h1690:i=1690
  · subst i;simp [CloseoutRowsCircuitReturnHeads.output,CloseoutRowsCircuitReturnHeads.h4,
      CloseoutRowsCircuitReturnHeads.h3,CloseoutRowsCircuitReturnHeads.h2,CloseoutRowsCircuitColdEntry.heads,CloseoutRowsCircuit.heads]
  by_cases h1689:i=1689
  · subst i;simp [CloseoutRowsCircuitReturnHeads.output,CloseoutRowsCircuitReturnHeads.h4,
      CloseoutRowsCircuitReturnHeads.h3,CloseoutRowsCircuitReturnHeads.h2,CloseoutRowsCircuitReturnHeads.h1,
      CloseoutRowsCircuitColdEntry.heads,CloseoutRowsCircuit.heads]
  simp only [CloseoutRowsCircuitReturnHeads.output,CloseoutRowsCircuitReturnHeads.h4,
    CloseoutRowsCircuitReturnHeads.h3,CloseoutRowsCircuitReturnHeads.h2,CloseoutRowsCircuitReturnHeads.h1,
    Function.update_of_ne h624,Function.update_of_ne h1692,Function.update_of_ne h297,
    Function.update_of_ne h1690,Function.update_of_ne h1689]
  by_cases hcore:i=1674
  · subst i;exact rh 1035
  by_cases hnative:i=1688
  · subst i;exact rh 1049
  have zero:CloseoutRowsCircuitColdEntry.heads out i=0:=by
    simp only [CloseoutRowsCircuitColdEntry.heads,if_neg hnative,CloseoutRowsCircuit.heads,
      if_neg (show i.val≠1674 from fun h=>hcore (Fin.ext h))]
  rw [zero]
  by_cases hit:∃ j,bottomSlots j=i
  · obtain ⟨j,hj⟩:=hit
    rw [←hj,rh,local_heads]
    have hid:=congrArg Fin.val hj
    have not1052:j.val≠1052:=by
      intro h;rw [bottom_val,if_pos h] at hid;omega
    have not1059:j.val≠1059:=by
      intro h;rw [bottom_val,if_neg not1052,if_pos h] at hid;omega
    rw [bottom_val,if_neg not1052,if_neg not1059] at hid
    split_ifs <;> omega
  · exact outside i (by simpa only [not_exists] using hit)

private theorem joined {t a b : ℕ} (p : Machine t a) (q : Machine t b) (fp fq : ℕ)
    (H : Fin t → ℕ) (A : Fin t → List Bool) (base : ExecutionReceipt t a) (last : ExecutionReceipt t b)
    (hp : runFrom p fp ⟨p.start,H,A⟩=some base)
    (hq : runFrom q fq ⟨q.start,base.final.heads,base.final.tapes⟩=some last)
    (ps : base.steps ≤ fp) (qs : last.steps ≤ fq) : ∃ r,
    runFrom (Composition.machine p q) (fp+1+fq) ⟨(Composition.machine p q).start,H,A⟩=some r ∧
      r.steps ≤ fp+1+fq ∧ r.final.heads=last.final.heads ∧ r.final.tapes=last.final.tapes:=by
  have he:Composition.restart base.final q.start=⟨q.start,base.final.heads,base.final.tapes⟩:=rfl
  rw [←he] at hq
  refine ⟨Composition.joinedReceipt base last,Composition.run_join p q _ _ _ base last hp hq,?_,rfl,rfl⟩
  change base.steps+1+last.steps ≤ fp+1+fq;omega

theorem traversal_run (threshold : Bool) (C core : ℕ) (words : List (List Bool))
    (out members : List Bool) (D W : ℕ) (flag : Bool)
    (H : Fin 1703 → ℕ) (A : Fin 1703 → List Bool)
    (hin : ∀ bits∈words,2*bits.length+1 ≤ C)
    (hcap : ∀ bits∈words,2*CloseoutRowsGateMeasured.budget bits+4 ≤ C)
    (hc : 1 ≤ C)
    (hb : descriptions core words D words.length ≤ C ∧ wires threshold core 1 members words W words.length ≤ C ∧
      (words.flatMap frame).length ≤ C ∧ 1+2*words.length ≤ C)
    (hh : ∀ i,H (bottomSlots i)=localHeads 0 1 out D W i)
    (ht : ∀ i,A (bottomSlots i)=localTapes C core words.length out (words.flatMap frame) members D W flag i)
    (hz : ∀ i,(∀ j,bottomSlots j≠i) → H i=0) : ∃ r,
    runFrom (machine threshold) (budget C words.length) ⟨(machine threshold).start,H,A⟩=some r ∧
      r.steps ≤ budget C words.length ∧
      r.final.heads=CloseoutRowsCircuitColdEntry.heads
        (out++(List.range words.length).flatMap (outputs threshold core 1 members words)) ∧
      (∀ i,r.final.tapes (bottomSlots i)=localTapes C core words.length
        (out++(List.range words.length).flatMap (outputs threshold core 1 members words))
        (words.flatMap frame) members (descriptions core words D words.length)
        (wires threshold core 1 members words W words.length) (validity core flag words words.length) i) ∧
      (∀ i,(∀ j,bottomSlots j≠i) → r.final.tapes i=A i):=by
  obtain ⟨base,hbase,bs,bh,bt,keep⟩:=bottoms_run threshold C core words out members D W flag H A hin hcap hh ht
  have headsBounds:base.final.heads 1689 ≤ C ∧ base.final.heads 1690 ≤ C ∧
      base.final.heads 297 ≤ C ∧ base.final.heads 1692 ≤ C ∧ base.final.heads 624 ≤ C:=by
    exact ⟨(bh 1050).trans_le hb.1,(bh 1051).trans_le hb.2.1,(bh 1052).trans_le hb.2.2.1,
      (bh 1053).trans_le hb.2.2.2,(bh 1059).trans_le hc⟩
  obtain ⟨last,hl,lh,lt,ls⟩:=CloseoutRowsCircuitReturnHeads.return_run C base.final.heads base.final.tapes headsBounds
    (bh 1055) (bh 1056) (bt 1055) (bt 1056)
  obtain ⟨r,hr,rs,rh,rt⟩:=joined (CloseoutRowsCircuitBottomDock.machine threshold) CloseoutRowsCircuitReturnHeads.machine
    _ _ H A base last hbase hl bs ls.le
  refine ⟨r,hr,rs,?_,?_,?_⟩
  · rw [rh,lh]
    exact returned_heads base.final.heads _ _ _ _ _ bh (fun i hi=>(keep i hi).1.trans (hz i hi))
  · intro i;rw [rt,lt];exact bt i
  · intro i hi;rw [rt,lt];exact (keep i hi).2

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottomReturned
