import Proof.CaseAnalysis.WitnessNodeFields

/-! The Boolean-node tag is a fixed finite lookup. It reads at most three
binary payload bits and their final marker, and rejects an overlong tag
before any numeric expansion. No new arithmetic implementation is needed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NodeTag
open LocalBitMultitape RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def flags (bits : List Bool) (j : Fin 5):=decide (bits.length ≤ 3 ∧ value bits=j.val)
def raw : Machine 6 64 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (56 ≤ q.val)
  rule:=fun q bs=>if hq:q.val<48 then
      some ⟨⟨q.val+8+(if q.val/8%2=1 ∧ bs 0 then 2^(q.val/8/2) else 0),by
        have hp:2^(q.val/8/2) ≤ 4:=Nat.pow_le_pow_right (by decide) (by omega : q.val/8/2 ≤ 2)
        split_ifs <;> omega⟩,fun _=>none,fun i=>if i=0 then .right else .stay⟩
    else some ⟨56,fun i=>if i=0 then none else some (!(bs 0) && decide (q.val%8=i.val-1)),fun _=>.stay⟩
def input (bits : List Bool) (i : Fin 6):=if i=0 then frame bits else []
def observed (r : ExecutionReceipt 6 64):=
  (r.final.tapes 0,List.ofFn (fun j : Fin 5=>r.final.tapes j.succ),r.steps)

theorem finite_observation (bits : List Bool) (hlen : bits.length=3) :
    (run raw 7 (input bits)).map observed=some (frame bits,List.ofFn (fun j : Fin 5=>[flags bits j]),7):=by
  cases bits with
  | nil=>simp at hlen
  | cons a bits=>
    cases bits with
    | nil=>simp at hlen
    | cons b bits=>
      cases bits with
      | nil=>simp at hlen
      | cons c bits=>
        have he:bits=[]:=List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen;omega)
        subst bits
        cases a <;> cases b <;> cases c <;> rfl

theorem raw_run (bits : List Bool) (hlen : bits.length=3) : ∃ r,
    run raw 7 (input bits)=some r ∧ r.final.tapes 0=frame bits ∧
      (∀ j : Fin 5,r.final.tapes j.succ=[flags bits j]) ∧ r.steps=7:=by
  have h:=finite_observation bits hlen
  cases hr:run raw 7 (input bits) with
  | none=>simp [hr] at h
  | some r=>
    simp only [hr,Option.map_some,Option.some.injEq,Prod.mk.injEq,observed] at h
    refine ⟨r,rfl,h.1,?_,h.2.2⟩
    exact fun j=>congrFun (List.ofFn_injective h.2.1) j

def machine:=Rewind.machine raw
def readyInput (bits : List Bool) : Fin 7→List Bool:=
  Fin.addCases (motive:=fun _ : Fin (6+1)=>List Bool) (input bits) (fun _=>[])
theorem tag_run (bits : List Bool) (hlen : bits.length=3) : ∃ out,
    ClockJoin.ReadyRun machine 16 (readyInput bits) out ∧ out 0=frame bits ∧
      (∀ j : Fin 5,out (j.succ.castAdd 1)=[flags bits j]):=by
  obtain ⟨base,hb,hsource,hflags,hsteps⟩:=raw_run bits hlen
  obtain ⟨r,hr,ht,_,hh,hs,_⟩:=Rewind.Workspace.reset_workspace raw _ _ base hb 0
  change run machine (2*base.steps+2) (readyInput bits)=some r at hr
  rw [hsteps] at hr hs
  exact ⟨r.final.tapes,⟨r,hr,rfl,hh,hs.le⟩,(ht 0).trans hsource,
    fun j=>(ht j.succ).trans (hflags j)⟩

theorem flags_nat (bits : List Bool) (h : BitFields.passes bits) (j : Fin 5) :
    flags (BitFields.payload bits) j=decide (value (BitFields.payload bits)=j.val):=by
  apply Bool.eq_iff_iff.mpr
  simp only [flags,decide_eq_true_eq]
  constructor
  · exact And.right
  · intro hv
    refine ⟨?_,hv⟩
    have hp:BitFields.payload bits=(value (BitFields.payload bits)).bits:=
      (BitFields.encoded_passes bits _ (BitFields.code_of_passes bits h).symm).2
    rw [hp,hv]
    fin_cases j <;> decide

end NearCubicWires.RepairOrdinary.CloseoutWitness.NodeTag
