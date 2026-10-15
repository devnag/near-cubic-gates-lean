import Proof.Amplification.RecoveryBoundedNativeFoldFocus

/-! The complete reusable reverse fold step, including its paid scratch reset. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeFold
open LocalBitMultitape RepairRepresentation RecoveryRootRound Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (conjunction : Bool) (ref acc C : ℕ) :=
  8*ref+9+1+nodeBudget conjunction ref acc C+1+(2*acc+4)+1+(2*C+4)

theorem step_run (conjunction : Bool) (ref acc C z : ℕ) (flag : Bool) (out pre : List Bool)
    (hpop : 2*ref+2 ≤ C) (hr : PCPPNativeSumAppend.budget 0 ref+1 ≤ C)
    (ha : PCPPNativeSumAppend.budget 0 acc+1 ≤ C) (hacc : acc+1 ≤ C) :
    ∃ r, runFrom (machine conjunction) (budget conjunction ref acc C)
      (entry conjunction acc C (pre.length+2*ref+1) flag out
        (pre++(frame (List.replicate ref true)).reverse++List.replicate z false))=some r ∧
      r.steps ≤ budget conjunction ref acc C ∧
      r.final.heads=heads (out++emitted conjunction ref acc) pre.length ∧
      r.final.tapes=data 0 (acc+1) C flag (out++emitted conjunction ref acc)
        (pre++List.replicate (2*ref+1+z) false) [] := by
  obtain ⟨a,har,ah,atapes,as⟩:=first_run ref acc C z flag out pre hpop
  obtain ⟨b,hbr,bs,bh,bt⟩:=node_run conjunction ref acc C pre.length flag out
    (pre++List.replicate (2*ref+1+z) false) (frame (List.replicate ref true)) hr ha
  have hb' : runFrom (second conjunction) (nodeBudget conjunction ref acc C)
      (restart a.final (second conjunction).start)=some b := by
    change runFrom (second conjunction) _ ⟨(second conjunction).start,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]; exact hbr
  have hab:=Composition.run_join first (second conjunction) _ _ _ a b har hb'
  obtain ⟨c,hcr,ch,ct,cs⟩:=increment_run ref acc C pre.length flag
    (out++emitted conjunction ref acc) (pre++List.replicate (2*ref+1+z) false)
    (frame (List.replicate ref true)) hacc
  have hc' : runFrom third (2*acc+4) (restart (joinedReceipt a b).final third.start)=some c := by
    change runFrom third _ ⟨third.start,b.final.heads,b.final.tapes⟩=some c
    rw [bh,bt]; exact hcr
  have habc:=Composition.run_join (Composition.machine first (second conjunction)) third _ _ _
    (joinedReceipt a b) c hab hc'
  obtain ⟨d,hdr,dh,dt,ds⟩:=erase_run ref (acc+1) C pre.length flag
    (out++emitted conjunction ref acc) (pre++List.replicate (2*ref+1+z) false)
    (frame (List.replicate ref true)) (by omega)
    (by simp only [frame_length,List.length_replicate]; omega)
  have hd' : runFrom last (2*C+4) (restart (joinedReceipt (joinedReceipt a b) c).final last.start)=some d := by
    change runFrom last _ ⟨last.start,c.final.heads,c.final.tapes⟩=some d
    rw [ch,ct]; exact hdr
  have full:=Composition.run_join (Composition.machine (Composition.machine first (second conjunction)) third)
    last _ _ _ (joinedReceipt (joinedReceipt a b) c) d habc hd'
  refine ⟨joinedReceipt (joinedReceipt (joinedReceipt a b) c) d,full,?_,dh,dt⟩
  change a.steps+1+b.steps+1+c.steps+1+d.steps ≤ budget conjunction ref acc C
  unfold budget
  omega

theorem bounded_run (conjunction : Bool) (ref acc W C z : ℕ) (flag : Bool) (out pre : List Bool)
    (hr : ref ≤ W) (ha : acc ≤ W) (hC : 16384*(W+1)^2 ≤ C) :
    ∃ r, runFrom (machine conjunction) (24*C+64)
      (entry conjunction acc C (pre.length+2*ref+1) flag out
        (pre++(frame (List.replicate ref true)).reverse++List.replicate z false))=some r ∧
      r.steps ≤ 24*C+64 ∧
      r.final.heads=heads (out++emitted conjunction ref acc) pre.length ∧
      r.final.tapes=data 0 (acc+1) C flag (out++emitted conjunction ref acc)
        (pre++List.replicate (2*ref+1+z) false) [] := by
  have href:=PCPPNativeClauseCapacity.sum_capacity 0 ref W C (by omega) hC
  have hacc:=PCPPNativeClauseCapacity.sum_capacity 0 acc W C (by omega) hC
  have hw : W+1 ≤ (W+1)^2 := by nlinarith
  have hpop : 2*ref+2 ≤ C := by nlinarith
  have hac : acc+1 ≤ C := by nlinarith
  obtain ⟨r,hrun,rs,rh,rt⟩:=step_run conjunction ref acc C z flag out pre hpop href hacc hac
  have hn:=node_budget_bound conjunction ref acc C href hacc
  have hb : budget conjunction ref acc C ≤ 24*C+64 := by
    unfold budget
    omega
  have more:=runFrom_moreFuel (machine conjunction) _ (24*C+64-budget conjunction ref acc C) _ r hrun
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,rs.trans hb,rh,rt⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeFold
