import Proof.CaseAnalysis.CaseTwoAssignmentSystematicBank
import Proof.CaseAnalysis.CaseTwoAssignmentPaths

/-! Complete systematic path through the actual assignment dispatcher,
including comparison, query positioning, source read, parity, and both returns. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Assignment
open LocalBitMultitape SourceInterfaces RepairRepresentation RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

private theorem systematic_dock (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (index : Fin (a.output r).systematicBits) (oldIndex : ℕ)
    (H : Fin (tapes a) → ℕ) (A : Fin (tapes a) → List Bool) (ph : H=heads a)
    (p15 : A (low a 15)=UnaryTemplate.tape index.val)
    (keep : ∀ i,(∀ j,prepareSlots a j≠i) → A i=input a r u index.val oldIndex i) : ∃ out,
    runFrom (systematic a) (1+1+SystematicBit.budget a r)
      ⟨(systematic a).start,H,A⟩=some out ∧
    out.final.tapes (low a 25)=[parityOn ((a.output r).systematicSupport index) u]:=by
  obtain ⟨s,hs,_,sb⟩:=SystematicReady.bit_run a r u index
  obtain ⟨last,hl,_,_,_,lt,_⟩:=RecoveryFocus.dock (systematicSlots a) (systematic_injective a)
    SystematicReady.machine _ H A _
    (by intro j;rw [ph];exact systematic_entry_heads a j)
    (systematic_entry_data a r u index.val oldIndex A p15 keep) s hs
  exact ⟨last,hl,(lt 11).trans sb⟩

theorem systematic_run (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity)
    (u : BitInput r.arity) (index : Fin (a.output r).systematicBits) (oldIndex : ℕ) : ∃ out,
    runFrom (machine a) (budget a r u index.val)
      ⟨(machine a).start,heads a,input a r u index.val oldIndex⟩=some out ∧
      out.steps≤budget a r u index.val ∧
      out.final.tapes (low a 25)=[parityOn ((a.output r).systematicSupport index) u]:=by
  obtain ⟨p,hp,_,ph,p15,p17,_,keep⟩:=prepared_run a r u index.val oldIndex
  have flag : readTapeBit (p.final.tapes (low a 17)) (p.final.heads (low a 17))=false:=by
    rw [ph,p17]
    change readTapeBit [decide ((a.output r).systematicBits ≤ index.val)] 0=false
    have hi : ¬(a.output r).systematicBits ≤ index.val:=by omega
    simp only [hi,decide_false]
    rfl
  obtain ⟨last,hl,lb⟩:=systematic_dock a r u index oldIndex p.final.heads p.final.tapes ph p15 keep
  let used:=VariablePrep.budget index.val (a.output r).systematicBits+1+
    (1+1+SystematicBit.budget a r+1)
  obtain ⟨out,ho,os,_,ot⟩:=AssignmentPaths.two (sizes a) (programs a) 0 (next a) 1
    (VariablePrep.budget index.val (a.output r).systematicBits)
    (1+1+SystematicBit.budget a r) (heads a) (input a r u index.val oldIndex) p last hp hl
    (by change some (if readTapeBit (p.final.tapes (low a 17))
          (p.final.heads (low a 17)) then (2 : Fin 4) else 1)=some 1
        rw [flag];rfl) (by rfl)
  have hb : used ≤ budget a r u index.val:=by unfold used budget;omega
  have more:=runFrom_moreFuel (machine a) used (budget a r u index.val-used) _ out ho
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨out,more,os.trans hb,?_⟩
  rw [ot]
  exact lb

end
end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.Assignment
