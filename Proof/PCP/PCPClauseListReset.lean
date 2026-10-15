import Proof.PCP.PCPTripleGlobalBounds

/-! Restore the emitted clause-code stream for the next serialization.
The reset log and every left move belong to the actual program. -/
namespace NearCubicWires.RepairOrdinary.PCPClauseList
open LocalBitMultitape
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 180) : Bool := decide (i=177)
noncomputable def resetMachine := MaskedReset.machine PCPTripleGlobal.machine selected

theorem reset_run {s : ℕ} (producer : Machine 180 s) (fuel : ℕ)
    (c : Configuration 180 s) (p : ExecutionReceipt 180 s)
    (hp : runFrom producer fuel c=some p) (hc : c.heads 177=0) :
    ∃ r,runFrom (MaskedReset.machine producer selected) (2*fuel+2) (Rewind.recording c 0)=some r ∧
      (∀ i : Fin 180,r.final.tapes (i.castAdd 1)=p.final.tapes i) ∧
      (∀ i : Fin 180,r.final.heads (i.castAdd 1)=if i=177 then 0 else p.final.heads i) ∧
      r.steps ≤ 2*fuel+2 := by
  have hhead : ∀ i,selected i=true → p.final.heads i ≤ p.steps := by
    intro i hi
    have he : i=177 := by simpa only [selected,Bool.decide_iff] using hi
    subst i
    have h := SelectiveReset.prefix_head (prefix_of_run producer fuel c p hp).1 177
    simpa only [hc,Nat.zero_add] using h
  obtain ⟨r,hr,rf,rs,_⟩ := MaskedReset.reset_run producer selected fuel c p hp hhead
  have hs := runFrom_steps_le producer fuel c p hp
  have hle : 2*p.steps+2 ≤ 2*fuel+2 := by omega
  have more := runFrom_moreFuel (MaskedReset.machine producer selected) (2*p.steps+2)
    ((2*fuel+2)-(2*p.steps+2)) _ r hr
  rw [Nat.add_sub_of_le hle] at more
  refine ⟨r,more,?_,?_,by omega⟩
  · intro i
    simp only [rf,SelectiveReset.finished,Rewind.config,Fin.addCases_left]
  · intro i
    simp only [rf,SelectiveReset.finished,Rewind.config,Fin.addCases_left,selected,Bool.decide_iff]

theorem global_reset_run (pre : List Bool) (groups : List (List (List Bool))) (suffix : List Bool)
    (hthree : ∀ fields∈groups,fields.length=3) :
    ∃ r,runFrom resetMachine (2*PCPTripleGlobal.budget (PCPTripleLoop.stream groups).length groups.length+2)
      (Rewind.recording (PCPTripleGlobal.entry groups.length
        (pre++PCPTripleLoop.stream groups++suffix) pre.length) 0)=some r ∧
      r.final.tapes 0=RepairSource.VerifierDecoding.CompareMachine.word groups.length ∧
      r.final.heads 0=1 ∧
      r.final.tapes 177=PCPTripleLoop.encoded groups ∧ r.final.heads 177=0 ∧
      r.steps ≤ 2*PCPTripleGlobal.budget (PCPTripleLoop.stream groups).length groups.length+2 := by
  obtain ⟨p,hp,p0,ph0,_p5,_ph5,p177,_ph177,_p37,_ph37,_ps⟩ :=
    PCPTripleGlobal.global_run pre groups suffix hthree
  obtain ⟨r,hr,rt,rh,rs⟩ := reset_run PCPTripleGlobal.machine _ _ p hp (by rfl)
  refine ⟨r,hr,(rt 0).trans p0,?_,(rt 177).trans p177,?_,rs⟩
  · exact (rh 0).trans ph0
  · exact rh 177

end NearCubicWires.RepairOrdinary.PCPClauseList
