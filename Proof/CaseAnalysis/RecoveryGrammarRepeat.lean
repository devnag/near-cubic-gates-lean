import Proof.CaseAnalysis.RecoveryGrammarRowBody
import Proof.PCP.VerifierDecodingRepeat

/-! Apply the existing finite driver to a bounded sequence of actual row
receipts. Only the demanded finite interval needs a body supplier. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarRepeat
open LocalBitMultitape RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine {t s : ℕ} (body : Machine t s):=RepeatMachine.machine body (fun _ _=>true)

theorem run {t s : ℕ} (body : Machine t s) (states : ℕ → Configuration t s) (cost n total pos first : ℕ)
    (hpos : pos+n=total)
    (hstart : ∀ i,first ≤ i → i < first+n → (states i).control=body.start)
    (supplier : ∀ i,first ≤ i → i < first+n →
      ∃ r,runFrom body cost (states i)=some r ∧ r.steps≤cost ∧
        r.final.heads=(states (i+1)).heads ∧ r.final.tapes=(states (i+1)).tapes) :
    ∃ r,runFrom (machine body) (n*(cost+2)+total+3)
      (RepeatMachine.cfg 0 (states first) total (pos+1))=some r ∧
      r.steps≤n*(cost+2)+total+3 ∧ r.final=RepeatMachine.cfg 3 (states (first+n)) total 1 := by
  induction n generalizing pos first with
  | zero=>
    have hp : pos=total:=by omega
    obtain ⟨r,rr,rf,rs⟩:=(RepeatMachine.exhaust body (fun _ _=>true) (states first) total).run
      (by simp [RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
    refine ⟨r,?_,?_,?_⟩
    · simpa only [machine,hp,Nat.zero_mul,Nat.zero_add] using rr
    · simpa only [Nat.zero_mul,Nat.zero_add] using rs.le
    · simpa only [Nat.add_zero] using rf
  | succ n ih=>
    obtain ⟨a,ar,as,ah,atapes⟩:=supplier first le_rfl (by omega)
    have step:=RepeatMachine.iteration body (fun _ _=>true) (states first) total pos a
      (hstart first le_rfl (by omega)) (by omega) ar
    change Timed (machine body) (a.steps+2) (RepeatMachine.cfg 0 (states first) total (pos+1))
      (RepeatMachine.cfg 0 a.final total (pos+2)) at step
    have endpoint : RepeatMachine.cfg 0 a.final total (pos+2)=
        RepeatMachine.cfg 0 (states (first+1)) total ((pos+1)+1) := by
      apply configuration_ext
      · rfl
      · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,ah,Nat.add_assoc]
      · simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,atapes]
    rw [endpoint] at step
    obtain ⟨last,lr,ls,lf⟩:=ih (pos+1) (first+1) (by omega)
      (fun i hlo hhi=>hstart i (by omega) (by omega))
      (fun i hlo hhi=>supplier i (by omega) (by omega))
    rcases step with ⟨space,pref⟩
    obtain ⟨r,rr,rf,rs,_⟩:=pref.followedBy last lr
    have fits : (a.steps+2)+(n*(cost+2)+total+3)≤(n+1)*(cost+2)+total+3 := by
      rw [Nat.add_mul,Nat.one_mul]
      omega
    have more:=runFrom_moreFuel (machine body) _
      ((n+1)*(cost+2)+total+3-((a.steps+2)+(n*(cost+2)+total+3))) _ r rr
    rw [Nat.add_sub_of_le fits] at more
    refine ⟨r,more,?_,?_⟩
    · rw [rs]
      omega
    · rw [rf,lf]
      congr 2;omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarRepeat
