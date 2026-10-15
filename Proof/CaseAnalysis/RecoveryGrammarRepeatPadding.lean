import Proof.CaseAnalysis.RecoveryGrammarPathStep

/-! The same finite driver runs over its physically retained false
backing. Exhaustion preserves that backing and resets the driver to head one. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarRepeat
open LocalBitMultitape RepairSource.VerifierDecoding RecoveryBoundedGrammarDriver
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (t B : ℕ) : Fin (t+1)→ℕ:=
  Fin.addCases (m:=t) (n:=1) (motive:=fun _=>ℕ) (fun _=>0) (fun _=>B)

theorem padded_cfg {t s : ℕ} (phase : Fin 5) (c : Configuration t s) (B total pos : ℕ) :
    ZeroPadding.config (caps t B) (RepeatMachine.cfg phase c total pos)=
      (⟨RepeatMachine.phaseCode s phase,heads c.heads pos,data c.tapes
        (ZeroPadding.pad B (CompareMachine.word total))⟩ : Configuration (t+1) (Fintype.card (RepeatMachine.Control s))) := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (m:=t) (n:=1) (fun j=>?_) (fun j=>?_) i
    · simp only [ZeroPadding.config,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,caps,data,
        Fin.addCases_left,ZeroPadding.pad_zero]
    · simp only [ZeroPadding.config,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,caps,data,
        Fin.addCases_right]

theorem padded_run {t s : ℕ} (body : Machine t s) (states : ℕ → Configuration t s)
    (cost n total pos first B : ℕ) (hpos : pos+n=total)
    (hstart : ∀ i,first ≤ i → i < first+n → (states i).control=body.start)
    (supplier : ∀ i,first ≤ i → i < first+n →
      ∃ r,runFrom body cost (states i)=some r ∧ r.steps≤cost ∧
        r.final.heads=(states (i+1)).heads ∧ r.final.tapes=(states (i+1)).tapes) :
    ∃ r,runFrom (machine body) (n*(cost+2)+total+3)
      ⟨(machine body).start,heads (states first).heads (pos+1),
        data (states first).tapes (ZeroPadding.pad B (CompareMachine.word total))⟩=some r ∧
      r.steps≤n*(cost+2)+total+3 ∧ r.final.heads=heads (states (first+n)).heads 1 ∧
      r.final.tapes=data (states (first+n)).tapes (ZeroPadding.pad B (CompareMachine.word total)) := by
  obtain ⟨a,ar,as,af⟩:=run body states cost n total pos first hpos hstart supplier
  obtain ⟨r,rr,rf,rs,_⟩:=ZeroPadding.run_config (machine body) (caps t B) _ _ a ar
  rw [padded_cfg] at rr
  rw [af,padded_cfg] at rf
  exact ⟨r,rr,rs.le.trans as,congrArg Configuration.heads rf,congrArg Configuration.tapes rf⟩

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarRepeat
