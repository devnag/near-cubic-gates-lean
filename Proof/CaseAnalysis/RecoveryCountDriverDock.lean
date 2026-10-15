import Proof.CaseAnalysis.RecoveryCountFits

/-! Refresh the actual next-candidate finite driver in the shared bank.
The one shared raw candidate has already advanced; the bound driver survives. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountDriverDock
open LocalBitMultitape RecoveryRootRound
open RecoveryBoundedCountBank
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=RecoveryFocus.machine grammarSlots RecoveryBoundedGrammarDriverBank.refresh

theorem run (q bound C count B P node total : ℕ) (fields : Fin 78→List Bool)
    (out stack packet source : List Bool) (proj : Fin 37→List Bool) (extra : Fin 12→List Bool)
    (raw : extra 1=RecoveryBoundedGrammarScalarAdd.unary B (count+1)) (hcount : count+4≤B) :
    ∃ r,runFrom machine (RecoveryBoundedGrammarDriverBank.refreshBudget B (count+1))
      ⟨machine.start,heads out stack 1 1,
        data B P (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) proj total
          (RecoveryBoundedGrammarCold.metadata q bound 0 C B extra)
          (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (bound+1)))
          (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count+1)))⟩=some r ∧
      r.steps≤RecoveryBoundedGrammarDriverBank.refreshBudget B (count+1) ∧ r.final.heads=heads out stack 1 1 ∧
      r.final.tapes=data B P (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) proj total
        (RecoveryBoundedGrammarCold.metadata q bound 0 C B extra)
        (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (bound+1)))
        (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count+2))) := by
  let cold:=RecoveryBoundedGrammarCold.metadata q bound 0 C B extra
  let A:=RecoveryBoundedGrammarCold.data fields node B P out stack packet source cold
  let H:=RecoveryBoundedGrammarCold.scanHeads (RecoveryBoundedGrammarCold.heads out stack) 1 1
  let scan:=RecoveryBoundedGrammarCold.scanData A B bound count
  let ambient:=data B P (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) proj total cold
    (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (bound+1)))
    (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count+1)))
  have hold : (scan 113).length≤B := by
    change (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count+1))).length≤B
    simp only [ZeroPadding.pad_length,RepairSource.VerifierDecoding.CompareMachine.word,
      List.length_cons,List.length_replicate]
    omega
  obtain ⟨a,ar,as,ah,atapes⟩:=RecoveryBoundedGrammarDriverBank.refresh_run B (count+1) H scan
    (by omega) hold (by exact raw)
    (by change ZeroPadding.pad 0 (List.replicate B false)=_;exact ZeroPadding.pad_zero _)
    (RecoveryBoundedGrammarCold.data76 fields node B P out stack packet source cold)
    (RecoveryBoundedGrammarCold.data77 fields node B P out stack packet source cold) rfl rfl rfl rfl rfl
  have ph:=grammar_heads out stack 1 1
  have pt:=grammar_data fields node B P bound count total out stack packet source proj cold
  obtain ⟨r,rr,rf,rs⟩:=RecoveryFocus.run_config grammarSlots grammar_injective RecoveryBoundedGrammarDriverBank.refresh
    (heads out stack 1 1) ambient _ _ a ar
  have start : RecoveryFocus.config grammarSlots (heads out stack 1 1) ambient
      ⟨RecoveryBoundedGrammarDriverBank.refresh.start,H,scan⟩=
      (⟨machine.start,heads out stack 1 1,ambient⟩ : Configuration 152 _) := by
    apply WilliamsSourceCrop.focus_same grammarSlots ⟨machine.start,heads out stack 1 1,ambient⟩ _
    · intro j;exact congrFun ph j
    · intro j;exact congrFun pt j
  rw [start] at rr
  refine ⟨r,rr,rs.le.trans as,?_,?_⟩
  · funext i
    cases hpick : RecoveryFocus.pick grammarSlots i with
    | none=>simp only [rf,RecoveryFocus.config,hpick]
    | some j=>
      have he:=RecoveryFocus.slot_of_pick grammarSlots hpick
      simpa only [rf,RecoveryFocus.config,hpick,ah] using
        (congrFun ph j).symm.trans (congrArg (heads out stack 1 1) he)
  · rw [rf]
    change install grammarSlots ambient a.final.tapes=_
    rw [atapes]
    have next : Function.update scan 113
        (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count+1+1)))=
        RecoveryBoundedGrammarCold.scanData A B bound (count+1) := by
      exact RecoveryBoundedGrammarDriverBank.update_count A _ _ _
    rw [next]
    apply RecoveryBoundedCountGrammarBank.install_data
    intro j
    have h:=congrFun (grammar_data fields node B P bound (count+1) total out stack packet source proj cold) j
    simpa only [Nat.add_assoc] using h

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountDriverDock
