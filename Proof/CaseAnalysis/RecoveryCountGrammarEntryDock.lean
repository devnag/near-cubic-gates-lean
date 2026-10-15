import Proof.CaseAnalysis.RecoveryCountGrammarRun

/-! Paid tag-zero packet selection starts each original grammar from
the preceding original row bank without changing either finite driver. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountGrammarBank
open LocalBitMultitape
open RecoveryBoundedCountBank
open RecoveryBoundedGrammarCold (Room ScalarFits selectedFields selectedWord tag metadata)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scan_heads (H : Fin 112→ℕ) (bp cp : ℕ) :
    RecoveryBoundedGrammarCold.scanHeads H bp cp=
      Fin.addCases (m:=112) (n:=2) H ![bp,cp] := by
  funext i
  fin_cases i <;> rfl
theorem scan_data (A : Fin 112→List Bool) (B bound count : ℕ) :
    RecoveryBoundedGrammarCold.scanData A B bound count=
      Fin.addCases (m:=112) (n:=2) A
        ![ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (bound+1)),
          ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count+1))] := by
  funext i
  fin_cases i <;> rfl

noncomputable def entryLocal:=TapeEmbedding.machine 2 RecoveryBoundedCountGrammarEntry.machine
noncomputable def entry:=RecoveryFocus.machine grammarSlots entryLocal

theorem entry_run {q bound W C D L S B P : ℕ}
    (room : Room W C D L S B P) (scalars : ScalarFits q bound 0 W)
    (current : Fin 78→List Bool) (node count total : ℕ) (out stack packet source : List Bool)
    (proj : Fin 37→List Bool) (extra : Fin 12→List Bool)
    (hPacket : packet.length≤B) (hc : ∀ j∈RecoveryBoundedRowReload.ports,(current j).length≤B) :
    ∃ r,runFrom entry (RecoveryBoundedGrammarCold.atomBudget B)
      ⟨entry.start,heads out stack 1 1,
        data B P (RecoveryBoundedGrammarBank.ready current node B out stack packet source)
          proj total (metadata q bound 0 C B extra)
          (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (bound+1)))
          (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count+1)))⟩=some r ∧
      r.steps≤RecoveryBoundedGrammarCold.atomBudget B ∧ r.final.heads=heads out stack 1 1 ∧
      r.final.tapes=data B P (RecoveryBoundedGrammarBank.ready (selectedFields (tag 0) q bound 0 C)
        node B out stack (ZeroPadding.pad B (selectedWord (tag 0) q bound 0 C)) source)
        proj total (metadata q bound 0 C B extra)
        (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (bound+1)))
        (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count+1))) := by
  obtain ⟨a,ar,as,ah,atapes⟩:=RecoveryBoundedCountGrammarEntry.run room scalars current node out stack packet source extra hPacket hc
  let eH : Fin 2→ℕ:=![1,1]
  let eT : Fin 2→List Bool:=
    ![ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (bound+1)),
      ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count+1))]
  let r:=TapeEmbedding.receipt eH eT a
  have er:=TapeEmbedding.run_embed RecoveryBoundedCountGrammarEntry.machine eH eT _ _ a ar
  have rr : runFrom entryLocal (RecoveryBoundedGrammarCold.atomBudget B)
      ⟨entryLocal.start,RecoveryBoundedGrammarCold.scanHeads (RecoveryBoundedGrammarCold.heads out stack) 1 1,
        RecoveryBoundedGrammarCold.scanData
          (RecoveryBoundedGrammarCold.data current node B P out stack packet source (metadata q bound 0 C B extra)) B bound count⟩=some r := by
    rw [scan_heads,scan_data]
    exact er
  have rh : r.final.heads=RecoveryBoundedGrammarCold.scanHeads (RecoveryBoundedGrammarCold.heads out stack) 1 1 := by
    change Fin.addCases (m:=112) (n:=2) (motive:=fun _ : Fin 114=>ℕ) a.final.heads eH=_
    rw [ah,scan_heads]
  have rt : r.final.tapes=RecoveryBoundedGrammarCold.scanData
      (RecoveryBoundedGrammarCold.data (selectedFields (tag 0) q bound 0 C) node B P out stack
        (ZeroPadding.pad B (selectedWord (tag 0) q bound 0 C)) source (metadata q bound 0 C B extra)) B bound count := by
    change Fin.addCases (m:=112) (n:=2) (motive:=fun _ : Fin 114=>List Bool) a.final.tapes eT=_
    rw [atapes,scan_data]
  exact focus_run entryLocal _ B P total node node bound count _ _ out stack packet out stack _ source proj _ _
    r rr as rh rt

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountGrammarBank
