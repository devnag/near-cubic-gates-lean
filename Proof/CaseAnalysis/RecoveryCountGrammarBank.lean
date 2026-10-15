import Proof.CaseAnalysis.RecoveryCountPacketDock
import Proof.CaseAnalysis.RecoveryGrammarBudget

/-! Exact graph/stack/metadata replacement at the original grammar boundary.
The unrelated projector and randomness driver remain outside the focus. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountGrammarBank
open LocalBitMultitape RecoveryRootRound
open RecoveryBoundedCountBank
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem install_data (B P total : ℕ) (A nextA : Fin 78→List Bool) (proj : Fin 37→List Bool)
    (cold nextCold : Fin 33→List Bool) (bd cd nextBd nextCd : List Bool) (localNext : Fin 114→List Bool)
    (hn : ∀ j,data B P nextA proj total nextCold nextBd nextCd (grammarSlots j)=localNext j) :
    install grammarSlots (data B P A proj total cold bd cd) localNext=
      data B P nextA proj total nextCold nextBd nextCd := by
  apply HierarchyWidth.install_eq grammarSlots grammar_injective
  · exact hn
  · intro i
    refine Fin.addCases (m:=116) (n:=36) (fun j=>?_) (fun j=>?_) i
    · refine Fin.addCases (m:=78) (n:=38) (fun k=>?_) (fun k=>?_) j
      · intro hi
        exact False.elim (hi (k.castAdd 36) (by
          simp only [grammarSlots,Fin.addCases_left]
          apply Fin.ext;rfl))
      · intro _
        simp only [data,Fin.addCases_left,RecoveryBoundedFixedRestart.data,
          RecoveryBoundedFixedContinue.data,Fin.addCases_right]
    · intro hi
      exact False.elim (hi (j.natAdd 78) (by simp only [grammarSlots,Fin.addCases_right]))

theorem heads_outside (out stack nextOut nextStack : List Bool) (bp cp nextBp nextCp : ℕ)
    (i : Fin 152) (hi : ∀ j,grammarSlots j≠i) :
    heads out stack bp cp i=heads nextOut nextStack nextBp nextCp i := by
  revert hi
  refine Fin.addCases (m:=116) (n:=36) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=78) (n:=38) (fun k=>?_) (fun k=>?_) j
    · intro hi
      exact False.elim (hi (k.castAdd 36) (by
        simp only [grammarSlots,Fin.addCases_left]
        apply Fin.ext;rfl))
    · intro _
      fin_cases k <;> rfl
  · intro hi
    exact False.elim (hi (j.natAdd 78) (by simp only [grammarSlots,Fin.addCases_right]))

theorem focus_run {s : ℕ} (worker : Machine 114 s) (fuel : ℕ)
    (B P total node nextNode bound count : ℕ) (fields nextFields : Fin 78→List Bool)
    (out stack packet nextOut nextStack nextPacket source : List Bool)
    (proj : Fin 37→List Bool) (cold nextCold : Fin 33→List Bool)
    (r : ExecutionReceipt 114 s)
    (hr : runFrom worker fuel
      ⟨worker.start,RecoveryBoundedGrammarCold.scanHeads (RecoveryBoundedGrammarCold.heads out stack) 1 1,
        RecoveryBoundedGrammarCold.scanData
          (RecoveryBoundedGrammarCold.data fields node B P out stack packet source cold) B bound count⟩=some r)
    (rs : r.steps≤fuel)
    (rh : r.final.heads=RecoveryBoundedGrammarCold.scanHeads (RecoveryBoundedGrammarCold.heads nextOut nextStack) 1 1)
    (rt : r.final.tapes=RecoveryBoundedGrammarCold.scanData
      (RecoveryBoundedGrammarCold.data nextFields nextNode B P nextOut nextStack nextPacket source nextCold) B bound count) :
    let before:=data B P (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) proj total cold
      (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (bound+1)))
      (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count+1)))
    let after:=data B P (RecoveryBoundedGrammarBank.ready nextFields nextNode B nextOut nextStack nextPacket source) proj total nextCold
      (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (bound+1)))
      (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count+1)))
    ∃ z,runFrom (RecoveryFocus.machine grammarSlots worker) fuel
      ⟨worker.start,heads out stack 1 1,before⟩=some z ∧ z.steps≤fuel ∧
      z.final.heads=heads nextOut nextStack 1 1 ∧ z.final.tapes=after := by
  dsimp only
  let A:=data B P (RecoveryBoundedGrammarBank.ready fields node B out stack packet source) proj total cold
    (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (bound+1)))
    (ZeroPadding.pad B (RepairSource.VerifierDecoding.CompareMachine.word (count+1)))
  obtain ⟨z,zr,_zc,zs,zh,zt,keep⟩:=RecoveryFocus.dock grammarSlots grammar_injective worker fuel
    (heads out stack 1 1) A _
    (fun j=>congrFun (grammar_heads out stack 1 1) j)
    (fun j=>congrFun (grammar_data fields node B P bound count total out stack packet source proj cold) j) r hr
  refine ⟨z,zr,zs.le.trans rs,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,grammarSlots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [zh,rh]
      exact (congrFun (grammar_heads nextOut nextStack 1 1) j).symm
    · have hn : ∀ j,grammarSlots j≠i:=by intro j he;exact hi ⟨j,he⟩
      exact (keep i hn).1.trans (heads_outside out stack nextOut nextStack 1 1 1 1 i hn)
  · have he : z.final.tapes=install grammarSlots A r.final.tapes := by
      funext i
      by_cases hi : ∃ j,grammarSlots j=i
      · obtain ⟨j,rfl⟩:=hi
        rw [install_slot grammarSlots grammar_injective]
        exact zt j
      · have hn : ∀ j,grammarSlots j≠i:=by intro j h;exact hi ⟨j,h⟩
        rw [install_other grammarSlots A r.final.tapes i hn]
        exact (keep i hn).2
    rw [he,rt]
    apply install_data
    intro j
    exact congrFun (grammar_data nextFields nextNode B P bound count total nextOut nextStack nextPacket source proj nextCold) j

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountGrammarBank
