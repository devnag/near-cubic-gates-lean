import Proof.CaseAnalysis.RecoveryGrammarAdvance

/-! Reload the canonical grammar work bank after a paid row update. This
reuses the existing erase/reload calls without saving another graph output. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarReload
open LocalBitMultitape Composition RecoveryRootRound
open RecoveryBoundedGrammarWorker (heads resultHeads resultData)
open RecoveryBoundedGrammarContinue (bank stackCapacity)
open RecoveryBoundedGrammarBank (ready base)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def raw:=Composition.machine RecoveryBoundedRowErase.machine RecoveryBoundedRowReload.machine
noncomputable def machine:=TapeEmbedding.machine 1 raw
def budget (next : Fin 78→List Bool) (B : ℕ):=(2*B+4)+1+RecoveryBoundedRowReload.budget next B

theorem erased_ready (fields : Fin 78→List Bool) (node B : ℕ) (out stack packet source : List Bool) :
    RecoveryBoundedRowErase.data B (ready fields node B out stack packet source)=base node B out stack packet source := by
  funext i
  fin_cases i <;> simp [RecoveryBoundedRowErase.data,ready,RecoveryBoundedRowReload.loaded_apply,
    RecoveryBoundedRowReload.ports,base]

theorem raw_run (fields next : Fin 78→List Bool) (node B : ℕ) (out stack tail source : List Bool)
    (hc : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B)
    (hn : ∀ j∈RecoveryBoundedRowReload.ports,(next j).length≤B)
    (hw : (RecoveryBoundedRowReload.word next).length≤B) :
    ∃ r,runFrom raw (budget next B)
      ⟨raw.start,heads out stack,ready fields node B out stack (RecoveryBoundedRowReload.word next++tail) source⟩=some r ∧
      r.steps≤budget next B ∧ r.final.heads=heads out stack ∧
      r.final.tapes=ready next node B out stack (RecoveryBoundedRowReload.word next++tail) source := by
  let packet:=RecoveryBoundedRowReload.word next++tail
  let A:=ready fields node B out stack packet source
  have hA : ∀ j,(A (RecoveryBoundedRowErase.work j)).length≤B := by
    intro j
    rw [show A=ready fields node B out stack packet source from rfl,RecoveryBoundedGrammarBank.ready_work]
    split
    · rename_i hj
      rw [ZeroPadding.pad_length]
      exact max_le le_rfl (hc _ hj)
    · simp only [List.length_replicate];exact le_rfl
  obtain ⟨a,ar,ah,atapes,as⟩:=RecoveryBoundedRowErase.erase_run B (heads out stack) A
    (RecoveryBoundedRowAfter.erase_heads out stack) hA
    (by dsimp only [A];rw [RecoveryBoundedGrammarBank.ready_kept _ _ _ _ _ _ _ _ (by decide)];rfl)
    (by dsimp only [A];rw [RecoveryBoundedGrammarBank.ready_kept _ _ _ _ _ _ _ _ (by decide)];rfl)
  rw [show A=ready fields node B out stack packet source from rfl,erased_ready] at atapes
  obtain ⟨b,br,bs,bh,bt⟩:=RecoveryBoundedRowReload.reload_run next B tail (heads out stack)
    (base node B out stack packet source) rfl rfl rfl (RecoveryBoundedRowAfter.heads_port out stack)
    rfl rfl rfl
    (by
      intro j hj
      rw [←erased_ready fields]
      exact RecoveryBoundedRowAfter.erased_port A B j hj)
    hn hw
  have br' : runFrom RecoveryBoundedRowReload.machine (RecoveryBoundedRowReload.budget next B)
      (restart a.final RecoveryBoundedRowReload.machine.start)=some b := by
    change runFrom _ _ ⟨_,a.final.heads,a.final.tapes⟩=some b
    rw [ah,atapes]
    exact br
  have joined:=Composition.run_join RecoveryBoundedRowErase.machine RecoveryBoundedRowReload.machine _ _ _ a b ar br'
  refine ⟨joinedReceipt a b,joined,?_,bh,bt⟩
  change a.steps+1+b.steps≤budget next B
  unfold budget
  omega

theorem padded_run (fields next : Fin 78→List Bool) (node B P : ℕ) (out stack tail source : List Bool)
    (hc : ∀ j∈RecoveryBoundedRowReload.ports,(fields j).length≤B)
    (hn : ∀ j∈RecoveryBoundedRowReload.ports,(next j).length≤B)
    (hw : (RecoveryBoundedRowReload.word next).length≤B) :
    ∃ r,runFrom machine (budget next B)
      (RecoveryBoundedGrammarStep.entry machine fields node B P out stack (RecoveryBoundedRowReload.word next++tail) source)=some r ∧
      r.steps≤budget next B ∧ r.final.heads=resultHeads out.length stack.length ∧
      r.final.tapes=bank (ready next node B out stack (RecoveryBoundedRowReload.word next++tail) source) B P := by
  obtain ⟨a,ar,as,ah,atapes⟩:=raw_run fields next node B out stack tail source hc hn hw
  let embedded:=TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _ : Fin 1=>List.replicate B false) a
  have er:=TapeEmbedding.run_embed raw (fun _ : Fin 1=>0) (fun _ : Fin 1=>List.replicate B false) _ _ a ar
  obtain ⟨r,rr,rt,rs,_⟩:=ZeroPadding.run_config machine (stackCapacity P) _ _ embedded er
  refine ⟨r,rr,rs.le.trans as,?_,?_⟩
  · rw [rt]
    change (Fin.addCases (m:=78) (n:=1) (motive:=fun _=>ℕ) a.final.heads (fun _ : Fin 1=>0))=_
    rw [ah]
    rfl
  · rw [rt]
    change (fun i=>ZeroPadding.pad (stackCapacity P i)
      ((Fin.addCases (m:=78) (n:=1) (motive:=fun _=>List Bool) a.final.tapes (fun _ : Fin 1=>List.replicate B false)) i))=_
    rw [atapes]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarReload
