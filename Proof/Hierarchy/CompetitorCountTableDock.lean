import Proof.Hierarchy.CompetitorCountTablePrefix

/-! Narrow receipt composition into the existing final159 merge/residue/
odd-slice machine. Same/cross fit is derived from the actual bank invariant;
the only semantic input is the intended natural count and its congruence. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
open CompetitorPlaneTable
open MatrixScoreBatch (Request)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def finalProgram (p : Program) := RecoveryFocus.machine (slot p) CompetitorFinalTable.machine

theorem final_dock {s : ℕ} (p : Program) (firstMachine : Machine (tapes p) s)
    (fuel : ℕ) (r : Request) (q : ℕ) (odd : Bool) (f : Fin r.U → Fin r.U → ℕ)
    (first : ExecutionReceipt (tapes p) s) (data : Fin (CompetitorCountBanks.tapes p) → List Bool)
    (out : Fin 34 → List Bool)
    (hr : run firstMachine fuel (input p r q odd)=some first) (hs : first.steps≤fuel)
    (hh : first.final.heads=heads p (MatrixScoreBatch.output r).length)
    (ht : first.final.tapes=extend p q odd data)
    (hn : ∀ i : Fin 35,data (CompetitorCountBanks.tableNative p i)=CompetitorPlaneTableEntry.tapes out r.p i)
    (hc : TableContext (natBitLength r.U) (CompetitorSameBucketColdDense.width r) (CompetitorCrossStateMeaning.state r) out)
    (hb : Bounded (natBitLength r.U) r.p (2*r.p) (CompetitorCrossStateMeaning.state r))
    (h0 : data (CompetitorCountBanks.field p 0)=MatrixScoreBatch.physicalInput r)
    (hU : data (CompetitorCountBanks.field p 44)=UnaryTemplate.tape r.U)
    (hbank : data (CompetitorCountBanks.bank p)=CompetitorCountBanks.sameWord r)
    (hq : q≤CompetitorSameBucketColdDense.width r) (he : odd=true → r.U/2+r.U/2=r.U)
    (hcount : ∀ i : Fin (r.U*r.U),f i.divNat i.modNat<2^q)
    (hcongruent : ∀ i : Fin (r.U*r.U),Int.ModEq ((2 : ℤ)^q)
      (SupplierPrinter.weightedDominance (MatrixScoreBatch.leftScore r) (MatrixScoreBatch.rightScore r)
        (MatrixScoreBatch.weight r) i.divNat i.modNat) (f i.divNat i.modNat)) :
    ∃ actual,run (Composition.machine firstMachine (finalProgram p))
      (fuel+1+CompetitorFinalTable.budget r.U (CompetitorSameBucketColdDense.width r) q) (input p r q odd)=some actual ∧
      actual.steps≤fuel+1+CompetitorFinalTable.budget r.U (CompetitorSameBucketColdDense.width r) q ∧
      actual.final.heads=heads p (MatrixScoreBatch.output r).length ∧
      actual.final.tapes (slot p 141)=CompetitorFinalTable.word q odd f ∧
      actual.final.tapes (slot p 36)=List.replicate q true ∧
      actual.final.tapes (slot p 37)=UnaryTemplate.tape r.U ∧
      actual.final.tapes (slot p 38)=[odd] ∧
      actual.final.tapes (old p (CompetitorCountBanks.field p 0))=MatrixScoreBatch.physicalInput r := by
  have context := entry_context (natBitLength r.U) (CompetitorSameBucketColdDense.width r) r.p
    (CompetitorCrossStateMeaning.state r) out (fun i => data (CompetitorCountBanks.tableNative p i)) hn hc
  have fit := CompetitorSameBucketState.combined_fit r (CompetitorCrossStateMeaning.state r) hb
  have congruent : ∀ i : Fin (r.U*r.U),Int.ModEq ((2 : ℤ)^q)
      ((((CompetitorCrossStateMeaning.state r).positive i+(CompetitorSameBucketState.state r).positive i : ℕ) : ℤ)-
        ((CompetitorCrossStateMeaning.state r).negative i+(CompetitorSameBucketState.state r).negative i : ℕ))
      (f i.divNat i.modNat) := by
    intro i
    rw [CompetitorCrossStateMeaning.combined_dominance]
    exact hcongruent i
  obtain ⟨child,ch,_,chh,cout,_,_,cq,cU,co,_⟩ := CompetitorFinalTable.native_run
    (natBitLength r.U) (CompetitorSameBucketColdDense.width r) q (MatrixScoreBatch.output r).length odd
    (CompetitorCrossStateMeaning.state r) (CompetitorSameBucketState.state r) f
    (fun i => data (CompetitorCountBanks.tableNative p i)) context hq he fit hcount congruent
  have cs := runFrom_steps_le CompetitorFinalTable.machine _ _ child ch
  obtain ⟨last,lh,lhh,lt,ls⟩ := CompetitorFinalTable.focus_run (slot p) (slot_injective p)
    CompetitorFinalTable.machine (CompetitorFinalTable.heads (MatrixScoreBatch.output r).length)
    (CompetitorFinalTable.input (fun i => data (CompetitorCountBanks.tableNative p i))
      (CompetitorCountBanks.sameWord r) q r.U odd)
    (heads p (MatrixScoreBatch.output r).length) (extend p q odd data) child ch chh
    (slot_heads p (MatrixScoreBatch.output r).length) (prepared_input p q r.U odd _ data hbank hU)
  have hl : runFrom (finalProgram p) (CompetitorFinalTable.budget r.U (CompetitorSameBucketColdDense.width r) q)
      (Composition.restart first.final (finalProgram p).start)=some last := by
    have hentry : Composition.restart first.final (finalProgram p).start=
        RecoveryCalls.restarted (finalProgram p) (heads p (MatrixScoreBatch.output r).length) (extend p q odd data) := by
      apply configuration_ext
      · rfl
      · exact hh
      · exact ht
    rw [hentry]
    exact lh
  have hj := Composition.run_join firstMachine (finalProgram p) fuel
    (CompetitorFinalTable.budget r.U (CompetitorSameBucketColdDense.width r) q) _ first last hr hl
  refine ⟨Composition.joinedReceipt first last,hj,?_,lhh,?_,?_,?_,?_,?_⟩
  · change first.steps+1+last.steps≤_
    omega
  · change last.final.tapes (slot p 141)=_
    rw [lt,install_slot _ (slot_injective p)]
    exact cout
  · change last.final.tapes (slot p 36)=_
    rw [lt,install_slot _ (slot_injective p)]
    exact cq
  · change last.final.tapes (slot p 37)=_
    rw [lt,install_slot _ (slot_injective p)]
    exact cU
  · change last.final.tapes (slot p 38)=_
    rw [lt,install_slot _ (slot_injective p)]
    exact co
  · change last.final.tapes (old p (CompetitorCountBanks.field p 0))=_
    rw [lt,install_other _ _ _ _ (slot_avoids_zero p),extend_old]
    exact h0

end NearCubicWires.RepairOrdinary.CompetitorCountTable
