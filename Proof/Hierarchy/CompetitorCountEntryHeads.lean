import Proof.Hierarchy.CompetitorCountTableBounds

/-! Recover the exact heads omitted by the older count-entry public receipt.
The executed machines and clocks are unchanged; determinism identifies their
accepted runs with the existing full count-fold endpoint. -/
namespace NearCubicWires.RepairOrdinary.CompetitorCountEntry
open LocalBitMultitape RecoveryExecution SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def finalHeads (b n : ℕ) (i : Fin 9) := if i.val=0 then b*n else if i.val=8 then 1 else 0

theorem loop_endpoint (b w : ℕ) (xs : List ℕ) (hw : b≤w)
    (hx : ∀ x∈xs,x<2^b) (hfit : xs.sum<2^w)
    (r : ExecutionReceipt 9 (Fintype.card (RepeatMachine.Control 17)))
    (hr : runFrom CompetitorCountFold.machine (xs.length*(16*w+20)+3) (loopStart b w xs)=some r) :
    r.final.heads=finalHeads b xs.length ∧ r.final.tapes 1=List.replicate b true ∧
      r.final.tapes 2=List.replicate w true := by
  obtain ⟨base,hbase,hf,_,_⟩ := CompetitorCountFold.count_fold_run [] [] b w zeroStore xs hw hx
    (by simpa [zeroStore] using hfit) (by simp [zeroStore]) (by simp [zeroStore])
  have hi : ZeroPadding.config (caps w) (loopStart b w xs)=
      RepeatMachine.cfg 0 (CompetitorCountAccumulator.cfg CompetitorCountAccumulator.machine.start zeroStore b w
        ([]++CompetitorCountFold.raw b xs++[]) 0) xs.length 1 := by
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i
      fin_cases i <;> simp [ZeroPadding.config,caps,loopStart,input,zeroStore,
        RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases,
        CompetitorCountAccumulator.cfg,CompetitorCountAccumulator.Store.tapes,ZeroPadding.pad]
  obtain ⟨padded,hpad,hfinal,_,_⟩ := ZeroPadding.run_config CompetitorCountFold.machine (caps w) _ _ r hr
  rw [hi] at hpad
  have he : padded=base := Option.some.inj (hpad.symm.trans hbase)
  rw [he,hf] at hfinal
  refine ⟨?_,?_,?_⟩
  · have hh := congrArg (fun c : Configuration 9 (Fintype.card (RepeatMachine.Control 17)) => c.heads) hfinal
    change _=r.final.heads at hh
    rw [← hh]
    simp only [List.length_nil,Nat.zero_add]
    funext i;fin_cases i <;> rfl
  · have ht := congrArg (fun c : Configuration 9 (Fintype.card (RepeatMachine.Control 17)) => c.tapes 1) hfinal
    simpa [ZeroPadding.config,caps,ZeroPadding.pad,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases,
      CompetitorCountAccumulator.cfg,CompetitorCountAccumulator.Store.tapes] using ht.symm
  · have ht := congrArg (fun c : Configuration 9 (Fintype.card (RepeatMachine.Control 17)) => c.tapes 2) hfinal
    simpa [ZeroPadding.config,caps,ZeroPadding.pad,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases,
      CompetitorCountAccumulator.cfg,CompetitorCountAccumulator.Store.tapes] using ht.symm

theorem entry_head_run (b w : ℕ) (xs : List ℕ) (hw : b≤w)
    (hx : ∀ x∈xs,x<2^b) (hfit : xs.sum<2^w) :
    ∃ r : ExecutionReceipt 9 (2+Fintype.card (RepeatMachine.Control 17)),
      run machine (xs.length*(16*w+20)+5) (input b w xs)=some r ∧
      r.final.tapes 5=frame (binary w xs.sum) ∧ r.final.tapes 0=CompetitorCountFold.raw b xs ∧
      r.steps=xs.length*(16*w+20)+5 ∧ r.final.heads=finalHeads b xs.length ∧
      r.final.tapes 1=List.replicate b true ∧ r.final.tapes 2=List.replicate w true := by
  obtain ⟨start,hs,hsf,hss⟩ := enter_run (input b w xs)
  obtain ⟨loop,hl,hl5,hl0,hls⟩ := loop_run b w xs hw hx hfit
  obtain ⟨hh,h1,h2⟩ := loop_endpoint b w xs hw hx hfit loop hl
  have he : Composition.restart start.final CompetitorCountFold.machine.start=loopStart b w xs := by
    rw [hsf]
    rfl
  have hl' : runFrom CompetitorCountFold.machine (xs.length*(16*w+20)+3)
      (Composition.restart start.final CompetitorCountFold.machine.start)=some loop := by
    rw [he]
    exact hl
  have hj := Composition.run_join enter CompetitorCountFold.machine 1 (xs.length*(16*w+20)+3) _ start loop hs hl'
  have ht : 1+1+(xs.length*(16*w+20)+3)=xs.length*(16*w+20)+5 := by omega
  rw [ht] at hj
  refine ⟨Composition.joinedReceipt start loop,hj,hl5,hl0,?_,hh,h1,h2⟩
  change start.steps+1+loop.steps=_
  omega

end NearCubicWires.RepairOrdinary.CompetitorCountEntry
