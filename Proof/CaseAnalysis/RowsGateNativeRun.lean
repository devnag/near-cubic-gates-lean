import Proof.CaseAnalysis.RowsGateNativeLayout

/-! Complete physical supported-gate request from the same parsed fields:
paid arity prefix, one supported weight pass, and strict signed threshold.
All three stages append on one output tape. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsGateNative
open LocalBitMultitape RepairRepresentation CloseoutRowsGateSupport
open RepairSource.VerifierDecoding RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem native_run (compressed : Bool) (fields : List (Bool×List Bool))
    (membership source : List Bool) (n w : ℕ) (hw : ∀ field∈fields,field.2.length ≤ w) : ∃ actual,
    run (machine compressed) (budget compressed fields membership n w)
      (input fields membership source n)=some actual ∧
      actual.steps ≤ budget compressed fields membership n w ∧
      actual.final.tapes 23=word compressed fields membership source n ∧
      actual.final.heads 23=(word compressed fields membership source n).length ∧
      actual.final.tapes 25=[validity fields membership true fields.length] := by
  obtain ⟨a,ha,as,aTape,ah,ao⟩ := CloseoutRowsGateNativePrefix.prefix_run compressed fields.length membership
    (fieldsInput fields membership source n) rfl rfl
  let firstRun := TapeEmbedding.receipt (fun _ : Fin 14 => 0) (fun _ : Fin 14 => []) a
  have firstReady := TapeEmbedding.run_embed (CloseoutRowsGateNativePrefix.machine compressed)
    (fun _ : Fin 14 => 0) (fun _ : Fin 14 => []) _ _ a ha
  rw [StreamPrepare.embed_initial] at firstReady
  have oldT (i : Fin 5) : firstRun.final.tapes (i.castAdd 33)=fieldsInput fields membership source n i :=
    (TapeEmbedding.receipt_tapes_old _ _ _ (i.castAdd 19)).trans (ao i).1
  have oldH (i : Fin 5) : firstRun.final.heads (i.castAdd 33)=0 :=
    (TapeEmbedding.receipt_heads_old _ _ _ (i.castAdd 19)).trans (ao i).2
  have fresh (i : Fin 38) (hi : 24 ≤ i.val) : firstRun.final.tapes i=[] ∧ firstRun.final.heads i=0 := by
    let j : Fin 14 := ⟨i.val-24,by omega⟩
    have he : i=j.natAdd 24 := Fin.ext (by dsimp [j];omega)
    rw [he]
    exact ⟨TapeEmbedding.receipt_tapes_new _ _ _ j,TapeEmbedding.receipt_heads_new _ _ _ j⟩
  let out := natWord (arity compressed fields membership)
  have prefixT : firstRun.final.tapes 23=out :=
    (TapeEmbedding.receipt_tapes_old _ _ _ 23).trans aTape
  have prefixH : firstRun.final.heads 23=out.length :=
    (TapeEmbedding.receipt_heads_old _ _ _ 23).trans ah
  obtain ⟨base,hbase,baseSteps,baseTape,baseHead,baseFlag⟩ :=
    CloseoutRowsGateSupport.append_run compressed fields membership out w hw
  obtain ⟨b,hb,_,bs,bh,bt,bkeep⟩ := RecoveryFocus.dock supportSlots support_injective
    (preparedMachine compressed) _ firstRun.final.heads firstRun.final.tapes _
    (by
      intro i;fin_cases i
      · exact oldH 0
      · exact (fresh 24 (by decide)).2
      · exact prefixH
      · exact oldH 2
      · exact (fresh 25 (by decide)).2
      · exact oldH 1)
    (by
      intro i;fin_cases i
      · exact oldT 0
      · exact (fresh 24 (by decide)).1
      · exact prefixT
      · exact oldT 2
      · exact (fresh 25 (by decide)).1
      · exact oldT 1) base hbase
  have firstJoined := Composition.run_join (prefixMachine compressed) (support compressed)
    _ _ _ firstRun b firstReady hb
  let withWeights := out++weights compressed fields membership
  have weightT : b.final.tapes 23=withWeights := (bt 2).trans baseTape
  have weightH : b.final.heads 23=withWeights.length := (bh 2).trans baseHead
  have bOld (i : Fin 5) (hi : i=3 ∨ i=4) :
      b.final.tapes (i.castAdd 33)=fieldsInput fields membership source n i ∧
      b.final.heads (i.castAdd 33)=0 := by
    have hn : ∀ j,supportSlots j≠i.castAdd 33 := by
      rcases hi with rfl|rfl <;> decide
    exact ⟨(bkeep _ hn).2.trans (oldT i),(bkeep _ hn).1.trans (oldH i)⟩
  have bFresh (i : Fin 38) (hi : 26 ≤ i.val) : b.final.tapes i=[] ∧ b.final.heads i=0 := by
    have hn : ∀ j,supportSlots j≠i := by
      intro j he
      have hv := congrArg Fin.val he
      fin_cases j <;> simp [supportSlots] at hv <;> omega
    exact ⟨(bkeep i hn).2.trans (fresh i (by omega)).1,
      (bkeep i hn).1.trans (fresh i (by omega)).2⟩
  have strictH (i : Fin 15) : b.final.heads (strictSlots i)=
      (CloseoutRowsStrictNative.entry source n [] withWeights).heads i := by
    rw [strict_entry_heads]
    by_cases h0 : i.val=0
    · have he : i=0 := Fin.ext h0
      subst i
      exact (bOld 4 (Or.inr rfl)).2
    by_cases h10 : i.val=10
    · have he : i=10 := Fin.ext h10
      subst i
      exact (bOld 3 (Or.inl rfl)).2
    by_cases h14 : i.val=14
    · have he : i=14 := Fin.ext h14
      subst i
      exact weightH
    · rw [if_neg h14]
      exact (bFresh _ (strict_fresh i h0 h10 h14)).2
  have strictT (i : Fin 15) : b.final.tapes (strictSlots i)=
      (CloseoutRowsStrictNative.entry source n [] withWeights).tapes i := by
    rw [strict_entry_tapes]
    by_cases h0 : i.val=0
    · have he : i=0 := Fin.ext h0
      subst i
      exact (bOld 4 (Or.inr rfl)).1
    by_cases h10 : i.val=10
    · have he : i=10 := Fin.ext h10
      subst i
      exact (bOld 3 (Or.inl rfl)).1
    by_cases h14 : i.val=14
    · have he : i=14 := Fin.ext h14
      subst i
      exact weightT
    · rw [if_neg h0,if_neg h10,if_neg h14]
      exact (bFresh _ (strict_fresh i h0 h10 h14)).1
  obtain ⟨last,hl,lastSteps,lastTape,lastHead⟩ := CloseoutRowsStrictNative.native_run source n [] withWeights
  obtain ⟨c,hc,_,cs,ch,ct,ckeep⟩ := RecoveryFocus.dock strictSlots strict_injective CloseoutRowsStrictNative.machine
    _ b.final.heads b.final.tapes _ strictH strictT last hl
  have joined := Composition.run_join (first compressed) strict _ _ _
    (Composition.joinedReceipt firstRun b) c firstJoined hc
  refine ⟨Composition.joinedReceipt (Composition.joinedReceipt firstRun b) c,joined,?_,?_,?_,?_⟩
  · change firstRun.steps+1+b.steps+1+c.steps ≤ _
    change a.steps+1+b.steps+1+c.steps ≤ _
    unfold budget
    omega
  · exact (ct 14).trans lastTape
  · exact (ch 14).trans lastHead
  · have hn : ∀ j,strictSlots j≠(25 : Fin 38) := by
      intro j he
      have hv := congrArg Fin.val he
      unfold strictSlots at hv
      split_ifs at hv <;> simp at hv <;> omega
    exact (ckeep 25 hn).2.trans ((bt 4).trans baseFlag)

end NearCubicWires.RepairOrdinary.CloseoutRowsGateNative
