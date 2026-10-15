import Proof.Amplification.RecoverySourceClauseAppend

/-! The original source-clause body now appends and physically erases its
scratch. Its exact output is the next iteration's input on the same tapes. -/
namespace NearCubicWires.RepairSource.RecoverySourceClauseReuse
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
open SourceInterfaces ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scratch_coverage (i : Fin 276) (hi : RecoverySourceClauseLoad.work i) :
    ∃ j,scratch j=i := by
  have hn159 : i.val≠159 := fun he=>hi.1 (Fin.ext he)
  have hn272 : i.val≠272 := fun he=>hi.2 (Fin.ext he)
  have hlt:=i.isLt
  by_cases h159 : i.val<159
  · refine ⟨⟨i.val,by omega⟩,?_⟩
    apply Fin.ext
    simp only [scratch,h159,ite_true]
  by_cases h272 : i.val<272
  · refine ⟨⟨i.val-1,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [scratch]
    split_ifs <;> omega
  · refine ⟨⟨i.val-2,by omega⟩,?_⟩
    apply Fin.ext
    dsimp [scratch]
    split_ifs <;> omega

theorem erase_away (i : Fin 280) (hi : i=159 ∨ i=272 ∨ i=276 ∨ i=277) :
    ∀ j,eraseSlots j≠i := by
  intro j
  refine Fin.addCases (m:=275) (n:=1) (fun j=>?_) (fun j=>?_) j
  · refine Fin.addCases (m:=274) (n:=1) (fun j=>?_) (fun j=>?_) j
    · intro he
      simp only [eraseSlots,Fin.addCases_left] at he
      have hv:=congrArg (fun k : Fin 280=>k.val) he
      change (scratch j).val=i.val at hv
      have hw:=scratch_work j
      have hn159 : (scratch j).val≠159 := fun h=>hw.1 (Fin.ext h)
      have hn272 : (scratch j).val≠272 := fun h=>hw.2 (Fin.ext h)
      have hlt:=(scratch j).isLt
      rcases hi with rfl|rfl|rfl|rfl <;> omega
    · simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right]
      rcases hi with rfl|rfl|rfl|rfl <;> decide
  · simp only [eraseSlots,Fin.addCases_right]
    rcases hi with rfl|rfl|rfl|rfl <;> decide

theorem coverage (i : Fin 280) :
    (i=159 ∨ i=272 ∨ i=276 ∨ i=277) ∨ ∃ j,eraseSlots j=i := by
  by_cases h159 : i=159
  · exact Or.inl (Or.inl h159)
  by_cases h272 : i=272
  · exact Or.inl (Or.inr (Or.inl h272))
  by_cases h276 : i=276
  · exact Or.inl (Or.inr (Or.inr (Or.inl h276)))
  by_cases h277 : i=277
  · exact Or.inl (Or.inr (Or.inr (Or.inr h277)))
  right
  by_cases h278 : i=278
  · exact ⟨274,h278.symm⟩
  by_cases h279 : i=279
  · exact ⟨275,h279.symm⟩
  have hlt : i.val<276 := by
    have hi:=i.isLt
    have h276v : i.val≠276 := fun h=>h276 (Fin.ext h)
    have h277v : i.val≠277 := fun h=>h277 (Fin.ext h)
    have h278v : i.val≠278 := fun h=>h278 (Fin.ext h)
    have h279v : i.val≠279 := fun h=>h279 (Fin.ext h)
    omega
  let k : Fin 276 := ⟨i.val,hlt⟩
  have hw : RecoverySourceClauseLoad.work k := by
    constructor
    · intro h; apply h159; exact Fin.ext (congrArg (fun j : Fin 276=>j.val) h)
    · intro h; apply h272; exact Fin.ext (congrArg (fun j : Fin 276=>j.val) h)
  obtain ⟨j,hj⟩ := scratch_coverage k hw
  refine ⟨(j.castAdd 1).castAdd 1,?_⟩
  simp only [eraseSlots,Fin.addCases_left,hj]
  rfl

theorem body_run {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n))
    (clause : Fin 3→Literal (pcp.queryCount n)) (pre suffix out : List Bool) (cap : Nat)
    (hcap : RecoverySourceClauseLoad.uniformBudget (pcp.queryCount n) (pcp.nativeWidth n)≤cap) : ∃ r,
    runFrom machine (5*cap+9)
      ⟨machine.start,heads pre.length out.length,
        data (RecoverySourceClauseRead.source pre (fun i=>(literalCode (clause i)).bits) suffix)
          (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness)) out cap⟩=some r ∧
      r.final.heads=heads
        (pre++RecoverySourceClauseRead.prefixes (fun i=>(literalCode (clause i)).bits) 3).length
        (out++frame (RecoverySourceClauseCode.word pcp x randomness clause)).length ∧
      r.final.tapes=
        data (RecoverySourceClauseRead.source pre (fun i=>(literalCode (clause i)).bits) suffix)
          (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness))
          (out++frame (RecoverySourceClauseCode.word pcp x randomness clause)) cap ∧
      r.steps≤5*cap+9 := by
  obtain ⟨a,ha,ah,atapes,awork,asteps⟩ := append_run pcp x randomness clause pre suffix out cap hcap
  let backing : Fin 274→List Bool := fun j=>a.final.tapes (nativeSlots (scratch j))
  have hin (j : Fin 276) : a.final.tapes (eraseSlots j)=
      (Fin.addCases (m:=275) (n:=1) (motive:=fun _=>List Bool)
        (Fin.addCases (m:=274) (n:=1) (motive:=fun _=>List Bool)
          backing (fun _=>List.replicate cap true))
        (fun _=>List.replicate (cap+1) false)) j := by
    refine Fin.addCases (m:=275) (n:=1) (fun j=>?_) (fun j=>?_) j
    · refine Fin.addCases (m:=274) (n:=1) (fun j=>?_) (fun j=>?_) j
      · simp only [eraseSlots,Fin.addCases_left,backing]
      · simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right]
        exact atapes 278 (by simp only [retained]; tauto)
    · simp only [eraseSlots,Fin.addCases_right]
      exact atapes 279 (by simp only [retained]; tauto)
  have hheads (j : Fin 276) : a.final.heads (eraseSlots j)=0 := by
    rw [ah]
    refine Fin.addCases (m:=275) (n:=1) (fun j=>?_) (fun j=>?_) j
    · refine Fin.addCases (m:=274) (n:=1) (fun j=>?_) (fun j=>?_) j
      · have hw:=scratch_work j
        have hn272 : (scratch j).val≠272 := fun h=>hw.2 (Fin.ext h)
        have hn276 : (scratch j).val≠276 := by have hi:=(scratch j).isLt; omega
        simp only [eraseSlots,Fin.addCases_left,heads,nativeSlots,Fin.val_castAdd,hn272,hn276,ite_false]
      · simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right]; rfl
    · simp only [eraseSlots,Fin.addCases_right]; rfl
  have ready := RecoveryScratchErase.erase_ready cap (cap+1) backing awork
  obtain ⟨b,hb,bh,bt,bs⟩ := ready.focus_at eraseSlots erase_injective a.final.heads a.final.tapes hin hheads
  have hall := Composition.run_join prefixMachine eraseMachine _ _ _ a b ha hb
  have htime : 3*cap+4+1+(2*cap+4)=5*cap+9 := by omega
  rw [htime] at hall
  refine ⟨_,hall,bh.trans ah,?_,?_⟩
  · change b.final.tapes=_
    rw [bt]
    funext i
    rcases coverage i with hi|⟨j,rfl⟩
    · rw [install_other eraseSlots _ _ _ (erase_away i hi)]
      exact atapes i (by rcases hi with h|h|h|h <;> subst i <;> simp only [retained] <;> tauto)
    · rw [install_slot eraseSlots erase_injective]
      refine Fin.addCases (m:=275) (n:=1) (fun j=>?_) (fun j=>?_) j
      · refine Fin.addCases (m:=274) (n:=1) (fun j=>?_) (fun j=>?_) j
        · have hw:=scratch_work j
          have hn159 : (scratch j).val≠159 := fun h=>hw.1 (Fin.ext h)
          have hn272 : (scratch j).val≠272 := fun h=>hw.2 (Fin.ext h)
          have hlt:=(scratch j).isLt
          have hn276 : (scratch j).val≠276 := by omega
          have hn278 : (scratch j).val≠278 := by omega
          have hn279 : (scratch j).val≠279 := by omega
          simp only [eraseSlots,Fin.addCases_left,data,nativeSlots,Fin.val_castAdd,
            hn159,hn272,hn276,hn278,hn279,ite_false]
        · simp only [eraseSlots,Fin.addCases_left,Fin.addCases_right]; rfl
      · simp only [eraseSlots,Fin.addCases_right,max_self]; rfl
  · change a.steps+1+b.steps≤5*cap+9
    omega

end NearCubicWires.RepairSource.RecoverySourceClauseReuse
