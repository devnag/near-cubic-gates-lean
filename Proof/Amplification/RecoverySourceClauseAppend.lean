import Proof.Amplification.RecoverySourceClauseReuseLayout

/-! Append one physically read original clause to the recovery formula.
All literal scratch is bounded for the immediately following paid erase. -/
namespace NearCubicWires.RepairSource.RecoverySourceClauseReuse
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
open SourceInterfaces ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev retained (i : Fin 280) : Prop :=
  i=159 ∨ i=272 ∨ i=276 ∨ i=277 ∨ i=278 ∨ i=279

theorem append_run {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n))
    (clause : Fin 3→Literal (pcp.queryCount n)) (pre suffix out : List Bool) (cap : Nat)
    (hcap : RecoverySourceClauseLoad.uniformBudget (pcp.queryCount n) (pcp.nativeWidth n)≤cap) : ∃ r,
    runFrom prefixMachine (3*cap+4)
      ⟨prefixMachine.start,heads pre.length out.length,
        data (RecoverySourceClauseRead.source pre (fun i=>(literalCode (clause i)).bits) suffix)
          (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness)) out cap⟩=some r ∧
      r.final.heads=heads
        (pre++RecoverySourceClauseRead.prefixes (fun i=>(literalCode (clause i)).bits) 3).length
        (out++frame (RecoverySourceClauseCode.word pcp x randomness clause)).length ∧
      (∀ i,retained i → r.final.tapes i=
        data (RecoverySourceClauseRead.source pre (fun i=>(literalCode (clause i)).bits) suffix)
          (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness))
          (out++frame (RecoverySourceClauseCode.word pcp x randomness clause)) cap i) ∧
      (∀ j : Fin 274,(r.final.tapes (nativeSlots (scratch j))).length≤cap) ∧
      r.steps≤3*cap+4 := by
  let codes : Fin 3→List Bool := fun i=>(literalCode (clause i)).bits
  let address := FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness)
  let source := RecoverySourceClauseRead.source pre codes suffix
  let word := RecoverySourceClauseCode.word pcp x randomness clause
  let pos := (pre++RecoverySourceClauseRead.prefixes codes 3).length
  obtain ⟨base,hbase,bword,baddress,bsource,bpos,bheads,bwork,bs⟩ :=
    RecoverySourceClauseLoad.padded_clause_run pcp x randomness clause pre suffix cap hcap
  obtain ⟨a,ha,_ac,asteps,ah,atapes,akeep⟩ := RecoveryFocus.dock nativeSlots native_injective
    RecoverySourceClauseLoad.machine _ (heads pre.length out.length) (data source address out cap) _
    (fun j=>(native_input pre codes suffix address out cap j).1)
    (fun j=>(native_input pre codes suffix address out cap j).2) base hbase
  have aheads : a.final.heads=heads pos out.length := by
    funext i
    by_cases hi : i.val<276
    · let j : Fin 276 := ⟨i.val,hi⟩
      have he : nativeSlots j=i := Fin.ext rfl
      rw [←he,ah]
      by_cases hj : j=272
      · rw [hj]; exact bpos
      · rw [bheads j hj]
        have hn272 : j.val≠272 := fun hh=>hj (Fin.ext hh)
        have hn276 : j.val≠276 := by have hlt:=j.isLt; omega
        simp only [heads,nativeSlots,Fin.val_castAdd,hn272,hn276,ite_false]
    · rw [(akeep i (outside_native i (by omega))).1]
      have hn272 : i.val≠272 := by omega
      simp only [heads,hn272,ite_false]
  have aword : a.final.tapes 262=ZeroPadding.pad cap (frame word) := (atapes 262).trans bword
  have wordFits : 2*word.length+1≤cap := by
    have hw:=bwork 262 (by decide)
    rw [bword,ZeroPadding.pad_length,frame_length] at hw
    change max cap (2*word.length+1)≤cap at hw
    omega
  obtain ⟨b,hb,bh,bt,bstep⟩ := CompetitorFieldEmit.field_run (262 : Fin 280) 276 277
    (by decide) (by decide) (by decide) word out cap a.final.heads a.final.tapes
    (by rw [aheads]; rfl) (by rw [aheads]; rfl) (by rw [aheads]; rfl)
    aword ((akeep 276 (outside_native 276 (by decide))).2)
    ((akeep 277 (outside_native 277 (by decide))).2) wordFits
  have hall := Composition.run_join first appendMachine _ _ _ a b ha hb
  have htime : RecoverySourceClauseLoad.uniformBudget (pcp.queryCount n) (pcp.nativeWidth n)+1+
      (4*word.length+3)≤3*cap+4 := by omega
  have hmore := runFrom_moreFuel prefixMachine _
    (3*cap+4-(RecoverySourceClauseLoad.uniformBudget (pcp.queryCount n) (pcp.nativeWidth n)+1+
      (4*word.length+3))) _ _ hall
  rw [Nat.add_sub_of_le htime] at hmore
  refine ⟨_,hmore,?_,?_,?_,?_⟩
  · change b.final.heads=_
    rw [bh,aheads]
    funext i
    by_cases hi : i=276
    · subst i; rw [Function.update_self]; rfl
    · rw [Function.update_of_ne hi]
      have hv : i.val≠276 := fun he=>hi (Fin.ext he)
      simp only [heads,hv,ite_false]
      rfl
  · intro i hi
    change b.final.tapes i=_
    rw [bt]
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · rw [Function.update_of_ne (by decide : (159 : Fin 280)≠276)]
      exact (atapes 159).trans baddress
    · rw [Function.update_of_ne (by decide : (272 : Fin 280)≠276)]
      exact (atapes 272).trans bsource
    · rw [Function.update_self]; rfl
    · rw [Function.update_of_ne (by decide : (277 : Fin 280)≠276)]
      exact (akeep 277 (outside_native 277 (by decide))).2
    · rw [Function.update_of_ne (by decide : (278 : Fin 280)≠276)]
      exact (akeep 278 (outside_native 278 (by decide))).2
    · rw [Function.update_of_ne (by decide : (279 : Fin 280)≠276)]
      exact (akeep 279 (outside_native 279 (by decide))).2
  · intro j
    change (b.final.tapes (nativeSlots (scratch j))).length≤cap
    have hn : nativeSlots (scratch j)≠276 := outside_native 276 (by decide) _
    rw [bt,Function.update_of_ne hn,atapes]
    exact bwork _ (scratch_work j)
  · change a.steps+1+b.steps≤3*cap+4
    rw [asteps,bstep]
    omega

end NearCubicWires.RepairSource.RecoverySourceClauseReuse
