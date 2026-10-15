import Proof.Amplification.RecoverySourceClauseLoadLayout

/-! Actual source-stream clause emission: load the next three original
literal fields, evaluate all three projected addresses and emit their original
CNF clause code. Source cursors and all handoff steps are retained and paid. -/
namespace NearCubicWires.RepairSource.RecoverySourceClauseLoad
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
open SourceInterfaces ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def budget (codes : Fin 3→List Bool) (Q R : Nat) :=
  RecoverySourceClauseRead.budget codes+1+RecoverySourceClauseCode.uniformBudget Q R

theorem clause_run {M : TimedDecisionMachine} {T : Nat→Nat} (pcp : ProjectionPCP M T) {n : Nat}
    (x : BitInput n) (randomness : BitInput (pcp.nativeWidth n))
    (clause : Fin 3→Literal (pcp.queryCount n)) (pre suffix : List Bool) : ∃ r,
    runFrom machine (budget (fun i=>(literalCode (clause i)).bits) (pcp.queryCount n) (pcp.nativeWidth n))
      ⟨machine.start,heads pre,input pre (fun i=>(literalCode (clause i)).bits) suffix
        (FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness))⟩=some r ∧
      r.final.tapes 262=RepairOrdinary.frame (RecoverySourceClauseCode.word pcp x randomness clause) ∧
      r.final.tapes 159=FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness) ∧
      r.final.tapes 272=RecoverySourceClauseRead.source pre (fun i=>(literalCode (clause i)).bits) suffix ∧
      r.final.heads 272=(pre++RecoverySourceClauseRead.prefixes (fun i=>(literalCode (clause i)).bits) 3).length ∧
      (∀ i : Fin 276,i≠272 → r.final.heads i=0) ∧
      r.steps≤budget (fun i=>(literalCode (clause i)).bits) (pcp.queryCount n) (pcp.nativeWidth n) := by
  let codes : Fin 3→List Bool := fun i=>(literalCode (clause i)).bits
  let address := FieldList.stream (RecoverySourceLiteralMeaning.fields pcp x randomness)
  obtain ⟨reader,hReader,rf,rs⟩ := RecoverySourceClauseRead.read_run pre codes suffix
  obtain ⟨first,hFirst,_fc,fs,fh,ft,fo⟩ := RecoveryFocus.dock readSlots read_injective
    RecoverySourceClauseRead.machine (RecoverySourceClauseRead.budget codes)
    (heads pre) (input pre codes suffix address) _
    (entry_heads pre codes suffix) (entry_tapes pre codes suffix address) reader hReader
  have firstHeads : ∀ i,first.final.heads (nativeSlots i)=0 :=
    native_heads pre codes suffix first.final.heads (by intro j; rw [fh,rf]; rfl) (fun i hi=>(fo i hi).1)
  have firstTapes : ∀ i,first.final.tapes (nativeSlots i)=RecoverySourceClauseCode.input codes address i :=
    native_tapes pre codes suffix address first.final.tapes (by intro j; rw [ft,rf]; rfl) (fun i hi=>(fo i hi).2)
  obtain ⟨out,hCode,hOut,hAddress,_hValue⟩ := RecoverySourceClauseCode.bounded_clause_run pcp x randomness clause
  obtain ⟨core,hCore,ct,ch,cs⟩ := hCode
  obtain ⟨last,hLast,_lc,ls,lh,lt,lo⟩ := RecoveryFocus.dock nativeSlots native_injective
    RecoverySourceClauseCode.machine (RecoverySourceClauseCode.uniformBudget (pcp.queryCount n) (pcp.nativeWidth n))
    first.final.heads first.final.tapes _ firstHeads firstTapes core hCore
  have hall := Composition.run_join readMachine nativeMachine _ _ _ first last hFirst hLast
  refine ⟨_,hall,?_,?_,?_,?_,?_,?_⟩
  · change last.final.tapes (nativeSlots 262)=_
    rw [lt,ct]
    exact hOut
  · change last.final.tapes (nativeSlots 159)=_
    rw [lt,ct]
    exact hAddress
  · change last.final.tapes 272=_
    rw [(lo 272 (by intro i he; have hv:=congrArg Fin.val he; have hi:=i.isLt; change i.val=272 at hv; omega)).2]
    change first.final.tapes (readSlots 0)=_
    rw [ft,rf]
    rfl
  · change last.final.heads 272=_
    rw [(lo 272 (by intro i he; have hv:=congrArg Fin.val he; have hi:=i.isLt; change i.val=272 at hv; omega)).1]
    change first.final.heads (readSlots 0)=_
    rw [fh,rf]
    rfl
  · intro i hi272
    change last.final.heads i=0
    by_cases hi : i.val<272
    · let j : Fin 272 := ⟨i.val,hi⟩
      have he : i=nativeSlots j := rfl
      rw [he,lh]
      exact ch j
    · have hne : i.val≠272 := fun he=>hi272 (Fin.ext he)
      have hv : i.val=273 ∨ i.val=274 ∨ i.val=275 := by have ht:=i.isLt; omega
      have hout : ∀ j,nativeSlots j≠i := by
        intro j he; have hh:=congrArg Fin.val he; have hj:=j.isLt
        change j.val=i.val at hh
        omega
      rw [(lo i hout).1]
      rcases hv with hv|hv|hv
      · have he : i=273 := Fin.ext hv
        subst i
        change first.final.heads (readSlots 4)=0
        rw [fh,rf]; rfl
      · have he : i=274 := Fin.ext hv
        subst i
        change first.final.heads (readSlots 5)=0
        rw [fh,rf]; rfl
      · have he : i=275 := Fin.ext hv
        subst i
        change first.final.heads (readSlots 6)=0
        rw [fh,rf]; rfl
  · change first.steps+1+last.steps≤budget codes (pcp.queryCount n) (pcp.nativeWidth n)
    rw [fs,rs,ls]
    exact Nat.add_le_add_left cs _

end NearCubicWires.RepairSource.RecoverySourceClauseLoad
