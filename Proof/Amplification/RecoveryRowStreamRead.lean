import Proof.Amplification.RecoveryRowStreamState

/-! The actual streamed four-field read feeds the clause workspace in the
shared row layout. Short rows retain an exact false status without imposing
unneeded restoration on their discarded arithmetic workspace. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowStream
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
open RecoveryClauseEvaluation
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem routing_other (left right : Fin 42→List Bool)
    (kind nextKind : List Bool) (flags : Fin 3→Bool) (old tail : Fin 5→List Bool)
    (hc : ∀ j : Fin 42,j≠0 → left j=right j) (i : Fin 51) (hi : ∀ j,rowSlots j≠i) :
    Fin.addCases (m:=46) (n:=5) (motive:=fun _=>List Bool) (RecoveryRowLeaf.tapes left kind flags) old i=
      Fin.addCases (m:=46) (n:=5) (motive:=fun _=>List Bool) (RecoveryRowLeaf.tapes right nextKind flags) tail i := by
  refine Fin.addCases (m:=46) (n:=5) (motive:=fun k=>(∀ j,rowSlots j≠k) →
    Fin.addCases (m:=46) (n:=5) (motive:=fun _=>List Bool) (RecoveryRowLeaf.tapes left kind flags) old k=
      Fin.addCases (m:=46) (n:=5) (motive:=fun _=>List Bool) (RecoveryRowLeaf.tapes right nextKind flags) tail k) ?_ ?_ i hi
  · intro j hj
    simp only [Fin.addCases_left]
    refine Fin.addCases (m:=42) (n:=4) (motive:=fun k=>(∀ a,rowSlots a≠k.castAdd 5) →
      RecoveryRowLeaf.tapes left kind flags k=RecoveryRowLeaf.tapes right nextKind flags k) ?_ ?_ j hj
    · intro k hk
      have h0 : k≠0 := by intro he; subst k; exact hk 4 rfl
      simpa only [RecoveryRowLeaf.tapes,Fin.addCases_left] using hc k h0
    · intro k hk
      simp only [RecoveryRowLeaf.tapes,Fin.addCases_right]
      fin_cases k
      · exact False.elim (hk 1 rfl)
      all_goals rfl
  · intro j hj
    fin_cases j
    · exact False.elim (hj 2 rfl)
    · exact False.elim (hj 3 rfl)
    · exact False.elim (hj 0 rfl)
    · exact False.elim (hj 5 rfl)
    · exact False.elim (hj 6 rfl)

theorem afterRead_other_tapes (d : Data) (bits : List Bool) (hw : 4*d.state.bits.length ≤ bits.length)
    {s : Nat} (q : Fin s) (i : Fin 51) (hi : ∀ j,rowSlots j≠i) :
    (d.cfg q).tapes i=((d.afterRead bits).cfg q).tapes i := by
  exact routing_other (RecoveryClauseEvaluation.tapes d.state d.extra)
    (RecoveryClauseEvaluation.tapes (d.afterRead bits).state (d.afterRead bits).extra)
    d.kind (d.afterRead bits).kind d.flags d.right (d.afterRead bits).right
    (fun j hj=>(replace_other d.state d.extra _ (words_length _ _ 3 hw) j hj).symm) i hi

theorem afterRead_other_heads (d : Data) (bits : List Bool) {s : Nat} (q : Fin s)
    (i : Fin 51) (hi : ∀ j,rowSlots j≠i) :
    (d.cfg q).heads i=((d.afterRead bits).cfg q).heads i := by
  refine Fin.addCases (m:=46) (n:=5) (motive:=fun k=>(∀ j,rowSlots j≠k) →
    (d.cfg q).heads k=((d.afterRead bits).cfg q).heads k) ?_ ?_ i hi
  · intro j _; simp [Data.cfg]
  · intro j hj
    fin_cases j
    · rfl
    · rfl
    · exact False.elim (hj 0 rfl)
    · rfl
    · rfl

open private focus_configuration from Proof.Amplification.RecoveryValuationStreamTapes

theorem read_output (d : Data) (bits : List Bool) (hw : 4*d.state.bits.length ≤ bits.length) :
    RecoveryFocus.config rowSlots (d.cfg readMachine.start).heads (d.cfg readMachine.start).tapes
      (RecoveryRowFields.terminal ({RecoveryRowFields.afterReads d.reader 0 4 bits with valid:=true} : RecoveryRowFields.Data))=
      (d.afterRead bits).cfg (RecoveryCalls.controlCode RecoveryRowFields.sizes none) := by
  let out : RecoveryRowFields.Data := {RecoveryRowFields.afterReads d.reader 0 4 bits with valid:=true}
  have hsource : out.source=d.source := RecoveryRowFields.afterReads_source d.reader 0 4 bits
  have hwidth : out.width=d.state.bits.length := RecoveryRowFields.afterReads_width d.reader 0 4 bits
  have hpos : out.pos=d.pos+8*d.state.bits.length := by
    have h := RecoveryRowFields.afterReads_pos d.reader 0 4 bits hw
    change out.pos=d.pos+8*d.state.bits.length
    simpa only [out,Data.reader,show 2*(4*d.state.bits.length)=8*d.state.bits.length by omega] using h
  have hfields : ∀ i,out.fields i=frame (RecoveryRowFields.words d.state.bits.length bits i) :=
    RecoveryRowFields.four_fields d.reader bits
  change RecoveryFocus.config rowSlots (d.cfg readMachine.start).heads (d.cfg readMachine.start).tapes
      (RecoveryRowFields.terminal out)=_
  apply focus_configuration rowSlots rowSlots_injective
  · rfl
  · intro j
    fin_cases j
    · exact hpos
    all_goals rfl
  · intro j
    fin_cases j
    · exact hsource
    · exact hfields 0
    · exact hfields 1
    · exact hfields 2
    · exact hfields 3
    · change RepairSource.VerifierDecoding.CompareMachine.word out.width=
        RepairSource.VerifierDecoding.CompareMachine.word (d.afterRead bits).state.bits.length
      rw [hwidth,afterRead_width d bits hw]
    · rfl
  · intro i hi
    exact afterRead_other_heads d bits _ i hi
  · intro i hi
    exact afterRead_other_tapes d bits hw _ i hi

theorem read_run (d : Data) (word pre bits : List Bool) (hd : d.Valid word)
    (hs : d.source=pre++frame bits) (hp : d.pos=pre.length) :
    ∃ r,runFrom readMachine (RecoveryRowFields.budget d.state.bits.length)
        (d.cfg readMachine.start)=some r ∧
      r.steps ≤ RecoveryRowFields.budget d.state.bits.length ∧
      r.final.heads 50=0 ∧ r.final.tapes 50=[(readRow d.state.bits.length bits).isSome] ∧
      ((readRow d.state.bits.length bits).isSome=true →
        r.final=(d.afterRead bits).cfg (RecoveryCalls.controlCode RecoveryRowFields.sizes none)) := by
  obtain ⟨base,hr,hn,hh,ht,hf⟩ := RecoveryRowFields.row_run d.reader pre bits hs hp (reader_valid d word hd)
  obtain ⟨r,hrun,hfinal,hsteps⟩ := RecoveryFocus.run_config rowSlots rowSlots_injective
    RecoveryRowFields.machine (d.cfg readMachine.start).heads (d.cfg readMachine.start).tapes _ _ base hr
  rw [read_input d] at hrun
  have hpick : RecoveryFocus.pick rowSlots (50 : Fin 51)=some 6 :=
    RecoveryFocus.pick_slot rowSlots rowSlots_injective 6
  refine ⟨r,hrun,hsteps.le.trans hn,?_,?_,?_⟩
  · simpa [hfinal,RecoveryFocus.config,hpick] using hh
  · simpa [hfinal,RecoveryFocus.config,hpick,Data.reader] using ht
  · intro ha
    have hw : 4*d.state.bits.length ≤ bits.length := by
      rw [RecoveryCertificateRow.row_isSome,decide_eq_true_eq] at ha
      exact ha
    rw [hfinal,hf ha]
    exact read_output d bits hw

end NearCubicWires.RepairOrdinary.RecoveryRowStream
