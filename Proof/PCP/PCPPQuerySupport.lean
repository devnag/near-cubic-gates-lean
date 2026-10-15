import Proof.PCP.PCPPQueryRows

/-! Actual metadata parsing and support-row selection on the explicit PCPP
output. Only the physical arity and query-index drivers remain entry inputs
at this prepared-object scope; the metadata offset is produced here. -/
namespace NearCubicWires.RepairOrdinary.PCPPQuerySupport
open LocalBitMultitape RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4→Fin 6 := ![3,0,4,5]
def header : Machine 6 16 := TapeEmbedding.machine 3 (PCPPQueryField.four false)
noncomputable def rows := RecoveryFocus.machine slots PCPPQueryRows.machine
noncomputable def machine := Composition.machine header rows
noncomputable def entry (source : List Bool) (arity index : ℕ) :=
  (⟨machine.start,![0,0,0,1,0,1],![source,[],[],UnaryTemplate.tape arity,[],CompareMachine.word index]⟩ :
    Configuration 6 (16+(Fintype.card (RepeatMachine.Control 5)+5)))
def budget (a b c arity index : ℕ) := PCPPQueryField.fourCost 3 a b c+1+PCPPQueryRows.budget arity index

theorem support_run (a b c arity : ℕ) (pre : List (List Bool))
    (row tail : List Bool) (hp : ∀ r∈pre,r.length=arity) (hr : row.length=arity) :
    let source := PCPPQueryField.fourBits 3 a b c++pre.flatten++row++tail
    ∃ r,runFrom machine (budget a b c arity pre.length) (entry source arity pre.length)=some r ∧
      r.final.tapes 0=source ∧
      r.final.heads 0=(PCPPQueryField.fourBits 3 a b c).length+pre.flatten.length+arity ∧
      r.final.tapes 3=UnaryTemplate.tape arity ∧ r.final.heads 3=1 ∧
      r.final.tapes 4=row ∧ r.final.heads 4=arity ∧
      r.final.tapes 5=CompareMachine.word pre.length ∧ r.final.heads 5=1 ∧
      r.steps=budget a b c arity pre.length := by
  dsimp only
  let fields := PCPPQueryField.fourBits 3 a b c
  let source := fields++pre.flatten++row++tail
  obtain ⟨first,hfirst,hff,hfs⟩ := PCPPQueryField.four_run false [] (pre.flatten++row++tail) [] [] 3 a b c
  have hsource : []++PCPPQueryField.fourBits 3 a b c++(pre.flatten++row++tail)=source := by
    simp [source,fields,List.append_assoc]
  rw [hsource] at hfirst hff
  simp only [List.length_nil,Nat.zero_add,PCPPQueryField.selected,Bool.false_eq_true,↓reduceIte,List.append_nil] at hfirst hff
  let extraHeads : Fin 3→ℕ := ![1,0,1]
  let extraTapes : Fin 3→List Bool := ![UnaryTemplate.tape arity,[],CompareMachine.word pre.length]
  have ha := TapeEmbedding.run_embed (PCPPQueryField.four false) extraHeads extraTapes _ _ first hfirst
  let ambient := TapeEmbedding.config extraHeads extraTapes first.final
  obtain ⟨localRun,hl,h0,h0h,h1,h1h,h2,h2h,h3,h3h,hsteps⟩ :=
    PCPPQueryRows.row_run arity fields pre row tail [] hp hr
  let localEntry := Composition.leftConfig 5 (PCPPQueryRows.cfg 0 arity source fields.length [] pre.length 1)
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes localEntry=
      Composition.restart ambient rows.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      dsimp only [ambient]
      rw [hff]
      fin_cases i <;> simp [localEntry,Composition.leftConfig,PCPPQueryRows.cfg,RepeatMachine.cfg,
        controlConfig,MatrixRawBlock.config,PCPPQueryField.store,slots,TapeEmbedding.config,
        extraHeads,Fin.addCases,fields]
    · intro i
      dsimp only [ambient]
      rw [hff]
      fin_cases i <;> simp [localEntry,Composition.leftConfig,PCPPQueryRows.cfg,RepeatMachine.cfg,
        controlConfig,MatrixRawBlock.config,PCPPQueryField.store,slots,TapeEmbedding.config,
        extraTapes,Fin.addCases]
  have hl' : runFrom PCPPQueryRows.machine (PCPPQueryRows.budget arity pre.length) localEntry=some localRun := hl
  obtain ⟨focused,hfocus,hfocusFinal,hfocusSteps⟩ := RecoveryFocus.run_config slots (by decide)
    PCPPQueryRows.machine ambient.heads ambient.tapes _ localEntry localRun hl'
  rw [hi] at hfocus
  have hj := Composition.run_join header rows (PCPPQueryField.fourCost 3 a b c)
    (PCPPQueryRows.budget arity pre.length) _ (TapeEmbedding.receipt extraHeads extraTapes first) focused ha hfocus
  have he : Composition.leftConfig (Fintype.card (RepeatMachine.Control 5)+5)
      (TapeEmbedding.config extraHeads extraTapes (PCPPQueryField.store 0 source 0 [] []))=
      entry source arity pre.length := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [he] at hj
  have ht (i : Fin 4) : focused.final.tapes (slots i)=localRun.final.tapes i := by
    simp only [hfocusFinal,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  have hh (i : Fin 4) : focused.final.heads (slots i)=localRun.final.heads i := by
    simp only [hfocusFinal,RecoveryFocus.config,RecoveryFocus.pick_slot slots (by decide)]
  refine ⟨Composition.joinedReceipt (TapeEmbedding.receipt extraHeads extraTapes first) focused,hj,
    (ht 1).trans h1,(hh 1).trans h1h,(ht 0).trans h0,(hh 0).trans h0h,
    (ht 2).trans (by simpa using h2),(hh 2).trans (by simpa [hr] using h2h),
    (ht 3).trans h3,(hh 3).trans h3h,?_⟩
  change first.steps+1+focused.steps=_
  rw [hfs,hfocusSteps,hsteps]
  rfl

end NearCubicWires.RepairOrdinary.PCPPQuerySupport
