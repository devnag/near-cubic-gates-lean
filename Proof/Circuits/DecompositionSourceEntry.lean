import Proof.Circuits.DecompositionSourceCounted
import Proof.Circuits.DecompositionSourceRecords

/-! Complete native source entry: one cold threshold request invokes the
same decomposition constructor once and emits the exact arity/child word
consumed by DecompositionLocalBounds.balancedSerializer. -/
namespace NearCubicWires.RepairOrdinary.DecompositionSource.Entry
open LocalBitMultitape RepairRepresentation ExecutableInterfaces Counted
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable (a : DecompositionAlgorithm)
def fieldSlots : Fin 3→Fin (tapes a) := ![sourceTape a,localTape a 14,localTape a 15]
def recordSlots : Fin 5→Fin (tapes a) :=
  ![sourceTape a,localTape a 14,localTape a 15,localTape a 12,fresh a 9]

theorem source_val : 16 ≤ (sourceTape a).val := by
  have hf := (Call.sourceProgram a).outputFresh
  simp only [sourceTape,old,Call.outputTape,Call.slots,hf,if_false,Fin.val_castAdd,Fin.val_natAdd]
  omega
theorem fieldSlots_injective : Function.Injective (fieldSlots a) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hs := source_val a
  fin_cases i <;> fin_cases j <;>
    simp [fieldSlots,localTape,old,Call.old] at hv ⊢ <;> omega
theorem recordSlots_injective : Function.Injective (recordSlots a) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hs := source_val a
  have ht := (Call.outputTape a).isLt
  have hsize : 16 ≤ Call.tapes a := by unfold Call.tapes; omega
  fin_cases i <;> fin_cases j <;>
    simp [recordSlots,localTape,sourceTape,old,Call.old,fresh] at hv ⊢ <;>
    dsimp [sourceTape,old] at hs <;> omega

theorem field_none_arity : RecoveryFocus.pick (fieldSlots a) (localTape a 12)=none := by
  have hn : ¬∃ j,fieldSlots a j=localTape a 12 := by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    have hs := source_val a
    fin_cases j <;> simp [fieldSlots,localTape,old,Call.old] at hv
    omega
  simp [RecoveryFocus.pick,hn]
theorem field_none_count : RecoveryFocus.pick (fieldSlots a) (fresh a 9)=none := by
  have hn : ¬∃ j,fieldSlots a j=fresh a 9 := by
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    have ht := (Call.outputTape a).isLt
    have hsize : 16 ≤ Call.tapes a := by unfold Call.tapes; omega
    fin_cases j <;> simp [fieldSlots,localTape,sourceTape,old,Call.old,fresh] at hv <;> omega
  simp [RecoveryFocus.pick,hn]

noncomputable def field := RecoveryFocus.machine (fieldSlots a) (PCPPQueryField.machine true)
noncomputable def prefixMachine := Composition.machine (Counted.machine a) (field a)
noncomputable def records := RecoveryFocus.machine (recordSlots a) Records.machine
noncomputable def machine := Composition.machine (prefixMachine a) (records a)
def budget (r : ExactDecompositionRequest) :=
  Counted.budget a r+PCPPQueryField.fieldCost (a.output r).children.length+
    ((a.output r).children.flatMap exactWord).length+(6*r.arity+10)*(a.output r).children.length+5
def output (r : ExactDecompositionRequest) := natWord r.arity++exactListWord (a.output r).children

theorem entry_run (r : ExactDecompositionRequest) :
    ∃ receipt,run (machine a) (budget a r) (Counted.input a r)=some receipt ∧
      receipt.steps ≤ budget a r ∧
      receipt.final.tapes (localTape a 15)=output a r ∧
      receipt.final.heads (localTape a 15)=(output a r).length ∧
      receipt.final.tapes (localTape a 12)=UnaryTemplate.tape r.arity ∧ receipt.final.heads (localTape a 12)=1 ∧
      receipt.final.tapes (fresh a 9)=UnaryTemplate.tape (a.output r).children.length ∧ receipt.final.heads (fresh a 9)=1 := by
  let gs := (a.output r).children
  obtain ⟨first,hfirst,hfs,hsource,hsourceHead,hm,hmh,hn,hnh,hback,hbackHead,hout,houtHead⟩ := Counted.counted_run a r
  have ht : ∀ j,first.final.tapes (fieldSlots a j)=
      (![[]++natWord gs.length++gs.flatMap exactWord,PCPPQueryField.saved r.arity [],natWord r.arity] : Fin 3→List Bool) j := by
    intro j
    fin_cases j
    · exact hsource
    · exact hback
    · exact hout
  have hh : ∀ j,first.final.heads (fieldSlots a j)=
      (![([] : List Bool).length,0,(natWord r.arity).length] : Fin 3→ℕ) j := by
    intro j
    fin_cases j
    · exact hsourceHead
    · exact hbackHead
    · exact houtHead
  obtain ⟨middle,hmid,hms,hmidSource,hmidSourceHead,hmidBack,hmidBackHead,hmidOut,hmidOutHead,hother⟩ :=
    Prepare.field_focus (fieldSlots a) (fieldSlots_injective a) first.final gs.length [] (gs.flatMap exactWord)
      (PCPPQueryField.saved r.arity []) (natWord r.arity) ht hh
  have hj := Composition.run_join (Counted.machine a) (field a) _ _ _ first middle hfirst hmid
  let joined := Composition.joinedReceipt first middle
  obtain ⟨last,hl,hlt,hlh,hls⟩ := Records.padded_run gs (natWord gs.length) []
    (PCPPQueryField.saved gs.length (PCPPQueryField.saved r.arity [])) (natWord r.arity++natWord gs.length)
  let localEntry : Configuration 5 _ :=
    ⟨Records.machine.start,![ (natWord gs.length).length,0,(natWord r.arity++natWord gs.length).length,1,1],
      ![natWord gs.length++gs.flatMap exactWord++[],
        PCPPQueryField.saved gs.length (PCPPQueryField.saved r.arity []),natWord r.arity++natWord gs.length,
        UnaryTemplate.tape r.arity,UnaryTemplate.tape gs.length]⟩
  obtain ⟨focused,hf,hff,hfsteps⟩ := RecoveryFocus.run_config (recordSlots a) (recordSlots_injective a)
    Records.machine joined.final.heads joined.final.tapes _ localEntry last hl
  have hi : RecoveryFocus.config (recordSlots a) joined.final.heads joined.final.tapes localEntry=
      Composition.restart joined.final (records a).start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      · change middle.final.heads (sourceTape a)=(natWord gs.length).length
        simpa [fieldSlots] using hmidSourceHead
      · exact hmidBackHead
      · exact hmidOutHead
      · change middle.final.heads (localTape a 12)=1
        rw [(hother _ (field_none_arity a)).2]
        exact hnh
      · change middle.final.heads (fresh a 9)=1
        rw [(hother _ (field_none_count a)).2]
        exact hmh
    · intro i
      fin_cases i
      · change middle.final.tapes (sourceTape a)=natWord gs.length++gs.flatMap exactWord++[]
        simpa [fieldSlots] using hmidSource
      · exact hmidBack
      · exact hmidOut
      · change middle.final.tapes (localTape a 12)=UnaryTemplate.tape r.arity
        rw [(hother _ (field_none_arity a)).1]
        exact hn
      · change middle.final.tapes (fresh a 9)=UnaryTemplate.tape gs.length
        rw [(hother _ (field_none_count a)).1]
        exact hm
  rw [hi] at hf
  have hall := Composition.run_join (prefixMachine a) (records a) _ _ _ joined focused hj hf
  have htime : (Counted.budget a r+1+PCPPQueryField.fieldCost gs.length)+1+
      ((gs.flatMap exactWord).length+(6*r.arity+10)*gs.length+3)=budget a r := by unfold budget gs; omega
  rw [htime] at hall
  change run (machine a) (budget a r) (Counted.input a r)=_ at hall
  have tape (j : Fin 5) : focused.final.tapes (recordSlots a j)=last.final.tapes j := by
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot (recordSlots a) (recordSlots_injective a)]
  have head (j : Fin 5) : focused.final.heads (recordSlots a j)=last.final.heads j := by
    simp only [hff,RecoveryFocus.config,RecoveryFocus.pick_slot (recordSlots a) (recordSlots_injective a)]
  refine ⟨Composition.joinedReceipt joined focused,hall,?_,?_,?_,?_,?_,?_,?_⟩
  · change (first.steps+1+middle.steps)+1+focused.steps ≤ _
    rw [hms,hfsteps,hls]
    unfold budget
    dsimp only [gs] at *
    omega
  · change focused.final.tapes (recordSlots a 2)=_
    rw [tape,hlt]
    simp [output,exactListWord,gs,List.append_assoc]
  · change focused.final.heads (recordSlots a 2)=_
    rw [head,hlh]
    simp [output,exactListWord,gs,List.append_assoc]
  · change focused.final.tapes (recordSlots a 3)=_
    rw [tape,hlt]; rfl
  · change focused.final.heads (recordSlots a 3)=_
    rw [head,hlh]; rfl
  · change focused.final.tapes (recordSlots a 4)=_
    rw [tape,hlt]; rfl
  · change focused.final.heads (recordSlots a 4)=_
    rw [head,hlh]; rfl

end NearCubicWires.RepairOrdinary.DecompositionSource.Entry
