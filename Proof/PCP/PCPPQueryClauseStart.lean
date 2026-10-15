import Proof.PCP.PCPPQueryClauseBank

/-! Paid entry moves put both actual clause-query templates at head one.
The allocated bank is exactly the padded-index reader's initial state. -/
namespace NearCubicWires.RepairOrdinary.PCPPQueryClauseBank
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (j : Fin 21) := if j=13 ∨ j=14 then 1 else 0
def enter : Machine 21 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>none,fun j=>if j=13 ∨ j=14 then .right else .stay⟩ else none

theorem enter_run (data : Fin 21→List Bool) : ∃ r,
    run enter 1 data=some r ∧ r.final.tapes=data ∧ r.final.heads=heads ∧ r.steps=1 := by
  have h : step enter (initialConfiguration enter data)=some (⟨1,heads,data⟩ : Configuration 21 2) := by
    simp only [step,enter,initialConfiguration,Fin.val_zero,↓reduceIte]
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext j
      by_cases hj : j=13 ∨ j=14 <;> simp [applyAction,heads,hj,HeadMove.apply]
    · rfl
  obtain ⟨r,hr,hf,hs⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf],hs⟩

noncomputable def startMachine := Composition.machine machine enter

theorem zero_index (C : ℕ) (hC : 2≤C) :
    ZeroPadding.pad C (UnaryTemplate.tape 0)=List.replicate C false := by
  have ht : UnaryTemplate.tape 0=List.replicate 2 false := rfl
  rw [ht,ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le hC]

theorem output_bank (source : List Bool) (arity C : ℕ) (hC : 2≤C) (j : Fin 19) :
    output source arity C (j.castAdd 2)=PCPPQueryIndexPadding.clauseData source arity 0 C [] j := by
  fin_cases j <;> simp [output,PCPPQueryIndexPadding.clauseData,PCPPQueryClauseReuse.data,
    ZeroPadding.pad]
  exact (zero_index C hC).symm

theorem start_run (source : List Bool) (arity C : ℕ) (hC : 2≤C) : ∃ r,
    run startMachine (2*arity+2*C+15) (input source arity C)=some r ∧
      (∀ j : Fin 19,r.final.tapes (j.castAdd 2)=PCPPQueryIndexPadding.clauseData source arity 0 C [] j) ∧
      (∀ j : Fin 19,r.final.heads (j.castAdd 2)=PCPPQueryClauseReuse.heads j) ∧
      r.final.tapes 19=List.replicate arity true ∧ r.final.heads 19=0 ∧
      r.steps≤2*arity+2*C+15 := by
  obtain ⟨first,hf,ft,fh,fs⟩ := prepare_ready source arity C
  obtain ⟨last,hl,lt,lh,ls⟩ := enter_run (output source arity C)
  have he : initialConfiguration enter (output source arity C)=Composition.restart first.final enter.start := by
    apply configuration_ext
    · rfl
    · funext j
      exact (fh j).symm
    · exact ft.symm
  change runFrom enter 1 _=some last at hl
  rw [he] at hl
  have joined:=Composition.run_join machine enter _ _ _ first last hf hl
  have hc : (2*arity+2*C+13)+1+1=2*arity+2*C+15 := by omega
  rw [hc] at joined
  refine ⟨Composition.joinedReceipt first last,joined,?_,?_,?_,?_,?_⟩
  · intro j
    change last.final.tapes (j.castAdd 2)=_
    rw [lt]
    exact output_bank source arity C hC j
  · intro j
    change last.final.heads (j.castAdd 2)=_
    rw [lh]
    fin_cases j <;> rfl
  · change last.final.tapes 19=_
    rw [lt]
    rfl
  · change last.final.heads 19=0
    rw [lh]
    rfl
  · change first.steps+1+last.steps≤_
    omega

end NearCubicWires.RepairOrdinary.PCPPQueryClauseBank
