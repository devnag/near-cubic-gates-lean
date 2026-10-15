import Proof.Amplification.RecoveryRowLookupReturn

/-! Paid entry to the reusable prior-row lookup. Its source is a retained
framed prefix, with physical width and row-count drivers. The entry clears
the first-match flag, initializes the empty-prefix success bit and positions
both drivers. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowLookupTable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowLookupStream
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clean (d : Data) : Data := {d with found:=false,row:={d.row with valid:=true}}
noncomputable def inputTapes (d : Data) (total : Nat) : Fin 15→List Bool :=
  Fin.addCases (m:=14) (n:=1) (motive:=fun _=>List Bool) (d.cfg (0 : Fin 1)).tapes
    (fun _=>CompareMachine.word total)

def positionMachine : Machine 15 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some ⟨1,
    fun i=>if i=6 then some true else if i=9 then some false else none,
    fun i=>if i=5 ∨ i=14 then .right else .stay⟩ else none

theorem inputTapes_eq (d : Data) (total : Nat) : inputTapes d total=
    ![d.row.source,d.row.fields 0,d.row.fields 1,d.row.fields 2,d.row.fields 3,
      CompareMachine.word d.row.width,[d.row.valid],frame d.key,frame d.saved,[d.found],
      [d.same],[d.aux],List.replicate d.copyCapacity false,List.replicate d.resetCapacity false,
      CompareMachine.word total] := by
  funext i
  fin_cases i <;> rfl

def positionedHeads (d : Data) : Fin 15→Nat := ![d.row.pos,0,0,0,0,1,0,0,0,0,0,0,0,0,1]

theorem positionedHeads_eq (d : Data) (total : Nat) :
    (RepeatMachine.cfg 0 (d.cfg (0 : Fin 1)) total 1).heads=positionedHeads d := by
  funext i
  fin_cases i <;> rfl

def movedHeads : Fin 15→Nat := fun i=>if i=5 ∨ i=14 then 1 else 0

theorem movedHeads_eq (d : Data) (hp : d.row.pos=0) : movedHeads=positionedHeads (clean d) := by
  funext i
  fin_cases i <;> simp [movedHeads,positionedHeads,clean,hp]

theorem cleaned_tapes (d : Data) (total : Nat) :
    Function.update (Function.update (inputTapes d total) 6 [true]) 9 [false]=inputTapes (clean d) total := by
  rw [inputTapes_eq,inputTapes_eq]
  funext i
  fin_cases i <;> simp [clean]

theorem position_step (tapes : Fin 15→List Bool) (oldValid oldFound : Bool)
    (hvalid : tapes 6=[oldValid]) (hfound : tapes 9=[oldFound]) :
    step positionMachine (initialConfiguration positionMachine tapes)=
      some (⟨1,movedHeads,Function.update (Function.update tapes 6 [true]) 9 [false]⟩ : Configuration 15 2) := by
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    by_cases hm : i=5 ∨ i=14 <;> simp [applyAction,positionMachine,initialConfiguration,movedHeads,hm,HeadMove.apply]
  · funext i
    by_cases h6 : i=6
    · subst i
      simp [applyAction,positionMachine,initialConfiguration,hvalid,writeTapeBit]
    · by_cases h9 : i=9
      · subst i
        simp [applyAction,positionMachine,initialConfiguration,hfound,writeTapeBit]
      · simp [applyAction,positionMachine,initialConfiguration,h6,h9]

theorem position_run (d : Data) (total : Nat) (hp : d.row.pos=0) :
    ∃ r,run positionMachine 1 (inputTapes d total)=some r ∧
      r.final.heads=positionedHeads (clean d) ∧
      r.final.tapes=inputTapes (clean d) total ∧ r.steps=1 := by
  have h := position_step (inputTapes d total) d.row.valid d.found (by rfl) (by rfl)
  rw [movedHeads_eq d hp,cleaned_tapes] at h
  obtain ⟨r,hr,hf,ht⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by rw [hf],ht⟩

noncomputable def positionedMachine := Composition.machine positionMachine machine

theorem clean_inv (width : Nat) (x : Cursor) (hx : Inv width x) :
    Inv width ⟨clean x.data,x.rest⟩ := hx

theorem positioned_run (width total : Nat) (d : Data) (bits : List Bool)
    (hx : Inv width ⟨d,bits⟩) (hp : d.row.pos=0) :
    ∃ r,run positionedMachine (total*(budget width+3)+5) (inputTapes d total)=some r ∧
      r.steps≤total*(budget width+3)+5 ∧ r.final.heads 6=0 ∧
      r.final.tapes 6=[(readMany (readRow d.row.width) total bits).isSome] ∧
      ((readMany (readRow d.row.width) total bits).isSome=true →
        r.final.tapes=inputTapes (RepeatMachine.iterate next total ⟨clean d,bits⟩).2.data total) := by
  obtain ⟨first,hr0,hh0,ht0,hs0⟩ := position_run d total hp
  obtain ⟨last,hr1,hs1,hf1,hh1,ht1⟩ := table_return width total ⟨clean d,bits⟩ (clean_inv width ⟨d,bits⟩ hx) rfl
  have hstart : Composition.restart first.final machine.start=
      RepeatMachine.cfg 0 (source ⟨clean d,bits⟩) total 1 := by
    apply configuration_ext
    · rfl
    · exact hh0.trans (positionedHeads_eq (clean d) total).symm
    · exact ht0
  have hnext : runFrom machine (total*(budget width+3)+3)
      (Composition.restart first.final machine.start)=some last := by rw [hstart]; exact hr1
  have hall := Composition.run_join positionMachine machine 1 (total*(budget width+3)+3)
    _ first last hr0 hnext
  have he : 1+1+(total*(budget width+3)+3)=total*(budget width+3)+5 := by omega
  rw [he] at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,hh1,ht1,?_⟩
  · change first.steps+1+last.steps≤_
    omega
  · intro ha
    have hiter : (RepeatMachine.iterate next total ⟨clean d,bits⟩).1=true := by
      rw [iterate_accepts]
      exact ha
    simp only [RepeatMachine.Result,hiter,↓reduceIte] at hf1
    change last.final.tapes=_
    rw [hf1]
    rfl

end NearCubicWires.RepairOrdinary.RecoveryRowLookupTable
