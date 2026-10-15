import Proof.MachineModel.OrdinaryMatrixScoreWeightLoop

/-! Common score width W=p+b+3 from the actual parsed Unary p at head1
and raw unary b=natBitLength d. Every copy, sum and rewind is executed. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreWidth
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fieldSlots : Fin 6 → Fin 13 := ![5,6,7,8,9,10]
def sumSlots : Fin 4 → Fin 13 := ![1,7,11,12]
def first : Machine 13 10 := TapeEmbedding.machine 8 MatrixScoreTemplateEntry.machine
noncomputable def fields : Machine 13 14 := RecoveryFocus.machine fieldSlots ClockFields.machine
noncomputable def prepared := Composition.machine first fields
noncomputable def sum : Machine 13 5 := RecoveryFocus.machine sumSlots ClockUnarySum.machine
noncomputable def machine := Composition.machine prepared sum
def extra (b : ℕ) : Fin 8 → List Bool := ![List.replicate b true,[],[],[],[],[],[],[]]
def input (p b : ℕ) : Configuration 13 29 :=
  ⟨0,fun i => if i=0 then 1 else 0,
    ![UnaryTemplate.tape p,[],[],[],[],List.replicate b true,[],[],[],[],[],[],[]]⟩

theorem width_run (p b : ℕ) :
    ∃ actual : ExecutionReceipt 13 29,
      runFrom machine (6*p+6*b+50) (input p b)=some actual ∧
      actual.final.tapes 0=UnaryTemplate.tape p ∧
      actual.final.tapes 1=List.replicate p true ∧
      actual.final.tapes 5=List.replicate b true ∧
      actual.final.tapes 7=List.replicate (b+3) true ∧
      actual.final.tapes 11=List.replicate (p+b+3) true ∧
      (∀ i,actual.final.heads i=0) ∧ actual.steps≤6*p+6*b+50 := by
  obtain ⟨base,hb,h0,h1,_,_,hh,hs⟩ := MatrixScoreTemplateEntry.entry_run p
  have he := TapeEmbedding.run_embed MatrixScoreTemplateEntry.machine (fun _ : Fin 8 => 0) (extra b) _ _ base hb
  let copied := TapeEmbedding.receipt (fun _ : Fin 8 => 0) (extra b) base
  have ch : ∀ i,copied.final.heads i=0 := by
    intro i
    fin_cases i <;> simp [copied,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,hh]
  obtain ⟨field,hf,f0,_,f2,_,_,_,fh,fs⟩ := ClockFields.fields_run b
  let fieldInput := initialConfiguration ClockFields.machine
    (Fin.addCases (m := 5) (n := 1) (motive := fun _ => List Bool)
      ![List.replicate b true,[],[],[],[]] (fun _ => []))
  have fi : RecoveryFocus.config fieldSlots copied.final.heads copied.final.tapes fieldInput=
      Composition.restart copied.final fields.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; simp [ch,fieldInput,initialConfiguration]
    · intro i
      fin_cases i <;> rfl
  obtain ⟨expanded,hex,hef,hes⟩ := RecoveryFocus.run_config fieldSlots (by decide) ClockFields.machine
    copied.final.heads copied.final.tapes _ fieldInput field hf
  rw [fi] at hex
  have hj := Composition.run_join first fields (4*p+14) (4*b+22) _ copied expanded he hex
  let middle := Composition.joinedReceipt copied expanded
  have mh : ∀ i,middle.final.heads i=0 := by
    intro i
    change expanded.final.heads i=0
    rw [hef]
    cases h : RecoveryFocus.pick fieldSlots i <;> simp [RecoveryFocus.config,h,ch,fh]
  have m0 : middle.final.tapes 0=UnaryTemplate.tape p := by
    change expanded.final.tapes 0=_
    rw [hef]
    simpa [RecoveryFocus.config,show RecoveryFocus.pick fieldSlots 0=none by decide,
      copied,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using h0
  have m1 : middle.final.tapes 1=List.replicate p true := by
    change expanded.final.tapes 1=_
    rw [hef]
    simpa [RecoveryFocus.config,show RecoveryFocus.pick fieldSlots 1=none by decide,
      copied,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases] using h1
  have m5 : middle.final.tapes 5=List.replicate b true := by
    change expanded.final.tapes (fieldSlots 0)=_
    rw [hef]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot fieldSlots (by decide)] using f0
  have m7 : middle.final.tapes 7=List.replicate (b+3) true := by
    change expanded.final.tapes (fieldSlots 2)=_
    rw [hef]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot fieldSlots (by decide)] using f2
  have m11 : middle.final.tapes 11=[] := by
    change expanded.final.tapes 11=_
    rw [hef]
    simp [RecoveryFocus.config,show RecoveryFocus.pick fieldSlots 11=none by decide,
      copied,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,extra]
  have m12 : middle.final.tapes 12=[] := by
    change expanded.final.tapes 12=_
    rw [hef]
    simp [RecoveryFocus.config,show RecoveryFocus.pick fieldSlots 12=none by decide,
      copied,TapeEmbedding.receipt,TapeEmbedding.config,Fin.addCases,extra]
  have sumReady := ClockUnarySum.sum_ready p (b+3)
  have sumi : ∀ i,middle.final.tapes (sumSlots i)=
      (![List.replicate p true,List.replicate (b+3) true,[],[]] : Fin 4 → List Bool) i := by
    intro i; fin_cases i
    · exact m1
    · exact m7
    · exact m11
    · exact m12
  obtain ⟨summed,sr,st,sh,ss⟩ := sumReady
  let sumInput := initialConfiguration ClockUnarySum.machine
    ![List.replicate p true,List.replicate (b+3) true,[],[]]
  have sumMatch : RecoveryFocus.config sumSlots middle.final.heads middle.final.tapes sumInput=
      Composition.restart middle.final sum.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; simp [mh,sumInput,initialConfiguration]
    · exact sumi
  obtain ⟨last,hl,hlf,hls⟩ := RecoveryFocus.run_config sumSlots (by decide) ClockUnarySum.machine
    middle.final.heads middle.final.tapes _ sumInput summed sr
  rw [sumMatch] at hl
  have hlh : last.final.heads=middle.final.heads := by
    rw [hlf]
    funext i
    cases h : RecoveryFocus.pick sumSlots i <;> simp [RecoveryFocus.config,h,sh,mh]
  have hlt : last.final.tapes=install sumSlots middle.final.tapes
      ![List.replicate p true,List.replicate (b+3) true,List.replicate (p+(b+3)) true,
        List.replicate (p+(b+3)+2) false] := by
    rw [hlf]
    change install sumSlots middle.final.tapes summed.final.tapes=_
    rw [st]
  have hall := Composition.run_join prepared sum ((4*p+14)+1+(4*b+22)) (2*(p+(b+3))+6) _ middle last hj hl
  have hin : Composition.leftConfig 5 (Composition.leftConfig 14
      (TapeEmbedding.config (fun _ : Fin 8 => 0) (extra b) (MatrixScoreTemplateEntry.input p)))=input p b := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hall
  have ht : ((4*p+14)+1+(4*b+22))+1+(2*(p+(b+3))+6)=6*p+6*b+50 := by omega
  rw [ht] at hall
  have other (i : Fin 13) (hi : ∀ j,sumSlots j≠i) : last.final.tapes i=middle.final.tapes i := by
    rw [hlt]
    exact install_other sumSlots _ _ i hi
  refine ⟨Composition.joinedReceipt middle last,hall,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (other 0 (by decide)).trans m0
  · change last.final.tapes (sumSlots 0)=_
    rw [hlt,install_slot sumSlots (by decide)]
    rfl
  · exact (other 5 (by decide)).trans m5
  · change last.final.tapes (sumSlots 1)=_
    rw [hlt,install_slot sumSlots (by decide)]
    rfl
  · change last.final.tapes (sumSlots 2)=_
    rw [hlt,install_slot sumSlots (by decide)]
    simp [Nat.add_assoc]
  · intro i
    change last.final.heads i=0
    rw [hlh]
    exact mh i
  · change (base.steps+1+expanded.steps)+1+last.steps≤_
    rw [hs,hes,fs,hls]
    omega

end NearCubicWires.RepairOrdinary.MatrixScoreWidth
