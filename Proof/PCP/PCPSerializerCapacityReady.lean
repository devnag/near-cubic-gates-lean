import Proof.PCP.PCPSerializerCapacityFocus

/-! Whole cold serializer capacity producer: counted framed source and its
physical count sentinel, blank scratch, exact retained cursors, raw byte mass
and raw fixed-polynomial capacity. -/
namespace NearCubicWires.RepairOrdinary.PCPSerializerCapacity
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.ProjectionNormalization RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def tapes (D : ℕ) := 5+DimensionPolynomial.tapes D
def old (D : ℕ) (i : Fin 5) : Fin (tapes D) := i.castAdd (DimensionPolynomial.tapes D)
def fresh (D : ℕ) (i : Fin (DimensionPolynomial.tapes D)) : Fin (tapes D) := i.natAdd 5
def slots (D : ℕ) (i : Fin (DimensionPolynomial.tapes D)) : Fin (tapes D) :=
  if i.val=0 then old D 1 else fresh D i

theorem slots_injective (D : ℕ) : Function.Injective (slots D) := by
  intro a b h
  apply Fin.ext
  have hv := congrArg Fin.val h
  dsimp only [slots,old,fresh] at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem slots_ne_old (D : ℕ) (i : Fin 5) (hi : i≠1) (j : Fin (DimensionPolynomial.tapes D)) :
    slots D j≠old D i := by
  intro he
  have hv := congrArg Fin.val he
  dsimp only [slots,old,fresh] at hv
  split_ifs at hv
  · have h : i=1 := Fin.ext (by simpa using hv.symm)
    exact hi h
  · have := i.isLt
    dsimp at hv
    omega

def heads (D pos : ℕ) : Fin (tapes D) → ℕ :=
  Fin.addCases ![pos,0,1,0,0] (fun _ => 0)
def input (D : ℕ) (source : List Bool) (count : ℕ) : Fin (tapes D) → List Bool :=
  Fin.addCases ![source,[],CompareMachine.word count,[],[]] (fun _ => [])
def entry {s : ℕ} (D : ℕ) (q : Fin s) (source : List Bool) (pos count : ℕ) : Configuration (tapes D) s :=
  ⟨q,heads D pos,input D source count⟩
noncomputable def massProgram (D : ℕ) := TapeEmbedding.machine (DimensionPolynomial.tapes D) MassReady.machine
noncomputable def powerProgram (D C : ℕ) := RecoveryFocus.machine (slots D) (Power.machine D C)
noncomputable def machine (D C : ℕ) := Composition.machine (massProgram D) (powerProgram D C)
def budget (D C B : ℕ) := 16*B+19+Power.budget D C B
def capacitySlot (D : ℕ) : Fin (tapes D) := slots D (Power.outputSlot D)

noncomputable def afterMass (D : ℕ) (source : List Bool) (B count sl ml : ℕ) : Fin (tapes D) → List Bool :=
  Fin.addCases ![source,List.replicate B true,CompareMachine.word count,
    List.replicate sl false,List.replicate ml false] (fun _ => [])

theorem mass_entry (D : ℕ) (source : List Bool) (pos count : ℕ) :
    TapeEmbedding.config (fun _ : Fin (DimensionPolynomial.tapes D) => 0) (fun _ => [])
      (MassReady.cfg MassReady.machine.start source pos 0 count 0 0)=
      entry D (massProgram D).start source pos count := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · fin_cases j <;> rfl
    · rfl

theorem power_input (D : ℕ) (source : List Bool) (B count sl ml : ℕ)
    (i : Fin (DimensionPolynomial.tapes D)) :
    afterMass D source B count sl ml (slots D i)=DimensionPolynomial.input D B i := by
  by_cases hi : i.val=0
  · simp [slots,hi,afterMass,old,DimensionPolynomial.input]
  · simp [slots,hi,afterMass,fresh,DimensionPolynomial.input]

theorem power_heads (D pos : ℕ) (i : Fin (DimensionPolynomial.tapes D)) : heads D pos (slots D i)=0 := by
  by_cases hi : i.val=0 <;> simp [slots,hi,heads,old,fresh]

theorem capacity_run (D C : ℕ) (pre : List Bool) (fields : List (List Bool)) (suffix : List Bool) :
    ∃ r,runFrom (machine D C) (budget D C (FieldList.stream fields).length)
      (entry D (machine D C).start (pre++FieldList.stream fields++suffix) pre.length fields.length)=some r ∧
      r.steps ≤ budget D C (FieldList.stream fields).length ∧
      r.final.heads=heads D pre.length ∧
      r.final.tapes (old D 0)=pre++FieldList.stream fields++suffix ∧
      r.final.tapes (old D 2)=CompareMachine.word fields.length ∧
      r.final.tapes (old D 1)=List.replicate (FieldList.stream fields).length true ∧
      r.final.tapes (capacitySlot D)=List.replicate (C*((FieldList.stream fields).length+1)^D) true := by
  let B := (FieldList.stream fields).length
  let source := pre++FieldList.stream fields++suffix
  obtain ⟨base,sl,ml,hb,hbs,hbf⟩ := MassReady.bounded_run pre fields suffix
  have hm := TapeEmbedding.run_embed MassReady.machine
    (fun _ : Fin (DimensionPolynomial.tapes D) => 0) (fun _ => []) _ _ base hb
  rw [mass_entry] at hm
  let first : ExecutionReceipt (tapes D) MassReady.size := TapeEmbedding.receipt (fun _ : Fin (DimensionPolynomial.tapes D) => 0) (fun _ => []) base
  change runFrom (massProgram D) (16*B+18) (entry D (massProgram D).start source pre.length fields.length)=some first at hm
  have hfh : first.final.heads=heads D pre.length := by
    simp only [first,TapeEmbedding.receipt,TapeEmbedding.config,hbf,MassReady.cfg]
    rfl
  have hft : first.final.tapes=afterMass D source B fields.length sl ml := by
    simp only [first,TapeEmbedding.receipt,TapeEmbedding.config,hbf,MassReady.cfg,source,B]
    rfl
  obtain ⟨powerOut,hp,hpB,hpC⟩ := Power.capacity_run D C B
  obtain ⟨last,hl,hlh,hlt,hls⟩ := hp.focus_at (slots D) (slots_injective D)
    (heads D pre.length) (afterMass D source B fields.length sl ml)
    (power_input D source B fields.length sl ml) (power_heads D pre.length)
  have he : Composition.restart first.final (powerProgram D C).start=
      (⟨(Power.machine D C).start,heads D pre.length,afterMass D source B fields.length sl ml⟩ :
        Configuration (tapes D) _) := by
    apply configuration_ext
    · rfl
    · exact hfh
    · exact hft
  have hl' : runFrom (powerProgram D C) (Power.budget D C B)
      (Composition.restart first.final (powerProgram D C).start)=some last := by
    rw [he]
    exact hl
  have hall := Composition.run_join (massProgram D) (powerProgram D C) _ _ _ first last hm hl'
  change runFrom (machine D C) ((16*B+18)+1+Power.budget D C B)
    (entry D (machine D C).start source pre.length fields.length)=some (Composition.joinedReceipt first last) at hall
  refine ⟨Composition.joinedReceipt first last,hall,?_,hlh,?_,?_,?_,?_⟩
  · dsimp only [Composition.joinedReceipt,first,TapeEmbedding.receipt,budget]
    dsimp only [B] at hls
    omega
  · change last.final.tapes (old D 0)=_
    rw [hlt,install_other _ _ _ _ (slots_ne_old D 0 (by decide))]
    rfl
  · change last.final.tapes (old D 2)=_
    rw [hlt,install_other _ _ _ _ (slots_ne_old D 2 (by decide))]
    rfl
  · change last.final.tapes (slots D ⟨0,by simp [DimensionPolynomial.tapes]⟩)=_
    rw [hlt,install_slot _ (slots_injective D)]
    exact hpB
  · change last.final.tapes (slots D (Power.outputSlot D))=_
    rw [hlt,install_slot _ (slots_injective D)]
    exact hpC

end NearCubicWires.RepairOrdinary.PCPSerializerCapacity
