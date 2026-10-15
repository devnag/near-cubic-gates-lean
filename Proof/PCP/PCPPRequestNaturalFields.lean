import Proof.PCP.PCPPSubstitutionRequest

/-! Parse one literal native natural into its physical width, binary field,
Boolean-atom stream and nonzero flag. No unary value expansion occurs. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNaturalFields
open LocalBitMultitape RecoveryExecution Streaming RepairRepresentation SignedSortKey
open DecompositionNativeMagnitude
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def initMachine : Machine 9 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ _ => some ⟨1,
    fun i => if i=6 ∨ i=8 then some false else none,fun _ => .stay⟩

theorem initialize_run (source : List Bool) (pos : ℕ) :
    ∃ r,runFrom initMachine 1 (input source pos)=some r ∧
      r.final=signed source pos false ∧ r.steps=1 := by
  have hs : step initMachine (input source pos)=some (signed source pos false) := by
    simp only [step,initMachine,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i; rfl
    · funext i; fin_cases i <;> simp [applyAction,input,signed,writeTapeBit]
  exact (Timed.single (by rfl) hs).run (by rfl)

noncomputable def first := Composition.machine initMachine fieldMachine
noncomputable def machine := Composition.machine first expand

theorem natural_field_run (pre tail : List Bool) (n : ℕ) :
    ∃ r,runFrom first (6*natBitLength n+9)
      (Composition.leftConfig 8 (input (pre++natWord n++tail) pre.length))=some r ∧
      r.final=Composition.rightConfig 2
        (fieldOutput (pre++natWord n++tail) (pre.length+(natWord n).length)
          (binary (natBitLength n) n) false) ∧ r.steps=6*natBitLength n+9 := by
  let bits := binary (natBitLength n) n
  let source := pre++natWord n++tail
  obtain ⟨s,hs,sf,ss⟩ := initialize_run source pre.length
  obtain ⟨p,hp,pf,ps⟩ := MatrixDimensionField.field_run pre bits tail
  have hsource : pre++List.replicate bits.length true++false::(bits++tail)=source := by
    simp [source,bits,WilliamsInputHeader.natWord_eq,binary_length,List.append_assoc]
  rw [hsource] at hp pf
  have extended := TapeEmbedding.run_embed MatrixDimensionField.machine (fun _ : Fin 3 => 0)
    (![ [false],[],[false] ] : Fin 3 → List Bool) _ _ p hp
  let r := TapeEmbedding.receipt (fun _ : Fin 3 => 0)
    (![ [false],[],[false] ] : Fin 3 → List Bool) p
  have hi : TapeEmbedding.config (fun _ : Fin 3 => 0)
      (![ [false],[],[false] ] : Fin 3 → List Bool)
      (Composition.leftConfig 4 (MatrixDimensionField.input source pre.length))=
      Composition.restart s.final fieldMachine.start := by
    rw [sf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,Composition.restart,
        MatrixDimensionField.input,MatrixDimensionHeader.input,TapeEmbedding.config,signed,Fin.addCases]
    · funext i; fin_cases i <;> rfl
  rw [hi] at extended
  have whole := Composition.run_join initMachine fieldMachine 1 _ _ s r hs extended
  have hw : bits.length=natBitLength n := binary_length _ _
  rw [hw] at whole
  have htime : 1+1+(6*natBitLength n+7)=6*natBitLength n+9 := by omega
  rw [htime] at whole
  refine ⟨Composition.joinedReceipt s r,whole,?_,?_⟩
  · change Composition.rightConfig 2
      (TapeEmbedding.config (fun _ : Fin 3 => 0) (![ [false],[],[false] ] : Fin 3 → List Bool) p.final)=_
    rw [pf]
    have hpos : pre.length+2*bits.length+1=pre.length+(natWord n).length := by
      rw [hw,DecompositionSource.natWord_length]
      omega
    rw [hpos]
    rfl
  · change s.steps+1+p.steps=_
    rw [ss,ps,hw]
    omega

theorem natural_run (pre tail : List Bool) (n : ℕ) :
    ∃ r,runFrom machine (10*natBitLength n+11)
      (Composition.leftConfig 6 (Composition.leftConfig 8
        (input (pre++natWord n++tail) pre.length)))=some r ∧
      r.final=output (pre++natWord n++tail) (pre.length+(natWord n).length)
        (binary (natBitLength n) n) false ∧ r.steps=10*natBitLength n+11 := by
  let bits := binary (natBitLength n) n
  let source := pre++natWord n++tail
  obtain ⟨p,hp,pf,ps⟩ := natural_field_run pre tail n
  obtain ⟨b,hb,bf,bs⟩ := DecompositionBitFields.field_run [] bits [] [] false
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add,Bool.false_or] at hb bf
  let selected := DecompositionBitFields.cfg 0 (frame bits) 0 [] false
  have hi : RecoveryFocus.config expandSlots p.final.heads p.final.tapes selected=
      Composition.restart p.final expand.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; rw [pf]; fin_cases i <;> rfl
    · intro i; rw [pf]; fin_cases i <;> rfl
  obtain ⟨f,hf,ff,fs⟩ := RecoveryFocus.run_config expandSlots expand_injective
    DecompositionBitFields.machine p.final.heads p.final.tapes _ selected b hb
  rw [hi] at hf
  have whole := Composition.run_join first expand _ _ _ p f hp hf
  have hw : bits.length=natBitLength n := binary_length _ _
  rw [hw] at whole
  have htime : (6*natBitLength n+9)+1+(4*natBitLength n+1)=10*natBitLength n+11 := by omega
  rw [htime] at whole
  refine ⟨Composition.joinedReceipt p f,whole,?_,?_⟩
  · change Composition.rightConfig 10 f.final=_
    rw [ff,bf,pf]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,expand_pick,DecompositionBitFields.cfg,fieldOutput,MatrixDimensionField.output,
        TapeEmbedding.config,output,DecompositionBitFields.stream_length,Fin.addCases,bits]
    · funext i
      fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,expand_pick,DecompositionBitFields.cfg,fieldOutput,MatrixDimensionField.output,
        TapeEmbedding.config,output,Fin.addCases,bits]
  · change p.steps+1+f.steps=_
    rw [ps,fs,bs,hw]
    omega

end NearCubicWires.RepairOrdinary.PCPPRequestNaturalFields
