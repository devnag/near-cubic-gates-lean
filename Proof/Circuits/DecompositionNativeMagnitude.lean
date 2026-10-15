import Proof.Circuits.DecompositionBitFields
import Proof.PCP.ProjectionDimensionCanonical

/-! A literal signed native field supplies its own sign, magnitude field,
bit-width driver, Boolean-atom stream, and nonzero flag. Magnitude values
are never expanded into unary. -/
namespace NearCubicWires.RepairOrdinary.DecompositionNativeMagnitude
open LocalBitMultitape RecoveryExecution Streaming RepairRepresentation SignedSortKey
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def signMachine : Machine 9 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ bs => some ⟨1,
    fun i => if i=6 then some (bs 0) else if i=8 then some false else none,
    fun i => if i=0 then .right else .stay⟩
def input (source : List Bool) (pos : ℕ) : Configuration 9 2 :=
  ⟨0,![pos,0,0,0,0,0,0,0,0],![source,[],[],[],[],[],[],[],[]]⟩
def signed (source : List Bool) (pos : ℕ) (sign : Bool) : Configuration 9 2 :=
  ⟨1,![pos,0,0,0,0,0,0,0,0],![source,[],[],[],[],[],[sign],[],[false]]⟩

theorem sign_run (pre tail : List Bool) (sign : Bool) :
    ∃ r,runFrom signMachine 1 (input (pre++sign::tail) pre.length)=some r ∧
      r.final=signed (pre++sign::tail) (pre.length+1) sign ∧ r.steps=1 := by
  have hs : step signMachine (input (pre++sign::tail) pre.length)=
      some (signed (pre++sign::tail) (pre.length+1) sign) := by
    simp [step,signMachine,input,Configuration.scanned,read_append]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [applyAction,signed,HeadMove.apply]
    · funext i; fin_cases i <;> simp [applyAction,signed,writeTapeBit]
  exact (Timed.single (by rfl) hs).run (by rfl)

noncomputable def fieldMachine := TapeEmbedding.machine 3 MatrixDimensionField.machine
noncomputable def first := Composition.machine signMachine fieldMachine
def fieldOutput (source : List Bool) (pos : ℕ) (bits : List Bool) (sign : Bool) :
    Configuration 9 8 := TapeEmbedding.config (fun _ : Fin 3 => 0)
      (![ [sign],[],[false] ] : Fin 3 → List Bool)
      (MatrixDimensionField.output source pos bits)

theorem field_run (pre tail : List Bool) (z : ℤ) :
    ∃ r,runFrom first (6*natBitLength z.natAbs+9)
      (Composition.leftConfig 8 (input (pre++intWord z++tail) pre.length))=some r ∧
      r.final=Composition.rightConfig 2
        (fieldOutput (pre++intWord z++tail) (pre.length+(intWord z).length)
          (binary (natBitLength z.natAbs) z.natAbs) (decide (z<0))) ∧
      r.steps=6*natBitLength z.natAbs+9 := by
  let b := decide (z<0)
  let bits := binary (natBitLength z.natAbs) z.natAbs
  let source := pre++intWord z++tail
  obtain ⟨s,hs,sf,ss⟩ := sign_run pre (natWord z.natAbs++tail) b
  have he : pre++b::(natWord z.natAbs++tail)=source := by simp [source,intWord,b]
  rw [he] at hs sf
  obtain ⟨p,hp,pf,ps⟩ := MatrixDimensionField.field_run (pre++[b]) bits tail
  have hsource : (pre++[b])++List.replicate bits.length true++false::(bits++tail)=source := by
    simp [source,intWord,b,bits,WilliamsInputHeader.natWord_eq,binary_length,List.append_assoc]
  rw [hsource] at hp pf
  have extended := TapeEmbedding.run_embed MatrixDimensionField.machine (fun _ : Fin 3 => 0)
    (![ [b],[],[false] ] : Fin 3 → List Bool) _ _ p hp
  let r := TapeEmbedding.receipt (fun _ : Fin 3 => 0)
    (![ [b],[],[false] ] : Fin 3 → List Bool) p
  have hi : TapeEmbedding.config (fun _ : Fin 3 => 0)
      (![ [b],[],[false] ] : Fin 3 → List Bool)
      (Composition.leftConfig 4 (MatrixDimensionField.input source (pre++[b]).length))=
      Composition.restart s.final fieldMachine.start := by
    rw [sf]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [Composition.leftConfig,Composition.restart,
        MatrixDimensionField.input,MatrixDimensionHeader.input,TapeEmbedding.config,signed,Fin.addCases]
    · funext i; fin_cases i <;> rfl
  rw [hi] at extended
  have whole := Composition.run_join signMachine fieldMachine 1 _ _ s r hs extended
  have hw : bits.length=natBitLength z.natAbs := binary_length _ _
  rw [hw] at whole
  have htime : 1+1+(6*natBitLength z.natAbs+7)=6*natBitLength z.natAbs+9 := by omega
  rw [htime] at whole
  refine ⟨Composition.joinedReceipt s r,whole,?_,?_⟩
  · change Composition.rightConfig 2
      (TapeEmbedding.config (fun _ : Fin 3 => 0) (![ [b],[],[false] ] : Fin 3 → List Bool) p.final)=_
    rw [pf]
    have hpos : (pre++[b]).length+2*bits.length+1=pre.length+(intWord z).length := by
      rw [hw,intWord, List.length_cons,DecompositionSource.natWord_length]
      simp only [List.length_append,List.length_singleton]
      omega
    rw [hpos]
    rfl
  · change s.steps+1+p.steps=_
    rw [ss,ps,hw]
    omega

def expandSlots : Fin 3 → Fin 9 := ![4,7,8]
theorem expand_injective : Function.Injective expandSlots := by decide
theorem expand_pick (i : Fin 9) : RecoveryFocus.pick expandSlots i=
    (![none,none,none,none,some 0,none,none,some 1,some 2] : Fin 9 → Option (Fin 3)) i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot expandSlots expand_injective 0
    | exact RecoveryFocus.pick_slot expandSlots expand_injective 1
    | exact RecoveryFocus.pick_slot expandSlots expand_injective 2
noncomputable def expand := RecoveryFocus.machine expandSlots DecompositionBitFields.machine
noncomputable def machine := Composition.machine first expand

def output (source : List Bool) (pos : ℕ) (bits : List Bool) (sign : Bool) : Configuration 9 16 :=
  ⟨15,![pos,0,0,1,2*bits.length+1,0,0,3*bits.length,0],
    ![source,List.replicate bits.length true,List.replicate bits.length true,
      UnaryTemplate.tape bits.length,frame bits,List.replicate (2*bits.length+1) false,
      [sign],DecompositionBitFields.stream bits,[DecompositionBitFields.present bits]]⟩

theorem magnitude_run (pre tail : List Bool) (z : ℤ) :
    ∃ r,runFrom machine (10*natBitLength z.natAbs+11)
      (Composition.leftConfig 6 (Composition.leftConfig 8
        (input (pre++intWord z++tail) pre.length)))=some r ∧
      r.final=output (pre++intWord z++tail) (pre.length+(intWord z).length)
        (binary (natBitLength z.natAbs) z.natAbs) (decide (z<0)) ∧
      r.steps=10*natBitLength z.natAbs+11 := by
  let bits := binary (natBitLength z.natAbs) z.natAbs
  let source := pre++intWord z++tail
  obtain ⟨p,hp,pf,ps⟩ := field_run pre tail z
  obtain ⟨b,hb,bf,bs⟩ := DecompositionBitFields.field_run [] bits [] [] false
  simp only [List.nil_append,List.append_nil,List.length_nil,Nat.zero_add,Bool.false_or] at hb bf
  let selected :=  DecompositionBitFields.cfg 0 (frame bits) 0 [] false
  have hi : RecoveryFocus.config expandSlots p.final.heads p.final.tapes selected=
      Composition.restart p.final expand.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [pf]
      fin_cases i <;> rfl
    · intro i
      rw [pf]
      fin_cases i <;> rfl
  obtain ⟨f,hf,ff,fs⟩ := RecoveryFocus.run_config expandSlots expand_injective
    DecompositionBitFields.machine p.final.heads p.final.tapes _ selected b hb
  rw [hi] at hf
  have whole := Composition.run_join first expand _ _ _ p f hp hf
  have hw : bits.length=natBitLength z.natAbs := binary_length _ _
  rw [hw] at whole
  have htime : (6*natBitLength z.natAbs+9)+1+(4*natBitLength z.natAbs+1)=
      10*natBitLength z.natAbs+11 := by omega
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

theorem native_positive (n : ℕ) (hn : 0<n) :
    DecompositionBitFields.fields (binary (natBitLength n) n)=DecompositionBitFields.fields n.bits := by
  rw [DimensionProducer.binary_bits n hn]
theorem native_code (n : ℕ) (hn : 0<n) :
    PCPTraversal.code (DecompositionBitFields.fields (binary (natBitLength n) n))=
      CanonicalBinary.encodeNat n := by
  rw [native_positive n hn,DecompositionBitFields.code]
  rfl

end NearCubicWires.RepairOrdinary.DecompositionNativeMagnitude
