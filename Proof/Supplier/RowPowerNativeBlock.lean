import Proof.Supplier.RowPowerBlockAppend
import Proof.Circuits.DecompositionNativeMagnitude
import Proof.Amplification.RecoveryFocusDock

/-! A complete native signed-field → P/N radix-block execution. The original
cache cursor advances once; existing output cursors are retained and extended.
Only the first native magnitude stage is used, with no atom or balanced code. -/
namespace NearCubicWires.RepairOrdinary.RowPowerNative
open LocalBitMultitape RecoveryExecution Streaming RepairRepresentation SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraHeads (positive negative : List Bool) : Fin 3 → ℕ := ![0,positive.length,negative.length]
def extraTapes (w : ℕ) (positive negative : List Bool) : Fin 3 → List Bool :=
  ![List.replicate w true,positive,negative]
noncomputable def first := TapeEmbedding.machine 3 DecompositionNativeMagnitude.first
def slots : Fin 5 → Fin 12 := ![9,4,6,10,11]
theorem injective : Function.Injective slots := by decide
noncomputable def last := RecoveryFocus.machine slots RowPowerBlock.machine
noncomputable def machine := Composition.machine first last

def entry (source : List Bool) (pos w : ℕ) (positive negative : List Bool) : Configuration 12 14 :=
  Composition.leftConfig 4 (TapeEmbedding.config (extraHeads positive negative)
    (extraTapes w positive negative)
    (Composition.leftConfig 8 (DecompositionNativeMagnitude.input source pos)))
def parsed (source : List Bool) (pos w : ℕ) (bits : List Bool) (sign : Bool)
    (positive negative : List Bool) : Configuration 12 10 :=
  TapeEmbedding.config (extraHeads positive negative) (extraTapes w positive negative)
    (Composition.rightConfig 2 (DecompositionNativeMagnitude.fieldOutput source pos bits sign))
noncomputable def output (source : List Bool) (pos w : ℕ) (bits : List Bool) (sign : Bool)
    (positive negative : List Bool) : Configuration 12 14 :=
  let p := parsed source pos w bits sign positive negative
  Composition.rightConfig 10 (RecoveryFocus.config slots p.heads p.tapes
    (RowPowerBlock.final (List.replicate w true) (frame bits) w (2*min w bits.length) sign
      (positive++marks (RowPowerBlock.digits false sign (ClockNormalize.resize w bits)))
      (negative++marks (RowPowerBlock.digits true sign (ClockNormalize.resize w bits)))))

theorem block_start (source : List Bool) (pos w : ℕ) (bits : List Bool) (sign : Bool)
    (positive negative : List Bool) :
    RecoveryFocus.config slots (parsed source pos w bits sign positive negative).heads
      (parsed source pos w bits sign positive negative).tapes
      (RowPowerBlock.cfg 0 (List.replicate w true) (frame bits) 0 0 sign positive negative)=
    Composition.restart (parsed source pos w bits sign positive negative) last.start := by
  apply WilliamsSourceCrop.focus_same
  · intro j
    fin_cases j <;> rfl
  · intro j
    fin_cases j <;> rfl

theorem field_run (pre suffix positive negative : List Bool) (z : ℤ) (w : ℕ) :
    ∃ r,runFrom machine (6*natBitLength z.natAbs+2*w+11)
      (entry (pre++intWord z++suffix) pre.length w positive negative)=some r ∧
      r.final=output (pre++intWord z++suffix) (pre.length+(intWord z).length) w
        (binary (natBitLength z.natAbs) z.natAbs) (decide (z<0)) positive negative ∧
      r.steps=6*natBitLength z.natAbs+2*w+11 := by
  let bits := binary (natBitLength z.natAbs) z.natAbs
  let sign := decide (z<0)
  let source := pre++intWord z++suffix
  obtain ⟨native,hn,nf,ns⟩ := DecompositionNativeMagnitude.field_run pre suffix z
  have he := TapeEmbedding.run_embed DecompositionNativeMagnitude.first
    (extraHeads positive negative) (extraTapes w positive negative) _ _ native hn
  let firstRun := TapeEmbedding.receipt (extraHeads positive negative) (extraTapes w positive negative) native
  have hf : firstRun.final=parsed source (pre.length+(intWord z).length) w bits sign positive negative := by
    change TapeEmbedding.config _ _ native.final=_
    rw [nf]
    rfl
  obtain ⟨body,hb,bf,bs⟩ := RowPowerBlock.append_run w bits [] positive negative sign
  simp only [List.append_nil] at hb bf
  obtain ⟨focused,hfocus,ff,fs⟩ := RecoveryFocus.run_config slots injective RowPowerBlock.machine
    firstRun.final.heads firstRun.final.tapes _ _ body hb
  have hi : RecoveryFocus.config slots firstRun.final.heads firstRun.final.tapes
      (RowPowerBlock.cfg 0 (List.replicate w true) (frame bits) 0 0 sign positive negative)=
      Composition.restart firstRun.final last.start := by rw [hf]; exact block_start _ _ _ _ _ _ _
  rw [hi] at hfocus
  have hj := Composition.run_join first last (6*natBitLength z.natAbs+9) (2*w+1)
    _ firstRun focused he hfocus
  have ht : 6*natBitLength z.natAbs+9+1+(2*w+1)=6*natBitLength z.natAbs+2*w+11 := by omega
  rw [ht] at hj
  refine ⟨Composition.joinedReceipt firstRun focused,hj,?_,?_⟩
  · change Composition.rightConfig 10 focused.final=_
    rw [ff,bf,hf]
    rfl
  · change firstRun.steps+1+focused.steps=_
    rw [fs,bs]
    change native.steps+1+(2*w+1)=_
    rw [ns]
    omega

theorem pick (i : Fin 12) : RecoveryFocus.pick slots i=
    (![none,none,none,none,some 1,none,some 2,none,none,some 0,some 3,some 4] :
      Fin 12 → Option (Fin 5)) i := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot slots injective 0
    | exact RecoveryFocus.pick_slot slots injective 1
    | exact RecoveryFocus.pick_slot slots injective 2
    | exact RecoveryFocus.pick_slot slots injective 3
    | exact RecoveryFocus.pick_slot slots injective 4
    | decide

theorem output_heads (source : List Bool) (pos w : ℕ) (bits : List Bool) (sign : Bool)
    (positive negative : List Bool) :
    (output source pos w bits sign positive negative).heads=
      ![pos,0,0,1,2*min w bits.length,0,0,0,0,w,positive.length+2*w,negative.length+2*w] := by
  funext i
  fin_cases i <;> simp [output,RecoveryFocus.config,pick,Composition.rightConfig,RowPowerBlock.final,
    parsed,TapeEmbedding.config,DecompositionNativeMagnitude.fieldOutput,MatrixDimensionField.output,
    extraHeads,Fin.addCases,RowPowerBlock.digits]

end NearCubicWires.RepairOrdinary.RowPowerNative
