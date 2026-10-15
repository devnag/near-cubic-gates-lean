import Proof.Supplier.RowPowerNativeReusable
import Proof.MachineModel.ClockScalarFields

/-! Exact reusable endpoint and binary meaning of the executed native-field
appender. Its output is ready for the next call on the same physical bank. -/
namespace NearCubicWires.RepairOrdinary.RowPowerNativeReusable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
open Streaming SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def heads (pos : ℕ) (positive negative : List Bool) : Fin 15 → ℕ :=
  ![pos,0,0,0,0,0,0,0,0,0,positive.length,negative.length,0,0,0]
def tapes (source : List Bool) (w C : ℕ) (positive negative : List Bool) : Fin 15 → List Bool :=
  ![source,List.replicate C false,List.replicate C false,List.replicate C false,
    List.replicate C false,List.replicate C false,List.replicate C false,
    List.replicate C false,List.replicate C false,List.replicate w true,
    positive++[false],negative++[false],List.replicate C false,
    List.replicate C true,List.replicate (C+1) false]
def block (w : ℕ) (z : ℤ) (negative : Bool) :=
  RowPowerBlock.digits negative (decide (z<0))
    (ClockNormalize.resize w (binary (natBitLength z.natAbs) z.natAbs))

theorem entry_heads (source : List Bool) (pos w C : ℕ) (positive negative : List Bool) :
    (entry source pos w C positive negative).heads=heads pos positive negative := by
  funext i
  fin_cases i <;> rfl

theorem entry_tapes (source : List Bool) (pos w C : ℕ) (positive negative : List Bool) :
    (entry source pos w C positive negative).tapes=tapes source w C positive negative := by
  funext i
  fin_cases i <;>
    simp [entry,RowPowerNativeReset.entry,RowPowerNativeReset.caps,ZeroPadding.config,
      Rewind.recording,Rewind.config,TapeEmbedding.config,Composition.leftConfig,
      RowPowerNative.entry,RowPowerNative.extraTapes,DecompositionNativeMagnitude.input,
      extra,tapes,Fin.addCases,ZeroPadding.pad]

theorem raw_output_live (source : List Bool) (pos w : ℕ) (z : ℤ)
    (positive negative : List Bool) (i : Fin 12) (hi : i=0 ∨ i=9 ∨ i=10 ∨ i=11) :
    (RowPowerNative.output source pos w (binary (natBitLength z.natAbs) z.natAbs)
      (decide (z<0)) positive negative).tapes i=
    (![source,[],[],[],[],[],[],[],[],List.replicate w true,
      positive++marks (block w z false)++[false],
      negative++marks (block w z true)++[false]] : Fin 12 → List Bool) i := by
  rcases hi with rfl|rfl|rfl|rfl
  all_goals simp [RowPowerNative.output,RecoveryFocus.config,RowPowerNative.pick,
    RowPowerNative.parsed,TapeEmbedding.config,RowPowerNative.extraTapes,
    DecompositionNativeMagnitude.fieldOutput,MatrixDimensionField.output,
    RowPowerBlock.final,Composition.rightConfig,Fin.addCases,block]

theorem reset_output_live (source : List Bool) (pos w C : ℕ) (z : ℤ)
    (positive negative : List Bool) (i : Fin 15) (hi : i=0 ∨ i=9 ∨ i=10 ∨ i=11) :
    (resetOutput source pos w C z positive negative).tapes i=
      tapes source w C (positive++marks (block w z false))
        (negative++marks (block w z true)) i := by
  rcases hi with rfl|rfl|rfl|rfl
  · change ZeroPadding.pad 0 ((RowPowerNative.output source pos w
      (binary (natBitLength z.natAbs) z.natAbs) (decide (z<0)) positive negative).tapes 0)=_
    rw [raw_output_live _ _ _ _ _ _ 0 (by simp)]
    simp [tapes,ZeroPadding.pad]
  · change ZeroPadding.pad 0 ((RowPowerNative.output source pos w
      (binary (natBitLength z.natAbs) z.natAbs) (decide (z<0)) positive negative).tapes 9)=_
    rw [raw_output_live _ _ _ _ _ _ 9 (by simp)]
    simp [tapes,ZeroPadding.pad]
  · change ZeroPadding.pad (positive.length+1) ((RowPowerNative.output source pos w
      (binary (natBitLength z.natAbs) z.natAbs) (decide (z<0)) positive negative).tapes 10)=_
    rw [raw_output_live _ _ _ _ _ _ 10 (by simp)]
    simp [tapes,ZeroPadding.pad,List.length_append]
  · change ZeroPadding.pad (negative.length+1) ((RowPowerNative.output source pos w
      (binary (natBitLength z.natAbs) z.natAbs) (decide (z<0)) positive negative).tapes 11)=_
    rw [raw_output_live _ _ _ _ _ _ 11 (by simp)]
    simp [tapes,ZeroPadding.pad,List.length_append]

theorem endpoint_tapes (source : List Bool) (pos w C : ℕ) (z : ℤ)
    (positive negative : List Bool) :
    cleared C (resetOutput source pos w C z positive negative).tapes=
      tapes source w C (positive++marks (block w z false))
        (negative++marks (block w z true)) := by
  funext i
  fin_cases i
  · exact (cleared_live C _ _ (by simp)).trans (reset_output_live _ _ _ _ _ _ _ _ (by simp))
  · exact cleared_work C _ 0
  · exact cleared_work C _ 1
  · exact cleared_work C _ 2
  · exact cleared_work C _ 3
  · exact cleared_work C _ 4
  · exact cleared_work C _ 5
  · exact cleared_work C _ 6
  · exact cleared_work C _ 7
  · exact (cleared_live C _ _ (by simp)).trans (reset_output_live _ _ _ _ _ _ _ _ (by simp))
  · exact (cleared_live C _ _ (by simp)).trans (reset_output_live _ _ _ _ _ _ _ _ (by simp))
  · exact (cleared_live C _ _ (by simp)).trans (reset_output_live _ _ _ _ _ _ _ _ (by simp))
  · exact cleared_work C _ 8
  · exact install_slot eraseSlots erase_injective _ _ (((0 : Fin 1).natAdd 9).castAdd 1)
  · exact install_slot eraseSlots erase_injective _ _ ((0 : Fin 1).natAdd 10)

theorem block_length (w : ℕ) (z : ℤ) (negative : Bool) : (block w z negative).length=w := by
  simp [block,RowPowerBlock.digits]

theorem endpoint_heads (source : List Bool) (pos w C : ℕ) (z : ℤ)
    (positive negative : List Bool) :
    (resetOutput source pos w C z positive negative).heads=
      heads pos (positive++marks (block w z false)) (negative++marks (block w z true)) := by
  have hh := RowPowerNativeReset.output_heads source pos w C z positive negative
  funext i
  fin_cases i <;> simp [resetOutput,TapeEmbedding.config,hh,Fin.addCases,heads,block_length]

theorem reusable_run (pre suffix positive negative : List Bool) (z : ℤ) (w C : ℕ)
    (hC : RowPowerNativeReset.rawTime z w+1≤C) :
    ∃ r,runFrom machine (budget z w C)
      ⟨machine.start,heads pre.length positive negative,
        tapes (pre++intWord z++suffix) w C positive negative⟩=some r ∧
      r.final.heads=heads (pre.length+(intWord z).length)
        (positive++marks (block w z false)) (negative++marks (block w z true)) ∧
      r.final.tapes=tapes (pre++intWord z++suffix) w C
        (positive++marks (block w z false)) (negative++marks (block w z true)) ∧
      r.steps=budget z w C := by
  obtain ⟨r,hr,rh,rt,rs⟩ := field_run pre suffix positive negative z w C hC
  have hi : entry (pre++intWord z++suffix) pre.length w C positive negative=
      ⟨machine.start,heads pre.length positive negative,tapes (pre++intWord z++suffix) w C positive negative⟩ :=
    configuration_ext rfl (entry_heads ..) (entry_tapes ..)
  rw [hi] at hr
  exact ⟨r,hr,rh.trans (endpoint_heads ..),rt.trans (endpoint_tapes ..),rs⟩

end NearCubicWires.RepairOrdinary.RowPowerNativeReusable
