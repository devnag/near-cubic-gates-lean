import Proof.MachineModel.OrdinaryMatrixDimensionHeader
import Proof.Hierarchy.CompetitorRawCell

/-! The dimension width and binary value are both read from the same raw
header. The width drivers used by the framing call are the literal output
of the preceding header scan. -/
namespace NearCubicWires.RepairOrdinary.MatrixDimensionField
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 5 → Fin 6 := ![0,1,2,4,5]
theorem slots_injective : Function.Injective slots := by decide
def header : Machine 6 4 := TapeEmbedding.machine 2 MatrixDimensionHeader.machine
noncomputable def field : Machine 6 4 := RecoveryFocus.machine slots CompetitorRawCell.machine
noncomputable def machine : Machine 6 8 := Composition.machine header field

def input (source : List Bool) (pos : ℕ) : Configuration 6 4 :=
  TapeEmbedding.config (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) (MatrixDimensionHeader.input source pos)
def output (source : List Bool) (pos : ℕ) (bits : List Bool) : Configuration 6 8 :=
  ⟨7,![pos,0,0,1,0,0],![source,List.replicate bits.length true,
    List.replicate bits.length true,UnaryTemplate.tape bits.length,frame bits,
    List.replicate (2*bits.length+1) false]⟩

theorem field_run (pre bits suffix : List Bool) :
    let source := pre ++ List.replicate bits.length true ++ false :: (bits ++ suffix)
    ∃ r : ExecutionReceipt 6 8,
      runFrom machine (6*bits.length+7)
        (Composition.leftConfig 4 (input source pre.length)) = some r ∧
      r.final = output source (pre.length+2*bits.length+1) bits ∧
      r.steps = 6*bits.length+7 := by
  dsimp only
  let source := pre ++ List.replicate bits.length true ++ false :: (bits ++ suffix)
  let preHeader := pre ++ List.replicate bits.length true ++ [false]
  obtain ⟨first,hfirst,hfinal,hsteps⟩ := MatrixDimensionHeader.header_run pre (bits++suffix) bits.length
  have he := TapeEmbedding.run_embed MatrixDimensionHeader.machine
    (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) _ _ first hfirst
  let ambient := TapeEmbedding.config (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) first.final
  obtain ⟨second,hsecond,hsfinal,hssteps⟩ := CompetitorRawCell.cell_run preHeader bits suffix [] 0 (by simp)
  have hsource : preHeader ++ bits ++ suffix = source := by simp [preHeader,source,List.append_assoc]
  have hlength : preHeader.length = pre.length+bits.length+1 := by simp [preHeader,Nat.add_assoc]
  rw [hsource,hlength] at hsecond hsfinal
  let entry := CompetitorRawCell.scan 0 source (pre.length+bits.length+1)
    bits.length bits.length 0 0 [] []
  have hsame : RecoveryFocus.config slots ambient.heads ambient.tapes entry =
      Composition.restart ambient field.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      dsimp only [ambient]
      rw [hfinal]
      fin_cases i <;> simp [slots,entry,CompetitorRawCell.scan,TapeEmbedding.config,
        MatrixDimensionHeader.output,Fin.addCases]
    · intro i
      dsimp only [ambient]
      rw [hfinal]
      fin_cases i <;> simp [slots,entry,CompetitorRawCell.scan,TapeEmbedding.config,
        MatrixDimensionHeader.output,Fin.addCases,source,StablePartition.Workspace.overlay]
  have hsecond' : runFrom CompetitorRawCell.machine (4*bits.length+3) entry = some second := by
    simpa [entry] using hsecond
  obtain ⟨focused,hfocus,hfocusFinal,hfocusSteps⟩ := RecoveryFocus.run_config slots slots_injective
    CompetitorRawCell.machine ambient.heads ambient.tapes (4*bits.length+3) entry second hsecond'
  rw [hsame] at hfocus
  have hjoin := Composition.run_join header field (2*bits.length+3) (4*bits.length+3) _
    (TapeEmbedding.receipt (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) first) focused he hfocus
  have htime : 2*bits.length+3+1+(4*bits.length+3) = 6*bits.length+7 := by omega
  rw [htime] at hjoin
  have hslot (i : Fin 5) : RecoveryFocus.pick slots (slots i) = some i :=
    RecoveryFocus.pick_slot slots slots_injective i
  have hnone : RecoveryFocus.pick slots (3 : Fin 6) = none := by decide
  have hpick : ∀ i : Fin 6, RecoveryFocus.pick slots i =
      (![some 0,some 1,some 2,none,some 3,some 4] : Fin 6 → Option (Fin 5)) i := by
    intro i; fin_cases i
    · exact hslot 0
    · exact hslot 1
    · exact hslot 2
    · exact hnone
    · exact hslot 3
    · exact hslot 4
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 2 => 0) (fun _ : Fin 2 => []) first) focused,hjoin,?_,?_⟩
  · change Composition.rightConfig 4 focused.final = _
    rw [hfocusFinal,hsfinal]
    dsimp only [ambient]
    rw [hfinal]
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,hpick,output,
        CompetitorRawCell.reset,TapeEmbedding.config,MatrixDimensionHeader.output,Fin.addCases]
      omega
    · funext i
      fin_cases i <;> simp [Composition.rightConfig,RecoveryFocus.config,hpick,output,
        CompetitorRawCell.reset,TapeEmbedding.config,MatrixDimensionHeader.output,Fin.addCases,source]
  · change first.steps+1+focused.steps = _
    rw [hsteps,hfocusSteps,hssteps]
    omega

end NearCubicWires.RepairOrdinary.MatrixDimensionField
