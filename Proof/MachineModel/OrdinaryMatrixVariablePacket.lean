import Proof.MachineModel.OrdinaryMatrixPacketDock

/-! The exact native source output and its generated driver dock to the
physical packet writer, retaining the external append cursor. -/
namespace NearCubicWires.RepairOrdinary.MatrixVariablePacket
open LocalBitMultitape MatrixScoreBatch RepairRepresentation MatrixWilliamsProduct
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def offset (a : WilliamsAlgorithm) : Fin (MatrixVariableCount.tapes a) :=
  ((424 : Fin 425).castAdd (source a).program.tapeCount).castAdd 17
noncomputable def count (a : WilliamsAlgorithm) := MatrixVariableCount.slots a 16
noncomputable def sourceTape (a : WilliamsAlgorithm) := (MatrixVariableProduct.outputTape a).castAdd 17
noncomputable def outputTape (a : WilliamsAlgorithm) := (16 : Fin 17).natAdd (MatrixVariableProduct.tapes a)
noncomputable def slots (a : WilliamsAlgorithm) : Fin 4 → Fin (MatrixVariableCount.tapes a) :=
  ![offset a,count a,sourceTape a,outputTape a]
theorem source_ne_offset (a : WilliamsAlgorithm) : (MatrixVariableProduct.outputTape a).val≠424 := by
  unfold MatrixVariableProduct.outputTape MatrixVariableProduct.slots
  split
  · change (422 : ℕ)≠424
    decide
  · simp only [Fin.val_natAdd]
    omega

theorem slots_injective (a : WilliamsAlgorithm) : Function.Injective (slots a) := by
  intro i j he
  have hk : 425≤MatrixVariableProduct.tapes a := by unfold MatrixVariableProduct.tapes; omega
  have hs := (MatrixVariableProduct.outputTape a).isLt
  have hn := source_ne_offset a
  have values (i : Fin 4) : (slots a i).val=
      (![(424 : ℕ),MatrixVariableProduct.tapes a+14,(MatrixVariableProduct.outputTape a).val,
        MatrixVariableProduct.tapes a+16] : Fin 4 → ℕ) i := by fin_cases i <;> rfl
  have hv : (![(424 : ℕ),MatrixVariableProduct.tapes a+14,(MatrixVariableProduct.outputTape a).val,
      MatrixVariableProduct.tapes a+16] : Fin 4 → ℕ) i=
    (![(424 : ℕ),MatrixVariableProduct.tapes a+14,(MatrixVariableProduct.outputTape a).val,
      MatrixVariableProduct.tapes a+16] : Fin 4 → ℕ) j := by
    rw [←values,←values]
    exact congrArg Fin.val he
  fin_cases i <;> fin_cases j <;> norm_num at hv <;> first | rfl | omega

noncomputable def last (a : WilliamsAlgorithm) (negative : Bool) :=
  RecoveryFocus.machine (slots a) (MatrixPacketDock.machine negative)
noncomputable def machine (a : WilliamsAlgorithm) (negative : Bool) :=
  Composition.machine (MatrixVariableCount.machine a negative) (last a negative)
noncomputable def input (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) (out : List Bool) :=
  Composition.leftConfig 14 (MatrixVariableCount.input a r bit out)
noncomputable def budget (a : WilliamsAlgorithm) (r : Request) (bit : ℕ) (negative : Bool) :=
  MatrixVariableCount.budget a r+1+MatrixPacketDock.budget bit (planeCounts r negative bit)

theorem call_run {s : ℕ} (a : WilliamsAlgorithm) (negative : Bool) (bit : ℕ)
    (bits out : List Bool) (c : Configuration (MatrixVariableCount.tapes a) s)
    (ct : ∀ j,c.tapes (slots a j)=(MatrixPacketDock.input bit bits out).tapes j)
    (ch : ∀ j,c.heads (slots a j)=(MatrixPacketDock.input bit bits out).heads j) : ∃ actual,
    runFrom (last a negative) (MatrixPacketDock.budget bit bits)
      (Composition.restart c (last a negative).start)=some actual ∧
    actual.final.tapes (outputTape a)=out++MatrixPacketPrefix.prefixWord negative bit++bits ∧
    actual.final.heads (outputTape a)=(out++MatrixPacketPrefix.prefixWord negative bit++bits).length ∧
    actual.final.tapes (offset a)=UnaryTemplate.tape (2*bit) ∧ actual.final.heads (offset a)=1 ∧
    actual.final.tapes (count a)=UnaryTemplate.tape bits.length ∧ actual.final.heads (count a)=1 ∧
    actual.final.tapes (sourceTape a)=bits ∧ actual.final.heads (sourceTape a)=bits.length ∧
    (∀ i,(∀ j,slots a j≠i) → actual.final.tapes i=c.tapes i ∧ actual.final.heads i=c.heads i) ∧
    actual.steps=MatrixPacketDock.budget bit bits := by
  obtain ⟨body,hb,bh,bt,bs⟩ := MatrixPacketDock.dock_run negative bit bits out
  let entry := MatrixPacketDock.input bit bits out
  have hi : RecoveryFocus.config (slots a) c.heads c.tapes entry=
      Composition.restart c (last a negative).start := WilliamsSourceCrop.focus_same (slots a) c entry ch ct
  obtain ⟨actual,ha,hf,hs⟩ := RecoveryFocus.run_config (slots a) (slots_injective a)
    (MatrixPacketDock.machine negative) c.heads c.tapes _ entry body hb
  rw [hi] at ha
  have localT (j : Fin 4) : actual.final.tapes (slots a j)=
      (![UnaryTemplate.tape (2*bit),UnaryTemplate.tape bits.length,bits,
        out++MatrixPacketPrefix.prefixWord negative bit++bits] : Fin 4 → List Bool) j := by
    rw [hf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots a) (slots_injective a),bt]
  have localH (j : Fin 4) : actual.final.heads (slots a j)=
      (![1,1,bits.length,(out++MatrixPacketPrefix.prefixWord negative bit++bits).length] : Fin 4 → ℕ) j := by
    rw [hf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot (slots a) (slots_injective a),bh]
  refine ⟨actual,ha,localT 3,localH 3,localT 0,localH 0,localT 1,localH 1,localT 2,localH 2,?_,hs.trans bs⟩
  intro i hi
  rw [hf]
  simp [RecoveryFocus.config,RecoveryFocus.pick,not_exists.mpr hi]

end NearCubicWires.RepairOrdinary.MatrixVariablePacket
