import Proof.MachineModel.OrdinaryWilliamsPaddingSentinel

/-! Position both physical raw-header cursors, preserving all four words
and restoring each width driver to its reusable head-one position. -/
namespace NearCubicWires.RepairOrdinary.WilliamsPaddingCursors
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 2 → Fin 4 := ![2,3]
noncomputable def first : Machine 4 7 := TapeEmbedding.machine 2 MatrixNaturalCursor.machine
noncomputable def second := RecoveryFocus.machine slots MatrixNaturalCursor.machine
noncomputable def machine := Composition.machine first second
def input (source header : List Bool) (u v : ℕ) : Fin 4 → List Bool :=
  ![source,UnaryTemplate.tape u,header,UnaryTemplate.tape v]

theorem cursors_run (source header : List Bool) (u v : ℕ) :
    ∃ r : ExecutionReceipt 4 14,
      run machine (3*u+3*v+11) (input source header u v)=some r ∧
      r.final.tapes=input source header u v ∧
      r.final.heads=![2*u+1,1,2*v+1,1] ∧ r.steps=3*u+3*v+11 := by
  obtain ⟨base,hb,hf,hs⟩ := MatrixNaturalCursor.cursor_run source u 0
  have he := TapeEmbedding.run_embed MatrixNaturalCursor.machine (fun _ : Fin 2 => 0)
    ![header,UnaryTemplate.tape v] _ _ base hb
  let ambient := TapeEmbedding.config (fun _ : Fin 2 => 0) ![header,UnaryTemplate.tape v] base.final
  obtain ⟨last,hl,hlf,hls⟩ := MatrixNaturalCursor.cursor_run header v 0
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes
      (MatrixNaturalCursor.cfg (s:=7) 0 header v 0 0)=Composition.restart ambient second.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) MatrixNaturalCursor.machine
    ambient.heads ambient.tapes _ _ last hl
  rw [hi] at hfocus
  have hj := Composition.run_join first second (3*u+5) (3*v+5) _
    (TapeEmbedding.receipt (fun _ : Fin 2 => 0) ![header,UnaryTemplate.tape v] base) focused he hfocus
  have htime : (3*u+5)+1+(3*v+5)=3*u+3*v+11 := by omega
  rw [htime] at hj
  have hin : Composition.leftConfig 7 (TapeEmbedding.config (fun _ : Fin 2 => 0)
      ![header,UnaryTemplate.tape v] (MatrixNaturalCursor.cfg (s:=7) 0 source u 0 0)) =
      initialConfiguration machine (input source header u v) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have p0 : RecoveryFocus.pick slots (0 : Fin 4)=none := by decide
  have p1 : RecoveryFocus.pick slots (1 : Fin 4)=none := by decide
  have p2 : RecoveryFocus.pick slots (2 : Fin 4)=some (0 : Fin 2) := RecoveryFocus.pick_slot slots (by decide) 0
  have p3 : RecoveryFocus.pick slots (3 : Fin 4)=some (1 : Fin 2) := RecoveryFocus.pick_slot slots (by decide) 1
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 2 => 0) ![header,UnaryTemplate.tape v] base) focused,hj,?_,?_,?_⟩
  · change focused.final.tapes=_
    rw [hff,hlf]
    dsimp only [ambient]
    rw [hf]
    funext i; fin_cases i <;> simp [RecoveryFocus.config,p0,p1,p2,p3,MatrixNaturalCursor.cfg,
      TapeEmbedding.config,Fin.addCases,input]
  · change focused.final.heads=_
    rw [hff,hlf]
    dsimp only [ambient]
    rw [hf]
    funext i; fin_cases i <;> simp [RecoveryFocus.config,p0,p1,p2,p3,MatrixNaturalCursor.cfg,
      TapeEmbedding.config,Fin.addCases]
  · change base.steps+1+focused.steps=_
    rw [hs,hfs,hls]
    exact htime

end NearCubicWires.RepairOrdinary.WilliamsPaddingCursors
