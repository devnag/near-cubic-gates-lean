import Proof.MachineModel.OrdinaryMatrixSentinelBitWidth

/-! Cold raw unary dimension to binary value and width. All intermediate
templates are produced by the same execution, and the complete phase pays
for restoration of all ten heads. -/
namespace NearCubicWires.RepairOrdinary.MatrixDimensionBinary
open LocalBitMultitape RepairSource.VerifierDecoding SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 6 → Fin 9 := ![3,4,5,6,7,8]
def header : Machine 9 4 := TapeEmbedding.machine 5 MatrixDimensionHeader.machine
noncomputable def width := RecoveryFocus.machine slots BitWidthMachine.machine
noncomputable def machine := Composition.machine header width
def input (n : ℕ) : Fin 9 → List Bool := fun i => if i=0 then List.replicate n true else []
def budget (n : ℕ) := 8*n^2+36*n+15

theorem binary_run (n : ℕ) (hn : 0<n) :
    ∃ r : ExecutionReceipt 9 29,
      run machine (budget n) (input n)=some r ∧
      r.final.tapes 1=List.replicate n true ∧ r.final.tapes 2=List.replicate n true ∧
      r.final.tapes 3=UnaryTemplate.tape n ∧
      r.final.tapes 5=frame (binary (natBitLength n) n) ∧
      r.final.tapes 8=CompareMachine.word (natBitLength n) ∧ r.steps ≤ budget n := by
  obtain ⟨base,hb,h1,h2,h3,hh,hs⟩ := MatrixRawDimension.raw_run n
  have he := TapeEmbedding.run_embed MatrixDimensionHeader.machine (fun _ : Fin 5 => 0)
    (fun _ : Fin 5 => []) _ _ base hb
  let ambient := TapeEmbedding.config (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base.final
  obtain ⟨last,hl,hl0,hl2,hl5,_,hls⟩ := MatrixSentinelBitWidth.width_run n hn
  have hi : RecoveryFocus.config slots ambient.heads ambient.tapes (MatrixSentinelBitWidth.input n)=
      Composition.restart ambient width.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i
      · change base.final.heads 3=1; rw [hh]; rfl
      all_goals rfl
    · intro i; fin_cases i
      · exact h3
      all_goals rfl
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots (by decide) BitWidthMachine.machine
    ambient.heads ambient.tapes _ (MatrixSentinelBitWidth.input n) last hl
  rw [hi] at hfocus
  have hj := Composition.run_join header width (2*n+3) (8*n^2+34*n+11) _
    (TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base) focused he hfocus
  have htime : (2*n+3)+1+(8*n^2+34*n+11)=budget n := by unfold budget; omega
  rw [htime] at hj
  have hin : Composition.leftConfig 25 (TapeEmbedding.config (fun _ : Fin 5 => 0)
      (fun _ : Fin 5 => []) (initialConfiguration MatrixDimensionHeader.machine (MatrixRawDimension.input n))) =
      initialConfiguration machine (input n) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at hj
  have hpick (i : Fin 6) : RecoveryFocus.pick slots (slots i)=some i := RecoveryFocus.pick_slot slots (by decide) i
  have other (i : Fin 9) (hi : RecoveryFocus.pick slots i=none) :
      focused.final.tapes i=ambient.tapes i := by rw [hff]; simp only [RecoveryFocus.config,hi]
  refine ⟨Composition.joinedReceipt
    (TapeEmbedding.receipt (fun _ : Fin 5 => 0) (fun _ : Fin 5 => []) base) focused,hj,
    (other 1 (by decide)).trans h1,(other 2 (by decide)).trans h2,?_,?_,?_,?_⟩
  · change focused.final.tapes (slots 0)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hl0
  · change focused.final.tapes (slots 2)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hl2
  · change focused.final.tapes (slots 5)=_
    rw [hff]; simpa only [RecoveryFocus.config,hpick] using hl5
  · change base.steps+1+focused.steps ≤ _
    rw [hs,hfs,←htime]
    omega

noncomputable def resetMachine := Rewind.machine machine
def resetInput (n : ℕ) : Fin 10 → List Bool :=
  Fin.addCases (motive := fun _ : Fin (9+1) => List Bool) (input n) (fun _ : Fin 1 => [])

theorem reset_run (n : ℕ) (hn : 0<n) :
    ∃ r : ExecutionReceipt 10 31,
      run resetMachine (16*n^2+72*n+32) (resetInput n)=some r ∧
      r.final.tapes 1=List.replicate n true ∧ r.final.tapes 2=List.replicate n true ∧
      r.final.tapes 3=UnaryTemplate.tape n ∧
      r.final.tapes 5=frame (binary (natBitLength n) n) ∧
      r.final.tapes 8=CompareMachine.word (natBitLength n) ∧
      (∀ i,r.final.heads i=0) ∧ r.steps ≤ 16*n^2+72*n+32 := by
  obtain ⟨base,hb,h1,h2,h3,h5,h8,hs⟩ := binary_run n hn
  obtain ⟨r,hr,ht,hh,hsteps,_⟩ := Rewind.reset_run machine (budget n) (input n) base hb
  have hbound : 2*base.steps+2 ≤ 16*n^2+72*n+32 := by unfold budget at hs; omega
  have hm := run_moreFuel resetMachine (2*base.steps+2)
    (16*n^2+72*n+32-(2*base.steps+2)) (resetInput n) r hr
  rw [Nat.add_sub_of_le hbound] at hm
  exact ⟨r,hm,(ht 1).trans h1,(ht 2).trans h2,(ht 3).trans h3,(ht 5).trans h5,
    (ht 8).trans h8,hh,hsteps.trans_le hbound⟩

end NearCubicWires.RepairOrdinary.MatrixDimensionBinary
