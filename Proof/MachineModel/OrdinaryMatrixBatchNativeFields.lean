import Proof.MachineModel.OrdinaryMatrixBatchSetupFields

/-! Full raw-batch setup followed by the paid native zero/driver initializer.
These are the actual shared fields for cut extraction and retained scoring. -/
namespace NearCubicWires.RepairOrdinary.MatrixBatchNativeFields
open LocalBitMultitape SignedSortKey MatrixScoreBatch
open MatrixScoreLeftLoop (C)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 21 → Fin 108 := ![23,90,91,92,93,28,94,95,96,97,77,98,99,100,101,102,103,104,105,106,107]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def first := TapeEmbedding.machine 18 MatrixBatchSetup.machine
noncomputable def last := RecoveryFocus.machine slots MatrixScoreColdFields.machine
noncomputable def machine := Composition.machine first last
def input (r : Request) : Fin 108 → List Bool := fun i => if i=0 then physicalInput r else []
def budget (r : Request) := MatrixBatchSetup.budget r+1+MatrixScoreColdFields.budget r.d r.M (C r)

theorem setup_run (r : Request) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
      actual.final.tapes 1=word r ∧ actual.final.heads 1=MatrixBatchSetup.gatesEnd r ∧
      actual.final.tapes 32=frame (binary r.M r.U) ∧ actual.final.heads 32=0 ∧
      actual.final.tapes 39=UnaryTemplate.tape r.U ∧ actual.final.heads 39=1 ∧
      actual.final.tapes 40=List.replicate r.p true ∧ actual.final.heads 40=0 ∧
      actual.final.tapes 49=List.replicate (r.S+1) true ∧ actual.final.heads 49=0 ∧
      actual.final.tapes 61=frame (binary (r.S+1) (2^r.S)) ∧ actual.final.heads 61=0 ∧
      actual.final.tapes 65=frame (binary (r.S+1) 0) ∧ actual.final.heads 65=0 ∧
      actual.final.tapes 77=List.replicate (C r) true ∧ actual.final.heads 77=0 ∧
      actual.final.tapes 80=List.replicate (natBitLength r.Gates) true ∧ actual.final.heads 80=0 ∧
      actual.final.tapes 83=frame (binary (natBitLength r.Gates) r.Gates) ∧ actual.final.heads 83=0 ∧
      actual.final.tapes 89=UnaryTemplate.tape r.Gates ∧ actual.final.heads 89=1 ∧
      actual.final.tapes 92=UnaryTemplate.tape r.d ∧ actual.final.heads 92=0 ∧
      actual.final.tapes 95=frame (binary r.d 0) ∧ actual.final.heads 95=0 ∧
      actual.final.tapes 99=frame (binary r.d 0) ∧ actual.final.heads 99=0 ∧
      actual.final.tapes 103=frame (binary r.M 0) ∧ actual.final.heads 103=0 ∧
      actual.final.tapes 106=List.replicate (C r) false ∧ actual.final.heads 106=0 ∧
      actual.final.tapes 107=List.replicate (C r+1) false ∧ actual.final.heads 107=0 ∧
      actual.steps≤budget r := by
  obtain ⟨base,hb,b0,h0,b1,h1,b23,h23,b28,h28,b32,h32,b39,h39,b40,h40,b49,h49,
    b61,h61,b65,h65,b77,h77,b80,h80,b83,h83,b89,h89,bs⟩ := MatrixBatchSetupFields.setup_run r
  have he := TapeEmbedding.run_embed MatrixBatchSetup.machine (fun _ : Fin 18 => 0) (fun _ : Fin 18 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 18 => 0) (fun _ : Fin 18 => []) base
  obtain ⟨fields,hf,fh,f3,f7,f12,f16,f10,f19,f20,fs⟩ := MatrixScoreColdFields.fields_run r.d r.M (C r)
  let entry := initialConfiguration MatrixScoreColdFields.machine (MatrixScoreColdFields.input r.d r.M (C r))
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      · exact h23
      · rfl
      · rfl
      · rfl
      · rfl
      · exact h28
      · rfl
      · rfl
      · rfl
      · rfl
      · exact h77
      all_goals rfl
    · intro i
      fin_cases i
      · exact b23
      · rfl
      · rfl
      · rfl
      · rfl
      · exact b28
      · rfl
      · rfl
      · rfl
      · rfl
      · exact b77
      all_goals rfl
  obtain ⟨focused,hfocus,hff,hfs⟩ := RecoveryFocus.run_config slots slots_injective MatrixScoreColdFields.machine
    prepared.final.heads prepared.final.tapes _ entry fields hf
  rw [hi] at hfocus
  have joined := Composition.run_join first last _ _ _ prepared focused he hfocus
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 18 => 0) (fun _ : Fin 18 => [])
      (initialConfiguration MatrixBatchSetup.machine (MatrixBatchSetup.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have otherT (i : Fin 90) (hn : RecoveryFocus.pick slots (i.castAdd 18)=none) :
      focused.final.tapes (i.castAdd 18)=base.final.tapes i := by
    rw [hff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have otherH (i : Fin 90) (hn : RecoveryFocus.pick slots (i.castAdd 18)=none) :
      focused.final.heads (i.castAdd 18)=base.final.heads i := by
    rw [hff]
    simp [RecoveryFocus.config,hn,prepared,TapeEmbedding.receipt,TapeEmbedding.config]
  have localT (i : Fin 21) : focused.final.tapes (slots i)=fields.final.tapes i := by
    rw [hff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have localH (i : Fin 21) : focused.final.heads (slots i)=0 := by
    rw [hff]; simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,fh]
  refine ⟨Composition.joinedReceipt prepared focused,joined,
    (otherT 0 (by decide)).trans b0,(otherH 0 (by decide)).trans h0,
    (otherT 1 (by decide)).trans b1,(otherH 1 (by decide)).trans h1,
    (otherT 32 (by decide)).trans b32,(otherH 32 (by decide)).trans h32,
    (otherT 39 (by decide)).trans b39,(otherH 39 (by decide)).trans h39,
    (otherT 40 (by decide)).trans b40,(otherH 40 (by decide)).trans h40,
    (otherT 49 (by decide)).trans b49,(otherH 49 (by decide)).trans h49,
    (otherT 61 (by decide)).trans b61,(otherH 61 (by decide)).trans h61,
    (otherT 65 (by decide)).trans b65,(otherH 65 (by decide)).trans h65,
    (localT 10).trans f10,localH 10,
    (otherT 80 (by decide)).trans b80,(otherH 80 (by decide)).trans h80,
    (otherT 83 (by decide)).trans b83,(otherH 83 (by decide)).trans h83,
    (otherT 89 (by decide)).trans b89,(otherH 89 (by decide)).trans h89,
    (localT 3).trans f3,localH 3,(localT 7).trans f7,localH 7,
    (localT 12).trans f12,localH 12,(localT 16).trans f16,localH 16,
    (localT 19).trans f19,localH 19,(localT 20).trans f20,localH 20,?_⟩
  change prepared.steps+1+focused.steps≤_
  rw [hfs]
  change base.steps+1+fields.steps≤budget r
  unfold budget
  omega

/-- The dead work of the native initializer, on the same run: every tape of the zero/driver initializer
ends with its head at cell 0 and at most `max (C r) (budget+1)` cells. The batch reuses these tapes as
gate scratch, which each gate erases before use. -/
theorem setup_run_dead (r : Request) :
    ∃ actual,run machine (budget r) (input r)=some actual ∧
      (∀ i : Fin 21,actual.final.heads (slots i)=0) ∧
      (∀ i : Fin 21,(actual.final.tapes (slots i)).length≤ max (C r) (MatrixScoreColdFields.budget r.d r.M (C r)+1)) := by
  obtain ⟨base,hb,b0,h0,b1,h1,b23,h23,b28,h28,b32,h32,b39,h39,b40,h40,b49,h49,
    b61,h61,b65,h65,b77,h77,b80,h80,b83,h83,b89,h89,bs⟩ := MatrixBatchSetupFields.setup_run r
  have he := TapeEmbedding.run_embed MatrixBatchSetup.machine (fun _ : Fin 18 => 0) (fun _ : Fin 18 => []) _ _ base hb
  let prepared := TapeEmbedding.receipt (fun _ : Fin 18 => 0) (fun _ : Fin 18 => []) base
  obtain ⟨fields,hf,fh,_,_,_,_,_,_,_,fs⟩ := MatrixScoreColdFields.fields_run r.d r.M (C r)
  let entry := initialConfiguration MatrixScoreColdFields.machine (MatrixScoreColdFields.input r.d r.M (C r))
  have hi : RecoveryFocus.config slots prepared.final.heads prepared.final.tapes entry=
      Composition.restart prepared.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      fin_cases i
      · exact h23
      · rfl
      · rfl
      · rfl
      · rfl
      · exact h28
      · rfl
      · rfl
      · rfl
      · rfl
      · exact h77
      all_goals rfl
    · intro i
      fin_cases i
      · exact b23
      · rfl
      · rfl
      · rfl
      · rfl
      · exact b28
      · rfl
      · rfl
      · rfl
      · rfl
      · exact b77
      all_goals rfl
  obtain ⟨focused,hfocus,hff,_⟩ := RecoveryFocus.run_config slots slots_injective MatrixScoreColdFields.machine
    prepared.final.heads prepared.final.tapes _ entry fields hf
  rw [hi] at hfocus
  have joined := Composition.run_join first last _ _ _ prepared focused he hfocus
  have hin : Composition.leftConfig _ (TapeEmbedding.config (fun _ : Fin 18 => 0) (fun _ : Fin 18 => [])
      (initialConfiguration MatrixBatchSetup.machine (MatrixBatchSetup.input r)))=
      initialConfiguration machine (input r) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · funext i; fin_cases i <;> rfl
  rw [hin] at joined
  have hm := common_width r
  have support := RecoveryTapeSupport.run_support MatrixScoreColdFields.machine _ entry fields hf (C r) 0
    (by intro i; exact Nat.le_refl 0)
    (by
      intro i
      have hc : r.d≤C r ∧ r.M≤C r := by unfold C; omega
      simp only [entry,initialConfiguration,MatrixScoreColdFields.input]
      split_ifs <;> simp <;> omega)
  refine ⟨Composition.joinedReceipt prepared focused,joined,?_,?_⟩
  · intro i
    change focused.final.heads (slots i)=0
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective,fh]
  · intro i
    change (focused.final.tapes (slots i)).length≤_
    rw [hff]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
    have h := support i
    omega

end NearCubicWires.RepairOrdinary.MatrixBatchNativeFields
