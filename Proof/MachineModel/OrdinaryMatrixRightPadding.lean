import Proof.MachineModel.OrdinaryMatrixRightRows

/-! The complete right-row selector followed by actual trailing-zero
production. Empty inner dimensions still produce the required padded bits. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightPadding
open LocalBitMultitape
open MatrixRightRows (Row fields output)
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def rowStates := Fintype.card (RepeatMachine.Control 34)
def cfg {s : ℕ} (q : Fin s) (source : List Bool) (pos : ℕ) (out : List Bool) (U used pad : ℕ) : Configuration 5 s :=
  ⟨q,![pos,out.length,1,1,1],![source,out,UnaryTemplate.tape U,CompareMachine.word used,UnaryTemplate.tape pad]⟩
noncomputable def rowsMachine : Machine 5 rowStates := TapeEmbedding.machine 1 MatrixRightRows.machine
def swap : Fin 5 ≃ Fin 5 where
  toFun := ![0,1,2,4,3]
  invFun := ![0,1,2,4,3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl
@[simp] theorem swap_inverse : (swap.symm : Fin 5 → Fin 5)=![0,1,2,4,3] := rfl
def zerosMachine : Machine 5 5 := TapeRenaming.machine swap (TapeEmbedding.machine 1 PaddedRow.zeros)
noncomputable def machine : Machine 5 (rowStates+5) := Composition.machine rowsMachine zerosMachine

theorem rows_place (phase : Fin 5) (source : List Bool) (pos : ℕ) (out : List Bool) (U used pad : ℕ) :
    TapeEmbedding.config (fun _ : Fin 1 => 1) (fun _ : Fin 1 => UnaryTemplate.tape pad)
      (RepeatMachine.cfg phase (MatrixRightRows.core source pos out U) used 1)=
      cfg (RepeatMachine.phaseCode 34 phase) source pos out U used pad := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeEmbedding.config,RepeatMachine.cfg,controlConfig,MatrixRightRows.core,
      PayloadCounted.config,cfg,Fin.addCases]
  · funext i
    fin_cases i <;> simp [TapeEmbedding.config,RepeatMachine.cfg,controlConfig,MatrixRightRows.core,
      PayloadCounted.config,cfg,Fin.addCases]

theorem zeros_place (q : Fin 5) (source : List Bool) (pos : ℕ) (out : List Bool) (U used pad : ℕ) :
    TapeRenaming.config swap
      (TapeEmbedding.config (fun _ : Fin 1 => 1) (fun _ : Fin 1 => CompareMachine.word used)
        (PaddedRow.config q source pos out U pad))=cfg q source pos out U used pad := by
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,PaddedRow.config,
      PayloadCounted.config,cfg,Fin.addCases]
  · funext i
    fin_cases i <;> simp [TapeRenaming.config,TapeEmbedding.config,PaddedRow.config,
      PayloadCounted.config,cfg,Fin.addCases]

theorem zeros_run (source : List Bool) (pos : ℕ) (out : List Bool) (U used pad : ℕ) :
    ∃ actual : ExecutionReceipt 5 5,runFrom zerosMachine (2*pad+4)
      (cfg 0 source pos out U used pad)=some actual ∧
      actual.final=cfg 4 source pos (out++List.replicate pad false) U used pad ∧ actual.steps=2*pad+4 := by
  obtain ⟨base,hbase,hf,hs,_⟩ := PaddedRow.zeros_run source pos out U pad
  have he := TapeEmbedding.run_embed PaddedRow.zeros (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => CompareMachine.word used) _ _ base hbase
  have hn := TapeRenaming.run_rename swap (TapeEmbedding.machine 1 PaddedRow.zeros) _ _ _ he
  rw [zeros_place] at hn
  refine ⟨TapeRenaming.receipt swap (TapeEmbedding.receipt (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => CompareMachine.word used) base),hn,?_,hs⟩
  change TapeRenaming.config swap (TapeEmbedding.config (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => CompareMachine.word used) base.final)=_
  rw [hf,zeros_place]

theorem padding_run (U pad : ℕ) (rows : List Row) (pre suffix out : List Bool)
    (hw : ∀ row ∈ rows,row.1.length=U ∧ row.2.length=U) :
    ∃ actual : ExecutionReceipt 5 (rowStates+5),
      runFrom machine ((fields rows).length+rows.length*(6*U+12)+2*pad+8)
        (cfg machine.start (pre++fields rows++suffix) pre.length out U rows.length pad)=some actual ∧
      actual.final=cfg (Fin.natAdd rowStates (4 : Fin 5)) (pre++fields rows++suffix)
        (pre.length+(fields rows).length) (out++output rows++List.replicate pad false) U rows.length pad ∧
      actual.steps ≤ (fields rows).length+rows.length*(6*U+12)+2*pad+8 := by
  obtain ⟨base,hbase,hf,hs⟩ := MatrixRightRows.complete_run U rows pre suffix out hw
  have he := TapeEmbedding.run_embed MatrixRightRows.machine (fun _ : Fin 1 => 1)
    (fun _ : Fin 1 => UnaryTemplate.tape pad) _ _ base hbase
  rw [rows_place] at he
  let first := TapeEmbedding.receipt (fun _ : Fin 1 => 1) (fun _ : Fin 1 => UnaryTemplate.tape pad) base
  have hff : first.final=cfg (RepeatMachine.phaseCode 34 3) (pre++fields rows++suffix)
      (pre.length+(fields rows).length) (out++output rows) U rows.length pad := by
    change TapeEmbedding.config _ _ base.final=_
    rw [hf,rows_place]
  obtain ⟨last,hl,hlf,hls⟩ := zeros_run (pre++fields rows++suffix)
    (pre.length+(fields rows).length) (out++output rows) U rows.length pad
  have hi : Composition.restart first.final zerosMachine.start=
      cfg 0 (pre++fields rows++suffix) (pre.length+(fields rows).length) (out++output rows) U rows.length pad := by
    rw [hff]
    rfl
  rw [←hi] at hl
  have hj := Composition.run_join rowsMachine zerosMachine
    ((fields rows).length+rows.length*(6*U+12)+3) (2*pad+4)
    (cfg rowsMachine.start (pre++fields rows++suffix) pre.length out U rows.length pad) first last he hl
  have htime : ((fields rows).length+rows.length*(6*U+12)+3)+1+(2*pad+4)=
      (fields rows).length+rows.length*(6*U+12)+2*pad+8 := by omega
  rw [htime] at hj
  refine ⟨Composition.joinedReceipt first last,hj,?_,?_⟩
  · change Composition.rightConfig rowStates last.final=_
    rw [hlf]
    rfl
  · change base.steps+1+last.steps ≤ _
    omega

end NearCubicWires.RepairOrdinary.MatrixRightPadding
