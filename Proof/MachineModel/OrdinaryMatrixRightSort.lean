import Proof.MachineModel.OrdinaryMatrixRightPlane

/-! Actual coordinate sort, paid rewind and literal right-matrix selection
and padding on eleven fixed tapes. Dimension templates are retained inputs. -/
namespace NearCubicWires.RepairOrdinary.MatrixRightSort
open LocalBitMultitape SupplierPrinter CoordinateKey
open RepairSource.VerifierDecoding
open WilliamsLoaderForms (rowMajorBitMatrix)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def planeStates := MatrixRightPadding.rowStates+5
noncomputable def sortMachine : Machine 11 88 := SortMatrix.sortMachine
noncomputable def planeMachine : Machine 11 planeStates :=
  TapeRenaming.machine SortRank.rankLayout (TapeEmbedding.machine 6 MatrixRightPadding.machine)
noncomputable def machine : Machine 11 (88+planeStates) := Composition.machine sortMachine planeMachine
noncomputable def input (req : SortCarrier.Request) (out : List Bool) (U used pad : ℕ) : Configuration 11 (88+planeStates) :=
  Composition.leftConfig planeStates (TapeEmbedding.config ![out.length,1,1,1]
    ![out,UnaryTemplate.tape U,CompareMachine.word used,UnaryTemplate.tape pad]
    (initialConfiguration (Rewind.machine SortCarrier.machine)
      (Fin.addCases (motive := fun _ : Fin (6+1) => List Bool)
        (SourceHandoff.sourceTapes (t := 6) (StablePartition.stream req.records)) (fun _ : Fin 1 => []))))

theorem joined_run {U Used Capacity : ℕ} (M : ℕ) (payload : Fin Used → Fin (U+U) → Bool)
    (hcap : Used ≤ Capacity) (req : SortCarrier.Request)
    (hgrid : SortCarrier.sorted req=grid M M payload) (out : List Bool) :
    ∃ actual : ExecutionReceipt 11 (88+planeStates),
      runFrom machine (2*SortCarrier.budget req.records+3+MatrixRightGrid.budget M U Used Capacity)
        (input req out U Used ((Capacity-Used)*U))=some actual ∧
      actual.final.tapes 7=out++rowMajorBitMatrix (padBooleanInner (Capacity := Capacity) (MatrixRightGrid.right payload)) ∧
      actual.final.heads 7=(out++rowMajorBitMatrix (padBooleanInner (Capacity := Capacity) (MatrixRightGrid.right payload))).length ∧
      actual.steps ≤ 2*SortCarrier.budget req.records+3+MatrixRightGrid.budget M U Used Capacity := by
  let pad := (Capacity-Used)*U
  let extras := ![out,UnaryTemplate.tape U,CompareMachine.word Used,UnaryTemplate.tape pad]
  let heads := ![out.length,1,1,1]
  obtain ⟨source,_,_,hsource,hout,hsteps,_⟩ := Classical.choose_spec (SortCarrier.raw_sort req.records req.uniform)
  have hout' : source.final.tapes 0=StablePartition.stream (grid M M payload) := by
    change source.final.tapes 0=StablePartition.stream (SortCarrier.sorted req) at hout
    rw [hgrid] at hout
    exact hout
  obtain ⟨reset,hreset,hresetOut,hresetHeads,hresetSteps,_⟩ :=
    Rewind.reset_run SortCarrier.machine (SortCarrier.budget req.records) _ source hsource
  have hfirst := TapeEmbedding.run_embed (Rewind.machine SortCarrier.machine) heads extras _ _ reset hreset
  let first := TapeEmbedding.receipt heads extras reset
  obtain ⟨selected,hselected,hselectedFinal,hselectedSteps⟩ := MatrixRightGrid.plane_run M payload hcap [] [false] out
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hselected hselectedFinal
  let retained : Fin 6 → List Bool := fun i => reset.final.tapes i.succ
  have he := TapeEmbedding.run_embed MatrixRightPadding.machine (fun _ : Fin 6 => 0) retained _ _ selected hselected
  have hsecond := TapeRenaming.run_rename SortRank.rankLayout (TapeEmbedding.machine 6 MatrixRightPadding.machine) _ _ _ he
  let second := TapeRenaming.receipt SortRank.rankLayout (TapeEmbedding.receipt (fun _ : Fin 6 => 0) retained selected)
  have hmid : Composition.restart first.final planeMachine.start=
      TapeRenaming.config SortRank.rankLayout (TapeEmbedding.config (fun _ : Fin 6 => 0) retained
        (MatrixRightPadding.cfg MatrixRightPadding.machine.start (StablePartition.stream (grid M M payload))
          0 out U Used pad)) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [Composition.restart,first,TapeEmbedding.receipt,TapeEmbedding.config,
        TapeRenaming.config,MatrixRightPadding.cfg,Fin.addCases,hresetHeads,heads]
    · have hzero := (hresetOut (0 : Fin 6)).trans hout'
      change reset.final.tapes 0=StablePartition.stream (grid M M payload) at hzero
      funext i
      fin_cases i <;> simp [Composition.restart,first,TapeEmbedding.receipt,TapeEmbedding.config,
        TapeRenaming.config,MatrixRightPadding.cfg,Fin.addCases,retained,extras,hzero]
  have hnext : runFrom planeMachine (MatrixRightGrid.budget M U Used Capacity)
      (Composition.restart first.final planeMachine.start)=some second := by
    rw [hmid]
    exact hsecond
  have hj := Composition.run_join sortMachine planeMachine (2*source.steps+2)
    (MatrixRightGrid.budget M U Used Capacity) _ first second hfirst hnext
  have hb : (2*source.steps+2)+1+MatrixRightGrid.budget M U Used Capacity ≤
      2*SortCarrier.budget req.records+3+MatrixRightGrid.budget M U Used Capacity := by omega
  have hm := runFrom_moreFuel machine ((2*source.steps+2)+1+MatrixRightGrid.budget M U Used Capacity)
    ((2*SortCarrier.budget req.records+3+MatrixRightGrid.budget M U Used Capacity)-
      ((2*source.steps+2)+1+MatrixRightGrid.budget M U Used Capacity)) _ _ hj
  rw [Nat.add_sub_of_le hb] at hm
  refine ⟨Composition.joinedReceipt first second,hm,?_,?_,?_⟩
  · change (TapeRenaming.config SortRank.rankLayout
      (TapeEmbedding.config (fun _ : Fin 6 => 0) retained selected.final)).tapes 7=_
    rw [hselectedFinal]
    simp [TapeRenaming.config,TapeEmbedding.config,MatrixRightPadding.cfg,Fin.addCases]
  · change (TapeRenaming.config SortRank.rankLayout
      (TapeEmbedding.config (fun _ : Fin 6 => 0) retained selected.final)).heads 7=_
    rw [hselectedFinal]
    simp [TapeRenaming.config,TapeEmbedding.config,MatrixRightPadding.cfg,Fin.addCases]
  · change reset.steps+1+selected.steps ≤ _
    rw [hresetSteps]
    omega

end NearCubicWires.RepairOrdinary.MatrixRightSort
