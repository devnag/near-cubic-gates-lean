import Proof.Supplier.RowTupleEnumerationReady
import Proof.Supplier.RowTupleSelectedList

/-! The actual binary producer, paid output rewind, and complete selected
list consumer share one tuple tape. No tuple bytes or unary tuple count
are supplied at input. Native cache and common metadata remain retained. -/
namespace NearCubicWires.RepairOrdinary.RowTupleEnumeratedEquations
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def enumSlots : Fin 41→Fin 88 := ![48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,44,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87]
def rowSlots (i : Fin 48) : Fin 88 := i.castAdd 40
theorem enum_injective : Function.Injective enumSlots := by decide
theorem row_injective : Function.Injective rowSlots := by
  intro i j h; exact Fin.ext (congrArg (fun k : Fin 88=>k.val) h)
noncomputable def first := RecoveryFocus.machine enumSlots RowTupleEnumerationReady.machine
noncomputable def last := RecoveryFocus.machine rowSlots RowTupleList.machine
noncomputable def machine := Composition.machine first last

def extra (w k M : ℕ) : Fin 40→List Bool := fun i=>
  if i=2 then CompareMachine.word w else if i=3 then frame (SignedSortKey.binary w (M-1))
    else if i=12 then CompareMachine.word k else if i=17 then List.replicate w true else []
noncomputable def input {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) (p F w k : ℕ)
    (rows : List (List Bool)) (out : List Bool) :=
  TapeEmbedding.config (fun _ : Fin 40=>0) (extra w k rows.length)
    (RowTupleList.cfg q gs p F w rows.length k rows [] 0 out 0)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (F w k : ℕ) (rows : List (List Bool)) :=
  RowTupleEnumerationReady.budget w k+1+
    RowTupleList.budget gs F w rows.length rows (RowTupleSubsets.selected w rows.length k)

theorem enum_pick (i : Fin 48) : RecoveryFocus.pick enumSlots (rowSlots i)=
    if i=44 then some 17 else none := by
  fin_cases i
  all_goals first | exact RecoveryFocus.pick_slot enumSlots enum_injective 17 | decide

private theorem core_heads {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) (p F w k : ℕ)
    (rows : List (List Bool)) (tuple out : List Bool) :
    (RowTupleList.cfg q gs p F w rows.length k rows tuple 0 out 0).heads=RowTupleCursorLayout.heads 0 out := by rfl
private theorem core_tapes {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) (p F w k : ℕ)
    (rows : List (List Bool)) (tuple out : List Bool) :
    (RowTupleList.cfg q gs p F w rows.length k rows tuple 0 out 0).tapes=
      fun i=>ZeroPadding.pad (RowTupleCursorBody.padding F i)
        (RowTupleCursorLayout.data gs 0 p F w rows.length k rows tuple out 0 [] i) := by rfl
private theorem vector_away {α : Type} (a b c d e f g h x y i j k : α) (ix : Fin 12) (hi:ix.val≠8) :
    (![a,b,c,d,e,f,g,h,x,i,j,k] : Fin 12→α) ix=![a,b,c,d,e,f,g,h,y,i,j,k] ix := by
  fin_cases ix <;> simp_all
private theorem data_away {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w k : ℕ)
    (rows : List (List Bool)) (left right out : List Bool) (i : Fin 48) (hi:i≠44) :
    RowTupleCursorLayout.data gs 0 p F w rows.length k rows left out 0 [] i=
      RowTupleCursorLayout.data gs 0 p F w rows.length k rows right out 0 [] i := by
  revert hi
  refine Fin.addCases (m:=36) (n:=12) (fun j=>?_) (fun j=>?_) i
  · intro _
    simp only [RowTupleCursorLayout.data,Fin.addCases_left]
  · intro hi
    simp only [RowTupleCursorLayout.data,Fin.addCases_right]
    apply vector_away
    intro hj
    apply hi
    apply Fin.ext
    simpa only [Fin.val_natAdd,hj] using (show 36+8=(44:Fin 48).val from rfl)

theorem equation_list_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w k : ℕ)
    (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM:0<rows.length) (hw:rows.length<2^w) (hk:k≤Q)
    (hp : RowTupleFixedCapacity.width gs Q≤p) (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (budget gs F w k rows) (input machine.start gs p F w k rows out)=some r ∧
      r.final.tapes (rowSlots 31)=out++RowTupleList.output gs p rows (RowTupleSubsets.selected w rows.length k) ∧
      r.final.heads (rowSlots 31)=(out++RowTupleList.output gs p rows (RowTupleSubsets.selected w rows.length k)).length ∧
      r.steps≤budget gs F w k rows := by
  obtain ⟨base,hbase,bt,bh,_⟩:=RowTupleEnumerationReady.enumerate_run w k rows.length hM hw.le
  let ambient:=input first.start gs p F w k rows out
  obtain ⟨a,ha,af,_⟩:=RecoveryFocus.run_config enumSlots enum_injective RowTupleEnumerationReady.machine
    ambient.heads ambient.tapes _ _ base hbase
  have hi : RecoveryFocus.config enumSlots ambient.heads ambient.tapes
      (initialConfiguration RowTupleEnumerationReady.machine (RowTupleEnumerationReady.input w k rows.length))=ambient := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  rw [hi] at ha
  obtain ⟨row,hr,rt,rh,_⟩:=RowTupleSelectedList.selected_run gs p F Q w k rows out hl hw hk hp hF
  obtain ⟨b,hbRun,bf,_⟩:=RecoveryFocus.run_config rowSlots row_injective RowTupleList.machine
    a.final.heads a.final.tapes _ _ row hr
  have hj : RecoveryFocus.config rowSlots a.final.heads a.final.tapes
      (RowTupleList.cfg RowTupleList.machine.start gs p F w rows.length k rows
        (RowTupleEnumeration.word w k rows.length) 0 out 0)=Composition.restart a.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [af]
      simp only [RecoveryFocus.config,enum_pick]
      by_cases h44:i=44
      · subst i
        simp only [ite_true,bh]
        exact (RowTupleList.fields RowTupleList.machine.start gs p F w rows.length k rows _ 0 out 0).2.1.symm
      · simp only [h44,ite_false,ambient,input,TapeEmbedding.config,rowSlots,Fin.addCases_left,core_heads]
    · intro i
      rw [af]
      simp only [RecoveryFocus.config,enum_pick]
      by_cases h44:i=44
      · subst i
        simp only [ite_true,bt]
        exact (RowTupleList.fields RowTupleList.machine.start gs p F w rows.length k rows _ 0 out 0).1.symm
      · simp only [h44,ite_false,ambient,input,TapeEmbedding.config,rowSlots,Fin.addCases_left,core_tapes]
        exact congrArg (ZeroPadding.pad (RowTupleCursorBody.padding F i)) (data_away gs p F w k rows [] _ out i h44)
  rw [hj] at hbRun
  have whole:=Composition.run_join first last _ _ _ a b ha hbRun
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,runFrom_steps_le machine _ _ _ whole⟩
  · change b.final.tapes (rowSlots 31)=_
    rw [bf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective] using rt
  · change b.final.heads (rowSlots 31)=_
    rw [bf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective] using rh

end NearCubicWires.RepairOrdinary.RowTupleEnumeratedEquations
