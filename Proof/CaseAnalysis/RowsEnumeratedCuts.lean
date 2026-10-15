import Proof.Supplier.RowTupleCutList

/-! The actual binary subset producer hands its rewound tuple stream to the
complete signed-cut consumer. One coefficient is retained for the whole
degree; coordinates and threshold are followed by that coefficient. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEnumeratedCuts
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def enumSlots : Fin 41 → Fin 89 :=
  ![49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,44,66,67,68,
    69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88]
def rowSlots (i : Fin 49) : Fin 89 := i.castAdd 40
theorem enum_injective : Function.Injective enumSlots := by decide
theorem row_injective : Function.Injective rowSlots := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 89 => k.val) h)
noncomputable def first := RecoveryFocus.machine enumSlots RowTupleEnumerationReady.machine
noncomputable def last := RecoveryFocus.machine rowSlots RowTupleCutList.machine
noncomputable def machine := Composition.machine first last

def core {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n))
    (p F w k : ℕ) (rows : List (List Bool)) (tuple : List Bool)
    (pos : ℕ) (out : List Bool) (bound : ℕ) (coefficient : ℤ) : Configuration 49 s :=
  ⟨q,Fin.addCases (m:=48) (n:=1) (motive:=fun _ => ℕ)
      (RowTupleCursorLayout.heads pos out) (fun _ : Fin 1 => 0),
    Fin.addCases (m:=48) (n:=1) (motive:=fun _ => List Bool)
      (fun i => ZeroPadding.pad (RowTupleCursorBody.padding F i)
        (RowTupleCursorLayout.data gs 0 p F w rows.length k rows tuple out bound [] i))
      (fun _ : Fin 1 => frame (MatrixScoreBatch.signMagnitude p coefficient))⟩

theorem cfg_eq {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n))
    (p F w k : ℕ) (rows : List (List Bool)) (tuple : List Bool)
    (pos : ℕ) (out : List Bool) (bound : ℕ) (coefficient : ℤ) :
    RowTupleCutList.cfg q gs p F w rows.length k rows tuple pos out bound coefficient=
      core q gs p F w k rows tuple pos out bound coefficient := by
  simp only [RowTupleCutList.cfg,RowTupleCutBody.entry,RowTupleList.cfg,
    RowTupleFramedBody.entry,RowTupleCursorBody.entry,Composition.restart,TapeEmbedding.config,core]

theorem core_fields {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n))
    (p F w k : ℕ) (rows : List (List Bool)) (tuple : List Bool)
    (pos : ℕ) (out : List Bool) (bound : ℕ) (coefficient : ℤ) :
    (core q gs p F w k rows tuple pos out bound coefficient).tapes 44=tuple ∧
      (core q gs p F w k rows tuple pos out bound coefficient).heads 44=pos := by
  have h := RowTupleCutList.fields q gs p F w rows.length k rows tuple pos out bound coefficient
  simpa only [cfg_eq] using And.intro h.1 h.2.1

noncomputable def input {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n))
    (p F w k : ℕ) (rows : List (List Bool)) (out : List Bool) (coefficient : ℤ) :=
  TapeEmbedding.config (fun _ : Fin 40 => 0)
    (RowTupleEnumeratedEquations.extra w k rows.length)
    (core q gs p F w k rows [] 0 out 0 coefficient)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w k : ℕ)
    (rows : List (List Bool)) :=
  RowTupleEnumerationReady.budget w k+1+
    RowTupleCutList.budget gs p F w rows.length rows (RowTupleSubsets.selected w rows.length k)
noncomputable def finished {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n))
    (p F w k : ℕ) (rows : List (List Bool)) (out : List Bool) (coefficient : ℤ) :=
  let xs := RowTupleSubsets.selected w rows.length k
  core q gs p F w k rows
    (RowTupleEnumeration.word w k rows.length) (RowTupleEnumeration.word w k rows.length).length
    (out++RowTupleCutList.output gs p rows xs coefficient)
    (RowTupleCutList.finalBound rows xs 0) coefficient

theorem enum_pick (i : Fin 49) : RecoveryFocus.pick enumSlots (rowSlots i)=
    if i=44 then some 17 else none := by
  fin_cases i
  all_goals first | exact RecoveryFocus.pick_slot enumSlots enum_injective 17 | decide

private theorem vector_away {α : Type} (a b c d e f g h x y i j k : α)
    (ix : Fin 12) (hi : ix.val≠8) :
    (![a,b,c,d,e,f,g,h,x,i,j,k] : Fin 12 → α) ix=![a,b,c,d,e,f,g,h,y,i,j,k] ix := by
  fin_cases ix <;> simp_all

private theorem data_away {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w k : ℕ)
    (rows : List (List Bool)) (left right out : List Bool) (i : Fin 48) (hi : i≠44) :
    RowTupleCursorLayout.data gs 0 p F w rows.length k rows left out 0 [] i=
      RowTupleCursorLayout.data gs 0 p F w rows.length k rows right out 0 [] i := by
  revert hi
  refine Fin.addCases (m:=36) (n:=12) (fun j => ?_) (fun j => ?_) i
  · intro _
    simp only [RowTupleCursorLayout.data,Fin.addCases_left]
  · intro hi
    simp only [RowTupleCursorLayout.data,Fin.addCases_right]
    apply vector_away
    intro hj
    apply hi
    apply Fin.ext
    simpa only [Fin.val_natAdd,hj] using (show 36+8=(44 : Fin 48).val from rfl)

private theorem input_away {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n))
    (p F w k : ℕ) (rows : List (List Bool)) (left right out : List Bool)
    (coefficient : ℤ) (i : Fin 49) (hi : i≠44) :
    (core q gs p F w k rows left 0 out 0 coefficient).tapes i=
      (core q gs p F w k rows right 0 out 0 coefficient).tapes i := by
  revert hi
  refine Fin.addCases (m:=48) (n:=1) (fun j => ?_) (fun j => ?_) i
  · intro hi
    simp only [core,Fin.addCases_left]
    apply congrArg
    exact data_away gs p F w k rows left right out j (fun h => hi (by subst j; rfl))
  · intro _
    simp only [core,Fin.addCases_right]

theorem cuts_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w k : ℕ)
    (rows : List (List Bool)) (out : List Bool) (coefficient : ℤ)
    (hl : ∀ row∈rows, row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hk : k≤Q)
    (hp : RowTupleFixedCapacity.width gs Q≤p)
    (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ actual, runFrom machine (budget gs p F w k rows)
      (input machine.start gs p F w k rows out coefficient)=some actual ∧
      (∀ i, actual.final.heads (rowSlots i)=
        (finished machine.start gs p F w k rows out coefficient).heads i) ∧
      (∀ i, actual.final.tapes (rowSlots i)=
        (finished machine.start gs p F w k rows out coefficient).tapes i) ∧
      actual.steps≤budget gs p F w k rows := by
  obtain ⟨base,hbase,bt,bh,_⟩ := RowTupleEnumerationReady.enumerate_run w k rows.length hM hw.le
  let ambient := input first.start gs p F w k rows out coefficient
  obtain ⟨a,ha,af,_⟩ := RecoveryFocus.run_config enumSlots enum_injective
    RowTupleEnumerationReady.machine ambient.heads ambient.tapes _ _ base hbase
  have hi : RecoveryFocus.config enumSlots ambient.heads ambient.tapes
      (initialConfiguration RowTupleEnumerationReady.machine (RowTupleEnumerationReady.input w k rows.length))=ambient := by
    apply WilliamsSourceCrop.focus_same
    · intro i; fin_cases i <;> rfl
    · intro i; fin_cases i <;> rfl
  rw [hi] at ha
  obtain ⟨row,hr,rh,rt,_⟩ := RowTupleCutList.list_run gs p F Q w rows.length k rows
    (RowTupleSubsets.selected w rows.length k) [] out 0 coefficient hl
    (fun ds hd => (RowTupleSelectedList.selected_fields w rows.length k ds hd).1)
    (fun ds hd => (RowTupleSelectedList.selected_fields w rows.length k ds hd).2)
    hw le_rfl hk hp hF
  have hstream : RowTupleCutList.stream w (RowTupleSubsets.selected w rows.length k)=
      RowTupleEnumeration.word w k rows.length := RowTupleSelectedList.stream_eq w rows.length k
  simp only [List.nil_append,List.length_nil,Nat.zero_add,hstream,cfg_eq] at hr rh rt
  obtain ⟨b,hb,bf,_⟩ := RecoveryFocus.run_config rowSlots row_injective RowTupleCutList.machine
    a.final.heads a.final.tapes _ _ row hr
  have hj : RecoveryFocus.config rowSlots a.final.heads a.final.tapes
      (core RowTupleCutList.machine.start gs p F w k rows
        (RowTupleEnumeration.word w k rows.length) 0 out 0 coefficient)=
      Composition.restart a.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [af]
      simp only [RecoveryFocus.config,enum_pick]
      by_cases h44 : i=44
      · subst i
        simp only [ite_true,bh]
        exact (core_fields RowTupleCutList.machine.start gs p F w k rows _ 0 out 0 coefficient).2.symm
      · simp only [h44,ite_false,ambient,input,TapeEmbedding.config,rowSlots,Fin.addCases_left]
        rfl
    · intro i
      rw [af]
      simp only [RecoveryFocus.config,enum_pick]
      by_cases h44 : i=44
      · subst i
        simp only [ite_true,bt]
        exact (core_fields RowTupleCutList.machine.start gs p F w k rows _ 0 out 0 coefficient).1.symm
      · simp only [h44,ite_false,ambient,input,TapeEmbedding.config,rowSlots,Fin.addCases_left]
        exact input_away RowTupleCutList.machine.start gs p F w k rows [] _ out coefficient i h44
  rw [hj] at hb
  have whole := Composition.run_join first last _ _ _ a b ha hb
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,runFrom_steps_le machine _ _ _ whole⟩
  · intro i
    change b.final.heads (rowSlots i)=_
    rw [bf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot _ row_injective,finished,core] using congrFun rh i
  · intro i
    change b.final.tapes (rowSlots i)=_
    rw [bf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot _ row_injective,finished,core] using congrFun rt i

end NearCubicWires.RepairOrdinary.CloseoutRowsEnumeratedCuts
