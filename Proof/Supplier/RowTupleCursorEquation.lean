import Proof.Supplier.RowTupleFixedCapacity
import Proof.Supplier.RowTupleCursorReady

/-! The complete equation body consumes one tuple at its retained stream
cursor. Its exact final configuration exposes the ports needed to clear
only the per-tuple data before the next selected tuple. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCursorEquation
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := RecoveryFocus.machine tupleSlots RowTupleCursorReady.machine
noncomputable def last := RecoveryFocus.machine rowSlots RowCommonCoordinateLoop.machine
noncomputable def machine := Composition.machine first last
abbrev width := @RowTupleFixedCapacity.width
noncomputable def common {n : ℕ} (gs : List (ExactThresholdGate n)) (p F : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool) :=
  RowCommonFixedCapacity.cfg gs p F (indices gs.length rows ds) 0 0 1 [] out
noncomputable def ambient {n : ℕ} (gs : List (ExactThresholdGate n)) (p F : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool) :=
  TapeEmbedding.config (fun _ : Fin 12=>0) (fun _=>[]) (common gs p F rows ds out)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ) :=
  Composition.restart (RecoveryFocus.config tupleSlots (ambient gs p F rows ds out).heads
    (ambient gs p F rows ds out).tapes
    (Composition.restart (RowTupleCursorReady.input gs.length w M rows ds pre tail bound) RowTupleCursorReady.machine.start)) machine.start
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) :=
  RowTupleMaskReady.budget gs.length w M ds.length (RowTupleMaskLoop.count rows ds)+1+
    RowCommonFixedCapacity.budget n F

theorem shared_fields {n : ℕ} (gs : List (ExactThresholdGate n)) (p F : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hF : RowCommonBounds.capacity gs (indices gs.length rows ds).length p≤F) :
    (common gs p F rows ds out).tapes 23=RowTupleMaskLoop.word rows ds ∧
      (common gs p F rows ds out).tapes 24=CompareMachine.word (RowTupleMaskLoop.count rows ds) := by
  have hf := index_fields gs.length rows ds hl hd
  have data := RowCommonReusable.entry_tapes gs 0 p F [] out (indices gs.length rows ds)
    (by have := RowCommonBounds.padding_fits gs (indices gs.length rows ds).length p; omega)
    ((RowCommonBounds.inner_fits gs (indices gs.length rows ds).length p).trans hF)
  constructor
  · change (RowCommonClear.entry gs 0 p F [] out (indices gs.length rows ds)).tapes 23=_
    rw [data]
    simpa [RowCommonReusable.data] using hf.1
  · change (RowCommonClear.entry gs 0 p F [] out (indices gs.length rows ds)).tapes 24=_
    rw [data]
    change CompareMachine.word (indices gs.length rows ds).length=_
    rw [hf.2]

noncomputable def middle {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ) :=
  RecoveryFocus.config tupleSlots (ambient gs p F rows ds out).heads
    (ambient gs p F rows ds out).tapes
    (⟨RowTupleCursorReady.machine.start,
      Function.update (RowTupleCursorReady.middleHeads gs.length w M rows ds pre tail bound) 3 1,
      RowTupleCursorReady.output gs.length w M rows ds pre tail bound⟩ : Configuration 14 _)
noncomputable def result {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ) :=
  let mid:=middle gs p F w M rows ds pre tail out bound
  RecoveryFocus.config rowSlots mid.heads mid.tapes
    (RowCommonFixedCapacity.cfg gs p F (indices gs.length rows ds) 3 (n+1) 1 []
      (out++RowCoordinateLoop.equationWord p (RowCoordinateLoop.equation gs (indices gs.length rows ds))))

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) (hQ : ds.length≤Q)
    (hp : width gs Q≤p) (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (budget gs F w M rows ds) (input gs p F w M rows ds pre tail out bound)=some r ∧
      r.final.heads=(result gs p F w M rows ds pre tail out bound).heads ∧
      r.final.tapes=(result gs p F w M rows ds pre tail out bound).tapes ∧
      r.steps≤budget gs F w M rows ds := by
  have hcap := RowCommonFixedCapacity.tuple_capacity gs p F Q rows ds hl hd hQ hF
  have hwidth : RowCoordinateLoop.width gs (indices gs.length rows ds)≤p := by
    have hc := (RowTupleEquationBounds.count_le gs.length rows ds hl hd).trans (Nat.mul_le_mul_left gs.length hQ)
    have hm := Nat.mul_le_mul_left (RowCachedCoordinateBounds.width gs) hc
    unfold RowCoordinateLoop.width
    rw [(index_fields gs.length rows ds hl hd).2]
    exact hm.trans hp
  obtain ⟨tuple,ht,th,tt,_⟩ := RowTupleCursorReady.tuple_run gs.length w M rows ds pre tail bound hl hd hb hM
  have tf:=RowTupleCursorReady.output_fields gs.length w M rows ds pre tail bound
  have t2 : tuple.final.tapes 2=RowTupleMaskLoop.word rows ds := by rw [tt]; exact tf.1
  have t3 : tuple.final.tapes 3=CompareMachine.word (RowTupleMaskLoop.count rows ds) := by rw [tt]; exact tf.2.1
  have h2 : tuple.final.heads 2=0 := by rw [th]; simpa using tf.2.2.1
  have h3 : tuple.final.heads 3=1 := by rw [th]; simp
  obtain ⟨a,ha,af,_⟩ := RecoveryFocus.run_config tupleSlots tuple_injective RowTupleCursorReady.machine
    (ambient gs p F rows ds out).heads (ambient gs p F rows ds out).tapes _ _ tuple ht
  obtain ⟨row,hr,rf,_⟩ := RowCommonFixedCapacity.equation_run gs p F (indices gs.length rows ds) [] out hwidth hcap
  obtain ⟨b,hbRun,bf,_⟩ := RecoveryFocus.run_config rowSlots row_injective RowCommonCoordinateLoop.machine
    a.final.heads a.final.tapes _ _ row hr
  have hs := shared_fields gs p F rows ds out hl hd hcap
  have he : RecoveryFocus.config rowSlots a.final.heads a.final.tapes (common gs p F rows ds out)=
      Composition.restart a.final last.start := by
    apply WilliamsSourceCrop.focus_same rowSlots (Composition.restart a.final last.start)
    · intro i
      change a.final.heads (rowSlots i)=(common gs p F rows ds out).heads i
      rw [af]
      simp only [RecoveryFocus.config,tuple_pick_core]
      by_cases h23 : i=23
      · subst i; simp only [ite_true,h2]; rfl
      by_cases h24 : i=24
      · subst i
        simp only [show (24 : Fin 36)≠23 by decide,ite_false,ite_true]
        rw [h3]; rfl
      simp only [h23,h24,ite_false]
      simp [ambient,TapeEmbedding.config,rowSlots]
    · intro i
      change a.final.tapes (rowSlots i)=(common gs p F rows ds out).tapes i
      rw [af]
      simp only [RecoveryFocus.config,tuple_pick_core]
      by_cases h23 : i=23
      · subst i; simp only [ite_true]; exact t2.trans hs.1.symm
      by_cases h24 : i=24
      · subst i; simp only [show (24 : Fin 36)≠23 by decide,ite_false,ite_true]; exact t3.trans hs.2.symm
      simp only [h23,h24,ite_false]
      simp [ambient,TapeEmbedding.config,rowSlots]
  change runFrom last _ (RecoveryFocus.config rowSlots a.final.heads a.final.tapes
    (common gs p F rows ds out))=some b at hbRun
  rw [he] at hbRun
  have whole := Composition.run_join first last _ _ _ a b ha hbRun
  have amidh : a.final.heads=(middle gs p F w M rows ds pre tail out bound).heads := by
    rw [af]
    simp only [middle,RecoveryFocus.config,th]
  have amidt : a.final.tapes=(middle gs p F w M rows ds pre tail out bound).tapes := by
    rw [af]
    simp only [middle,RecoveryFocus.config,tt]
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,runFrom_steps_le machine _ _ _ whole⟩
  · change b.final.heads=_
    rw [bf,rf]
    simp only [result,RecoveryFocus.config,amidh]
  · change b.final.tapes=_
    rw [bf,rf]
    simp only [result,RecoveryFocus.config,amidt]

end NearCubicWires.RepairOrdinary.RowTupleCursorEquation
