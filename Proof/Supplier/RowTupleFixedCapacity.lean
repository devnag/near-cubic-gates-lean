import Proof.Supplier.RowCommonFixedCapacity

/-! The actual tuple-to-equation caller uses one common width and one
source-sized allocation for every tuple up to degree Q. Per-tuple width and
allocation conditions are discharged by the computed occurrence-count bound. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFixedCapacity
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ) :=
  RowCachedCoordinateBounds.width gs*(gs.length*Q)
noncomputable def common {n : ℕ} (gs : List (ExactThresholdGate n)) (p F : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool) :=
  RowCommonFixedCapacity.cfg gs p F (indices gs.length rows ds) 0 0 1 [] out
noncomputable def ambient {n : ℕ} (gs : List (ExactThresholdGate n)) (p F : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool) :=
  TapeEmbedding.config (fun _ : Fin 12=>0) (fun _=>[]) (common gs p F rows ds out)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool) :=
  Composition.restart (RecoveryFocus.config tupleSlots (ambient gs p F rows ds out).heads
    (ambient gs p F rows ds out).tapes
    (Composition.restart (RowTupleMaskReady.input gs.length w M rows ds tail) RowTupleMaskReady.machine.start)) machine.start
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

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p F Q w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) (hQ : ds.length≤Q)
    (hp : width gs Q≤p) (hF : RowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (budget gs F w M rows ds) (input gs p F w M rows ds tail out)=some r ∧
      r.final.tapes 31=out++RowCoordinateLoop.equationWord p
        (RowCoordinateLoop.equation gs (indices gs.length rows ds)) ∧
      r.final.heads 31=(out++RowCoordinateLoop.equationWord p
        (RowCoordinateLoop.equation gs (indices gs.length rows ds))).length ∧
      r.steps≤budget gs F w M rows ds := by
  have hcap := RowCommonFixedCapacity.tuple_capacity gs p F Q rows ds hl hd hQ hF
  have hwidth : RowCoordinateLoop.width gs (indices gs.length rows ds)≤p := by
    have hc := (RowTupleEquationBounds.count_le gs.length rows ds hl hd).trans (Nat.mul_le_mul_left gs.length hQ)
    have hm := Nat.mul_le_mul_left (RowCachedCoordinateBounds.width gs) hc
    unfold RowCoordinateLoop.width
    rw [(index_fields gs.length rows ds hl hd).2]
    exact hm.trans hp
  obtain ⟨tuple,ht,t2,t3,h2,h3,_⟩ := RowTupleMaskReady.tuple_run gs.length w M rows ds tail hl hd hb hM
  obtain ⟨a,ha,af,_⟩ := RecoveryFocus.run_config tupleSlots tuple_injective RowTupleMaskReady.machine
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
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,runFrom_steps_le machine _ _ _ whole⟩
  · change b.final.tapes (rowSlots 31)=_
    rw [bf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective]
    rw [rf]
    change (RowCommonClear.entry gs (n+1) p F [] _ (indices gs.length rows ds)).tapes 31=_
    rw [RowCommonReusable.entry_tapes gs (n+1) p F [] _ (indices gs.length rows ds)
      (by have := RowCommonBounds.padding_fits gs (indices gs.length rows ds).length p; omega)
      ((RowCommonBounds.inner_fits gs (indices gs.length rows ds).length p).trans hcap)]
    rfl
  · change b.final.heads (rowSlots 31)=_
    rw [bf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective]
    rw [rf]
    rfl

end NearCubicWires.RepairOrdinary.RowTupleFixedCapacity
