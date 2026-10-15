import Proof.Supplier.RowCommonCoordinateLoop
import Proof.Supplier.RowTupleMaskReady

/-! A whole selected tuple now reaches the complete common-width equation
emitter through shared physical occurrence/count tapes. The ordered native
positions come from executed cache lookups, including all repetitions. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCommonEquation
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def one (N : ℕ) (bits : List Bool) : List (Fin N) :=
  if h : bits.length≤N then RowMaskMeaning.typed N 0 bits (by omega) else []
def indices (N : ℕ) (rows : List (List Bool)) (ds : List ℕ) : List (Fin N) :=
  ds.flatMap fun d=>one N (RowTupleMaskLoop.mask rows d)
theorem mask_length (N : ℕ) (rows : List (List Bool)) (d : ℕ)
    (hl : ∀ row∈rows,row.length=N) (hd : d<rows.length) : (RowTupleMaskLoop.mask rows d).length=N := by
  simp only [RowTupleMaskLoop.mask,List.getElem?_eq_getElem hd,Option.getD_some]
  exact hl _ (List.getElem_mem hd)
theorem index_fields (N : ℕ) (rows : List (List Bool)) (ds : List ℕ)
    (hl : ∀ row∈rows,row.length=N) (hd : ∀ d∈ds,d<rows.length) :
    RowOccurrenceLoop.word (indices N rows ds)=RowTupleMaskLoop.word rows ds ∧
      (indices N rows ds).length=RowTupleMaskLoop.count rows ds := by
  induction ds with
  | nil => simp [indices,RowOccurrenceLoop.word,RowTupleMaskLoop.word,RowTupleMaskLoop.count]
  | cons d ds ih =>
    have hlen := mask_length N rows d hl (hd d (by simp))
    obtain ⟨hw,hc⟩ := ih (fun a ha=>hd a (List.mem_cons_of_mem d ha))
    have hone : one N (RowTupleMaskLoop.mask rows d)=RowMaskMeaning.typed N 0 (RowTupleMaskLoop.mask rows d) (by omega) := by
      simp only [one,dif_pos (show (RowTupleMaskLoop.mask rows d).length≤N by omega)]
    have ow := RowMaskMeaning.typed_word N 0 (RowTupleMaskLoop.mask rows d) (by omega)
    have oc := RowMaskMeaning.typed_length N 0 (RowTupleMaskLoop.mask rows d) (by omega)
    constructor
    · change RowOccurrenceLoop.word (one N (RowTupleMaskLoop.mask rows d)++indices N rows ds)=_
      rw [show RowOccurrenceLoop.word (one N (RowTupleMaskLoop.mask rows d)++indices N rows ds)=
        RowOccurrenceLoop.word (one N (RowTupleMaskLoop.mask rows d))++RowOccurrenceLoop.word (indices N rows ds) by
          simp only [RowOccurrenceLoop.word,List.flatMap_append],hone,←ow,hw]
      rfl
    · change (one N (RowTupleMaskLoop.mask rows d)++indices N rows ds).length=_
      rw [List.length_append,hone,oc,hc]
      rfl

def tupleSlots : Fin 14→Fin 48 := ![36,37,23,24,38,39,40,41,42,43,44,45,46,47]
theorem tuple_injective : Function.Injective tupleSlots := by decide
def rowSlots (i : Fin 36) : Fin 48 := i.castAdd 12
theorem row_injective : Function.Injective rowSlots := by
  intro i j h; exact Fin.ext (congrArg (fun a : Fin 48=>a.val) h)
noncomputable def first := RecoveryFocus.machine tupleSlots RowTupleMaskReady.machine
noncomputable def last := RecoveryFocus.machine rowSlots RowCommonCoordinateLoop.machine
noncomputable def machine := Composition.machine first last
noncomputable def common {n : ℕ} (gs : List (ExactThresholdGate n)) (p : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool) :=
  RowCommonCoordinateLoop.cfg gs p (indices gs.length rows ds) 0 0 1 [] out
noncomputable def ambient {n : ℕ} (gs : List (ExactThresholdGate n)) (p : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool) :=
  TapeEmbedding.config (fun _ : Fin 12=>0) (fun _=>[]) (common gs p rows ds out)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) (p w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool) :=
  Composition.restart (RecoveryFocus.config tupleSlots (ambient gs p rows ds out).heads
    (ambient gs p rows ds out).tapes
    (Composition.restart (RowTupleMaskReady.input gs.length w M rows ds tail) RowTupleMaskReady.machine.start)) machine.start
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (p w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) :=
  RowTupleMaskReady.budget gs.length w M ds.length (RowTupleMaskLoop.count rows ds)+1+
    RowCommonCoordinateLoop.budget gs p (indices gs.length rows ds)

theorem tuple_pick_core (i : Fin 36) : RecoveryFocus.pick tupleSlots (rowSlots i)=
    (if i=23 then some 2 else if i=24 then some 3 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 2
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 3
    | decide

theorem shared_fields {n : ℕ} (gs : List (ExactThresholdGate n)) (p : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length) :
    (common gs p rows ds out).tapes 23=RowTupleMaskLoop.word rows ds ∧
      (common gs p rows ds out).tapes 24=CompareMachine.word (RowTupleMaskLoop.count rows ds) := by
  have hf := index_fields gs.length rows ds hl hd
  have data := RowCommonReusable.entry_tapes gs 0 p (RowCommonBounds.capacity gs (indices gs.length rows ds).length p)
    [] out (indices gs.length rows ds) (by unfold RowCommonBounds.capacity; omega)
    (RowCommonBounds.inner_fits gs _ p)
  constructor
  · change (RowCommonClear.entry gs 0 p (RowCommonBounds.capacity gs (indices gs.length rows ds).length p)
      [] out (indices gs.length rows ds)).tapes 23=_
    rw [data]
    simpa [RowCommonReusable.data] using hf.1
  · change (RowCommonClear.entry gs 0 p (RowCommonBounds.capacity gs (indices gs.length rows ds).length p)
      [] out (indices gs.length rows ds)).tapes 24=_
    rw [data]
    change CompareMachine.word (indices gs.length rows ds).length=_
    rw [hf.2]

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) (p w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M)
    (hp : RowCoordinateLoop.width gs (indices gs.length rows ds)≤p) :
    ∃ r,runFrom machine (budget gs p w M rows ds) (input gs p w M rows ds tail out)=some r ∧
      r.final.tapes 31=out++RowCoordinateLoop.equationWord p
        (RowCoordinateLoop.equation gs (indices gs.length rows ds)) ∧
      r.final.heads 31=(out++RowCoordinateLoop.equationWord p
        (RowCoordinateLoop.equation gs (indices gs.length rows ds))).length ∧
      r.steps≤budget gs p w M rows ds := by
  obtain ⟨tuple,ht,t2,t3,h2,h3,_⟩ := RowTupleMaskReady.tuple_run gs.length w M rows ds tail hl hd hb hM
  obtain ⟨a,ha,af,_⟩ := RecoveryFocus.run_config tupleSlots tuple_injective RowTupleMaskReady.machine
    (ambient gs p rows ds out).heads (ambient gs p rows ds out).tapes _ _ tuple ht
  obtain ⟨row,hr,rf,_⟩ := RowCommonCoordinateLoop.equation_run gs p (indices gs.length rows ds) [] out hp
  obtain ⟨b,hbRun,bf,_⟩ := RecoveryFocus.run_config rowSlots row_injective RowCommonCoordinateLoop.machine
    a.final.heads a.final.tapes _ _ row hr
  have hs := shared_fields gs p rows ds out hl hd
  have he : RecoveryFocus.config rowSlots a.final.heads a.final.tapes (common gs p rows ds out)=
      Composition.restart a.final last.start := by
    apply WilliamsSourceCrop.focus_same rowSlots (Composition.restart a.final last.start)
    · intro i
      change a.final.heads (rowSlots i)=(common gs p rows ds out).heads i
      rw [af]
      simp only [RecoveryFocus.config,tuple_pick_core]
      by_cases h23 : i=23
      · subst i; simp only [ite_true,h2]; rfl
      by_cases h24 : i=24
      · subst i
        simp only [show (24 : Fin 36)≠23 by decide,ite_false,ite_true]
        rw [h3]
        rfl
      simp only [h23,h24,ite_false]
      simp [ambient,TapeEmbedding.config,rowSlots]
    · intro i
      change a.final.tapes (rowSlots i)=(common gs p rows ds out).tapes i
      rw [af]
      simp only [RecoveryFocus.config,tuple_pick_core]
      by_cases h23 : i=23
      · subst i; simp only [ite_true]; exact t2.trans hs.1.symm
      by_cases h24 : i=24
      · subst i; simp only [show (24 : Fin 36)≠23 by decide,ite_false,ite_true]; exact t3.trans hs.2.symm
      simp only [h23,h24,ite_false]
      simp [ambient,TapeEmbedding.config,rowSlots]
  change runFrom last _ (RecoveryFocus.config rowSlots a.final.heads a.final.tapes
    (common gs p rows ds out))=some b at hbRun
  rw [he] at hbRun
  have whole := Composition.run_join first last _ _ _ a b ha hbRun
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,runFrom_steps_le machine _ _ _ whole⟩
  · change b.final.tapes (rowSlots 31)=_
    rw [bf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective]
    rw [rf]
    change (RowCommonClear.entry gs (n+1) p (RowCommonBounds.capacity gs (indices gs.length rows ds).length p)
      [] _ (indices gs.length rows ds)).tapes 31=_
    rw [RowCommonReusable.entry_tapes gs (n+1) p _ [] _ (indices gs.length rows ds)
      (by unfold RowCommonBounds.capacity; omega) (RowCommonBounds.inner_fits gs _ p)]
    rfl
  · change b.final.heads (rowSlots 31)=_
    rw [bf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective]
    rw [rf]
    rfl

end NearCubicWires.RepairOrdinary.RowTupleCommonEquation
