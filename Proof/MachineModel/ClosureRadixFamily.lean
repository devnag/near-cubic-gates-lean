import Proof.MachineModel.ClosureRadix
import Proof.Supplier.RowTupleCommonEquation
import Proof.Supplier.RowTupleEquationBounds
import Proof.Supplier.RowCommonFixedCapacity
import Proof.Supplier.RowTupleFixedCapacity
import Proof.Supplier.RowTupleCursorEquation
import Proof.Supplier.RowTupleBlank
import Proof.Supplier.RowTupleCursorLayout
import Proof.Supplier.RowTupleResetBounds
import Proof.Supplier.RowTupleCursorBody
import Proof.Supplier.RowTupleFramedBody
import Proof.Supplier.RowTupleList
import Proof.Supplier.RowTupleSelectedList
import Proof.Supplier.RowTupleEnumeratedEquations
import Proof.Supplier.RowTupleCutBody
import Proof.Supplier.RowTupleCutList
import Proof.CaseAnalysis.RowsEnumeratedCuts
import Proof.CaseAnalysis.RowsComputedCuts
import Proof.CaseAnalysis.RowsDegreeReset
import Proof.CaseAnalysis.RowsCacheInput
import Proof.CaseAnalysis.RowsCutMeaning
import Proof.CaseAnalysis.RowsReusableCuts
import Proof.CaseAnalysis.RowsLoopLayout
import Proof.CaseAnalysis.RowsLoopBoundary
import Proof.CaseAnalysis.RowsLoopInterface
import Proof.CaseAnalysis.RowsDegreeBody
import Proof.CaseAnalysis.RowsDegreeLoop
import Proof.CaseAnalysis.RowsDegreeRange
import Proof.CaseAnalysis.RowsPolynomial
import Proof.CaseAnalysis.RowsSharedDigits
import Proof.CaseAnalysis.RowsSharedInput
import Proof.CaseAnalysis.RowsPreparationBounds
import Proof.CaseAnalysis.RowsPreparationFits
import Proof.CaseAnalysis.RowsPreparationInput
import Proof.CaseAnalysis.RowsScratch
import Proof.CaseAnalysis.RowsPreparedPolynomial
import Proof.CaseAnalysis.RowsBankFields
import Proof.CaseAnalysis.RowsBankCapacity
import Proof.CaseAnalysis.RowsBankPolynomial
import Proof.CaseAnalysis.RowsSourceLoad
import Proof.CaseAnalysis.RowsPacketPolynomial
import Proof.CaseAnalysis.RowsPacketIndependent
import Proof.CaseAnalysis.RowsPacketOptional
import Proof.CaseAnalysis.RowsFamilyLoop
import Proof.MachineModel.ClosureRadixCoordinate
import Proof.MachineModel.ClosureMaskDegree

/-! A whole selected tuple now reaches the complete common-width equation
emitter through shared physical occurrence/count tapes. The ordered native
positions come from executed cache lookups, including all repetitions. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleCommonEquation
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
    P1CompactRowOccurrenceLoop.word (indices N rows ds)=RowTupleMaskLoop.word rows ds ∧
      (indices N rows ds).length=RowTupleMaskLoop.count rows ds := by
  induction ds with
  | nil => simp [indices,P1CompactRowOccurrenceLoop.word,RowTupleMaskLoop.word,RowTupleMaskLoop.count]
  | cons d ds ih =>
    have hlen := mask_length N rows d hl (hd d (by simp))
    obtain ⟨hw,hc⟩ := ih (fun a ha=>hd a (List.mem_cons_of_mem d ha))
    have hone : one N (RowTupleMaskLoop.mask rows d)=RowMaskMeaning.typed N 0 (RowTupleMaskLoop.mask rows d) (by omega) := by
      simp only [one,dif_pos (show (RowTupleMaskLoop.mask rows d).length≤N by omega)]
    have ow := RowMaskMeaning.typed_word N 0 (RowTupleMaskLoop.mask rows d) (by omega)
    change RowMaskLoop.word 0 (RowTupleMaskLoop.mask rows d) = P1CompactRowOccurrenceLoop.word (RowMaskMeaning.typed N 0 (RowTupleMaskLoop.mask rows d) (by omega)) at ow
    have oc := RowMaskMeaning.typed_length N 0 (RowTupleMaskLoop.mask rows d) (by omega)
    constructor
    · change P1CompactRowOccurrenceLoop.word (one N (RowTupleMaskLoop.mask rows d)++indices N rows ds)=_
      rw [show P1CompactRowOccurrenceLoop.word (one N (RowTupleMaskLoop.mask rows d)++indices N rows ds)=
        P1CompactRowOccurrenceLoop.word (one N (RowTupleMaskLoop.mask rows d))++P1CompactRowOccurrenceLoop.word (indices N rows ds) by
          simp only [P1CompactRowOccurrenceLoop.word,List.flatMap_append],hone,←ow,hw]
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
noncomputable def last := RecoveryFocus.machine rowSlots P1CompactRowCommonCoordinateLoop.machine
noncomputable def machine := Composition.machine first last
noncomputable def common {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool) :=
  P1CompactRowCommonCoordinateLoop.cfg gs p (indices gs.length rows ds) 0 0 1 [] out
noncomputable def ambient {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool) :=
  TapeEmbedding.config (fun _ : Fin 12=>0) (fun _=>[]) (common gs p rows ds out)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool) :=
  Composition.restart (RecoveryFocus.config tupleSlots (ambient gs p rows ds out).heads
    (ambient gs p rows ds out).tapes
    (Composition.restart (RowTupleMaskReady.input gs.length w M rows ds tail) RowTupleMaskReady.machine.start)) machine.start
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) :=
  RowTupleMaskReady.budget gs.length w M ds.length (RowTupleMaskLoop.count rows ds)+1+
    P1CompactRowCommonCoordinateLoop.budget gs p (indices gs.length rows ds)

theorem tuple_pick_core (i : Fin 36) : RecoveryFocus.pick tupleSlots (rowSlots i)=
    (if i=23 then some 2 else if i=24 then some 3 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 2
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 3
    | decide

theorem shared_fields {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length) :
    (common gs p rows ds out).tapes 23=RowTupleMaskLoop.word rows ds ∧
      (common gs p rows ds out).tapes 24=CompareMachine.word (RowTupleMaskLoop.count rows ds) := by
  have hf := index_fields gs.length rows ds hl hd
  have data := P1CompactRowCommonReusable.entry_tapes gs 0 p (P1CompactRowCommonBounds.capacity gs (indices gs.length rows ds).length p)
    [] out (indices gs.length rows ds) (by unfold P1CompactRowCommonBounds.capacity; omega)
    (P1CompactRowCommonBounds.inner_fits gs _ p)
  constructor
  · change (P1CompactRowCommonClear.entry gs 0 p (P1CompactRowCommonBounds.capacity gs (indices gs.length rows ds).length p)
      [] out (indices gs.length rows ds)).tapes 23=_
    rw [data]
    simpa [P1CompactRowCommonReusable.data] using hf.1
  · change (P1CompactRowCommonClear.entry gs 0 p (P1CompactRowCommonBounds.capacity gs (indices gs.length rows ds).length p)
      [] out (indices gs.length rows ds)).tapes 24=_
    rw [data]
    change CompareMachine.word (indices gs.length rows ds).length=_
    rw [hf.2]

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M)
    (hp : P1CompactRowCoordinateLoop.width gs (indices gs.length rows ds)≤p) :
    ∃ r,runFrom machine (budget gs p w M rows ds) (input gs p w M rows ds tail out)=some r ∧
      r.final.tapes 31=out++P1CompactRowCoordinateLoop.equationWord p
        (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds)) ∧
      r.final.heads 31=(out++P1CompactRowCoordinateLoop.equationWord p
        (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds))).length ∧
      r.steps≤budget gs p w M rows ds := by
  obtain ⟨tuple,ht,t2,t3,h2,h3,_⟩ := RowTupleMaskReady.tuple_run gs.length w M rows ds tail hl hd hb hM
  obtain ⟨a,ha,af,_⟩ := RecoveryFocus.run_config tupleSlots tuple_injective RowTupleMaskReady.machine
    (ambient gs p rows ds out).heads (ambient gs p rows ds out).tapes _ _ tuple ht
  obtain ⟨row,hr,rf,_⟩ := P1CompactRowCommonCoordinateLoop.equation_run gs p (indices gs.length rows ds) [] out hp
  obtain ⟨b,hbRun,bf,_⟩ := RecoveryFocus.run_config rowSlots row_injective P1CompactRowCommonCoordinateLoop.machine
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
    change (P1CompactRowCommonClear.entry gs (n+1) p (P1CompactRowCommonBounds.capacity gs (indices gs.length rows ds).length p)
      [] _ (indices gs.length rows ds)).tapes 31=_
    rw [P1CompactRowCommonReusable.entry_tapes gs (n+1) p _ [] _ (indices gs.length rows ds)
      (by unfold P1CompactRowCommonBounds.capacity; omega) (P1CompactRowCommonBounds.inner_fits gs _ p)]
    rfl
  · change b.final.heads (rowSlots 31)=_
    rw [bf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective]
    rw [rf]
    rfl

end NearCubicWires.RepairOrdinary.P1CompactRowTupleCommonEquation

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowTupleCommonEquation_machine_unchanged : @P1CompactRowTupleCommonEquation.machine = @RowTupleCommonEquation.machine := rfl
end NearCubicWires.RepairOrdinary

/-! The tuple equation caller accepts the binary frame emitted by the
actual enumerator. Its time is bounded using source dimensions and tuple
degree, without a separate supplied selected-occurrence count. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleEquationBounds
open LocalBitMultitape RepairRepresentation SignedSortKey P1CompactRowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem count_le (N : ℕ) (rows : List (List Bool)) (ds : List ℕ)
    (hl : ∀ row∈rows,row.length=N) (hd : ∀ d∈ds,d<rows.length) :
    RowTupleMaskLoop.count rows ds≤N*ds.length := by
  induction ds with
  | nil => simp [RowTupleMaskLoop.count]
  | cons d ds ih =>
    have htail := ih (fun a ha=>hd a (List.mem_cons_of_mem d ha))
    have hm := mask_length N rows d hl (hd d (by simp))
    have hc : (RowTupleMaskLoop.mask rows d).count true≤N := by
      simpa only [hm] using (List.count_le_length (a:=true) (l:=RowTupleMaskLoop.mask rows d))
    simp only [RowTupleMaskLoop.count,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p w M k : ℕ) :=
  RowTupleMaskReady.budget gs.length w M k (gs.length*k)+1+
    ((n+1)*(P1CompactRowCommonBounds.bound gs (gs.length*k) p+2*n+13)+3)

theorem budget_le {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length) :
    P1CompactRowTupleCommonEquation.budget gs p w M rows ds≤budget gs p w M ds.length := by
  have hc := count_le gs.length rows ds hl hd
  have hi := (index_fields gs.length rows ds hl hd).2
  have hm : P1CompactRowCommonBounds.bound gs (indices gs.length rows ds).length p≤
      P1CompactRowCommonBounds.bound gs (gs.length*ds.length) p := by
    rw [hi]
    have hmul := Nat.mul_le_mul_right (RowCachedCoordinateBounds.size gs (P1Radix.bits gs))
      (Nat.mul_le_mul_left 65536 (Nat.add_le_add_right hc 1))
    unfold P1CompactRowCommonBounds.bound
    omega
  unfold P1CompactRowTupleCommonEquation.budget budget
  apply Nat.add_le_add
  · apply Nat.add_le_add_right
    unfold RowTupleMaskReady.budget
    omega
  · unfold P1CompactRowCommonCoordinateLoop.budget P1CompactRowCommonCoordinateLoop.bodyBudget
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    omega

theorem encoded_tuple (w : ℕ) (ds : List ℕ) (hd : ∀ d∈ds,d<2^w) :
    frame (binary (w*ds.length+1) (RowTupleDigits.encode w ds))=
      RowTupleFilterLoop.word w ds++frame [false] := by
  have h := RowTupleFilterReusable.counter_word w ds.length (RowTupleDigits.encode w ds)
    (RowTupleDigits.encode_bound w ds hd)
  rwa [RowTupleDigits.digits_encode w ds hd] at h

theorem input_tuple {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool) :
    (input gs p w M rows ds tail out).tapes 44=RowTupleFilterLoop.word w ds++tail := by
  change (RecoveryFocus.config tupleSlots (ambient gs p rows ds out).heads
    (ambient gs p rows ds out).tapes
    (Composition.restart (RowTupleMaskReady.input gs.length w M rows ds tail) RowTupleMaskReady.machine.start)).tapes
      (tupleSlots 10)=_
  simp only [RecoveryFocus.config,RecoveryFocus.pick_slot tupleSlots tuple_injective]
  simp [Composition.restart,RowTupleMaskReady.input,RowTupleMaskReady.before,
    RowTupleMaskLoop.cfg,RepairSource.VerifierDecoding.RepeatMachine.cfg,controlConfig,
    ZeroPadding.config,Rewind.Workspace.capacities,Rewind.recording,Rewind.config,TapeEmbedding.config,
    RowTupleMaskBody.cfg,RowMaskLookupReusable.cfg,Fin.addCases,ZeroPadding.pad]

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M)
    (hp : P1CompactRowCoordinateLoop.width gs (indices gs.length rows ds)≤p) :
    (input gs p w M rows ds (frame [false]++tail) out).tapes 44=
      frame (binary (w*ds.length+1) (RowTupleDigits.encode w ds))++tail ∧
    ∃ r,runFrom machine (budget gs p w M ds.length)
      (input gs p w M rows ds (frame [false]++tail) out)=some r ∧
      r.final.tapes 31=out++P1CompactRowCoordinateLoop.equationWord p
        (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds)) ∧
      r.final.heads 31=(out++P1CompactRowCoordinateLoop.equationWord p
        (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds))).length ∧
      r.steps≤budget gs p w M ds.length := by
  constructor
  · rw [input_tuple,encoded_tuple w ds (fun d hh=>(hd d hh).trans hb),List.append_assoc]
  · obtain ⟨r,hr,rt,rh,rs⟩ := P1CompactRowTupleCommonEquation.equation_run gs p w M rows ds (frame [false]++tail) out hl hd hb hM hp
    have hbound := budget_le gs p w M rows ds hl hd
    have hmore := runFrom_moreFuel machine _ (budget gs p w M ds.length-P1CompactRowTupleCommonEquation.budget gs p w M rows ds)
      _ r hr
    rw [Nat.add_sub_of_le hbound] at hmore
    exact ⟨r,hmore,rt,rh,rs.trans hbound⟩

end NearCubicWires.RepairOrdinary.P1CompactRowTupleEquationBounds

/-! The complete equation emitter accepts any sufficiently large fixed
allocation. One source-size allocation can therefore serve every selected
tuple; its size need not depend on the runtime selected-occurrence count. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonFixedCapacity
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem capacity_mono {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p a b : ℕ) (h : a≤b) :
    P1CompactRowCommonBounds.capacity gs a p≤P1CompactRowCommonBounds.capacity gs b p := by
  have hm := Nat.mul_le_mul_right (RowCachedCoordinateBounds.size gs (P1Radix.bits gs))
    (Nat.mul_le_mul_left 16384 (Nat.add_le_add_right h 1))
  unfold P1CompactRowCommonBounds.capacity
  omega

theorem coefficient_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : P1CompactRowCoordinateLoop.width gs indices≤p) (hF : P1CompactRowCommonBounds.capacity gs indices.length p≤F) :
    ∃ r,runFrom P1CompactRowCommonClear.machine (4*F+7) (P1CompactRowCommonClear.entry gs j p F tail out indices)=some r ∧
      r.final.heads=(P1CompactRowCommonClear.entry gs j p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices).heads ∧
      r.final.tapes=(P1CompactRowCommonClear.entry gs j p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices).tapes ∧
      r.steps≤4*F+7 := by
  have hcall := (P1CompactRowCommonBounds.call_fits gs j hj p indices).trans hF
  obtain ⟨r,hr,rh,rt,rs⟩ := P1CompactRowCommonReusable.reusable_run gs j hj p F tail out indices hp hcall
    ((P1CompactRowCommonBounds.padding_fits gs indices.length p).trans hF)
    ((P1CompactRowCommonBounds.inner_fits gs indices.length p).trans hF)
  have hb : 2*P1CompactRowCommonCoefficient.budget gs j hj p indices+2*F+7≤4*F+7 := by omega
  have more := runFrom_moreFuel P1CompactRowCommonClear.machine _
    (4*F+7-(2*P1CompactRowCommonCoefficient.budget gs j hj p indices+2*F+7)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,rh,rt,rs.trans hb⟩

noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Composition.restart (P1CompactRowCommonClear.entry gs j p F tail out indices) P1CompactRowCommonCoordinateBody.machine.start

theorem coordinate_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hF : P1CompactRowCommonBounds.capacity gs indices.length p≤F) :
    Function.update (P1CompactRowCommonClear.entry gs j p F tail out indices).tapes 15 (UnaryTemplate.tape (j+1))=
      (P1CompactRowCommonClear.entry gs (j+1) p F tail out indices).tapes := by
  have hpos : 1≤F := by have := P1CompactRowCommonBounds.padding_fits gs indices.length p; omega
  have hinner := (P1CompactRowCommonBounds.inner_fits gs indices.length p).trans hF
  rw [P1CompactRowCommonReusable.entry_tapes gs j p F tail out indices hpos hinner,
    P1CompactRowCommonReusable.entry_tapes gs (j+1) p F tail out indices hpos hinner]
  funext i; fin_cases i <;> simp [P1CompactRowCommonReusable.data]

theorem body_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : P1CompactRowCoordinateLoop.width gs indices≤p) (hF : P1CompactRowCommonBounds.capacity gs indices.length p≤F) :
    ∃ r,runFrom P1CompactRowCommonCoordinateBody.machine (4*F+2*j+17) (entry gs j p F tail out indices)=some r ∧
      r.final.heads=(entry gs (j+1) p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices).heads ∧
      r.final.tapes=(entry gs (j+1) p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices).tapes ∧
      r.steps≤4*F+2*j+17 := by
  obtain ⟨a,ha,ah,atapes,as⟩ := coefficient_run gs j hj p F tail out indices hp hF
  have hhead : a.final.heads 15=1 := by rw [ah]; rfl
  have htape : a.final.tapes 15=UnaryTemplate.tape j := by
    rw [atapes,P1CompactRowCommonReusable.entry_tapes gs j p F tail _ indices
      (by have := P1CompactRowCommonBounds.padding_fits gs indices.length p; omega)
      ((P1CompactRowCommonBounds.inner_fits gs indices.length p).trans hF)]
    rfl
  obtain ⟨b,hb,bh,bt,bs⟩ := P1CompactRowCommonCoordinateBody.increment_run j a.final.heads a.final.tapes hhead htape
  have whole := Composition.run_join P1CompactRowCommonClear.machine P1CompactRowCommonCoordinateBody.increment _ _ _ a b ha hb
  rw [show 4*F+7+1+(2*j+9)=4*F+2*j+17 by omega] at whole
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,?_⟩
  · change b.final.heads=_
    rw [bh,ah]
    exact P1CompactRowCommonCoordinateBody.coordinate_heads gs j (j+1) p F tail _ indices
  · change b.final.tapes=_
    rw [bt,atapes]
    exact coordinate_tapes gs j p F tail _ indices hF
  · change a.steps+1+b.steps≤_
    omega

noncomputable def cfg {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F : ℕ) (indices : List (Fin gs.length))
    (phase : Fin 5) (j driver : ℕ) (tail out : List Bool) :=
  RepeatMachine.cfg phase (entry gs j p F tail out indices) (n+1) driver
def budget (n F : ℕ) := (n+1)*(4*F+2*n+20)+3

theorem remaining {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F : ℕ) (indices : List (Fin gs.length))
    (j count : ℕ) (hj : j+count=n+1) (tail out : List Bool)
    (hp : P1CompactRowCoordinateLoop.width gs indices≤p) (hF : P1CompactRowCommonBounds.capacity gs indices.length p≤F) :
    ∃ time,time≤count*(4*F+2*n+19)+(n+1)+3 ∧
      Timed P1CompactRowCommonCoordinateLoop.machine time (cfg gs p F indices 0 j (j+1) tail out)
        (cfg gs p F indices 3 (n+1) 1 tail (out++P1CompactRowCommonCoordinateLoop.word gs indices p j count)) := by
  induction count generalizing j out with
  | zero =>
    have he : j=n+1 := by omega
    subst j
    refine ⟨n+1+3,by omega,?_⟩
    simpa only [cfg,P1CompactRowCommonCoordinateLoop.machine,P1CompactRowCommonCoordinateLoop.word,List.append_nil] using
      RepeatMachine.exhaust P1CompactRowCommonCoordinateBody.machine (fun _ _=>true) (entry gs (n+1) p F tail out indices) (n+1)
  | succ count ih =>
    have hjn : j≤n := by omega
    obtain ⟨r,hr,rh,rt,rs⟩ := body_run gs j hjn p F tail out indices hp hF
    have hs : r.steps≤4*F+2*n+17 := by omega
    have ht := RepeatMachine.iteration P1CompactRowCommonCoordinateBody.machine (fun _ _=>true)
      (entry gs j p F tail out indices) (n+1) j r (by rfl) (by omega) hr
    simp only [↓reduceIte] at ht
    have he := P1CompactRowOccurrenceLoop.cfg_eq 0 r.final
      (entry gs (j+1) p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hjn indices))) indices)
      (n+1) (j+2) rh rt
    rw [he] at ht
    obtain ⟨time,hbound,htail⟩ := ih (j+1) (by omega)
      (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hjn indices)))
    rw [show j+1+1=j+2 by omega] at htail
    have whole := ht.trans htail
    refine ⟨r.steps+2+time,?_,?_⟩
    · nlinarith
    · simpa only [cfg,P1CompactRowCommonCoordinateLoop.machine,P1CompactRowCommonCoordinateLoop.word,
        P1CompactRowCommonCoordinateLoop.field,dif_pos hjn,List.append_assoc] using whole

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F : ℕ) (indices : List (Fin gs.length))
    (tail out : List Bool) (hp : P1CompactRowCoordinateLoop.width gs indices≤p)
    (hF : P1CompactRowCommonBounds.capacity gs indices.length p≤F) :
    ∃ r,runFrom P1CompactRowCommonCoordinateLoop.machine (budget n F) (cfg gs p F indices 0 0 1 tail out)=some r ∧
      r.final=cfg gs p F indices 3 (n+1) 1 tail
        (out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs indices)) ∧ r.steps≤budget n F := by
  obtain ⟨time,hbound,ht⟩ := remaining gs p F indices 0 (n+1) (by omega) tail out hp hF
  have hb : time≤budget n F := by unfold budget; nlinarith
  obtain ⟨r,hr,rf,rs⟩ := ht.run
    (by simp [P1CompactRowCommonCoordinateLoop.machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have more := runFrom_moreFuel P1CompactRowCommonCoordinateLoop.machine time (budget n F-time) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  rw [P1CompactRowCommonCoordinateLoop.word_equation] at rf
  exact ⟨r,more,rf,rs.le.trans hb⟩

theorem tuple_capacity {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (hrows : ∀ row∈rows,row.length=gs.length)
    (hd : ∀ d∈ds,d<rows.length) (hQ : ds.length≤Q)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    P1CompactRowCommonBounds.capacity gs (P1CompactRowTupleCommonEquation.indices gs.length rows ds).length p≤F := by
  have hc := P1CompactRowTupleEquationBounds.count_le gs.length rows ds hrows hd
  rw [(P1CompactRowTupleCommonEquation.index_fields gs.length rows ds hrows hd).2]
  apply (capacity_mono gs p _ _ (hc.trans (Nat.mul_le_mul_left gs.length hQ))).trans hF

end NearCubicWires.RepairOrdinary.P1CompactRowCommonFixedCapacity

/-! The actual tuple-to-equation caller uses one common width and one
source-sized allocation for every tuple up to degree Q. Per-tuple width and
allocation conditions are discharged by the computed occurrence-count bound. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleFixedCapacity
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (Q : ℕ) :=
  P1Radix.bits gs*(P1Radix.effectiveDegree gs*Q)
noncomputable def common {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool) :=
  P1CompactRowCommonFixedCapacity.cfg gs p F (indices gs.length rows ds) 0 0 1 [] out
noncomputable def ambient {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool) :=
  TapeEmbedding.config (fun _ : Fin 12=>0) (fun _=>[]) (common gs p F rows ds out)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool) :=
  Composition.restart (RecoveryFocus.config tupleSlots (ambient gs p F rows ds out).heads
    (ambient gs p F rows ds out).tapes
    (Composition.restart (RowTupleMaskReady.input gs.length w M rows ds tail) RowTupleMaskReady.machine.start)) machine.start
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) :=
  RowTupleMaskReady.budget gs.length w M ds.length (RowTupleMaskLoop.count rows ds)+1+
    P1CompactRowCommonFixedCapacity.budget n F

theorem shared_fields {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hF : P1CompactRowCommonBounds.capacity gs (indices gs.length rows ds).length p≤F) :
    (common gs p F rows ds out).tapes 23=RowTupleMaskLoop.word rows ds ∧
      (common gs p F rows ds out).tapes 24=CompareMachine.word (RowTupleMaskLoop.count rows ds) := by
  have hf := index_fields gs.length rows ds hl hd
  have data := P1CompactRowCommonReusable.entry_tapes gs 0 p F [] out (indices gs.length rows ds)
    (by have := P1CompactRowCommonBounds.padding_fits gs (indices gs.length rows ds).length p; omega)
    ((P1CompactRowCommonBounds.inner_fits gs (indices gs.length rows ds).length p).trans hF)
  constructor
  · change (P1CompactRowCommonClear.entry gs 0 p F [] out (indices gs.length rows ds)).tapes 23=_
    rw [data]
    simpa [P1CompactRowCommonReusable.data] using hf.1
  · change (P1CompactRowCommonClear.entry gs 0 p F [] out (indices gs.length rows ds)).tapes 24=_
    rw [data]
    change CompareMachine.word (indices gs.length rows ds).length=_
    rw [hf.2]

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w M : ℕ)
    (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (ds : List ℕ) (tail out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) (hQ : ds.length≤Q)
    (hp : width gs Q≤p) (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (budget gs F w M rows ds) (input gs p F w M rows ds tail out)=some r ∧
      r.final.tapes 31=out++P1CompactRowCoordinateLoop.equationWord p
        (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds)) ∧
      r.final.heads 31=(out++P1CompactRowCoordinateLoop.equationWord p
        (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds))).length ∧
      r.steps≤budget gs F w M rows ds := by
  have hcap := P1CompactRowCommonFixedCapacity.tuple_capacity gs p F Q rows ds hl hd hQ hF
  have hwidth : P1CompactRowCoordinateLoop.width gs (indices gs.length rows ds)≤p := by
    have hc := (P1MaskDegree.count_le gs rows ds hd).trans (Nat.mul_le_mul_left (P1Radix.effectiveDegree gs) hQ)
    have hm := Nat.mul_le_mul_left (P1Radix.bits gs) hc
    unfold P1CompactRowCoordinateLoop.width
    rw [(index_fields gs.length rows ds hl hd).2]
    exact hm.trans hp
  obtain ⟨tuple,ht,t2,t3,h2,h3,_⟩ := RowTupleMaskReady.tuple_run gs.length w M rows ds tail hl hd hb hM
  obtain ⟨a,ha,af,_⟩ := RecoveryFocus.run_config tupleSlots tuple_injective RowTupleMaskReady.machine
    (ambient gs p F rows ds out).heads (ambient gs p F rows ds out).tapes _ _ tuple ht
  obtain ⟨row,hr,rf,_⟩ := P1CompactRowCommonFixedCapacity.equation_run gs p F (indices gs.length rows ds) [] out hwidth hcap
  obtain ⟨b,hbRun,bf,_⟩ := RecoveryFocus.run_config rowSlots row_injective P1CompactRowCommonCoordinateLoop.machine
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
    change (P1CompactRowCommonClear.entry gs (n+1) p F [] _ (indices gs.length rows ds)).tapes 31=_
    rw [P1CompactRowCommonReusable.entry_tapes gs (n+1) p F [] _ (indices gs.length rows ds)
      (by have := P1CompactRowCommonBounds.padding_fits gs (indices gs.length rows ds).length p; omega)
      ((P1CompactRowCommonBounds.inner_fits gs (indices gs.length rows ds).length p).trans hcap)]
    rfl
  · change b.final.heads (rowSlots 31)=_
    rw [bf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective]
    rw [rf]
    rfl

end NearCubicWires.RepairOrdinary.P1CompactRowTupleFixedCapacity

/-! The complete equation body consumes one tuple at its retained stream
cursor. Its exact final configuration exposes the ports needed to clear
only the per-tuple data before the next selected tuple. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleCursorEquation
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := RecoveryFocus.machine tupleSlots RowTupleCursorReady.machine
noncomputable def last := RecoveryFocus.machine rowSlots P1CompactRowCommonCoordinateLoop.machine
noncomputable def machine := Composition.machine first last
abbrev width := @P1CompactRowTupleFixedCapacity.width
noncomputable def common {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool) :=
  P1CompactRowCommonFixedCapacity.cfg gs p F (indices gs.length rows ds) 0 0 1 [] out
noncomputable def ambient {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool) :=
  TapeEmbedding.config (fun _ : Fin 12=>0) (fun _=>[]) (common gs p F rows ds out)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ) :=
  Composition.restart (RecoveryFocus.config tupleSlots (ambient gs p F rows ds out).heads
    (ambient gs p F rows ds out).tapes
    (Composition.restart (RowTupleCursorReady.input gs.length w M rows ds pre tail bound) RowTupleCursorReady.machine.start)) machine.start
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) :=
  RowTupleMaskReady.budget gs.length w M ds.length (RowTupleMaskLoop.count rows ds)+1+
    P1CompactRowCommonFixedCapacity.budget n F

theorem shared_fields {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hF : P1CompactRowCommonBounds.capacity gs (indices gs.length rows ds).length p≤F) :
    (common gs p F rows ds out).tapes 23=RowTupleMaskLoop.word rows ds ∧
      (common gs p F rows ds out).tapes 24=CompareMachine.word (RowTupleMaskLoop.count rows ds) := by
  have hf := index_fields gs.length rows ds hl hd
  have data := P1CompactRowCommonReusable.entry_tapes gs 0 p F [] out (indices gs.length rows ds)
    (by have := P1CompactRowCommonBounds.padding_fits gs (indices gs.length rows ds).length p; omega)
    ((P1CompactRowCommonBounds.inner_fits gs (indices gs.length rows ds).length p).trans hF)
  constructor
  · change (P1CompactRowCommonClear.entry gs 0 p F [] out (indices gs.length rows ds)).tapes 23=_
    rw [data]
    simpa [P1CompactRowCommonReusable.data] using hf.1
  · change (P1CompactRowCommonClear.entry gs 0 p F [] out (indices gs.length rows ds)).tapes 24=_
    rw [data]
    change CompareMachine.word (indices gs.length rows ds).length=_
    rw [hf.2]

noncomputable def middle {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ) :=
  RecoveryFocus.config tupleSlots (ambient gs p F rows ds out).heads
    (ambient gs p F rows ds out).tapes
    (⟨RowTupleCursorReady.machine.start,
      Function.update (RowTupleCursorReady.middleHeads gs.length w M rows ds pre tail bound) 3 1,
      RowTupleCursorReady.output gs.length w M rows ds pre tail bound⟩ : Configuration 14 _)
noncomputable def result {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ) :=
  let mid:=middle gs p F w M rows ds pre tail out bound
  RecoveryFocus.config rowSlots mid.heads mid.tapes
    (P1CompactRowCommonFixedCapacity.cfg gs p F (indices gs.length rows ds) 3 (n+1) 1 []
      (out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds))))

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w M : ℕ)
    (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) (hQ : ds.length≤Q)
    (hp : width gs Q≤p) (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (budget gs F w M rows ds) (input gs p F w M rows ds pre tail out bound)=some r ∧
      r.final.heads=(result gs p F w M rows ds pre tail out bound).heads ∧
      r.final.tapes=(result gs p F w M rows ds pre tail out bound).tapes ∧
      r.steps≤budget gs F w M rows ds := by
  have hcap := P1CompactRowCommonFixedCapacity.tuple_capacity gs p F Q rows ds hl hd hQ hF
  have hwidth : P1CompactRowCoordinateLoop.width gs (indices gs.length rows ds)≤p := by
    have hc := (P1MaskDegree.count_le gs rows ds hd).trans (Nat.mul_le_mul_left (P1Radix.effectiveDegree gs) hQ)
    have hm := Nat.mul_le_mul_left (P1Radix.bits gs) hc
    unfold P1CompactRowCoordinateLoop.width
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
  obtain ⟨row,hr,rf,_⟩ := P1CompactRowCommonFixedCapacity.equation_run gs p F (indices gs.length rows ds) [] out hwidth hcap
  obtain ⟨b,hbRun,bf,_⟩ := RecoveryFocus.run_config rowSlots row_injective P1CompactRowCommonCoordinateLoop.machine
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

end NearCubicWires.RepairOrdinary.P1CompactRowTupleCursorEquation

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowTupleCursorEquation_machine_unchanged : @P1CompactRowTupleCursorEquation.machine = @RowTupleCursorEquation.machine := rfl
end NearCubicWires.RepairOrdinary

/-! The whole tuple-to-equation machine starts with blank scratch and
recording tapes. Zero-padding transport removes the earlier supplied false
allocations without changing the machine, actual data, or execution time. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleBlank
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def keep (i : Fin 48) : Bool := decide (i=0 ∨ i=9 ∨ i=13 ∨ i=18 ∨ i=21 ∨ i=29 ∨
  i=31 ∨ i=33 ∨ i=35 ∨ i=36 ∨ i=38 ∨ i=39 ∨ i=40 ∨ i=44 ∨ i=45 ∨ i=46)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool) :=
  let c:=P1CompactRowTupleFixedCapacity.input gs p F w M rows ds tail out
  {c with tapes:=fun i=>if keep i then c.tapes i else []}
noncomputable def padding {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool) : Fin 48→ℕ :=
  fun i=>if keep i then 0 else (P1CompactRowTupleFixedCapacity.input gs p F w M rows ds tail out).tapes i |>.length

theorem tuple_pick (i : Fin 48) : RecoveryFocus.pick tupleSlots i=
    (if i=36 then some 0 else if i=37 then some 1 else if i=23 then some 2 else if i=24 then some 3
    else if i=38 then some 4 else if i=39 then some 5 else if i=40 then some 6 else if i=41 then some 7
    else if i=42 then some 8 else if i=43 then some 9 else if i=44 then some 10 else if i=45 then some 11
    else if i=46 then some 12 else if i=47 then some 13 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 0
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 1
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 2
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 3
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 4
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 5
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 6
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 7
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 8
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 9
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 10
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 11
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 12
    | exact RecoveryFocus.pick_slot tupleSlots tuple_injective 13
    | decide

theorem zero_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool)
    (hF : 1≤F) (hD : RowCachedCoordinateBounds.outer gs (P1Radix.bits gs)≤F)
    (i : Fin 48) (hi : keep i=false) :
    (P1CompactRowTupleFixedCapacity.input gs p F w M rows ds tail out).tapes i=
      List.replicate ((P1CompactRowTupleFixedCapacity.input gs p F w M rows ds tail out).tapes i).length false := by
  have hc : (P1CompactRowTupleFixedCapacity.common gs p F rows ds out).tapes=
      Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
        (P1CompactRowCommonReusable.data gs 0 p F [] out (indices gs.length rows ds))
        (fun _=>CompareMachine.word (n+1)) := by
    change Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
      (P1CompactRowCommonClear.entry gs 0 p F [] out (indices gs.length rows ds)).tapes
      (fun _=>CompareMachine.word (n+1))=_
    rw [P1CompactRowCommonReusable.entry_tapes gs 0 p F [] out (indices gs.length rows ds) hF hD]
  simp only [P1CompactRowTupleFixedCapacity.input,Composition.restart,RecoveryFocus.config,
    tuple_pick,P1CompactRowTupleFixedCapacity.ambient,TapeEmbedding.config,hc]
  fin_cases i <;> simp only [keep,decide_eq_false_iff_not] at hi
  all_goals first
    | (exact False.elim (hi (by decide)))
    | (simp [P1CompactRowCommonReusable.data,RowTupleMaskReady.input,RowTupleMaskReady.before,
        RowTupleMaskReady.start,RowTupleMaskLoop.cfg,RepeatMachine.cfg,controlConfig,
        TapeEmbedding.config,RowTupleMaskBody.cfg,RowMaskLookupReusable.cfg,RowMaskConsume.bank,
        RowMaskPositionParts.cfg,RowMaskPositionParts.tapes,RowMaskConsume.capacities,
        ZeroPadding.config,ZeroPadding.pad,Rewind.recording,Rewind.config,Rewind.Workspace.capacities,
        Fin.addCases,UnaryTemplate.tape,CompareMachine.word])
  all_goals simp only [List.replicate_succ]

theorem padded_input {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (tail out : List Bool)
    (hF : 1≤F) (hD : RowCachedCoordinateBounds.outer gs (P1Radix.bits gs)≤F) :
    ZeroPadding.config (padding gs p F w M rows ds tail out) (input gs p F w M rows ds tail out)=
      P1CompactRowTupleFixedCapacity.input gs p F w M rows ds tail out := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    cases hi:keep i
    · simpa [ZeroPadding.config,padding,input,hi,ZeroPadding.pad] using
        (zero_tapes gs p F w M rows ds tail out hF hD i hi).symm
    · simp [ZeroPadding.config,padding,input,hi,ZeroPadding.pad_zero]

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w M : ℕ)
    (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (ds : List ℕ) (tail out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) (hQ : ds.length≤Q)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p) (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (P1CompactRowTupleFixedCapacity.budget gs F w M rows ds)
      (input gs p F w M rows ds tail out)=some r ∧
      r.final.tapes 31=out++P1CompactRowCoordinateLoop.equationWord p
        (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds)) ∧
      r.final.heads 31=(out++P1CompactRowCoordinateLoop.equationWord p
        (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds))).length ∧
      r.steps≤P1CompactRowTupleFixedCapacity.budget gs F w M rows ds := by
  obtain ⟨base,hbRun,bt,bh,bs⟩:=P1CompactRowTupleFixedCapacity.equation_run gs p F Q w M rows ds tail out hl hd hb hM hQ hp hF
  have hpos : 1≤F := by have := P1CompactRowCommonBounds.padding_fits gs (gs.length*Q) p; omega
  have hinner := (P1CompactRowCommonBounds.inner_fits gs (gs.length*Q) p).trans hF
  rw [←padded_input gs p F w M rows ds tail out hpos hinner] at hbRun
  obtain ⟨r,hr,rf,rs,_⟩:=ZeroPadding.run_unpad machine (padding gs p F w M rows ds tail out) _ _ base hbRun
  have ht:=congrArg (fun c=>c.tapes (31 : Fin 48)) rf
  have hh:=congrArg (fun c=>c.heads (31 : Fin 48)) rf
  refine ⟨r,hr,?_,hh.trans bh,rs.le.trans bs⟩
  simpa [ZeroPadding.config,padding,keep,ZeroPadding.pad_zero] using ht.trans bt

end NearCubicWires.RepairOrdinary.P1CompactRowTupleBlank

/-! The exact reusable tuple-store layout: only the coordinate counter,
occurrence stream and count need erasure between adjacent tuples. The
cached last lookup bound remains available and is overwritten by the next
digit read. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleCursorLayout
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation RowMaskPositionParts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j p F w M k : ℕ)
    (rows : List (List Bool)) (tuple out : List Bool) (bound : ℕ) (is : List (Fin gs.length)) : Fin 48→List Bool :=
  Fin.addCases (m:=36) (n:=12) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
      (P1CompactRowCommonReusable.data gs j p F [] out is) (fun _=>CompareMachine.word (n+1)))
    ![rows.flatten,List.replicate (gs.length+2) false,UnaryTemplate.tape gs.length,
      frame (SignedSortKey.binary w 0),frame (SignedSortKey.binary w bound),[false],
      List.replicate (2*w+1) false,List.replicate (RowMaskLookupReusable.capacity gs.length w M) false,
      tuple,CompareMachine.word w,CompareMachine.word k,
      List.replicate (RowTupleCursorReady.capacity gs.length w M k) false]
def heads (pos : ℕ) (out : List Bool) : Fin 48→ℕ := fun i=>
  if i=31 then out.length else if i=44 then pos else
    if i=15 ∨ i=18 ∨ i=24 ∨ i=35 ∨ i=37 ∨ i=38 ∨ i=45 ∨ i=46 then 1 else 0

theorem row_pick (i : Fin 48) : RecoveryFocus.pick rowSlots i=
    Fin.addCases (m:=36) (n:=12) (motive:=fun _=>Option (Fin 36)) (fun j=>some j) (fun _=>none) i := by
  refine Fin.addCases (m:=36) (n:=12) (fun j=>?_) (fun j=>?_) i
  · simpa only [rowSlots,Fin.addCases_left] using RecoveryFocus.pick_slot rowSlots row_injective j
  · fin_cases j <;> decide

theorem fold_static (rows : List (List Bool)) (ds : List ℕ) (x : Data)
    (hp:x.pos=0) (hi:x.index=0) (hc:x.counter=0) (hf:x.flag=false) :
    (RowTupleMaskLoop.fold rows x ds).source=x.source ∧
      (RowTupleMaskLoop.fold rows x ds).pos=0 ∧
      (RowTupleMaskLoop.fold rows x ds).index=0 ∧
      (RowTupleMaskLoop.fold rows x ds).counter=0 ∧
      (RowTupleMaskLoop.fold rows x ds).flag=false := by
  induction ds generalizing x with
  | nil => exact ⟨rfl,hp,hi,hc,hf⟩
  | cons d ds ih =>
    exact ih (RowTupleMaskLoop.advance rows x d) rfl rfl rfl rfl

private theorem tuple_input_tapes (N w M : ℕ) (rows : List (List Bool)) (ds : List ℕ)
    (pre tail : List Bool) (bound : ℕ) :
    (RowTupleCursorReady.input N w M rows ds pre tail bound).tapes=
      (![rows.flatten,List.replicate (N+2) false,[],CompareMachine.word 0,UnaryTemplate.tape N,
        frame (SignedSortKey.binary w 0),frame (SignedSortKey.binary w bound),[false],
        List.replicate (2*w+1) false,List.replicate (RowMaskLookupReusable.capacity N w M) false,
        pre++RowTupleFilterLoop.word w ds++tail,CompareMachine.word w,CompareMachine.word ds.length,
        List.replicate (RowTupleCursorReady.capacity N w M ds.length) false] : Fin 14→List Bool) := by
  funext i
  fin_cases i <;> simp [RowTupleCursorReady.input,RowTupleCursorReady.before,
    RowTupleCursorReady.start,RowTupleMaskLoop.cfg,RepeatMachine.cfg,controlConfig,
    TapeEmbedding.config,RowTupleMaskBody.cfg,RowMaskLookupReusable.cfg,RowMaskConsume.bank,
    RowMaskPositionParts.cfg,RowMaskPositionParts.tapes,RowMaskConsume.capacities,
    ZeroPadding.config,ZeroPadding.pad,Rewind.recording,Rewind.config,Rewind.Workspace.capacities,
    Fin.addCases,UnaryTemplate.tape,CompareMachine.word,List.replicate_succ]

theorem input_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ)
    (hF : 1≤F) (hD : RowCachedCoordinateBounds.outer gs (P1Radix.bits gs)≤F) :
    (P1CompactRowTupleCursorEquation.input gs p F w M rows ds pre tail out bound).tapes=
      data gs 0 p F w M ds.length rows (pre++RowTupleFilterLoop.word w ds++tail) out bound [] := by
  have hc : (P1CompactRowTupleCursorEquation.common gs p F rows ds out).tapes=
      Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
        (P1CompactRowCommonReusable.data gs 0 p F [] out (indices gs.length rows ds))
        (fun _=>CompareMachine.word (n+1)) := by
    change Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
      (P1CompactRowCommonClear.entry gs 0 p F [] out (indices gs.length rows ds)).tapes
      (fun _=>CompareMachine.word (n+1))=_
    rw [P1CompactRowCommonReusable.entry_tapes gs 0 p F [] out _ hF hD]
  funext i
  simp only [P1CompactRowTupleCursorEquation.input,Composition.restart,RecoveryFocus.config,
    P1CompactRowTupleBlank.tuple_pick,P1CompactRowTupleCursorEquation.ambient,TapeEmbedding.config,hc,tuple_input_tapes]
  fin_cases i <;> simp [data,P1CompactRowCommonReusable.data,Fin.addCases,P1CompactRowOccurrenceLoop.word,CompareMachine.word]

theorem input_heads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ) :
    (P1CompactRowTupleCursorEquation.input gs p F w M rows ds pre tail out bound).heads=heads pre.length out := by
  funext i
  simp only [P1CompactRowTupleCursorEquation.input,Composition.restart,RecoveryFocus.config,
    P1CompactRowTupleBlank.tuple_pick,P1CompactRowTupleCursorEquation.ambient,TapeEmbedding.config]
  fin_cases i <;> rfl

theorem result_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ)
    (hF : 1≤F) (hD : RowCachedCoordinateBounds.outer gs (P1Radix.bits gs)≤F) :
    (P1CompactRowTupleCursorEquation.result gs p F w M rows ds pre tail out bound).tapes=
      data gs (n+1) p F w M ds.length rows (pre++RowTupleFilterLoop.word w ds++tail)
        (out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds)))
        (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound (indices gs.length rows ds) := by
  have hc : (P1CompactRowCommonFixedCapacity.cfg gs p F (indices gs.length rows ds) 3 (n+1) 1 []
      (out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds)))).tapes=
      Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
        (P1CompactRowCommonReusable.data gs (n+1) p F []
          (out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds)))
          (indices gs.length rows ds)) (fun _=>CompareMachine.word (n+1)) := by
    change Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
      (P1CompactRowCommonClear.entry gs (n+1) p F [] _ (indices gs.length rows ds)).tapes
      (fun _=>CompareMachine.word (n+1))=_
    rw [P1CompactRowCommonReusable.entry_tapes gs (n+1) p F [] _ _ hF hD]
  obtain ⟨hs,_,hi,hc0,hf⟩:=fold_static rows ds (RowTupleCursorReady.start rows bound) rfl rfl rfl rfl
  simp only [RowTupleCursorReady.start] at hs hi hc0 hf
  funext i
  simp only [P1CompactRowTupleCursorEquation.result,RecoveryFocus.config,row_pick,hc]
  fin_cases i
  all_goals first | rfl | skip
  all_goals simp [data,P1CompactRowTupleCursorEquation.middle,RecoveryFocus.config,P1CompactRowTupleBlank.tuple_pick,
    RowTupleCursorReady.output,RowTupleCursorReady.after,RowTupleMaskLoop.cfg,RepeatMachine.cfg,
    controlConfig,TapeEmbedding.config,RowTupleMaskBody.cfg,RowMaskLookupReusable.cfg,
    RowMaskConsume.bank,ZeroPadding.config,RowMaskPositionParts.cfg,RowMaskPositionParts.tapes,
    RowMaskConsume.capacities,ZeroPadding.pad,Fin.addCases,hs,hi,hc0,hf,
    RowTupleCursorReady.start,UnaryTemplate.tape,List.replicate_succ]

theorem result_heads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ) :
    (P1CompactRowTupleCursorEquation.result gs p F w M rows ds pre tail out bound).heads=
      heads (pre.length+2*w*ds.length)
        (out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds))) := by
  have hp:=(fold_static rows ds (RowTupleCursorReady.start rows bound) rfl rfl rfl rfl).2.1
  funext i
  simp only [P1CompactRowTupleCursorEquation.result,RecoveryFocus.config,row_pick]
  fin_cases i
  all_goals first | rfl | skip
  all_goals simp [heads,P1CompactRowTupleCursorEquation.middle,RecoveryFocus.config,P1CompactRowTupleBlank.tuple_pick,
    RowTupleCursorReady.middleHeads,RowTupleCursorReady.after,RowTupleCursorReady.selected,
    RowTupleMaskLoop.cfg,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,RowTupleMaskBody.cfg,
    RowMaskLookupReusable.cfg,RowMaskPositionParts.heads,Fin.addCases,hp]

end NearCubicWires.RepairOrdinary.P1CompactRowTupleCursorLayout

/-! The three changing tuple fields fit the same actual source-derived
allocation already used by the equation consumer. This pays their physical
erasure without another runtime capacity. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleResetBounds
open RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem occurrence_length (N : ℕ) (is : List (Fin N)) :
    (P1CompactRowOccurrenceLoop.word is).length≤N*is.length := by
  induction is with
  | nil => simp [P1CompactRowOccurrenceLoop.word]
  | cons i is ih =>
    have hi:=i.isLt
    simp only [P1CompactRowOccurrenceLoop.word,List.flatMap_cons,List.length_append,
      RowIndexField.word,List.length_replicate,List.length_cons,List.length_nil] at *
    nlinarith

theorem fields_fit {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F : ℕ)
    (is : List (Fin gs.length)) (hF : P1CompactRowCommonBounds.capacity gs is.length p≤F) :
    n+3≤F ∧ (P1CompactRowOccurrenceLoop.word is).length≤F ∧ is.length+1≤F := by
  let S:=RowCachedCoordinateBounds.size gs (P1Radix.bits gs)
  have hn : n+1≤S := by
    have h : n+1≤(n+1)*(gs.length+1) := by nlinarith
    unfold S RowCachedCoordinateBounds.size
    omega
  have hN : gs.length≤S := by
    have h : gs.length+1≤(n+1)*(gs.length+1) := by nlinarith
    unfold S RowCachedCoordinateBounds.size
    omega
  have h1 : 1≤S := by omega
  have ha : S≤(is.length+1)*S := by nlinarith
  have hb : is.length+1≤(is.length+1)*S := by nlinarith
  have hc : gs.length*is.length≤(is.length+1)*S := by
    have h:=Nat.mul_le_mul_right is.length hN
    nlinarith
  have hcap : (is.length+1)*S+64≤F := by
    have h : (is.length+1)*S≤16384*(is.length+1)*S := by nlinarith
    unfold P1CompactRowCommonBounds.capacity at hF
    change 16384*(is.length+1)*S+16*p+64≤F at hF
    omega
  have hword:=occurrence_length gs.length is
  exact ⟨by omega,by omega,by omega⟩

end NearCubicWires.RepairOrdinary.P1CompactRowTupleResetBounds

/-! A reusable whole-tuple body: the actual selected digits produce the
common-width equation, then paid erasure restores all per-tuple fields.
The stream cursor advances and the equation append cursor stays live. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleCursorBody
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padding (F : ℕ) : Fin 48→ℕ := fun i=>if i=15 ∨ i=23 ∨ i=24 then F else 0
noncomputable def machine := Composition.machine P1CompactRowTupleCursorEquation.machine RowTupleCursorErase.machine
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out : List Bool) (bound : ℕ) :=
  (⟨machine.start,P1CompactRowTupleCursorLayout.heads pos out,
    fun i=>ZeroPadding.pad (padding F i) (P1CompactRowTupleCursorLayout.data gs 0 p F w M k rows tuple out bound [] i)⟩ : Configuration 48 _)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) := P1CompactRowTupleCursorEquation.budget gs F w M rows ds+2*F+9

theorem erase_pick (i : Fin 48) : RecoveryFocus.pick RowTupleCursorErase.eraseSlots i=
    if i=15 then some 0 else if i=23 then some 1 else if i=24 then some 2
    else if i=33 then some 3 else if i=34 then some 4 else none := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot _ RowTupleCursorErase.injective 0
    | exact RecoveryFocus.pick_slot _ RowTupleCursorErase.injective 1
    | exact RecoveryFocus.pick_slot _ RowTupleCursorErase.injective 2
    | exact RecoveryFocus.pick_slot _ RowTupleCursorErase.injective 3
    | exact RecoveryFocus.pick_slot _ RowTupleCursorErase.injective 4
    | decide

theorem cleared_data {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j p F w M k : ℕ)
    (rows : List (List Bool)) (tuple out : List Bool) (bound : ℕ) (is : List (Fin gs.length)) (hF:2≤F) :
    RowTupleCursorErase.cleared F
      (fun i=>ZeroPadding.pad (padding F i) (P1CompactRowTupleCursorLayout.data gs j p F w M k rows tuple out bound is i))=
      fun i=>ZeroPadding.pad (padding F i) (P1CompactRowTupleCursorLayout.data gs 0 p F w M k rows tuple out bound [] i) := by
  funext i
  simp only [RowTupleCursorErase.cleared,install,erase_pick]
  fin_cases i <;> simp [padding,RowTupleCursorErase.eraseInput,P1CompactRowTupleCursorLayout.data,
    P1CompactRowCommonReusable.data,Fin.addCases,ZeroPadding.pad,UnaryTemplate.tape,CompareMachine.word,
    P1CompactRowOccurrenceLoop.word]
  all_goals simp only [←List.replicate_succ]
  all_goals first | rfl | (congr 1; omega)

theorem tuple_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w M : ℕ)
    (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) (hQ : ds.length≤Q)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p) (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (budget gs F w M rows ds)
      (entry gs p F w M ds.length rows (pre++RowTupleFilterLoop.word w ds++tail) pre.length out bound)=some r ∧
      r.final.heads=(entry gs p F w M ds.length rows (pre++RowTupleFilterLoop.word w ds++tail)
        (pre.length+2*w*ds.length)
        (out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds)))
        (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound).heads ∧
      r.final.tapes=(entry gs p F w M ds.length rows (pre++RowTupleFilterLoop.word w ds++tail)
        (pre.length+2*w*ds.length)
        (out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds)))
        (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound).tapes ∧
      r.steps≤budget gs F w M rows ds := by
  have hcap:=P1CompactRowCommonFixedCapacity.tuple_capacity gs p F Q rows ds hl hd hQ hF
  have hpos : 2≤F := by have := P1CompactRowCommonBounds.padding_fits gs (gs.length*Q) p; omega
  have hinner:=(P1CompactRowCommonBounds.inner_fits gs (gs.length*Q) p).trans hF
  obtain ⟨base,hbase,bh,bt,bs⟩:=P1CompactRowTupleCursorEquation.equation_run gs p F Q w M rows ds pre tail out bound hl hd hb hM hQ hp hF
  obtain ⟨a,ha,af,as,_⟩:=ZeroPadding.run_config P1CompactRowTupleCursorEquation.machine (padding F) _ _ base hbase
  let output:=out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds))
  let lastBound:=(RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound
  have ah : a.final.heads=P1CompactRowTupleCursorLayout.heads (pre.length+2*w*ds.length) output := by
    rw [af]
    change base.final.heads=_
    rw [bh,P1CompactRowTupleCursorLayout.result_heads]
  have atapes : a.final.tapes=fun i=>ZeroPadding.pad (padding F i)
      (P1CompactRowTupleCursorLayout.data gs (n+1) p F w M ds.length rows
        (pre++RowTupleFilterLoop.word w ds++tail) output lastBound (indices gs.length rows ds) i) := by
    rw [af]
    change (fun i=>ZeroPadding.pad (padding F i) (base.final.tapes i))=_
    rw [bt,P1CompactRowTupleCursorLayout.result_tapes gs p F w M rows ds pre tail out bound (by omega) hinner]
  have fits:=P1CompactRowTupleResetBounds.fields_fit gs p F (indices gs.length rows ds) hcap
  obtain ⟨b,hbRun,bh',bt',_⟩:=RowTupleCursorErase.clear_run F a.final.heads a.final.tapes
    (by rw [ah]; rfl) (by rw [ah]; rfl) (by rw [ah]; rfl) (by rw [ah]; rfl) (by rw [ah]; rfl)
    (by
      intro i
      rw [atapes]
      fin_cases i
      · simpa [RowTupleCursorErase.workSlots,padding,P1CompactRowTupleCursorLayout.data,
          P1CompactRowCommonReusable.data,Fin.addCases,UnaryTemplate.tape] using (show n+1+1<F by omega)
      · simpa [RowTupleCursorErase.workSlots,padding,P1CompactRowTupleCursorLayout.data,
          P1CompactRowCommonReusable.data,Fin.addCases] using fits.2.1
      · simpa [RowTupleCursorErase.workSlots,padding,P1CompactRowTupleCursorLayout.data,
          P1CompactRowCommonReusable.data,Fin.addCases,CompareMachine.word] using fits.2.2)
    (by rw [atapes]; simp [padding,P1CompactRowTupleCursorLayout.data,P1CompactRowCommonReusable.data,Fin.addCases])
    (by rw [atapes]; simp [padding,P1CompactRowTupleCursorLayout.data,P1CompactRowCommonReusable.data,Fin.addCases])
  change runFrom RowTupleCursorErase.machine _ (Composition.restart a.final RowTupleCursorErase.machine.start)=some b at hbRun
  have whole:=Composition.run_join P1CompactRowTupleCursorEquation.machine RowTupleCursorErase.machine _ _ _ a b ha hbRun
  have inputEq : Composition.leftConfig 8
      (ZeroPadding.config (padding F) (P1CompactRowTupleCursorEquation.input gs p F w M rows ds pre tail out bound))=
      entry gs p F w M ds.length rows (pre++RowTupleFilterLoop.word w ds++tail) pre.length out bound := by
    apply configuration_ext
    · rfl
    · exact P1CompactRowTupleCursorLayout.input_heads gs p F w M rows ds pre tail out bound
    · change (fun i=>ZeroPadding.pad (padding F i) ((P1CompactRowTupleCursorEquation.input gs p F w M rows ds pre tail out bound).tapes i))=_
      rw [P1CompactRowTupleCursorLayout.input_tapes gs p F w M rows ds pre tail out bound (by omega) hinner]
      rfl
  rw [inputEq,show P1CompactRowTupleCursorEquation.budget gs F w M rows ds+1+(2*F+8)=budget gs F w M rows ds by unfold budget; omega] at whole
  refine ⟨Composition.joinedReceipt a b,whole,bh'.trans ah,?_,runFrom_steps_le machine _ _ _ whole⟩
  change b.final.tapes=_
  rw [bt',atapes,cleared_data gs (n+1) p F w M ds.length rows _ output lastBound _ hpos]
  rfl

end NearCubicWires.RepairOrdinary.P1CompactRowTupleCursorBody

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowTupleCursorBody_machine_unchanged : @P1CompactRowTupleCursorBody.machine = @RowTupleCursorBody.machine := rfl
end NearCubicWires.RepairOrdinary

/-! One actual enumerated frame executes through the complete reusable
equation body and its paid three-cell trailer. The next cursor is exactly
the end of that frame, including the zero-degree case. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleFramedBody
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def word (w : ℕ) (ds : List ℕ) := frame (SignedSortKey.binary (w*ds.length+1) (RowTupleDigits.encode w ds))
theorem word_length (w : ℕ) (ds : List ℕ) : (word w ds).length=2*w*ds.length+3 := by
  simp [word]
  ring
noncomputable def machine := Composition.machine P1CompactRowTupleCursorBody.machine RowTupleFrame.skip
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out : List Bool) (bound : ℕ) :=
  Composition.restart (P1CompactRowTupleCursorBody.entry gs p F w M k rows tuple pos out bound) machine.start
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) := P1CompactRowTupleCursorBody.budget gs F w M rows ds+4

theorem tuple_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w M : ℕ)
    (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) (hQ : ds.length≤Q)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p) (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (budget gs F w M rows ds)
      (entry gs p F w M ds.length rows (pre++word w ds++tail) pre.length out bound)=some r ∧
      r.final.heads=(entry gs p F w M ds.length rows (pre++word w ds++tail)
        (pre.length+(word w ds).length)
        (out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds)))
        (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound).heads ∧
      r.final.tapes=(entry gs p F w M ds.length rows (pre++word w ds++tail)
        (pre.length+(word w ds).length)
        (out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds)))
        (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound).tapes ∧
      r.steps≤budget gs F w M rows ds := by
  have hword : word w ds=RowTupleFilterLoop.word w ds++RowTupleFrame.trailer :=
    RowTupleFrame.encoded_word w ds (fun d hd'=>(hd d hd').trans hb)
  have htape : pre++word w ds++tail=pre++RowTupleFilterLoop.word w ds++(RowTupleFrame.trailer++tail) := by
    rw [hword]
    simp only [List.append_assoc]
  obtain ⟨a,ha,ah,atapes,_⟩:=P1CompactRowTupleCursorBody.tuple_run gs p F Q w M rows ds pre
    (RowTupleFrame.trailer++tail) out bound hl hd hb hM hQ hp hF
  rw [←htape] at ha ah atapes
  obtain ⟨b,hbRun,bh,bt,_⟩:=RowTupleFrame.skip_run a.final.heads a.final.tapes
  change runFrom RowTupleFrame.skip 3 (Composition.restart a.final RowTupleFrame.skip.start)=some b at hbRun
  have whole:=Composition.run_join P1CompactRowTupleCursorBody.machine RowTupleFrame.skip _ _ _ a b ha hbRun
  have budgetEq : P1CompactRowTupleCursorBody.budget gs F w M rows ds+1+3=budget gs F w M rows ds := by unfold budget; omega
  rw [budgetEq] at whole
  refine ⟨Composition.joinedReceipt a b,whole,?_,bt.trans atapes,runFrom_steps_le machine _ _ _ whole⟩
  change b.final.heads=_
  rw [bh,ah]
  funext i
  by_cases hi:i=44
  · subst i
    simp [entry,Composition.restart,P1CompactRowTupleCursorBody.entry,P1CompactRowTupleCursorLayout.heads,word_length]
    omega
  · simp [entry,Composition.restart,P1CompactRowTupleCursorBody.entry,P1CompactRowTupleCursorLayout.heads,hi]

end NearCubicWires.RepairOrdinary.P1CompactRowTupleFramedBody

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowTupleFramedBody_machine_unchanged : @P1CompactRowTupleFramedBody.machine = @RowTupleFramedBody.machine := rfl
end NearCubicWires.RepairOrdinary

/-! Execute every actual selected tuple frame, without a supplied unary
frame count. The physical stream marker controls entry and termination;
all equations append in the enumerator's exact occurrence order. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleList
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := StreamController.machine P1CompactRowTupleFramedBody.machine 44
noncomputable def cfg {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out : List Bool) (bound : ℕ) :=
  Composition.restart (P1CompactRowTupleFramedBody.entry gs p F w M k rows tuple pos out bound) q
def stream (w : ℕ) (xs : List (List ℕ)) := xs.flatMap (P1CompactRowTupleFramedBody.word w)
def output {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p : ℕ)
    (rows : List (List Bool)) (xs : List (List ℕ)) := xs.flatMap fun ds=>
  P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds))
def finalBound (rows : List (List Bool)) : List (List ℕ)→ℕ→ℕ
  | [],b=>b
  | ds::xs,b=>finalBound rows xs (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows b) ds).bound
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (F w M : ℕ)
    (rows : List (List Bool)) (xs : List (List ℕ)) :=
  (xs.map fun ds=>P1CompactRowTupleFramedBody.budget gs F w M rows ds+2).sum+1

theorem fields {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out : List Bool) (bound : ℕ) :
    (cfg q gs p F w M k rows tuple pos out bound).tapes 44=tuple ∧
      (cfg q gs p F w M k rows tuple pos out bound).heads 44=pos ∧
      (cfg q gs p F w M k rows tuple pos out bound).tapes 31=out ∧
      (cfg q gs p F w M k rows tuple pos out bound).heads 31=out.length := by
  simp [cfg,Composition.restart,P1CompactRowTupleFramedBody.entry,P1CompactRowTupleCursorBody.entry,
    P1CompactRowTupleCursorBody.padding,P1CompactRowTupleCursorLayout.heads,P1CompactRowTupleCursorLayout.data,
    P1CompactRowCommonReusable.data,Fin.addCases]

private theorem read_end (pre : List Bool) : readTapeBit pre pre.length=false := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simp [readTapeBit,List.getD]

private theorem read_frame (pre tail : List Bool) (w : ℕ) (ds : List ℕ) :
    readTapeBit (pre++P1CompactRowTupleFramedBody.word w ds++tail) pre.length=true := by
  simpa only [P1CompactRowTupleFramedBody.word,SignedSortKey.binary,frame,List.append_assoc,List.cons_append] using
    Streaming.read_append pre
      ((RowTupleDigits.encode w ds%2==1)::frame (SignedSortKey.binary (w*ds.length) (RowTupleDigits.encode w ds/2))++tail) true

private theorem round_run {t s : ℕ} (p : Machine t s) (tape : Fin t)
    (fuel tailFuel : ℕ) (c : Configuration t s) (body : ExecutionReceipt t s)
    (tail : ExecutionReceipt t (s+2)) (hc : c.control=p.start)
    (hread : c.scanned tape=true) (hbody : runFrom p fuel c=some body)
    (htail : runFrom (StreamController.machine p tape) tailFuel
      (controlConfig (fun _ => test s) body.final)=some tail) :
    ∃ r, runFrom (StreamController.machine p tape) (fuel+tailFuel+2)
      (controlConfig (fun _ => test s) c)=some r ∧ r.final=tail.final := by
  obtain ⟨bodyPrefix,halted⟩ := StreamController.body_prefix p tape fuel c body hbody
  let returned : ExecutionReceipt t (s+2) :=
    ⟨tail.final,tail.steps+1,max body.final.tapeCells tail.peakTapeCells⟩
  have hr : runFrom (StreamController.machine p tape) (tailFuel+1)
      (controlConfig code body.final)=some returned :=
    runFrom_step (StreamController.machine p tape) _ _ tail
      (StreamController.body_halted p tape _) (StreamController.return_step p tape _ halted) htail
  obtain ⟨middle,hm,hmf,_,_⟩ := bodyPrefix.followedBy returned hr
  have hrestart : Composition.restart c p.start=c := by
    cases c with
    | mk control heads tapes => cases hc; rfl
  have he := StreamController.enter_step p tape c hread
  rw [hrestart] at he
  let result : ExecutionReceipt t (s+2) :=
    ⟨middle.final,middle.steps+1,max c.tapeCells middle.peakTapeCells⟩
  have hrun : runFrom (StreamController.machine p tape) ((body.steps+(tailFuel+1))+1)
      (controlConfig (fun _ => test s) c)=some result :=
    runFrom_step (StreamController.machine p tape) _ _ middle
      (StreamController.test_halted p tape) he hm
  have hs := runFrom_steps_le p fuel c body hbody
  have hmore := runFrom_moreFuel (StreamController.machine p tape) _ (fuel-body.steps) _ result hrun
  have ht : ((body.steps+(tailFuel+1))+1)+(fuel-body.steps)=fuel+tailFuel+2 := by omega
  rw [ht] at hmore
  exact ⟨result,hmore,hmf⟩

theorem list_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w M k : ℕ)
    (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (xs : List (List ℕ)) (pre out : List Bool) (bound : ℕ)
    (hl : ∀ row∈rows,row.length=gs.length)
    (hk : ∀ ds∈xs,ds.length=k) (hd : ∀ ds∈xs,∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) (hQ : k≤Q)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p) (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (budget gs F w M rows xs)
      (cfg machine.start gs p F w M k rows (pre++stream w xs) pre.length out bound)=some r ∧
      r.final.heads=(cfg machine.start gs p F w M k rows (pre++stream w xs)
        (pre.length+(stream w xs).length) (out++output gs p rows xs) (finalBound rows xs bound)).heads ∧
      r.final.tapes=(cfg machine.start gs p F w M k rows (pre++stream w xs)
        (pre.length+(stream w xs).length) (out++output gs p rows xs) (finalBound rows xs bound)).tapes ∧
      r.steps≤budget gs F w M rows xs := by
  induction xs generalizing pre out bound with
  | nil =>
    let c:=P1CompactRowTupleFramedBody.entry gs p F w M k rows pre pre.length out bound
    have hr : c.scanned 44=false := by
      change readTapeBit (c.tapes 44) (c.heads 44)=false
      obtain ⟨ht,hh,_,_⟩:=fields P1CompactRowTupleFramedBody.machine.start gs p F w M k rows pre pre.length out bound
      change c.tapes 44=pre at ht
      change c.heads 44=pre.length at hh
      rw [ht,hh]
      exact read_end pre
    obtain ⟨r,hrun,rf,rs⟩:=(Timed.single (StreamController.test_halted P1CompactRowTupleFramedBody.machine 44)
      (StreamController.stop_step P1CompactRowTupleFramedBody.machine 44 c hr)).run
      (StreamController.stop_halted P1CompactRowTupleFramedBody.machine 44)
    refine ⟨r,?_,?_,?_,?_⟩
    · simpa only [budget,List.map_nil,List.sum_nil,stream,List.flatMap_nil,List.append_nil,
        cfg,machine,StreamController.machine,controlConfig,Composition.restart,c,Nat.zero_add] using hrun
    · rw [rf]
      simp only [cfg,Composition.restart,controlConfig,stream,List.flatMap_nil,List.length_nil,
        Nat.add_zero,List.append_nil,output,finalBound]
      rfl
    · rw [rf]
      simp only [cfg,Composition.restart,controlConfig,stream,List.flatMap_nil,List.length_nil,
        Nat.add_zero,List.append_nil,output,finalBound]
      rfl
    · simpa [budget] using rs.le
  | cons ds xs ih =>
    have hk0:=hk ds (by simp)
    have hd0:=hd ds (by simp)
    obtain ⟨a,ha,ah,atapes,_⟩:=P1CompactRowTupleFramedBody.tuple_run gs p F Q w M rows ds pre
      (stream w xs) out bound hl hd0 hb hM (hk0.trans_le hQ) hp hF
    rw [hk0] at ha ah atapes
    let nextOut:=out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds))
    let nextBound:=(RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound
    obtain ⟨b,hbRun,bh,bt,_⟩:=ih (pre++P1CompactRowTupleFramedBody.word w ds) nextOut nextBound
      (fun d hd'=>hk d (List.mem_cons_of_mem ds hd'))
      (fun d hd'=>hd d (List.mem_cons_of_mem ds hd'))
    have hnext : (controlConfig (fun _=>test _) a.final)=
        cfg machine.start gs p F w M k rows ((pre++P1CompactRowTupleFramedBody.word w ds)++stream w xs)
          (pre++P1CompactRowTupleFramedBody.word w ds).length nextOut nextBound := by
      apply configuration_ext
      · rfl
      · change a.final.heads=_
        rw [ah]
        simp only [cfg,Composition.restart,List.length_append,nextOut,nextBound]
      · change a.final.tapes=_
        rw [atapes]
        rfl
    rw [←hnext] at hbRun
    have hr : (P1CompactRowTupleFramedBody.entry gs p F w M k rows
        (pre++P1CompactRowTupleFramedBody.word w ds++stream w xs) pre.length out bound).scanned 44=true := by
      have hf:=fields P1CompactRowTupleFramedBody.machine.start gs p F w M k rows
        (pre++P1CompactRowTupleFramedBody.word w ds++stream w xs) pre.length out bound
      change readTapeBit
        ((cfg P1CompactRowTupleFramedBody.machine.start gs p F w M k rows
          (pre++P1CompactRowTupleFramedBody.word w ds++stream w xs) pre.length out bound).tapes 44)
        ((cfg P1CompactRowTupleFramedBody.machine.start gs p F w M k rows
          (pre++P1CompactRowTupleFramedBody.word w ds++stream w xs) pre.length out bound).heads 44)=true
      rw [hf.1,hf.2.1]
      exact read_frame pre (stream w xs) w ds
    obtain ⟨r,hRun,rf⟩:=round_run P1CompactRowTupleFramedBody.machine 44 _ _ _ a b rfl hr ha hbRun
    have htime : P1CompactRowTupleFramedBody.budget gs F w M rows ds+budget gs F w M rows xs+2=
        budget gs F w M rows (ds::xs) := by simp only [budget,List.map_cons,List.sum_cons]; omega
    rw [htime] at hRun
    refine ⟨r,?_,?_,?_,?_⟩
    · simpa only [machine,StreamController.machine,cfg,Composition.restart,controlConfig,stream,List.flatMap_cons,List.append_assoc] using hRun
    · rw [rf,bh]
      simp only [cfg,Composition.restart,stream,output,List.flatMap_cons,List.length_append,
        finalBound,nextOut,nextBound,List.append_assoc,Nat.add_assoc]
    · rw [rf,bt]
      simp only [cfg,Composition.restart,stream,output,List.flatMap_cons,List.length_append,
        finalBound,nextOut,nextBound,List.append_assoc,Nat.add_assoc]
    · exact runFrom_steps_le machine _ _ _ (by
        simpa only [machine,StreamController.machine,cfg,Composition.restart,controlConfig,stream,List.flatMap_cons,List.append_assoc] using hRun)

end NearCubicWires.RepairOrdinary.P1CompactRowTupleList

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowTupleList_machine_unchanged : @P1CompactRowTupleList.machine = @RowTupleList.machine := rfl
end NearCubicWires.RepairOrdinary

/-! The complete equation list consumes the actual checked enumeration
order. Width and validity of every tuple are discharged from the filter;
no selected tuple list or occurrence multiplicity is changed. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleSelectedList
open LocalBitMultitape RepairRepresentation
open RowTupleSubsets RowTupleDigits P1CompactRowTupleList
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem selected_fields (w M k : ℕ) (ds : List ℕ) (hd:ds∈selected w M k) :
    ds.length=k ∧ ∀ d∈ds,d<M := by
  obtain ⟨hc,hv⟩:=List.mem_filter.mp hd
  exact ⟨((candidates_mem w k ds).mp hc).1,((valid_iff M ds).mp hv).2⟩

theorem stream_eq (w M k : ℕ) : stream w (selected w M k)=RowTupleEnumeration.word w k M := by
  unfold stream RowTupleEnumeration.word
  have h : ∀ xs : List (List ℕ),(∀ ds∈xs,ds.length=k) →
      xs.flatMap (P1CompactRowTupleFramedBody.word w)=xs.flatMap (fun ds=>frame (SignedSortKey.binary (w*k+1) (encode w ds))) := by
    intro xs hx
    induction xs with
    | nil => rfl
    | cons ds xs ih =>
      simp only [List.flatMap_cons,P1CompactRowTupleFramedBody.word,hx ds (by simp)]
      rw [ih (fun d hd=>hx d (List.mem_cons_of_mem ds hd))]
  exact h _ (fun ds hd=>(selected_fields w M k ds hd).1)

theorem selected_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w k : ℕ)
    (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hw:rows.length<2^w) (hk:k≤Q)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p) (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom P1CompactRowTupleList.machine
      (P1CompactRowTupleList.budget gs F w rows.length rows (selected w rows.length k))
      (cfg P1CompactRowTupleList.machine.start gs p F w rows.length k rows (RowTupleEnumeration.word w k rows.length) 0 out 0)=some r ∧
      r.final.tapes 31=out++output gs p rows (selected w rows.length k) ∧
      r.final.heads 31=(out++output gs p rows (selected w rows.length k)).length ∧
      r.steps≤P1CompactRowTupleList.budget gs F w rows.length rows (selected w rows.length k) := by
  obtain ⟨r,hr,rh,rt,rs⟩:=list_run gs p F Q w rows.length k rows (selected w rows.length k) [] out 0
    hl (fun ds hd=>(selected_fields w rows.length k ds hd).1)
    (fun ds hd=>(selected_fields w rows.length k ds hd).2) hw le_rfl hk hp hF
  simp only [List.nil_append,List.length_nil,Nat.zero_add,stream_eq] at hr rh rt
  refine ⟨r,hr,?_,?_,rs⟩
  · rw [rt]
    exact (fields P1CompactRowTupleList.machine.start gs p F w rows.length k rows _ _ _ _).2.2.1
  · rw [rh]
    exact (fields P1CompactRowTupleList.machine.start gs p F w rows.length k rows _ _ _ _).2.2.2

end NearCubicWires.RepairOrdinary.P1CompactRowTupleSelectedList

/-! The actual binary producer, paid output rewind, and complete selected
list consumer share one tuple tape. No tuple bytes or unary tuple count
are supplied at input. Native cache and common metadata remain retained. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleEnumeratedEquations
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
noncomputable def last := RecoveryFocus.machine rowSlots P1CompactRowTupleList.machine
noncomputable def machine := Composition.machine first last

def extra (w k M : ℕ) : Fin 40→List Bool := fun i=>
  if i=2 then CompareMachine.word w else if i=3 then frame (SignedSortKey.binary w (M-1))
    else if i=12 then CompareMachine.word k else if i=17 then List.replicate w true else []
noncomputable def input {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w k : ℕ)
    (rows : List (List Bool)) (out : List Bool) :=
  TapeEmbedding.config (fun _ : Fin 40=>0) (extra w k rows.length)
    (P1CompactRowTupleList.cfg q gs p F w rows.length k rows [] 0 out 0)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (F w k : ℕ) (rows : List (List Bool)) :=
  RowTupleEnumerationReady.budget w k+1+
    P1CompactRowTupleList.budget gs F w rows.length rows (RowTupleSubsets.selected w rows.length k)

theorem enum_pick (i : Fin 48) : RecoveryFocus.pick enumSlots (rowSlots i)=
    if i=44 then some 17 else none := by
  fin_cases i
  all_goals first | exact RecoveryFocus.pick_slot enumSlots enum_injective 17 | decide

private theorem core_heads {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w k : ℕ)
    (rows : List (List Bool)) (tuple out : List Bool) :
    (P1CompactRowTupleList.cfg q gs p F w rows.length k rows tuple 0 out 0).heads=P1CompactRowTupleCursorLayout.heads 0 out := by rfl
private theorem core_tapes {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w k : ℕ)
    (rows : List (List Bool)) (tuple out : List Bool) :
    (P1CompactRowTupleList.cfg q gs p F w rows.length k rows tuple 0 out 0).tapes=
      fun i=>ZeroPadding.pad (P1CompactRowTupleCursorBody.padding F i)
        (P1CompactRowTupleCursorLayout.data gs 0 p F w rows.length k rows tuple out 0 [] i) := by rfl
private theorem vector_away {α : Type} (a b c d e f g h x y i j k : α) (ix : Fin 12) (hi:ix.val≠8) :
    (![a,b,c,d,e,f,g,h,x,i,j,k] : Fin 12→α) ix=![a,b,c,d,e,f,g,h,y,i,j,k] ix := by
  fin_cases ix <;> simp_all
private theorem data_away {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w k : ℕ)
    (rows : List (List Bool)) (left right out : List Bool) (i : Fin 48) (hi:i≠44) :
    P1CompactRowTupleCursorLayout.data gs 0 p F w rows.length k rows left out 0 [] i=
      P1CompactRowTupleCursorLayout.data gs 0 p F w rows.length k rows right out 0 [] i := by
  revert hi
  refine Fin.addCases (m:=36) (n:=12) (fun j=>?_) (fun j=>?_) i
  · intro _
    simp only [P1CompactRowTupleCursorLayout.data,Fin.addCases_left]
  · intro hi
    simp only [P1CompactRowTupleCursorLayout.data,Fin.addCases_right]
    apply vector_away
    intro hj
    apply hi
    apply Fin.ext
    simpa only [Fin.val_natAdd,hj] using (show 36+8=(44:Fin 48).val from rfl)

theorem equation_list_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w k : ℕ)
    (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM:0<rows.length) (hw:rows.length<2^w) (hk:k≤Q)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p) (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (budget gs F w k rows) (input machine.start gs p F w k rows out)=some r ∧
      r.final.tapes (rowSlots 31)=out++P1CompactRowTupleList.output gs p rows (RowTupleSubsets.selected w rows.length k) ∧
      r.final.heads (rowSlots 31)=(out++P1CompactRowTupleList.output gs p rows (RowTupleSubsets.selected w rows.length k)).length ∧
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
  obtain ⟨row,hr,rt,rh,_⟩:=P1CompactRowTupleSelectedList.selected_run gs p F Q w k rows out hl hw hk hp hF
  obtain ⟨b,hbRun,bf,_⟩:=RecoveryFocus.run_config rowSlots row_injective P1CompactRowTupleList.machine
    a.final.heads a.final.tapes _ _ row hr
  have hj : RecoveryFocus.config rowSlots a.final.heads a.final.tapes
      (P1CompactRowTupleList.cfg P1CompactRowTupleList.machine.start gs p F w rows.length k rows
        (RowTupleEnumeration.word w k rows.length) 0 out 0)=Composition.restart a.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [af]
      simp only [RecoveryFocus.config,enum_pick]
      by_cases h44:i=44
      · subst i
        simp only [ite_true,bh]
        exact (P1CompactRowTupleList.fields P1CompactRowTupleList.machine.start gs p F w rows.length k rows _ 0 out 0).2.1.symm
      · simp only [h44,ite_false,ambient,input,TapeEmbedding.config,rowSlots,Fin.addCases_left,core_heads]
    · intro i
      rw [af]
      simp only [RecoveryFocus.config,enum_pick]
      by_cases h44:i=44
      · subst i
        simp only [ite_true,bt]
        exact (P1CompactRowTupleList.fields P1CompactRowTupleList.machine.start gs p F w rows.length k rows _ 0 out 0).1.symm
      · simp only [h44,ite_false,ambient,input,TapeEmbedding.config,rowSlots,Fin.addCases_left,core_tapes]
        exact congrArg (ZeroPadding.pad (P1CompactRowTupleCursorBody.padding F i)) (data_away gs p F w k rows [] _ out i h44)
  rw [hj] at hbRun
  have whole:=Composition.run_join first last _ _ _ a b ha hbRun
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,runFrom_steps_le machine _ _ _ whole⟩
  · change b.final.tapes (rowSlots 31)=_
    rw [bf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective] using rt
  · change b.final.heads (rowSlots 31)=_
    rw [bf]
    simpa only [RecoveryFocus.config,RecoveryFocus.pick_slot rowSlots row_injective] using rh

end NearCubicWires.RepairOrdinary.P1CompactRowTupleEnumeratedEquations

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowTupleEnumeratedEquations_machine_unchanged : @P1CompactRowTupleEnumeratedEquations.machine = @RowTupleEnumeratedEquations.machine := rfl
end NearCubicWires.RepairOrdinary

/-! The actual tuple consumer emits the complete signed cut: all equation
coordinates, its threshold, then the cached binLift coefficient. The cache
is retained at head zero while the row append cursor stays live. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleCutBody
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 1 P1CompactRowTupleFramedBody.machine
noncomputable def machine := Composition.machine first RowTupleCutAppend.machine
noncomputable def entry {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out : List Bool) (bound : ℕ) (coefficient : ℤ) :=
  TapeEmbedding.config (fun _ : Fin 1=>0) (fun _ : Fin 1=>frame (MatrixScoreBatch.signMagnitude p coefficient))
    (P1CompactRowTupleList.cfg q gs p F w M k rows tuple pos out bound)
def word {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p : ℕ) (rows : List (List Bool)) (ds : List ℕ)
    (coefficient : ℤ) :=
  P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds))++
    frame (MatrixScoreBatch.signMagnitude p coefficient)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) := P1CompactRowTupleFramedBody.budget gs F w M rows ds+4*p+9

theorem fields {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out : List Bool) (bound : ℕ) (coefficient : ℤ) :
    (entry q gs p F w M k rows tuple pos out bound coefficient).heads 48=0 ∧
      (entry q gs p F w M k rows tuple pos out bound coefficient).heads 31=out.length ∧
      (entry q gs p F w M k rows tuple pos out bound coefficient).heads 34=0 ∧
      (entry q gs p F w M k rows tuple pos out bound coefficient).tapes 48=frame (MatrixScoreBatch.signMagnitude p coefficient) ∧
      (entry q gs p F w M k rows tuple pos out bound coefficient).tapes 31=out ∧
      (entry q gs p F w M k rows tuple pos out bound coefficient).tapes 34=List.replicate (F+1) false := by
  simp [entry,TapeEmbedding.config,P1CompactRowTupleList.cfg,P1CompactRowTupleFramedBody.entry,Composition.restart,
    P1CompactRowTupleCursorBody.entry,P1CompactRowTupleCursorBody.padding,P1CompactRowTupleCursorLayout.data,P1CompactRowTupleCursorLayout.heads,
    P1CompactRowCommonReusable.data,Fin.addCases]

private theorem output_heads {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out next : List Bool) (bound : ℕ) (coefficient : ℤ) :
    Function.update (entry q gs p F w M k rows tuple pos out bound coefficient).heads 31 next.length=
      (entry q gs p F w M k rows tuple pos next bound coefficient).heads := by
  funext i
  fin_cases i <;> simp [entry,TapeEmbedding.config,P1CompactRowTupleList.cfg,P1CompactRowTupleFramedBody.entry,Composition.restart,
    P1CompactRowTupleCursorBody.entry,P1CompactRowTupleCursorLayout.heads,Fin.addCases]
private theorem output_tapes {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out next : List Bool) (bound : ℕ) (coefficient : ℤ) :
    Function.update (entry q gs p F w M k rows tuple pos out bound coefficient).tapes 31 next=
      (entry q gs p F w M k rows tuple pos next bound coefficient).tapes := by
  funext i
  fin_cases i <;> simp [entry,TapeEmbedding.config,P1CompactRowTupleList.cfg,P1CompactRowTupleFramedBody.entry,Composition.restart,
    P1CompactRowTupleCursorBody.entry,P1CompactRowTupleCursorBody.padding,P1CompactRowTupleCursorLayout.data,P1CompactRowCommonReusable.data,Fin.addCases]

theorem tuple_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w M : ℕ)
    (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (ds : List ℕ) (pre tail out : List Bool) (bound : ℕ) (coefficient : ℤ)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) (hQ : ds.length≤Q)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p) (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (budget gs p F w M rows ds)
      (entry machine.start gs p F w M ds.length rows (pre++P1CompactRowTupleFramedBody.word w ds++tail) pre.length out bound coefficient)=some r ∧
      r.final.heads=(entry machine.start gs p F w M ds.length rows (pre++P1CompactRowTupleFramedBody.word w ds++tail)
        (pre.length+(P1CompactRowTupleFramedBody.word w ds).length) (out++word gs p rows ds coefficient)
        (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound coefficient).heads ∧
      r.final.tapes=(entry machine.start gs p F w M ds.length rows (pre++P1CompactRowTupleFramedBody.word w ds++tail)
        (pre.length+(P1CompactRowTupleFramedBody.word w ds).length) (out++word gs p rows ds coefficient)
        (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound coefficient).tapes ∧
      r.steps≤budget gs p F w M rows ds := by
  obtain ⟨base,hbase,bh,bt,_⟩:=P1CompactRowTupleFramedBody.tuple_run gs p F Q w M rows ds pre tail out bound hl hd hb hM hQ hp hF
  let a:=TapeEmbedding.receipt (fun _ : Fin 1=>0) (fun _ : Fin 1=>frame (MatrixScoreBatch.signMagnitude p coefficient)) base
  have ha:=TapeEmbedding.run_embed P1CompactRowTupleFramedBody.machine (fun _ : Fin 1=>0)
    (fun _ : Fin 1=>frame (MatrixScoreBatch.signMagnitude p coefficient)) _ _ base hbase
  let next:=entry first.start gs p F w M ds.length rows (pre++P1CompactRowTupleFramedBody.word w ds++tail)
    (pre.length+(P1CompactRowTupleFramedBody.word w ds).length)
    (out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds)))
    (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound coefficient
  have ah : a.final.heads=next.heads := by
    change Fin.addCases (m:=48) (n:=1) (motive:=fun _=>ℕ) base.final.heads (fun _=>0)=_
    rw [bh]
    rfl
  have atapes : a.final.tapes=next.tapes := by
    change Fin.addCases (m:=48) (n:=1) (motive:=fun _=>List Bool) base.final.tapes
      (fun _=>frame (MatrixScoreBatch.signMagnitude p coefficient))=_
    rw [bt]
    rfl
  have cap : 2*(MatrixScoreBatch.signMagnitude p coefficient).length+1≤F+1 := by
    have h:=P1CompactRowCommonBounds.padding_fits gs (gs.length*Q) p
    simp only [MatrixScoreBatch.signMagnitude,List.length_cons,SignedSortKey.binary_length]
    omega
  have hf:=fields first.start gs p F w M ds.length rows (pre++P1CompactRowTupleFramedBody.word w ds++tail)
    (pre.length+(P1CompactRowTupleFramedBody.word w ds).length)
    (out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds)))
    (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound coefficient
  obtain ⟨b,hbRun,bh',bt',_⟩:=RowTupleCutAppend.append_run (MatrixScoreBatch.signMagnitude p coefficient)
    (out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs (indices gs.length rows ds)))
    (F+1) a.final.heads a.final.tapes cap (by rw [ah]; exact hf.1) (by rw [ah]; exact hf.2.1)
    (by rw [ah]; exact hf.2.2.1) (by rw [atapes]; exact hf.2.2.2.1)
    (by rw [atapes]; exact hf.2.2.2.2.1) (by rw [atapes]; exact hf.2.2.2.2.2)
  change runFrom RowTupleCutAppend.machine _ (Composition.restart a.final RowTupleCutAppend.machine.start)=some b at hbRun
  have whole:=Composition.run_join first RowTupleCutAppend.machine _ _ _ a b ha hbRun
  have timeEq : P1CompactRowTupleFramedBody.budget gs F w M rows ds+1+
      (4*(MatrixScoreBatch.signMagnitude p coefficient).length+4)=budget gs p F w M rows ds := by
    simp only [MatrixScoreBatch.signMagnitude,List.length_cons,SignedSortKey.binary_length,budget]
    omega
  rw [timeEq] at whole
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,runFrom_steps_le machine _ _ _ whole⟩
  · change b.final.heads=_
    rw [bh',ah]
    simpa only [next,word,entry,TapeEmbedding.config,P1CompactRowTupleList.cfg,P1CompactRowTupleFramedBody.entry,Composition.restart,List.append_assoc]
      using output_heads first.start gs p F w M ds.length rows _ _ _ _ _ coefficient
  · change b.final.tapes=_
    rw [bt',atapes]
    simpa only [next,word,entry,TapeEmbedding.config,P1CompactRowTupleList.cfg,P1CompactRowTupleFramedBody.entry,Composition.restart,List.append_assoc]
      using output_tapes first.start gs p F w M ds.length rows _ _ _ _ _ coefficient

end NearCubicWires.RepairOrdinary.P1CompactRowTupleCutBody

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowTupleCutBody_machine_unchanged : @P1CompactRowTupleCutBody.machine = @RowTupleCutBody.machine := rfl
end NearCubicWires.RepairOrdinary

/-! The actual selected tuple stream emits every complete signed cut,
reusing one cached coefficient and retaining the whole-row append cursor. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowTupleCutList
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding P1CompactRowTupleCommonEquation
open RecordController (code test stop)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := StreamController.machine P1CompactRowTupleCutBody.machine 44
noncomputable def cfg {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out : List Bool) (bound : ℕ) (coefficient : ℤ) :=
  P1CompactRowTupleCutBody.entry q gs p F w M k rows tuple pos out bound coefficient
def stream (w : ℕ) (xs : List (List ℕ)) := xs.flatMap (P1CompactRowTupleFramedBody.word w)
def output {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p : ℕ)
    (rows : List (List Bool)) (xs : List (List ℕ)) (coefficient : ℤ) := xs.flatMap fun ds=>
  P1CompactRowTupleCutBody.word gs p rows ds coefficient
def finalBound (rows : List (List Bool)) : List (List ℕ)→ℕ→ℕ
  | [],b=>b
  | ds::xs,b=>finalBound rows xs (RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows b) ds).bound
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M : ℕ)
    (rows : List (List Bool)) (xs : List (List ℕ)) :=
  (xs.map fun ds=>P1CompactRowTupleCutBody.budget gs p F w M rows ds+2).sum+1

theorem fields {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w M k : ℕ)
    (rows : List (List Bool)) (tuple : List Bool) (pos : ℕ) (out : List Bool) (bound : ℕ) (coefficient : ℤ) :
    (cfg q gs p F w M k rows tuple pos out bound coefficient).tapes 44=tuple ∧
      (cfg q gs p F w M k rows tuple pos out bound coefficient).heads 44=pos ∧
      (cfg q gs p F w M k rows tuple pos out bound coefficient).tapes 31=out ∧
      (cfg q gs p F w M k rows tuple pos out bound coefficient).heads 31=out.length := by
  simp [cfg,P1CompactRowTupleCutBody.entry,TapeEmbedding.config,Composition.restart,P1CompactRowTupleList.cfg,P1CompactRowTupleFramedBody.entry,P1CompactRowTupleCursorBody.entry,
    P1CompactRowTupleCursorBody.padding,P1CompactRowTupleCursorLayout.heads,P1CompactRowTupleCursorLayout.data,
    P1CompactRowCommonReusable.data,Fin.addCases]

private theorem read_end (pre : List Bool) : readTapeBit pre pre.length=false := by
  induction pre with
  | nil => rfl
  | cons b pre ih => simp [readTapeBit,List.getD]

private theorem read_frame (pre tail : List Bool) (w : ℕ) (ds : List ℕ) :
    readTapeBit (pre++P1CompactRowTupleFramedBody.word w ds++tail) pre.length=true := by
  simpa only [P1CompactRowTupleFramedBody.word,SignedSortKey.binary,frame,List.append_assoc,List.cons_append] using
    Streaming.read_append pre
      ((RowTupleDigits.encode w ds%2==1)::frame (SignedSortKey.binary (w*ds.length) (RowTupleDigits.encode w ds/2))++tail) true

private theorem round_run {t s : ℕ} (p : Machine t s) (tape : Fin t)
    (fuel tailFuel : ℕ) (c : Configuration t s) (body : ExecutionReceipt t s)
    (tail : ExecutionReceipt t (s+2)) (hc : c.control=p.start)
    (hread : c.scanned tape=true) (hbody : runFrom p fuel c=some body)
    (htail : runFrom (StreamController.machine p tape) tailFuel
      (controlConfig (fun _ => test s) body.final)=some tail) :
    ∃ r, runFrom (StreamController.machine p tape) (fuel+tailFuel+2)
      (controlConfig (fun _ => test s) c)=some r ∧ r.final=tail.final := by
  obtain ⟨bodyPrefix,halted⟩ := StreamController.body_prefix p tape fuel c body hbody
  let returned : ExecutionReceipt t (s+2) :=
    ⟨tail.final,tail.steps+1,max body.final.tapeCells tail.peakTapeCells⟩
  have hr : runFrom (StreamController.machine p tape) (tailFuel+1)
      (controlConfig code body.final)=some returned :=
    runFrom_step (StreamController.machine p tape) _ _ tail
      (StreamController.body_halted p tape _) (StreamController.return_step p tape _ halted) htail
  obtain ⟨middle,hm,hmf,_,_⟩ := bodyPrefix.followedBy returned hr
  have hrestart : Composition.restart c p.start=c := by
    cases c with
    | mk control heads tapes => cases hc; rfl
  have he := StreamController.enter_step p tape c hread
  rw [hrestart] at he
  let result : ExecutionReceipt t (s+2) :=
    ⟨middle.final,middle.steps+1,max c.tapeCells middle.peakTapeCells⟩
  have hrun : runFrom (StreamController.machine p tape) ((body.steps+(tailFuel+1))+1)
      (controlConfig (fun _ => test s) c)=some result :=
    runFrom_step (StreamController.machine p tape) _ _ middle
      (StreamController.test_halted p tape) he hm
  have hs := runFrom_steps_le p fuel c body hbody
  have hmore := runFrom_moreFuel (StreamController.machine p tape) _ (fuel-body.steps) _ result hrun
  have ht : ((body.steps+(tailFuel+1))+1)+(fuel-body.steps)=fuel+tailFuel+2 := by omega
  rw [ht] at hmore
  exact ⟨result,hmore,hmf⟩

theorem list_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w M k : ℕ)
    (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (xs : List (List ℕ)) (pre out : List Bool) (bound : ℕ) (coefficient : ℤ)
    (hl : ∀ row∈rows,row.length=gs.length)
    (hk : ∀ ds∈xs,ds.length=k) (hd : ∀ ds∈xs,∀ d∈ds,d<rows.length)
    (hb : rows.length<2^w) (hM : rows.length≤M) (hQ : k≤Q)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p) (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ r,runFrom machine (budget gs p F w M rows xs)
      (cfg machine.start gs p F w M k rows (pre++stream w xs) pre.length out bound coefficient)=some r ∧
      r.final.heads=(cfg machine.start gs p F w M k rows (pre++stream w xs)
        (pre.length+(stream w xs).length) (out++output gs p rows xs coefficient) (finalBound rows xs bound) coefficient).heads ∧
      r.final.tapes=(cfg machine.start gs p F w M k rows (pre++stream w xs)
        (pre.length+(stream w xs).length) (out++output gs p rows xs coefficient) (finalBound rows xs bound) coefficient).tapes ∧
      r.steps≤budget gs p F w M rows xs := by
  induction xs generalizing pre out bound with
  | nil =>
    let c:=P1CompactRowTupleCutBody.entry P1CompactRowTupleCutBody.machine.start gs p F w M k rows pre pre.length out bound coefficient
    have hr : c.scanned 44=false := by
      change readTapeBit (c.tapes 44) (c.heads 44)=false
      obtain ⟨ht,hh,_,_⟩:=fields P1CompactRowTupleCutBody.machine.start gs p F w M k rows pre pre.length out bound coefficient
      change c.tapes 44=pre at ht
      change c.heads 44=pre.length at hh
      rw [ht,hh]
      exact read_end pre
    obtain ⟨r,hrun,rf,rs⟩:=(Timed.single (StreamController.test_halted P1CompactRowTupleCutBody.machine 44)
      (StreamController.stop_step P1CompactRowTupleCutBody.machine 44 c hr)).run
      (StreamController.stop_halted P1CompactRowTupleCutBody.machine 44)
    refine ⟨r,?_,?_,?_,?_⟩
    · simpa only [budget,List.map_nil,List.sum_nil,stream,List.flatMap_nil,List.append_nil,
        cfg,P1CompactRowTupleCutBody.entry,TapeEmbedding.config,P1CompactRowTupleList.cfg,P1CompactRowTupleFramedBody.entry,
        machine,StreamController.machine,controlConfig,Composition.restart,c,Nat.zero_add] using hrun
    · rw [rf]
      simp only [cfg,P1CompactRowTupleCutBody.entry,P1CompactRowTupleList.cfg,P1CompactRowTupleFramedBody.entry,Composition.restart,TapeEmbedding.config,controlConfig,stream,List.flatMap_nil,List.length_nil,
        Nat.add_zero,List.append_nil,output,finalBound]
      rfl
    · rw [rf]
      simp only [cfg,P1CompactRowTupleCutBody.entry,P1CompactRowTupleList.cfg,P1CompactRowTupleFramedBody.entry,Composition.restart,TapeEmbedding.config,controlConfig,stream,List.flatMap_nil,List.length_nil,
        Nat.add_zero,List.append_nil,output,finalBound]
      rfl
    · simpa [budget] using rs.le
  | cons ds xs ih =>
    have hk0:=hk ds (by simp)
    have hd0:=hd ds (by simp)
    obtain ⟨a,ha,ah,atapes,_⟩:=P1CompactRowTupleCutBody.tuple_run gs p F Q w M rows ds pre
      (stream w xs) out bound coefficient hl hd0 hb hM (hk0.trans_le hQ) hp hF
    rw [hk0] at ha ah atapes
    let nextOut:=out++P1CompactRowTupleCutBody.word gs p rows ds coefficient
    let nextBound:=(RowTupleMaskLoop.fold rows (RowTupleCursorReady.start rows bound) ds).bound
    obtain ⟨b,hbRun,bh,bt,_⟩:=ih (pre++P1CompactRowTupleFramedBody.word w ds) nextOut nextBound
      (fun d hd'=>hk d (List.mem_cons_of_mem ds hd'))
      (fun d hd'=>hd d (List.mem_cons_of_mem ds hd'))
    have hnext : (controlConfig (fun _=>test _) a.final)=
        cfg machine.start gs p F w M k rows ((pre++P1CompactRowTupleFramedBody.word w ds)++stream w xs)
          (pre++P1CompactRowTupleFramedBody.word w ds).length nextOut nextBound coefficient := by
      apply configuration_ext
      · rfl
      · change a.final.heads=_
        rw [ah]
        simp only [cfg,P1CompactRowTupleCutBody.entry,TapeEmbedding.config,P1CompactRowTupleList.cfg,P1CompactRowTupleFramedBody.entry,Composition.restart,List.length_append,nextOut,nextBound]
      · change a.final.tapes=_
        rw [atapes]
        rfl
    rw [←hnext] at hbRun
    have hr : (P1CompactRowTupleCutBody.entry P1CompactRowTupleCutBody.machine.start gs p F w M k rows
        (pre++P1CompactRowTupleFramedBody.word w ds++stream w xs) pre.length out bound coefficient).scanned 44=true := by
      have hf:=fields P1CompactRowTupleCutBody.machine.start gs p F w M k rows
        (pre++P1CompactRowTupleFramedBody.word w ds++stream w xs) pre.length out bound coefficient
      change readTapeBit
        ((cfg P1CompactRowTupleCutBody.machine.start gs p F w M k rows
          (pre++P1CompactRowTupleFramedBody.word w ds++stream w xs) pre.length out bound coefficient).tapes 44)
        ((cfg P1CompactRowTupleCutBody.machine.start gs p F w M k rows
          (pre++P1CompactRowTupleFramedBody.word w ds++stream w xs) pre.length out bound coefficient).heads 44)=true
      rw [hf.1,hf.2.1]
      exact read_frame pre (stream w xs) w ds
    obtain ⟨r,hRun,rf⟩:=round_run P1CompactRowTupleCutBody.machine 44 _ _ _ a b rfl hr ha hbRun
    have htime : P1CompactRowTupleCutBody.budget gs p F w M rows ds+budget gs p F w M rows xs+2=
        budget gs p F w M rows (ds::xs) := by simp only [budget,List.map_cons,List.sum_cons]; omega
    rw [htime] at hRun
    refine ⟨r,?_,?_,?_,?_⟩
    · simpa only [machine,StreamController.machine,cfg,P1CompactRowTupleCutBody.entry,TapeEmbedding.config,P1CompactRowTupleList.cfg,P1CompactRowTupleFramedBody.entry,Composition.restart,controlConfig,stream,List.flatMap_cons,List.append_assoc] using hRun
    · rw [rf,bh]
      simp only [cfg,P1CompactRowTupleCutBody.entry,TapeEmbedding.config,P1CompactRowTupleList.cfg,P1CompactRowTupleFramedBody.entry,Composition.restart,stream,output,List.flatMap_cons,List.length_append,
        finalBound,nextOut,nextBound,List.append_assoc,Nat.add_assoc]
    · rw [rf,bt]
      simp only [cfg,P1CompactRowTupleCutBody.entry,TapeEmbedding.config,P1CompactRowTupleList.cfg,P1CompactRowTupleFramedBody.entry,Composition.restart,stream,output,List.flatMap_cons,List.length_append,
        finalBound,nextOut,nextBound,List.append_assoc,Nat.add_assoc]
    · exact runFrom_steps_le machine _ _ _ (by
        simpa only [machine,StreamController.machine,cfg,P1CompactRowTupleCutBody.entry,TapeEmbedding.config,P1CompactRowTupleList.cfg,P1CompactRowTupleFramedBody.entry,Composition.restart,controlConfig,stream,List.flatMap_cons,List.append_assoc] using hRun)

end NearCubicWires.RepairOrdinary.P1CompactRowTupleCutList

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowTupleCutList_machine_unchanged : @P1CompactRowTupleCutList.machine = @RowTupleCutList.machine := rfl
end NearCubicWires.RepairOrdinary

/-! The actual binary subset producer hands its rewound tuple stream to the
complete signed-cut consumer. One coefficient is retained for the whole
degree; coordinates and threshold are followed by that coefficient. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsEnumeratedCuts
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
noncomputable def last := RecoveryFocus.machine rowSlots P1CompactRowTupleCutList.machine
noncomputable def machine := Composition.machine first last

def core {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w k : ℕ) (rows : List (List Bool)) (tuple : List Bool)
    (pos : ℕ) (out : List Bool) (bound : ℕ) (coefficient : ℤ) : Configuration 49 s :=
  ⟨q,Fin.addCases (m:=48) (n:=1) (motive:=fun _ => ℕ)
      (P1CompactRowTupleCursorLayout.heads pos out) (fun _ : Fin 1 => 0),
    Fin.addCases (m:=48) (n:=1) (motive:=fun _ => List Bool)
      (fun i => ZeroPadding.pad (P1CompactRowTupleCursorBody.padding F i)
        (P1CompactRowTupleCursorLayout.data gs 0 p F w rows.length k rows tuple out bound [] i))
      (fun _ : Fin 1 => frame (MatrixScoreBatch.signMagnitude p coefficient))⟩

theorem cfg_eq {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w k : ℕ) (rows : List (List Bool)) (tuple : List Bool)
    (pos : ℕ) (out : List Bool) (bound : ℕ) (coefficient : ℤ) :
    P1CompactRowTupleCutList.cfg q gs p F w rows.length k rows tuple pos out bound coefficient=
      core q gs p F w k rows tuple pos out bound coefficient := by
  simp only [P1CompactRowTupleCutList.cfg,P1CompactRowTupleCutBody.entry,P1CompactRowTupleList.cfg,
    P1CompactRowTupleFramedBody.entry,P1CompactRowTupleCursorBody.entry,Composition.restart,TapeEmbedding.config,core]

theorem core_fields {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w k : ℕ) (rows : List (List Bool)) (tuple : List Bool)
    (pos : ℕ) (out : List Bool) (bound : ℕ) (coefficient : ℤ) :
    (core q gs p F w k rows tuple pos out bound coefficient).tapes 44=tuple ∧
      (core q gs p F w k rows tuple pos out bound coefficient).heads 44=pos := by
  have h := P1CompactRowTupleCutList.fields q gs p F w rows.length k rows tuple pos out bound coefficient
  simpa only [cfg_eq] using And.intro h.1 h.2.1

noncomputable def input {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w k : ℕ) (rows : List (List Bool)) (out : List Bool) (coefficient : ℤ) :=
  TapeEmbedding.config (fun _ : Fin 40 => 0)
    (P1CompactRowTupleEnumeratedEquations.extra w k rows.length)
    (core q gs p F w k rows [] 0 out 0 coefficient)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w k : ℕ)
    (rows : List (List Bool)) :=
  RowTupleEnumerationReady.budget w k+1+
    P1CompactRowTupleCutList.budget gs p F w rows.length rows (RowTupleSubsets.selected w rows.length k)
noncomputable def finished {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w k : ℕ) (rows : List (List Bool)) (out : List Bool) (coefficient : ℤ) :=
  let xs := RowTupleSubsets.selected w rows.length k
  core q gs p F w k rows
    (RowTupleEnumeration.word w k rows.length) (RowTupleEnumeration.word w k rows.length).length
    (out++P1CompactRowTupleCutList.output gs p rows xs coefficient)
    (P1CompactRowTupleCutList.finalBound rows xs 0) coefficient

theorem enum_pick (i : Fin 49) : RecoveryFocus.pick enumSlots (rowSlots i)=
    if i=44 then some 17 else none := by
  fin_cases i
  all_goals first | exact RecoveryFocus.pick_slot enumSlots enum_injective 17 | decide

private theorem vector_away {α : Type} (a b c d e f g h x y i j k : α)
    (ix : Fin 12) (hi : ix.val≠8) :
    (![a,b,c,d,e,f,g,h,x,i,j,k] : Fin 12 → α) ix=![a,b,c,d,e,f,g,h,y,i,j,k] ix := by
  fin_cases ix <;> simp_all

private theorem data_away {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w k : ℕ)
    (rows : List (List Bool)) (left right out : List Bool) (i : Fin 48) (hi : i≠44) :
    P1CompactRowTupleCursorLayout.data gs 0 p F w rows.length k rows left out 0 [] i=
      P1CompactRowTupleCursorLayout.data gs 0 p F w rows.length k rows right out 0 [] i := by
  revert hi
  refine Fin.addCases (m:=36) (n:=12) (fun j => ?_) (fun j => ?_) i
  · intro _
    simp only [P1CompactRowTupleCursorLayout.data,Fin.addCases_left]
  · intro hi
    simp only [P1CompactRowTupleCursorLayout.data,Fin.addCases_right]
    apply vector_away
    intro hj
    apply hi
    apply Fin.ext
    simpa only [Fin.val_natAdd,hj] using (show 36+8=(44 : Fin 48).val from rfl)

private theorem input_away {s n : ℕ} (q : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
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

theorem cuts_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w k : ℕ)
    (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (out : List Bool) (coefficient : ℤ)
    (hl : ∀ row∈rows, row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hk : k≤Q)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
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
  obtain ⟨row,hr,rh,rt,_⟩ := P1CompactRowTupleCutList.list_run gs p F Q w rows.length k rows
    (RowTupleSubsets.selected w rows.length k) [] out 0 coefficient hl
    (fun ds hd => (P1CompactRowTupleSelectedList.selected_fields w rows.length k ds hd).1)
    (fun ds hd => (P1CompactRowTupleSelectedList.selected_fields w rows.length k ds hd).2)
    hw le_rfl hk hp hF
  have hstream : P1CompactRowTupleCutList.stream w (RowTupleSubsets.selected w rows.length k)=
      RowTupleEnumeration.word w k rows.length := P1CompactRowTupleSelectedList.stream_eq w rows.length k
  simp only [List.nil_append,List.length_nil,Nat.zero_add,hstream,cfg_eq] at hr rh rt
  obtain ⟨b,hb,bf,_⟩ := RecoveryFocus.run_config rowSlots row_injective P1CompactRowTupleCutList.machine
    a.final.heads a.final.tapes _ _ row hr
  have hj : RecoveryFocus.config rowSlots a.final.heads a.final.tapes
      (core P1CompactRowTupleCutList.machine.start gs p F w k rows
        (RowTupleEnumeration.word w k rows.length) 0 out 0 coefficient)=
      Composition.restart a.final last.start := by
    apply WilliamsSourceCrop.focus_same
    · intro i
      rw [af]
      simp only [RecoveryFocus.config,enum_pick]
      by_cases h44 : i=44
      · subst i
        simp only [ite_true,bh]
        exact (core_fields P1CompactRowTupleCutList.machine.start gs p F w k rows _ 0 out 0 coefficient).2.symm
      · simp only [h44,ite_false,ambient,input,TapeEmbedding.config,rowSlots,Fin.addCases_left]
        rfl
    · intro i
      rw [af]
      simp only [RecoveryFocus.config,enum_pick]
      by_cases h44 : i=44
      · subst i
        simp only [ite_true,bt]
        exact (core_fields P1CompactRowTupleCutList.machine.start gs p F w k rows _ 0 out 0 coefficient).1.symm
      · simp only [h44,ite_false,ambient,input,TapeEmbedding.config,rowSlots,Fin.addCases_left]
        exact input_away P1CompactRowTupleCutList.machine.start gs p F w k rows [] _ out coefficient i h44
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

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsEnumeratedCuts

namespace NearCubicWires.RepairOrdinary
theorem P1CompactCloseoutRowsEnumeratedCuts_machine_unchanged : @P1CompactCloseoutRowsEnumeratedCuts.machine = @CloseoutRowsEnumeratedCuts.machine := rfl
end NearCubicWires.RepairOrdinary

/-! A complete fixed-degree row call starts with a blank coefficient cache.
Unary j and p produce (-2)^j once, then the actual positional enumeration
and signed-cut writer run at their retained native cache and output cursors. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsComputedCuts
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coefficientSlots (i : Fin 14) : Fin 103 :=
  if i.val=12 then 48 else i.natAdd 89
def old (i : Fin 89) : Fin 103 := i.castAdd 14
theorem coefficient_injective : Function.Injective coefficientSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [coefficientSlots] at hv
  split_ifs at hv <;> simp only [Fin.val_natAdd] at hv <;> omega
theorem outside (i : Fin 89) (hi : i≠48) : ∀ j,coefficientSlots j≠old i := by
  intro j h
  have hv := congrArg Fin.val h
  simp only [coefficientSlots,old,Fin.val_castAdd] at hv
  split_ifs at hv
  · exact hi (Fin.ext hv.symm)
  · simp only [Fin.val_natAdd] at hv
    have hb := i.isLt
    omega

noncomputable def first := RecoveryFocus.machine coefficientSlots CloseoutRowsDegreeCoefficient.machine
noncomputable def last := TapeEmbedding.machine 14 P1CompactCloseoutRowsEnumeratedCuts.machine
noncomputable def machine := Composition.machine first last
noncomputable def body {s n : ℕ} (state : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  P1CompactCloseoutRowsEnumeratedCuts.input state gs p F w (j+1) rows out ((-2 : ℤ)^j)
noncomputable def input {s n : ℕ} (state : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) : Configuration 103 s :=
  ⟨state,Fin.addCases (m := 89) (n := 14) (motive := fun _ => ℕ)
      (body state gs p F w j rows out).heads (fun _ => 0),
    Fin.addCases (m := 89) (n := 14) (motive := fun _ => List Bool)
      (Function.update (body state gs p F w j rows out).tapes 48 [])
      (CloseoutRowsDegreeCoefficient.input j p)⟩
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w j : ℕ) (rows : List (List Bool)) :=
  CloseoutRowsDegreeCoefficient.budget j p+1+P1CompactCloseoutRowsEnumeratedCuts.budget gs p F w (j+1) rows

theorem body_coefficient {s n : ℕ} (state : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :
    (body state gs p F w j rows out).heads 48=0 ∧
    (body state gs p F w j rows out).tapes 48=
      frame (MatrixScoreBatch.signMagnitude p ((-2 : ℤ)^j)) := by
  constructor
  · change (body state gs p F w j rows out).heads ((48 : Fin 49).castAdd 40)=0
    simp only [body,P1CompactCloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,Fin.addCases_left]
    change (P1CompactCloseoutRowsEnumeratedCuts.core state gs p F w (j+1) rows [] 0 out 0 ((-2 : ℤ)^j)).heads
      ((0 : Fin 1).natAdd 48)=0
    simp only [P1CompactCloseoutRowsEnumeratedCuts.core,Fin.addCases_right]
  · change (body state gs p F w j rows out).tapes ((48 : Fin 49).castAdd 40)=_
    simp only [body,P1CompactCloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,Fin.addCases_left]
    change (P1CompactCloseoutRowsEnumeratedCuts.core state gs p F w (j+1) rows [] 0 out 0 ((-2 : ℤ)^j)).tapes
      ((0 : Fin 1).natAdd 48)=_
    simp only [P1CompactCloseoutRowsEnumeratedCuts.core,Fin.addCases_right]

theorem cuts_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q w j : ℕ)
    (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hj : j<Q) (hQp : Q≤p)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∃ actual,runFrom machine (budget gs p F w j rows)
      (input machine.start gs p F w j rows out)=some actual ∧
      (∀ i,actual.final.heads (old (P1CompactCloseoutRowsEnumeratedCuts.rowSlots i))=
        (P1CompactCloseoutRowsEnumeratedCuts.finished machine.start gs p F w (j+1) rows out ((-2 : ℤ)^j)).heads i) ∧
      (∀ i,actual.final.tapes (old (P1CompactCloseoutRowsEnumeratedCuts.rowSlots i))=
        (P1CompactCloseoutRowsEnumeratedCuts.finished machine.start gs p F w (j+1) rows out ((-2 : ℤ)^j)).tapes i) ∧
      actual.steps≤budget gs p F w j rows := by
  obtain ⟨⟨cof,hcof,ct,ch,_⟩,cw⟩ := CloseoutRowsDegreeCoefficient.coefficient_ready j p (hj.trans_le hQp)
  let start := input first.start gs p F w j rows out
  have hh : ∀ i,start.heads (coefficientSlots i)=0 := by
    intro i
    by_cases hz : i.val=12
    · have he : i=12 := Fin.ext hz
      subst i
      change (body first.start gs p F w j rows out).heads 48=0
      exact (body_coefficient first.start gs p F w j rows out).1
    · simp only [coefficientSlots,hz,↓reduceIte,start,input,Fin.addCases_right]
  have ht : ∀ i,start.tapes (coefficientSlots i)=CloseoutRowsDegreeCoefficient.input j p i := by
    intro i
    by_cases hz : i.val=12
    · have he : i=12 := Fin.ext hz
      subst i
      change Function.update (body first.start gs p F w j rows out).tapes 48 [] 48=[]
      exact Function.update_self _ _ _
    · simp only [coefficientSlots,hz,↓reduceIte,start,input,Fin.addCases_right]
  obtain ⟨a,ha,_,_,ah,atapeC,ak⟩ := RecoveryFocus.dock coefficientSlots coefficient_injective
    CloseoutRowsDegreeCoefficient.machine _ start.heads start.tapes _ hh ht cof hcof
  have ahead : ∀ i,a.final.heads (old i)=(body P1CompactCloseoutRowsEnumeratedCuts.machine.start gs p F w j rows out).heads i := by
    intro i
    by_cases hz : i=48
    · subst i
      change a.final.heads (coefficientSlots 12)=_
      rw [ah,ch]
      exact (body_coefficient _ gs p F w j rows out).1.symm
    · rw [(ak (old i) (outside i hz)).1]
      simp only [start,input,old,Fin.addCases_left,body,P1CompactCloseoutRowsEnumeratedCuts.input,
        TapeEmbedding.config,P1CompactCloseoutRowsEnumeratedCuts.core]
  have atape : ∀ i,a.final.tapes (old i)=(body P1CompactCloseoutRowsEnumeratedCuts.machine.start gs p F w j rows out).tapes i := by
    intro i
    by_cases hz : i=48
    · subst i
      change a.final.tapes (coefficientSlots 12)=_
      rw [atapeC,ct,cw]
      exact (body_coefficient _ gs p F w j rows out).2.symm
    · rw [(ak (old i) (outside i hz)).2]
      simp only [start,input,old,Fin.addCases_left,Function.update_of_ne hz,
        body,P1CompactCloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,P1CompactCloseoutRowsEnumeratedCuts.core]
  obtain ⟨child,hchild,childH,childT,_⟩ := P1CompactCloseoutRowsEnumeratedCuts.cuts_run gs p F Q w (j+1)
    rows out ((-2 : ℤ)^j) hl hM hw hj hp hF
  let tail := TapeEmbedding.receipt (fun i : Fin 14 => a.final.heads (i.natAdd 89))
    (fun i : Fin 14 => a.final.tapes (i.natAdd 89)) child
  have htail := TapeEmbedding.run_embed P1CompactCloseoutRowsEnumeratedCuts.machine
    (fun i : Fin 14 => a.final.heads (i.natAdd 89))
    (fun i : Fin 14 => a.final.tapes (i.natAdd 89)) _ _ child hchild
  have hi : TapeEmbedding.config (fun i : Fin 14 => a.final.heads (i.natAdd 89))
      (fun i : Fin 14 => a.final.tapes (i.natAdd 89))
      (body P1CompactCloseoutRowsEnumeratedCuts.machine.start gs p F w j rows out)=
      Composition.restart a.final last.start := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m := 89) (n := 14) ?_ ?_ i <;> intro k
      · simpa only [TapeEmbedding.config,Composition.restart,Fin.addCases_left,old] using (ahead k).symm
      · simp only [TapeEmbedding.config,Composition.restart,Fin.addCases_right]
    · funext i
      refine Fin.addCases (m := 89) (n := 14) ?_ ?_ i <;> intro k
      · simpa only [TapeEmbedding.config,Composition.restart,Fin.addCases_left,old] using (atape k).symm
      · simp only [TapeEmbedding.config,Composition.restart,Fin.addCases_right]
  change runFrom last _ (TapeEmbedding.config
    (fun i : Fin 14 => a.final.heads (i.natAdd 89))
    (fun i : Fin 14 => a.final.tapes (i.natAdd 89))
    (body P1CompactCloseoutRowsEnumeratedCuts.machine.start gs p F w j rows out))=some tail at htail
  rw [hi] at htail
  have hfirst : runFrom first (CloseoutRowsDegreeCoefficient.budget j p)
      (input first.start gs p F w j rows out)=some a := ha
  have whole := Composition.run_join first last _ _ _ a tail hfirst htail
  refine ⟨Composition.joinedReceipt a tail,whole,?_,?_,runFrom_steps_le machine _ _ _ whole⟩
  · intro i
    change tail.final.heads ((P1CompactCloseoutRowsEnumeratedCuts.rowSlots i).castAdd 14)=_
    rw [TapeEmbedding.receipt_heads_old]
    exact childH i
  · intro i
    change tail.final.tapes ((P1CompactCloseoutRowsEnumeratedCuts.rowSlots i).castAdd 14)=_
    rw [TapeEmbedding.receipt_tapes_old]
    exact childT i

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsComputedCuts

namespace NearCubicWires.RepairOrdinary
theorem P1CompactCloseoutRowsComputedCuts_machine_unchanged : @P1CompactCloseoutRowsComputedCuts.machine = @CloseoutRowsComputedCuts.machine := rfl
end NearCubicWires.RepairOrdinary

/-! The fixed-degree call executes one recorded rewind of its reusable
work tapes. Its append cursor is excluded. The coarse capacity concerns
only those work tapes, so accumulated row output never enters this charge. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeReset
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

open CloseoutRowsDegreeReset

theorem input_heads {s n : ℕ} (state : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) (i : Fin 103)
    (hi : selected i=true) :
    (P1CompactCloseoutRowsComputedCuts.input state gs p F w j rows out).heads i=0 := by
  revert hi
  refine Fin.addCases (m := 89) (n := 14) (fun k => ?_) (fun k => ?_) i
  · simp only [P1CompactCloseoutRowsComputedCuts.input,Fin.addCases_left,
      P1CompactCloseoutRowsComputedCuts.body,P1CompactCloseoutRowsEnumeratedCuts.input,TapeEmbedding.config]
    refine Fin.addCases (m := 49) (n := 40) (fun a => ?_) (fun a => ?_) k
    · intro ha
      have hval : a.val=44 ∨ a.val=47 ∨ a.val=48 := by
        have hraw : a.val=44 ∨ a.val=47 ∨ a.val=48 ∨ 49 ≤ a.val := by
          simpa [selected,Fin.ext_iff] using ha
        have hb := a.isLt
        omega
      rcases hval with h44|h47|h48
      · have he : a=44 := Fin.ext h44
        subst a
        rfl
      · have he : a=47 := Fin.ext h47
        subst a
        rfl
      · have he : a=48 := Fin.ext h48
        subst a
        rfl
    · intro _
      simp only [Fin.addCases_right]
  · intro _
    simp only [P1CompactCloseoutRowsComputedCuts.input,Fin.addCases_right]

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeReset

/-! The native cache fixes the actual common coordinate width. Incidence
lists retain every monomial occurrence, including empty monomials. Native
coordinate order is exactly the signed cut order consumed by the row printer. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsCacheInput
open RepairRepresentation SupplierPipeline SupplierPrime SupplierEstimator ThresholdCompiler
open MatrixScoreBatch RowBinLift
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def coordinates {l r : ℕ} (e : LabelledEquation (Fin (l+r))) : Equation l r :=
  ⟨Sum.elim (fun i => e.weights (i.castAdd r)) (fun i => e.weights (i.natAdd l)),e.target⟩

theorem coordinates_magnitude {l r : ℕ} (e : LabelledEquation (Fin (l+r))) :
    equationMagnitudeBound (coordinates e)=equationMagnitudeBound e := by
  simp [coordinates,equationMagnitudeBound,Fintype.sum_sum_type,Fin.sum_univ_add]

theorem cut_word {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (p : ℕ)
    (rows : List (List Bool)) (ds : List ℕ) (c : ℤ) :
    P1CompactRowTupleCutBody.word gs p rows ds c=cutWord p
      (split c (coordinates (P1CompactRowCoordinateLoop.equation gs
        (P1CompactRowTupleCommonEquation.indices gs.length rows ds)))) := by
  simp [P1CompactRowTupleCutBody.word,P1CompactRowCoordinateLoop.equationWord,EquationWidenLoop.stream,
    cutWord,fields,split,coordinates,List.ofFn_add,List.flatMap_append,List.append_assoc]
  congr 1

def monomial {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (bits : List Bool) :=
  (P1CompactRowCachedEquation.equations gs (P1CompactRowTupleCommonEquation.one gs.length bits)).map coordinates
def polynomial {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (rows : List (List Bool)) :=
  rows.map (monomial gs)
def family {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (bank : List (List (List Bool))) :=
  bank.map (polynomial gs)

theorem family_length {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (bank : List (List (List Bool))) : (family gs bank).length=bank.length := by simp [family]

theorem one_length (N : ℕ) (bits : List Bool) :
    (P1CompactRowTupleCommonEquation.one N bits).length≤N := by
  unfold P1CompactRowTupleCommonEquation.one
  split_ifs with h
  · exact (RowMaskMeaning.typed_le N 0 bits (by omega)).trans h
  · simp

theorem monomial_length {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (bits : List Bool) :
    (monomial gs bits).length≤gs.length := by
  simpa only [monomial,P1CompactRowCachedEquation.equations,List.length_map] using one_length gs.length bits

theorem monomial_fit {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (bits : List Bool)
    (e : Equation l r) (he : e∈monomial gs bits) :
    equationMagnitudeBound e<2^(P1Radix.bits gs) := by
  obtain ⟨native,hn,rfl⟩ := List.mem_map.mp he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hn
  rw [coordinates_magnitude]
  exact P1CompactRowCachedEquation.cache_radix_safe gs i

theorem family_lengths {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (bank : List (List (List Bool))) (ms : List (List (Equation l r)))
    (hm : ms∈family gs bank) (m : List (Equation l r)) (hmem : m∈ms) : m.length≤gs.length := by
  obtain ⟨rows,_,rfl⟩ := List.mem_map.mp hm
  obtain ⟨bits,_,rfl⟩ := List.mem_map.mp hmem
  exact monomial_length gs bits

theorem family_fit {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (bank : List (List (List Bool))) (ms : List (List (Equation l r)))
    (hm : ms∈family gs bank) (e : Equation l r) (he : e∈ms.flatten) :
    equationMagnitudeBound e<2^(P1Radix.bits gs) := by
  obtain ⟨rows,_,rfl⟩ := List.mem_map.mp hm
  obtain ⟨m,hm,he⟩ := List.mem_flatten.mp he
  obtain ⟨bits,_,rfl⟩ := List.mem_map.mp hm
  exact monomial_fit gs bits e he

def input (s Q : ℕ) (gs : List (ExactThresholdGate ((s+1)/2+s/2))) [_radix : P1Radix gs]
    (bank : List (List (List Bool))) (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (family gs bank)).length^100≤2^s) : EquationRow.Input :=
  CloseoutRows.commonInput s (P1Radix.bits gs) gs.length Q (family gs bank)
    hs hg (family_lengths gs bank) (family_fit gs bank)

theorem input_width (s Q : ℕ) (gs : List (ExactThresholdGate ((s+1)/2+s/2))) [_radix : P1Radix gs]
    (bank : List (List (List Bool))) (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (family gs bank)).length^100≤2^s) :
    (EquationRow.request (input s Q gs bank hs hg)).p=
      (P1Radix.bits gs)*(gs.length*Q)+Q+1 := rfl

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsCacheInput

/-! The actual tuple-cut bytes are precisely the common-width row's cuts.
All degree and monomial occurrences remain in their enumerated order. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsCutMeaning
open RepairRepresentation SupplierPipeline MatrixScoreBatch RowBinLift
open P1CompactCloseoutRowsCacheInput
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem coordinates_stack {l r : ℕ} (b : ℤ)
    (es : List (LabelledEquation (Fin (l+r)))) :
    coordinates (stackEquations b es)=stackEquations b (es.map coordinates) := by
  induction es with
  | nil =>
    simp only [List.map_nil,stackEquations,coordinates]
    congr 1
    funext i
    cases i <;> rfl
  | cons e es ih =>
    simp only [List.map_cons,stackEquations,←ih,coordinates]
    congr 1
    funext i
    cases i <;> rfl

theorem fetch_polynomial {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (rows : List (List Bool)) (d : ℕ) :
    RowTupleTerms.fetch (polynomial gs rows) d=monomial gs (RowTupleMaskLoop.mask rows d) := by
  simp only [RowTupleTerms.fetch,polynomial,RowTupleMaskLoop.mask,List.getElem?_map]
  cases h : rows[d]? with
  | none => simp [monomial,P1CompactRowTupleCommonEquation.one,P1CompactRowCachedEquation.equations,
      RowMaskMeaning.typed,RowMaskMeaning.positions]
  | some bits => rfl

theorem selected_equations {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (rows : List (List Bool)) (ds : List ℕ) :
    (P1CompactRowCachedEquation.equations gs (P1CompactRowTupleCommonEquation.indices gs.length rows ds)).map coordinates=
      (RowTupleTerms.selectedMonomials (polynomial gs rows) ds).flatten := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [P1CompactRowTupleCommonEquation.indices,List.flatMap_cons,P1CompactRowCachedEquation.equations,
      List.map_append,RowTupleTerms.selectedMonomials,List.map_cons,List.flatten_cons]
    rw [fetch_polynomial]
    exact congrArg (List.append (monomial gs (RowTupleMaskLoop.mask rows d))) ih

theorem tuple_word {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (p : ℕ) (rows : List (List Bool)) (ds : List ℕ) (c : ℤ) :
    P1CompactRowTupleCutBody.word gs p rows ds c=cutWord p (split c
      (RowPowerBinLift.stack (P1Radix.bits gs)
        (RowTupleTerms.selectedMonomials (polynomial gs rows) ds).flatten)) := by
  rw [cut_word,P1CompactRowCoordinateLoop.equation]
  simp only [RowPowerBinLift.stack,coordinates_stack,selected_equations]

def degreeCuts {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (w j : ℕ) (rows : List (List Bool)) : List Cut :=
  (RowTupleSubsets.selected w rows.length (j+1)).map fun ds =>
    split ((-2 : ℤ)^j) (RowPowerBinLift.stack (P1Radix.bits gs)
      (RowTupleTerms.selectedMonomials (polynomial gs rows) ds).flatten)

theorem degree_output {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (p w j : ℕ) (rows : List (List Bool)) :
    P1CompactRowTupleCutList.output gs p rows (RowTupleSubsets.selected w rows.length (j+1)) ((-2 : ℤ)^j)=
      (degreeCuts gs w j rows).flatMap (cutWord p) := by
  simp only [P1CompactRowTupleCutList.output,degreeCuts,List.flatMap_map]
  apply List.flatMap_congr
  intro ds _
  exact tuple_word gs p rows ds _

theorem polynomial_output {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (p Q : ℕ) (rows : List (List Bool)) :
    ((List.range (min Q rows.length)).flatMap fun j =>
      P1CompactRowTupleCutList.output gs p rows
        (RowTupleSubsets.selected (RowTupleSubsets.digitWidth rows.length) rows.length (j+1)) ((-2 : ℤ)^j))=
      (CloseoutRows.orderedCuts (P1Radix.bits gs) Q (polynomial gs rows)).flatMap (cutWord p) := by
  simp only [CloseoutRows.orderedCuts,RowTupleTerms.terms,polynomial,List.length_map,
    List.map_flatMap,List.flatMap_assoc,List.flatMap_map]
  apply List.flatMap_congr
  intro j _
  simpa only [degreeCuts,polynomial,List.flatMap_map] using
    degree_output gs p (RowTupleSubsets.digitWidth rows.length) j rows

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsCutMeaning

/-! Actual fixed-degree cut production followed by paid scratch reuse.
The native cache and the row append cursor survive; the next call reloads
only degree metadata into the erased work bank. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsReusableCuts
open LocalBitMultitape RecoveryExecution CloseoutRowsDegreeReset P1CompactCloseoutRowsDegreeReset
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := CloseoutRowsDegreeClean.machine P1CompactCloseoutRowsComputedCuts.machine
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  CloseoutRowsDegreeClean.input
    (P1CompactCloseoutRowsComputedCuts.input P1CompactCloseoutRowsComputedCuts.machine.start gs p F w j rows out) C
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) :=
  CloseoutRowsDegreeClean.budget (P1CompactCloseoutRowsComputedCuts.budget gs p F w j rows) C

theorem finished_output {s n : ℕ} (state : Fin s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :
    (P1CompactCloseoutRowsEnumeratedCuts.finished state gs p F w (j+1) rows out ((-2 : ℤ)^j)).tapes 31=
        out++P1CompactRowTupleCutList.output gs p rows (RowTupleSubsets.selected w rows.length (j+1)) ((-2 : ℤ)^j) ∧
    (P1CompactCloseoutRowsEnumeratedCuts.finished state gs p F w (j+1) rows out ((-2 : ℤ)^j)).heads 31=
        (out++P1CompactRowTupleCutList.output gs p rows (RowTupleSubsets.selected w rows.length (j+1)) ((-2 : ℤ)^j)).length := by
  have h := P1CompactRowTupleCutList.fields state gs p F w rows.length (j+1) rows
    (RowTupleEnumeration.word w (j+1) rows.length) (RowTupleEnumeration.word w (j+1) rows.length).length
    (out++P1CompactRowTupleCutList.output gs p rows (RowTupleSubsets.selected w rows.length (j+1)) ((-2 : ℤ)^j))
    (P1CompactRowTupleCutList.finalBound rows (RowTupleSubsets.selected w rows.length (j+1)) 0) ((-2 : ℤ)^j)
  simpa only [P1CompactCloseoutRowsEnumeratedCuts.cfg_eq,P1CompactCloseoutRowsEnumeratedCuts.finished] using h.2.2

theorem fixed_degree_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (p F Q w j C : ℕ) (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hj : j<Q) (hQp : Q≤p)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (hc : P1CompactCloseoutRowsComputedCuts.budget gs p F w j rows+1≤C)
    (ht : ∀ i,selected i=true →
      ((P1CompactCloseoutRowsComputedCuts.input P1CompactCloseoutRowsComputedCuts.machine.start gs p F w j rows out).tapes i).length≤C) :
    ∃ actual,runFrom machine (budget gs p F w j C rows) (input gs p F w j C rows out)=some actual ∧
      actual.final.tapes 31=out++(P1CompactCloseoutRowsCutMeaning.degreeCuts gs w j rows).flatMap (MatrixScoreBatch.cutWord p) ∧
      actual.final.heads 31=(out++(P1CompactCloseoutRowsCutMeaning.degreeCuts gs w j rows).flatMap (MatrixScoreBatch.cutWord p)).length ∧
      (∀ i,actual.final.heads ((work i).castAdd 3)=0 ∧
        actual.final.tapes ((work i).castAdd 3)=List.replicate C false) ∧
      actual.final.tapes 103=List.replicate C false ∧
      actual.final.tapes 104=List.replicate C true ∧
      actual.final.tapes 105=List.replicate (C+1) false ∧
      actual.steps≤budget gs p F w j C rows := by
  obtain ⟨raw,hr,rh,rt,_⟩ := P1CompactCloseoutRowsComputedCuts.cuts_run gs p F Q w j rows out hl hM hw hj hQp hp hF
  obtain ⟨actual,ha,ah,atapes,_,log1,_,driver,_,log2,hs⟩ := CloseoutRowsDegreeClean.clean_run
    P1CompactCloseoutRowsComputedCuts.machine _ _ C raw hr
    (P1CompactCloseoutRowsDegreeReset.input_heads _ gs p F w j rows out) ht hc
  have hout := finished_output P1CompactCloseoutRowsComputedCuts.machine.start gs p F w j rows out
  have rawT : raw.final.tapes 31=out++P1CompactRowTupleCutList.output gs p rows
      (RowTupleSubsets.selected w rows.length (j+1)) ((-2 : ℤ)^j) := (rt 31).trans hout.1
  have rawH : raw.final.heads 31=(out++P1CompactRowTupleCutList.output gs p rows
      (RowTupleSubsets.selected w rows.length (j+1)) ((-2 : ℤ)^j)).length := (rh 31).trans hout.2
  refine ⟨actual,ha,?_,?_,?_,log1,driver,log2,hs⟩
  · have h := atapes 31
    change actual.final.tapes 31=raw.final.tapes 31 at h
    rw [h,rawT,P1CompactCloseoutRowsCutMeaning.degree_output]
  · have h := ah 31
    change actual.final.heads 31=raw.final.heads 31 at h
    rw [h,rawH,P1CompactCloseoutRowsCutMeaning.degree_output]
  · intro i
    have hh := ah (work i)
    have htape := atapes (work i)
    simpa [work_selected] using And.intro hh htape

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsReusableCuts

namespace NearCubicWires.RepairOrdinary
theorem P1CompactCloseoutRowsReusableCuts_machine_unchanged : @P1CompactCloseoutRowsReusableCuts.machine = @CloseoutRowsReusableCuts.machine := rfl
end NearCubicWires.RepairOrdinary

/-! One exact boundary for the degree loop: native row context, 57 work
tapes, the retained C driver/logs, and six short templates. The worker
receipt describes every physical head and tape needed by its next call. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsLoopLayout
open LocalBitMultitape RecoveryExecution CloseoutRowsDegreeReset P1CompactCloseoutRowsDegreeReset
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def templates (p w M j : ℕ) : Fin 6→List Bool :=
  ![CompareMachine.word w,frame (SignedSortKey.binary w (M-1)),CompareMachine.word (j+1),
    List.replicate w true,List.replicate j true,List.replicate p true]
def extra (p w M j C : ℕ) : Fin 9→List Bool :=
  Fin.addCases (m:=3) (n:=6) (motive:=fun _=>List Bool)
    ![List.replicate C false,List.replicate C true,List.replicate (C+1) false] (templates p w M j)
noncomputable def rawInput {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  P1CompactCloseoutRowsComputedCuts.input (0 : Fin 1) gs p F w j rows out
noncomputable def inputHeads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) : Fin 112→ℕ :=
  Fin.addCases (m:=103) (n:=9) (motive:=fun _=>ℕ) (rawInput gs p F w j rows out).heads (fun _=>0)
noncomputable def inputTapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) : Fin 112→List Bool :=
  Fin.addCases (m:=103) (n:=9) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (caps C i) ((rawInput gs p F w j rows out).tapes i))
    (extra p w rows.length j C)
noncomputable def nativeEnd {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  P1CompactCloseoutRowsEnumeratedCuts.finished (0 : Fin 1) gs p F w (j+1) rows out ((-2 : ℤ)^j)
noncomputable def finalHeads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) : Fin 112→ℕ :=
  Fin.addCases (m:=49) (n:=63) (motive:=fun _=>ℕ)
    (fun i=>if selected (i.castAdd 54) then 0 else (nativeEnd gs p F w j rows out).heads i) (fun _=>0)
noncomputable def finalTapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) : Fin 112→List Bool :=
  Fin.addCases (m:=103) (n:=9) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=49) (n:=54) (motive:=fun _=>List Bool)
      (fun i=>if selected (i.castAdd 54) then List.replicate C false else
        (nativeEnd gs p F w j rows out).tapes i) (fun _=>List.replicate C false))
    (extra p w rows.length j C)
noncomputable def worker := TapeEmbedding.machine 6 P1CompactCloseoutRowsReusableCuts.machine

theorem old_selected (i : Fin 54) : selected (i.natAdd 49)=true := by
  apply decide_eq_true
  right; right; right
  dsimp
  omega

theorem worker_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w j C : ℕ) (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hj : j<Q) (hQp : Q≤p)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (hc : P1CompactCloseoutRowsComputedCuts.budget gs p F w j rows+1≤C)
    (ht : ∀ i,selected i=true → ((rawInput gs p F w j rows out).tapes i).length≤C) :
    ∃ actual,runFrom worker (P1CompactCloseoutRowsReusableCuts.budget gs p F w j C rows)
      ⟨worker.start,inputHeads gs p F w j rows out,inputTapes gs p F w j C rows out⟩=some actual ∧
      actual.final.heads=finalHeads gs p F w j rows out ∧
      actual.final.tapes=finalTapes gs p F w j C rows out ∧
      actual.steps≤P1CompactCloseoutRowsReusableCuts.budget gs p F w j C rows := by
  obtain ⟨raw,hr,rh,rt,_⟩ := P1CompactCloseoutRowsComputedCuts.cuts_run gs p F Q w j rows out hl hM hw hj hQp hp hF
  obtain ⟨clean,hclean,ch,ct,lh,lt,dh,dt,eh,et,_⟩ := CloseoutRowsDegreeClean.clean_run
    P1CompactCloseoutRowsComputedCuts.machine _ _ C raw hr
    (P1CompactCloseoutRowsDegreeReset.input_heads _ gs p F w j rows out) ht hc
  let actual := TapeEmbedding.receipt (fun _ : Fin 6=>0) (templates p w rows.length j) clean
  have he := TapeEmbedding.run_embed P1CompactCloseoutRowsReusableCuts.machine (fun _ : Fin 6=>0)
    (templates p w rows.length j) _ _ clean hclean
  have hi : TapeEmbedding.config (fun _ : Fin 6=>0) (templates p w rows.length j)
      (P1CompactCloseoutRowsReusableCuts.input gs p F w j C rows out)=
      (⟨worker.start,inputHeads gs p F w j rows out,inputTapes gs p F w j C rows out⟩ :
        Configuration 112 _) := by
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (m:=103) (n:=9) (fun k=>?_) (fun k=>?_) i
      · change (TapeEmbedding.config (fun _ : Fin 6=>0) (templates p w rows.length j)
          (P1CompactCloseoutRowsReusableCuts.input gs p F w j C rows out)).heads
          (((k.castAdd 1).castAdd 2).castAdd 6)=_
        simp only [TapeEmbedding.config,Fin.addCases_left,P1CompactCloseoutRowsReusableCuts.input,
          CloseoutRowsDegreeClean.input,Composition.leftConfig,CloseoutRowsDegreeReset.input,
          ZeroPadding.config,Rewind.recording,Rewind.config,inputHeads]
        rfl
      · fin_cases k <;> rfl
    · funext i
      refine Fin.addCases (m:=103) (n:=9) (fun k=>?_) (fun k=>?_) i
      · change (TapeEmbedding.config (fun _ : Fin 6=>0) (templates p w rows.length j)
          (P1CompactCloseoutRowsReusableCuts.input gs p F w j C rows out)).tapes
          (((k.castAdd 1).castAdd 2).castAdd 6)=_
        simp only [TapeEmbedding.config,Fin.addCases_left,P1CompactCloseoutRowsReusableCuts.input,
          CloseoutRowsDegreeClean.input,Composition.leftConfig,CloseoutRowsDegreeReset.input,
          ZeroPadding.config,Rewind.recording,Rewind.config,Rewind.Workspace.capacities,
          ZeroPadding.pad_zero,inputTapes]
        rfl
      · fin_cases k <;> rfl
  change runFrom worker (P1CompactCloseoutRowsReusableCuts.budget gs p F w j C rows)
    (TapeEmbedding.config (fun _ : Fin 6=>0) (templates p w rows.length j)
      (P1CompactCloseoutRowsReusableCuts.input gs p F w j C rows out))=some actual at he
  rw [hi] at he
  refine ⟨actual,he,?_,?_,runFrom_steps_le worker _ _ _ he⟩
  · funext i
    refine Fin.addCases (m:=103) (n:=9) (fun k=>?_) (fun k=>?_) i
    · change actual.final.heads ((k.castAdd 3).castAdd 6)=_
      rw [TapeEmbedding.receipt_heads_old,ch]
      refine Fin.addCases (m:=49) (n:=54) (fun a=>?_) (fun a=>?_) k
      · have hh := rh a
        change raw.final.heads (a.castAdd 54)=(nativeEnd gs p F w j rows out).heads a at hh
        rw [hh]
        change _=finalHeads gs p F w j rows out (a.castAdd 63)
        simp only [finalHeads,Fin.addCases_left]
      · rw [old_selected]
        simp only [↓reduceIte]
        change 0=finalHeads gs p F w j rows out ((a.castAdd 9).natAdd 49)
        simp only [finalHeads,Fin.addCases_right]
    · fin_cases k
      · exact lh
      · exact dh
      · exact eh
      all_goals rfl
  · funext i
    refine Fin.addCases (m:=103) (n:=9) (fun k=>?_) (fun k=>?_) i
    · change actual.final.tapes ((k.castAdd 3).castAdd 6)=_
      rw [TapeEmbedding.receipt_tapes_old,ct]
      refine Fin.addCases (m:=49) (n:=54) (fun a=>?_) (fun a=>?_) k
      · have htape := rt a
        change raw.final.tapes (a.castAdd 54)=(nativeEnd gs p F w j rows out).tapes a at htape
        rw [htape]
        simp only [finalTapes,Fin.addCases_left]
      · rw [old_selected]
        simp only [↓reduceIte]
        simp only [finalTapes,Fin.addCases_left,Fin.addCases_right]
    · fin_cases k
      · exact lt
      · exact dt
      · exact et
      all_goals rfl

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsLoopLayout

/-! The accepted degree pass, four small updates and six metadata copies
return exactly the next pass's boundary, including the append cursor. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsLoopBoundary
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout CloseoutRowsDegreeReset P1CompactCloseoutRowsDegreeReset
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def emitted {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p w j : ℕ)
    (rows : List (List Bool)) := P1CompactRowTupleCutList.output gs p rows
      (RowTupleSubsets.selected w rows.length (j+1)) ((-2 : ℤ)^j)
noncomputable def advanced {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  CloseoutRowsDegreeNext.output (finalTapes gs p F w j C rows out) w (j+1) j
noncomputable def reloaded {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  CloseoutRowsMetadataReload.data (advanced gs p F w j C rows out) C
    (templates p w rows.length (j+1)) 6

theorem original_outside (i : Fin 49) (j : Fin 6) :
    CloseoutRowsMetadataReload.dest j≠i.castAdd 63 := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  have hd : ∀ k : Fin 6,51≤(CloseoutRowsMetadataReload.dest k).val := by decide
  have hj := hd j
  change (CloseoutRowsMetadataReload.dest j).val=i.val at hv
  omega

theorem work_pick (i : Fin 54) :
    RecoveryFocus.pick CloseoutRowsMetadataReload.dest ((i.natAdd 49).castAdd 9)=
      if i=2 then some 0 else if i=3 then some 1 else if i=12 then some 2
      else if i=17 then some 3 else if i=40 then some 4 else if i=41 then some 5 else none := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot _ CloseoutRowsMetadataReload.dest_injective 0
    | exact RecoveryFocus.pick_slot _ CloseoutRowsMetadataReload.dest_injective 1
    | exact RecoveryFocus.pick_slot _ CloseoutRowsMetadataReload.dest_injective 2
    | exact RecoveryFocus.pick_slot _ CloseoutRowsMetadataReload.dest_injective 3
    | exact RecoveryFocus.pick_slot _ CloseoutRowsMetadataReload.dest_injective 4
    | exact RecoveryFocus.pick_slot _ CloseoutRowsMetadataReload.dest_injective 5
    | decide

theorem pad_nil (C : ℕ) : ZeroPadding.pad C []=List.replicate C false := by simp [ZeroPadding.pad]

theorem native_low {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) (i : Fin 36) :
    reloaded gs p F w j C rows out (i.castAdd 76)=
      inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) (i.castAdd 76) := by
  rw [reloaded,CloseoutRowsMetadataReload.data_other _ _ _ _ (i.castAdd 76) (original_outside (i.castAdd 13))]
  have hb := i.isLt
  have h40 : (i.castAdd 76 : Fin 112)≠40 := by intro h; have hv:=congrArg Fin.val h; change i.val=40 at hv; omega
  have h46 : (i.castAdd 76 : Fin 112)≠46 := by intro h; have hv:=congrArg Fin.val h; change i.val=46 at hv; omega
  have h108 : (i.castAdd 76 : Fin 112)≠108 := by intro h; have hv:=congrArg Fin.val h; change i.val=108 at hv; omega
  have h110 : (i.castAdd 76 : Fin 112)≠110 := by intro h; have hv:=congrArg Fin.val h; change i.val=110 at hv; omega
  have h48 : (i.castAdd 53 : Fin 89)≠48 := by intro h; have hv:=congrArg Fin.val h; change i.val=48 at hv; omega
  have hs : selected (i.castAdd 67)=false := by
    apply decide_eq_false
    intro h
    have hv : i.val=44 ∨ i.val=47 ∨ i.val=48 ∨ 49 ≤ i.val := by simpa [Fin.ext_iff] using h
    rcases hv with hv|hv|hv|hv <;> omega
  have left : advanced gs p F w j C rows out (i.castAdd 76)=
      (nativeEnd gs p F w j rows out).tapes (i.castAdd 13) := by
    simp only [advanced,CloseoutRowsDegreeNext.output,CloseoutRowsDegreeNext.nextRaw,
      CloseoutRowsDegreeNext.nextTemplate,CloseoutRowsDegreeNext.nextNative,CloseoutRowsDegreeNext.zeroBound,
      Function.update_of_ne h110,Function.update_of_ne h108,Function.update_of_ne h46,Function.update_of_ne h40]
    change finalTapes gs p F w j C rows out (((i.castAdd 13).castAdd 54).castAdd 9)=_
    have hs' : selected ((i.castAdd 13).castAdd 54)=false := hs
    simp only [finalTapes,Fin.addCases_left,hs',Bool.false_eq_true,↓reduceIte]
  have right : inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) (i.castAdd 76)=
      (rawInput gs p F w (j+1) rows (out++emitted gs p w j rows)).tapes (i.castAdd 67) := by
    change inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) ((i.castAdd 67).castAdd 9)=_
    simp only [inputTapes,Fin.addCases_left,caps,hs,Bool.false_eq_true,↓reduceIte,ZeroPadding.pad_zero]
  rw [left,right]
  change _=(rawInput gs p F w (j+1) rows (out++emitted gs p w j rows)).tapes ((i.castAdd 53).castAdd 14)
  simp only [rawInput,P1CompactCloseoutRowsComputedCuts.input,Fin.addCases_left]
  rw [Function.update_of_ne h48]
  change _=(P1CompactCloseoutRowsEnumeratedCuts.input (0 : Fin 1) gs p F w (j+1+1) rows
    (out++emitted gs p w j rows) ((-2 : ℤ)^(j+1))).tapes ((i.castAdd 13).castAdd 40)
  simp only [P1CompactCloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,Fin.addCases_left]
  rw [show (i.castAdd 13 : Fin 49)=(i.castAdd 12).castAdd 1 from rfl]
  simp only [nativeEnd,P1CompactCloseoutRowsEnumeratedCuts.finished,P1CompactCloseoutRowsEnumeratedCuts.core,
    Fin.addCases_left,P1CompactRowTupleCursorLayout.data]
  rfl

theorem native_high {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool)
    (h47 : RowTupleCursorReady.capacity gs.length w rows.length (j+2)≤C) (i : Fin 13) :
    reloaded gs p F w j C rows out ((i.natAdd 36).castAdd 63)=
      inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) ((i.natAdd 36).castAdd 63) := by
  rw [reloaded,CloseoutRowsMetadataReload.data_other _ _ _ _ _ (original_outside (i.natAdd 36))]
  fin_cases i
  all_goals simp [advanced,CloseoutRowsDegreeNext.output,CloseoutRowsDegreeNext.nextRaw,
    CloseoutRowsDegreeNext.nextTemplate,CloseoutRowsDegreeNext.nextNative,CloseoutRowsDegreeNext.zeroBound,
    finalTapes,inputTapes,rawInput,P1CompactCloseoutRowsComputedCuts.input,P1CompactCloseoutRowsComputedCuts.body,
    P1CompactCloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,nativeEnd,P1CompactCloseoutRowsEnumeratedCuts.finished,
    P1CompactCloseoutRowsEnumeratedCuts.core,P1CompactRowTupleCursorLayout.data,
    P1CompactRowTupleCursorBody.padding,caps,selected,Fin.addCases,pad_nil,
    Rewind.Workspace.pad_zeros,h47,Nat.add_assoc]

theorem native_next {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool)
    (h47 : RowTupleCursorReady.capacity gs.length w rows.length (j+2)≤C) (i : Fin 49) :
    reloaded gs p F w j C rows out (i.castAdd 63)=
      inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) (i.castAdd 63) := by
  refine Fin.addCases (m:=36) (n:=13) (fun a=>?_) (fun a=>?_) i
  · exact native_low gs p F w j C rows out a
  · exact native_high gs p F w j C rows out h47 a

theorem work_next {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) (i : Fin 54) :
    reloaded gs p F w j C rows out ((i.natAdd 49).castAdd 9)=
      inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) ((i.natAdd 49).castAdd 9) := by
  simp only [reloaded,CloseoutRowsMetadataReload.data,work_pick]
  fin_cases i
  all_goals simp [advanced,CloseoutRowsDegreeNext.output,CloseoutRowsDegreeNext.nextRaw,
    CloseoutRowsDegreeNext.nextTemplate,CloseoutRowsDegreeNext.nextNative,CloseoutRowsDegreeNext.zeroBound,
    finalTapes,inputTapes,rawInput,P1CompactCloseoutRowsComputedCuts.input,P1CompactCloseoutRowsComputedCuts.body,
    P1CompactCloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,P1CompactRowTupleEnumeratedEquations.extra,
    CloseoutRowsDegreeCoefficient.input,caps,selected,Fin.addCases,templates,pad_nil,Nat.add_assoc]

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsLoopBoundary

/-! The full next-call identity and actual metadata inputs at the shared
degree boundary. Every source and cursor is inherited from one receipt. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsLoopInterface
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsLoopBoundary CloseoutRowsDegreeReset P1CompactCloseoutRowsDegreeReset
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem extra_outside (i : Fin 9) (j : Fin 6) :
    CloseoutRowsMetadataReload.dest j≠i.natAdd 103 := by
  intro h
  have hv := congrArg Fin.val h
  have hd : ∀ k : Fin 6,(CloseoutRowsMetadataReload.dest k).val≤90 := by decide
  have hj := hd j
  change (CloseoutRowsMetadataReload.dest j).val=103+i.val at hv
  omega

theorem extra_next {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) (i : Fin 9) :
    reloaded gs p F w j C rows out (i.natAdd 103)=
      inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) (i.natAdd 103) := by
  rw [reloaded,CloseoutRowsMetadataReload.data_other _ _ _ _ _ (extra_outside i)]
  fin_cases i
  all_goals simp [advanced,CloseoutRowsDegreeNext.output,CloseoutRowsDegreeNext.nextRaw,
    CloseoutRowsDegreeNext.nextTemplate,CloseoutRowsDegreeNext.nextNative,CloseoutRowsDegreeNext.zeroBound,
    finalTapes,inputTapes,extra,templates,Fin.addCases,Nat.add_assoc]

theorem all_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool)
    (h47 : RowTupleCursorReady.capacity gs.length w rows.length (j+2)≤C) :
    reloaded gs p F w j C rows out=
      inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) := by
  funext i
  refine Fin.addCases (m:=103) (n:=9) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=49) (n:=54) (fun b=>?_) (fun b=>?_) a
    · exact native_next gs p F w j C rows out h47 b
    · exact work_next gs p F w j C rows out b
  · exact extra_next gs p F w j C rows out a

theorem all_heads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :
    finalHeads gs p F w j rows out=
      inputHeads gs p F w (j+1) rows (out++emitted gs p w j rows) := by
  funext i
  refine Fin.addCases (m:=103) (n:=9) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=49) (n:=54) (fun b=>?_) (fun b=>?_) a
    · fin_cases b
      all_goals simp [finalHeads,inputHeads,rawInput,P1CompactCloseoutRowsComputedCuts.input,
        P1CompactCloseoutRowsComputedCuts.body,P1CompactCloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,
        nativeEnd,P1CompactCloseoutRowsEnumeratedCuts.finished,P1CompactCloseoutRowsEnumeratedCuts.core,
        P1CompactRowTupleCursorLayout.heads,selected,Fin.addCases,emitted]
    · fin_cases b <;> rfl
  · fin_cases a <;> rfl

theorem initial_reload {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    CloseoutRowsMetadataReload.data (advanced gs p F w j C rows out) C
      (templates p w rows.length (j+1)) 0=advanced gs p F w j C rows out := by
  funext i
  cases hp : RecoveryFocus.pick CloseoutRowsMetadataReload.dest i with
  | none=>simp only [CloseoutRowsMetadataReload.data,hp]
  | some k=>
    have hi := RecoveryFocus.slot_of_pick CloseoutRowsMetadataReload.dest hp
    simp only [CloseoutRowsMetadataReload.data,hp,Nat.not_lt_zero,↓reduceIte]
    rw [←hi]
    fin_cases k <;> rfl

theorem metadata_fields {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    (∀ i,advanced gs p F w j C rows out (CloseoutRowsMetadataReload.source i)=templates p w rows.length (j+1) i) ∧
      advanced gs p F w j C rows out 104=List.replicate C true ∧
      advanced gs p F w j C rows out 105=List.replicate (C+1) false ∧
      (∀ i k,finalHeads gs p F w j rows out (CloseoutRowsMetadataReload.slots i k)=0) := by
  refine ⟨?_,rfl,rfl,?_⟩
  · intro i
    fin_cases i <;> rfl
  · intro i k
    fin_cases i <;> fin_cases k <;> rfl

theorem templates_bound (p w M j C : ℕ) (hc : 2*w+p+j+3≤C) :
    ∀ i,(templates p w M (j+1) i).length≤C := by
  intro i
  fin_cases i <;> simp [templates,CompareMachine.word,frame_length,SignedSortKey.binary_length] <;> omega

theorem advance_fields {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    finalTapes gs p F w j C rows out 39=frame (SignedSortKey.binary w 0) ∧
      finalTapes gs p F w j C rows out 40=frame (SignedSortKey.binary w
        (P1CompactRowTupleCutList.finalBound rows (RowTupleSubsets.selected w rows.length (j+1)) 0)) ∧
      finalTapes gs p F w j C rows out 46=CompareMachine.word (j+1) ∧
      finalTapes gs p F w j C rows out 108=CompareMachine.word (j+1) ∧
      finalTapes gs p F w j C rows out 110=List.replicate j true ∧
      finalTapes gs p F w j C rows out 103=List.replicate C false ∧
      finalTapes gs p F w j C rows out 105=List.replicate (C+1) false ∧
      (∀ i,finalHeads gs p F w j rows out (CloseoutRowsDegreeNext.frameSlots i)=0) ∧
      finalHeads gs p F w j rows out 46=1 ∧
      finalHeads gs p F w j rows out 108=0 ∧ finalHeads gs p F w j rows out 110=0 := by
  refine ⟨?_,?_,?_,rfl,rfl,rfl,rfl,?_,rfl,rfl,rfl⟩
  · simp [finalTapes,nativeEnd,P1CompactCloseoutRowsEnumeratedCuts.finished,P1CompactCloseoutRowsEnumeratedCuts.core,
      selected,P1CompactRowTupleCursorLayout.data,P1CompactRowTupleCursorBody.padding,Fin.addCases]
  · simp [finalTapes,nativeEnd,P1CompactCloseoutRowsEnumeratedCuts.finished,P1CompactCloseoutRowsEnumeratedCuts.core,
      selected,P1CompactRowTupleCursorLayout.data,P1CompactRowTupleCursorBody.padding,Fin.addCases]
  · simp [finalTapes,nativeEnd,P1CompactCloseoutRowsEnumeratedCuts.finished,P1CompactCloseoutRowsEnumeratedCuts.core,
      selected,P1CompactRowTupleCursorLayout.data,P1CompactRowTupleCursorBody.padding,Fin.addCases]
  · intro i
    fin_cases i <;> rfl

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsLoopInterface

/-! One executed degree transition: print and clean the positional cuts,
advance the retained counters, and reload six short templates. The joined
receipt has exactly the next degree's entry configuration. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeBody
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsLoopBoundary P1CompactCloseoutRowsLoopInterface
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first {s : ℕ} (callee : Machine 112 s) :=
  Composition.machine callee CloseoutRowsDegreeNext.machine
noncomputable def machine {s : ℕ} (callee : Machine 112 s) :=
  Composition.machine (first callee) CloseoutRowsMetadataReload.machine
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F w j C : ℕ)
    (rows : List (List Bool)) :=
  P1CompactCloseoutRowsReusableCuts.budget gs p F w j C rows+1+
    CloseoutRowsDegreeNext.budget w (j+1) j+1+6*(2*C+5)

theorem join_run {s n : ℕ} (callee : Machine 112 s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool)
    (work : ExecutionReceipt 112 s)
    (hr : runFrom callee (P1CompactCloseoutRowsReusableCuts.budget gs p F w j C rows)
      ⟨callee.start,inputHeads gs p F w j rows out,inputTapes gs p F w j C rows out⟩=some work)
    (hh : work.final.heads=finalHeads gs p F w j rows out)
    (ht : work.final.tapes=finalTapes gs p F w j C rows out)
    (hcopy : 4*w+3≤C) (hmeta : 2*w+p+j+3≤C)
    (h47 : RowTupleCursorReady.capacity gs.length w rows.length (j+2)≤C) :
    ∃ actual,runFrom (machine callee) (budget gs p F w j C rows)
      ⟨(machine callee).start,inputHeads gs p F w j rows out,inputTapes gs p F w j C rows out⟩=some actual ∧
      actual.final.heads=inputHeads gs p F w (j+1) rows (out++emitted gs p w j rows) ∧
      actual.final.tapes=inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) ∧
      actual.steps≤budget gs p F w j C rows := by
  obtain ⟨a0,a1,an,aTemplate,aj,a2,a3,aH,aN,aT,aJ⟩ := advance_fields gs p F w j C rows out
  obtain ⟨next,hn,nh,nt,_⟩ := CloseoutRowsDegreeNext.next_run
    (finalTapes gs p F w j C rows out) (finalHeads gs p F w j rows out)
    w _ (j+1) j C a0 a1 an aTemplate aj a2 a3 aH aN aT aJ hcopy (by omega)
  have hni : (⟨CloseoutRowsDegreeNext.machine.start,finalHeads gs p F w j rows out,
      finalTapes gs p F w j C rows out⟩ : Configuration 112 _)=
      Composition.restart work.final CloseoutRowsDegreeNext.machine.start := by
    apply configuration_ext
    · rfl
    · exact hh.symm
    · exact ht.symm
  rw [hni] at hn
  have hfirst := Composition.run_join callee CloseoutRowsDegreeNext.machine _ _ _ work next hr hn
  obtain ⟨hs,hd,hl,hH⟩ := metadata_fields gs p F w j C rows out
  obtain ⟨last,hLast,lh,lt,_⟩ := CloseoutRowsMetadataReload.reload_run
    (advanced gs p F w j C rows out) (finalHeads gs p F w j rows out) C
    (templates p w rows.length (j+1)) hs (templates_bound p w rows.length j C hmeta) hd hl hH
  rw [initial_reload] at hLast
  have hli : (⟨CloseoutRowsMetadataReload.machine.start,finalHeads gs p F w j rows out,
      advanced gs p F w j C rows out⟩ : Configuration 112 _)=
      Composition.restart (Composition.joinedReceipt work next).final CloseoutRowsMetadataReload.machine.start := by
    apply configuration_ext
    · rfl
    · exact nh.symm
    · exact nt.symm
  rw [hli] at hLast
  have whole := Composition.run_join (first callee) CloseoutRowsMetadataReload.machine _ _ _
    (Composition.joinedReceipt work next) last hfirst hLast
  refine ⟨_,whole,lh.trans (all_heads gs p F w j rows out),
    lt.trans (all_tapes gs p F w j C rows out h47),runFrom_steps_le (machine callee) _ _ _ whole⟩

theorem body_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w j C : ℕ) (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hj : j<Q) (hQp : Q≤p)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (hc : P1CompactCloseoutRowsComputedCuts.budget gs p F w j rows+1≤C)
    (ht : ∀ i,CloseoutRowsDegreeReset.selected i=true →
      ((rawInput gs p F w j rows out).tapes i).length≤C)
    (hcopy : 4*w+3≤C) (hmeta : 2*w+p+j+3≤C)
    (h47 : RowTupleCursorReady.capacity gs.length w rows.length (j+2)≤C) :
    ∃ actual,runFrom (machine worker) (budget gs p F w j C rows)
      ⟨(machine worker).start,inputHeads gs p F w j rows out,inputTapes gs p F w j C rows out⟩=some actual ∧
      actual.final.heads=inputHeads gs p F w (j+1) rows (out++emitted gs p w j rows) ∧
      actual.final.tapes=inputTapes gs p F w (j+1) C rows (out++emitted gs p w j rows) ∧
      actual.steps≤budget gs p F w j C rows := by
  obtain ⟨r,hr,rh,rt,_⟩ := worker_run gs p F Q w j C rows out hl hM hw hj hQp hp hF hc ht
  exact join_run worker gs p F w j C rows out r hr rh rt hcopy hmeta h47

theorem budget_le {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool))
    (hc : P1CompactCloseoutRowsComputedCuts.budget gs p F w j rows+1≤C)
    (hmeta : 2*w+p+j+3≤C) :
    budget gs p F w j C rows≤40*C+100 := by
  unfold budget P1CompactCloseoutRowsReusableCuts.budget CloseoutRowsDegreeClean.budget
    CloseoutRowsDegreeNext.budget
  omega

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeBody

namespace NearCubicWires.RepairOrdinary
theorem P1CompactCloseoutRowsDegreeBody_machine_unchanged : @P1CompactCloseoutRowsDegreeBody.machine = @CloseoutRowsDegreeBody.machine := rfl
end NearCubicWires.RepairOrdinary

/-! The literal Q driver executes only the required degree transitions.
Exhaustion includes its physical rewind; no body call at degree Q is
assumed. The growing cut pre is retained throughout the loop. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeLoop
open LocalBitMultitape RecoveryExecution P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsLoopBoundary
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine {t s : ℕ} (body : Machine t s) := RepeatMachine.machine body (fun _ _=>true)

theorem remaining {t s : ℕ} (body : Machine t s)
    (source : ℕ→List Bool→ Configuration t s) (emit : ℕ→List Bool) (cost Q : ℕ)
    (hstart : ∀ j<Q,∀ out,(source j out).control=body.start)
    (supplier : ∀ j<Q,∀ out,∃ r,runFrom body cost (source j out)=some r ∧
      r.final.heads=(source (j+1) (out++emit j)).heads ∧
      r.final.tapes=(source (j+1) (out++emit j)).tapes ∧ r.steps≤cost)
    (j n : ℕ) (out : List Bool) (hn : j+n=Q) :
    ∃ time≤n*(cost+2)+Q+3,Timed (machine body) time
      (RepeatMachine.cfg 0 (source j out) Q (j+1))
      (RepeatMachine.cfg 3 (source (j+n) (out++(List.range' j n).flatMap emit)) Q 1) := by
  induction n generalizing j out with
  | zero=>
    have hj : j=Q := by omega
    subst j
    refine ⟨Q+3,by simp,?_⟩
    simpa only [machine,Nat.add_zero,List.range'_zero,List.flatMap_nil,List.append_nil] using
      RepeatMachine.exhaust body (fun _ _=>true) (source Q out) Q
  | succ n ih=>
    have hj : j<Q := by omega
    obtain ⟨r,hr,rh,rt,rs⟩ := supplier j hj out
    have hstep := RepeatMachine.iteration body (fun _ _=>true) (source j out) Q j r
      (hstart j hj out) hj hr
    simp only [↓reduceIte] at hstep
    rw [P1CompactRowOccurrenceLoop.cfg_eq 0 r.final (source (j+1) (out++emit j)) Q (j+2) rh rt] at hstep
    obtain ⟨time,htime,htail⟩ := ih (j+1) (out++emit j) (by omega)
    rw [show j+1+1=j+2 by omega] at htail
    have whole := hstep.trans htail
    refine ⟨r.steps+2+time,by nlinarith,?_⟩
    have he : j+1+n=j+(n+1) := by omega
    simpa only [machine,List.range'_succ,List.flatMap_cons,List.append_assoc,he] using whole

theorem loop_run {t s : ℕ} (body : Machine t s)
    (source : ℕ→List Bool→ Configuration t s) (emit : ℕ→List Bool) (cost Q : ℕ)
    (hstart : ∀ j<Q,∀ out,(source j out).control=body.start)
    (supplier : ∀ j<Q,∀ out,∃ r,runFrom body cost (source j out)=some r ∧
      r.final.heads=(source (j+1) (out++emit j)).heads ∧
      r.final.tapes=(source (j+1) (out++emit j)).tapes ∧ r.steps≤cost)
    (out : List Bool) :
    ∃ r,runFrom (machine body) (Q*(cost+3)+3) (RepeatMachine.cfg 0 (source 0 out) Q 1)=some r ∧
      r.final=RepeatMachine.cfg 3 (source Q (out++(List.range Q).flatMap emit)) Q 1 ∧
      r.steps≤Q*(cost+3)+3 := by
  obtain ⟨time,hb,ht⟩ := remaining body source emit cost Q hstart supplier 0 Q out (by omega)
  simp only [Nat.zero_add,←List.range_eq_range'] at ht
  have hbound : time≤Q*(cost+3)+3 := by nlinarith
  obtain ⟨r,hr,hf,hs⟩ := ht.run
    (by simp [machine,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have more := runFrom_moreFuel (machine body) time (Q*(cost+3)+3-time) _ r hr
  rw [Nat.add_sub_of_le hbound] at more
  exact ⟨r,more,hf,hs.le.trans hbound⟩

noncomputable def entry {s n : ℕ} (body : Machine 112 s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) : Configuration 112 s :=
  ⟨body.start,inputHeads gs p F w j rows out,inputTapes gs p F w j C rows out⟩
def budget (Q C : ℕ) := Q*(40*C+103)+3

theorem degrees_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hQp : Q≤p)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (hc : ∀ j<Q,P1CompactCloseoutRowsComputedCuts.budget gs p F w j rows+1≤C)
    (ht : ∀ j<Q,∀ pre i,CloseoutRowsDegreeReset.selected i=true →
      ((rawInput gs p F w j rows pre).tapes i).length≤C)
    (hcopy : 4*w+3≤C) (hmeta : ∀ j<Q,2*w+p+j+3≤C)
    (h47 : ∀ j<Q,RowTupleCursorReady.capacity gs.length w rows.length (j+2)≤C) :
    ∃ actual,runFrom (machine (P1CompactCloseoutRowsDegreeBody.machine worker)) (budget Q C)
      (RepeatMachine.cfg 0 (entry (P1CompactCloseoutRowsDegreeBody.machine worker) gs p F w 0 C rows out) Q 1)=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (entry (P1CompactCloseoutRowsDegreeBody.machine worker) gs p F w Q C rows
          (out++(List.range Q).flatMap (fun j=>emitted gs p w j rows))) Q 1 ∧
      actual.steps≤budget Q C := by
  apply loop_run (P1CompactCloseoutRowsDegreeBody.machine worker)
    (fun j pre=>entry (P1CompactCloseoutRowsDegreeBody.machine worker) gs p F w j C rows pre)
    (fun j=>emitted gs p w j rows) (40*C+100) Q (by intro j hj pre; rfl) _ out
  intro j hj pre
  obtain ⟨r,hr,rh,rt,rs⟩ := P1CompactCloseoutRowsDegreeBody.body_run gs p F Q w j C rows pre
    hl hM hw hj hQp hp hF (hc j hj) (ht j hj pre) hcopy (hmeta j hj) (h47 j hj)
  have hb := P1CompactCloseoutRowsDegreeBody.budget_le gs p F w j C rows (hc j hj) (hmeta j hj)
  have more := runFrom_moreFuel (P1CompactCloseoutRowsDegreeBody.machine worker) _
    (40*C+100-P1CompactCloseoutRowsDegreeBody.budget gs p F w j C rows) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,rh,rt,rs.trans hb⟩

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeLoop

namespace NearCubicWires.RepairOrdinary
theorem P1CompactCloseoutRowsDegreeLoop_machine_unchanged : @P1CompactCloseoutRowsDegreeLoop.machine = @CloseoutRowsDegreeLoop.machine := rfl
end NearCubicWires.RepairOrdinary

/-! The physical degree loop may use its existing Q driver. Degrees above
the actual monomial count emit no positional subset, so no extra physical
min(Q,M) controller is needed and the exact cut list is unchanged. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeRange
open MatrixScoreBatch P1CompactCloseoutRowsCutMeaning P1CompactCloseoutRowsCacheInput
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem selected_nil (w M j : ℕ) (hw : M≤2^w) (hj : M≤j) :
    RowTupleSubsets.selected w M (j+1)=[] := by
  have h := RowTupleSubsets.selected_perm w M (j+1) hw
  have hb : (List.range M).length<j+1 := by simp; omega
  rw [List.sublistsLen_of_length_lt hb] at h
  exact List.perm_nil.mp h

theorem degree_nil {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (w j : ℕ) (rows : List (List Bool)) (hw : rows.length≤2^w) (hj : rows.length≤j) :
    degreeCuts gs w j rows=[] := by
  simp only [degreeCuts,selected_nil w rows.length j hw hj,List.map_nil]

theorem all_degrees {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (Q w : ℕ) (rows : List (List Bool)) (hw : rows.length≤2^w) :
    (List.range Q).flatMap (fun j=>degreeCuts gs w j rows)=
      (List.range (min Q rows.length)).flatMap (fun j=>degreeCuts gs w j rows) := by
  by_cases hQ : Q≤rows.length
  · rw [Nat.min_eq_left hQ]
  · have hM : rows.length≤Q := by omega
    rw [Nat.min_eq_right hM]
    clear hQ
    induction Q,hM using Nat.le_induction with
    | base => rfl
    | succ Q hQ ih =>
      simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
        List.append_nil,degree_nil gs w Q rows hw hQ,ih]

theorem polynomial_output {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (p Q : ℕ) (rows : List (List Bool)) :
    ((List.range Q).flatMap fun j=>P1CompactRowTupleCutList.output gs p rows
      (RowTupleSubsets.selected (RowTupleSubsets.digitWidth rows.length) rows.length (j+1)) ((-2 : ℤ)^j))=
      (CloseoutRows.orderedCuts (P1Radix.bits gs) Q (polynomial gs rows)).flatMap (cutWord p) := by
  rw [←P1CompactCloseoutRowsCutMeaning.polynomial_output gs p Q rows]
  simp_rw [degree_output]
  rw [←List.flatMap_assoc,←List.flatMap_assoc,
    all_degrees gs Q _ rows (RowTupleSubsets.digit_fit rows.length).le]

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsDegreeRange

/-! The executed degree loop prints exactly one polynomial's complete
signed-cut word, in the permitted positional order and with every duplicate
monomial occurrence retained. Its output cursor remains at the append end. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPolynomial
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsLoopBoundary
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def body := P1CompactCloseoutRowsDegreeBody.machine worker
noncomputable def machine := P1CompactCloseoutRowsDegreeLoop.machine body
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  RepeatMachine.cfg 0 (P1CompactCloseoutRowsDegreeLoop.entry body gs p F w 0 C rows out) Q 1

theorem output_fields {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    inputTapes gs p F w j C rows out 31=out ∧ inputHeads gs p F w j rows out 31=out.length := by
  have hf := P1CompactRowTupleCutList.fields (0 : Fin 1) gs p F w rows.length (j+1) rows [] 0 out 0 ((-2 : ℤ)^j)
  rw [P1CompactCloseoutRowsEnumeratedCuts.cfg_eq] at hf
  constructor
  · change ZeroPadding.pad 0 ((P1CompactCloseoutRowsEnumeratedCuts.core (0 : Fin 1) gs p F w (j+1)
      rows [] 0 out 0 ((-2 : ℤ)^j)).tapes 31)=out
    simpa only [ZeroPadding.pad_zero] using hf.2.2.1
  · exact hf.2.2.2

theorem polynomial_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : w=RowTupleSubsets.digitWidth rows.length) (hQp : Q≤p)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F)
    (hc : ∀ j<Q,P1CompactCloseoutRowsComputedCuts.budget gs p F w j rows+1≤C)
    (ht : ∀ j<Q,∀ pre i,CloseoutRowsDegreeReset.selected i=true →
      ((rawInput gs p F w j rows pre).tapes i).length≤C)
    (hcopy : 4*w+3≤C) (hmeta : ∀ j<Q,2*w+p+j+3≤C)
    (h47 : ∀ j<Q,RowTupleCursorReady.capacity gs.length w rows.length (j+2)≤C) :
    ∃ actual,runFrom machine (P1CompactCloseoutRowsDegreeLoop.budget Q C) (input gs p F Q w C rows out)=some actual ∧
      actual.final.tapes 31=out++
        (CloseoutRows.orderedCuts (P1Radix.bits gs) Q
          (P1CompactCloseoutRowsCacheInput.polynomial gs rows)).flatMap (MatrixScoreBatch.cutWord p) ∧
      actual.final.heads 31=(out++
        (CloseoutRows.orderedCuts (P1Radix.bits gs) Q
          (P1CompactCloseoutRowsCacheInput.polynomial gs rows)).flatMap (MatrixScoreBatch.cutWord p)).length ∧
      actual.final.heads 112=1 ∧ actual.final.tapes 112=CompareMachine.word Q ∧
      actual.steps≤P1CompactCloseoutRowsDegreeLoop.budget Q C := by
  have hfit : rows.length<2^w := by rw [hw]; exact RowTupleSubsets.digit_fit rows.length
  obtain ⟨actual,ha,hf,hs⟩ := P1CompactCloseoutRowsDegreeLoop.degrees_run gs p F Q w C rows out
    hl hM hfit hQp hp hF hc ht hcopy hmeta h47
  have hout : (List.range Q).flatMap (fun j=>emitted gs p w j rows)=
      (CloseoutRows.orderedCuts (P1Radix.bits gs) Q
        (P1CompactCloseoutRowsCacheInput.polynomial gs rows)).flatMap (MatrixScoreBatch.cutWord p) := by
    rw [hw]
    exact P1CompactCloseoutRowsDegreeRange.polynomial_output gs p Q rows
  refine ⟨actual,ha,?_,?_,?_,?_,hs⟩
  · rw [hf]
    change inputTapes gs p F w Q C rows (out++(List.range Q).flatMap (fun j=>emitted gs p w j rows)) 31=_
    rw [(output_fields gs p F w Q C rows _).1,hout]
  · rw [hf]
    change inputHeads gs p F w Q rows (out++(List.range Q).flatMap (fun j=>emitted gs p w j rows)) 31=_
    rw [(output_fields gs p F w Q C rows _).2,hout]
  · rw [hf]
    rfl
  · rw [hf]
    rfl

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPolynomial

namespace NearCubicWires.RepairOrdinary
theorem P1CompactCloseoutRowsPolynomial_machine_unchanged : @P1CompactCloseoutRowsPolynomial.machine = @CloseoutRowsPolynomial.machine := rfl
end NearCubicWires.RepairOrdinary

/-! One shared digit width may serve an entire live-family bank. Changing
the binary enumeration width only permutes positional subsets; no repeated
monomial or cut is removed and the matrix coordinate width is unchanged. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSharedDigits
open P1CompactCloseoutRowsCutMeaning P1CompactCloseoutRowsCacheInput MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cuts {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (Q w : ℕ) (rows : List (List Bool)) :=
  (List.range Q).flatMap (fun j=>degreeCuts gs w j rows)

theorem degree_perm {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (w j : ℕ) (rows : List (List Bool)) (hw : rows.length≤2^w) :
    (degreeCuts gs w j rows).Perm
      (degreeCuts gs (RowTupleSubsets.digitWidth rows.length) j rows) := by
  exact ((RowTupleSubsets.selected_perm w rows.length (j+1) hw).trans
    (RowTupleSubsets.chosen_perm rows.length (j+1)).symm).map _

theorem canonical_cuts {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (Q : ℕ) (rows : List (List Bool)) :
    cuts gs Q (RowTupleSubsets.digitWidth rows.length) rows=
      CloseoutRows.orderedCuts (P1Radix.bits gs) Q (polynomial gs rows) := by
  rw [cuts,P1CompactCloseoutRowsDegreeRange.all_degrees gs Q _ rows (RowTupleSubsets.digit_fit rows.length).le]
  simp only [CloseoutRows.orderedCuts,RowTupleTerms.terms,polynomial,List.length_map,
    List.map_flatMap,List.map_map,Function.comp_def,degreeCuts]

theorem cuts_perm {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (Q w : ℕ) (rows : List (List Bool)) (hw : rows.length≤2^w) :
    (cuts gs Q w rows).Perm
      (CloseoutRows.orderedCuts (P1Radix.bits gs) Q (polynomial gs rows)) := by
  rw [←canonical_cuts gs Q rows]
  apply List.Perm.flatMap_left
  intro j _
  exact degree_perm gs w j rows hw

theorem emitted_word {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (p Q w : ℕ) (rows : List (List Bool)) :
    (List.range Q).flatMap (fun j=>P1CompactCloseoutRowsLoopBoundary.emitted gs p w j rows)=
      (cuts gs Q w rows).flatMap (cutWord p) := by
  simp only [P1CompactCloseoutRowsLoopBoundary.emitted,degree_output,cuts,List.flatMap_assoc]

theorem batch_perm {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (Q w : ℕ) (bank : List (List (List Bool))) (hw : ∀ rows∈bank,rows.length≤2^w) :
    (bank.flatMap (cuts gs Q w)).Perm
      (RowPowerBinLift.batch (P1Radix.bits gs) Q (family gs bank)) := by
  have hp : (bank.flatMap (cuts gs Q w)).Perm
      (bank.flatMap (fun rows=>CloseoutRows.orderedCuts (P1Radix.bits gs) Q (polynomial gs rows))) := by
    apply List.Perm.flatMap_left
    intro rows hr
    exact cuts_perm gs Q w rows (hw rows hr)
  exact hp.trans (by simpa only [CloseoutRows.orderedBatch,family,List.flatMap_map] using
    CloseoutRows.ordered_batch_perm (P1Radix.bits gs) Q (family gs bank))

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSharedDigits

/-! The shared digit-width family inhabits the literal row input and
count-table premises. The cache width, single successor widening, scalar
width and complete matrix dimensions are inherited without alteration. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSharedInput
open MatrixScoreBatch P1CompactCloseoutRowsCacheInput P1CompactCloseoutRowsSharedDigits
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def input (s Q w : ℕ) (gs : List (ExactThresholdGate ((s+1)/2+s/2))) [_radix : P1Radix gs]
    (bank : List (List (List Bool))) (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (family gs bank)).length^100 ≤ 2^s)
    (hw : ∀ rows∈bank,rows.length ≤ 2^w) : EquationRow.Input :=
  let base := P1CompactCloseoutRowsCacheInput.input s Q gs bank hs hg
  let hp := (batch_perm gs Q w bank hw).trans
    (CloseoutRows.ordered_batch_perm (P1Radix.bits gs) Q (family gs bank)).symm
  { d:=base.d, p:=base.p, odd:=base.odd, cuts:=bank.flatMap (cuts gs Q w)
    lengths:=fun c hc=>base.lengths c (hp.mem_iff.mp hc)
    fits:=fun c hc=>base.fits c (hp.mem_iff.mp hc)
    oddPositive:=base.oddPositive
    gateSquare:=by rw [hp.length_eq]; exact base.gateSquare }

theorem input_perm (s Q w : ℕ) (gs : List (ExactThresholdGate ((s+1)/2+s/2))) [_radix : P1Radix gs]
    (bank : List (List (List Bool))) (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (family gs bank)).length^100 ≤ 2^s)
    (hw : ∀ rows∈bank,rows.length ≤ 2^w) :
    (input s Q w gs bank hs hg hw).cuts.Perm
      (RowPowerBinLift.batch (P1Radix.bits gs) Q (family gs bank)) :=
  batch_perm gs Q w bank hw

theorem common_width (s Q w : ℕ) (gs : List (ExactThresholdGate ((s+1)/2+s/2))) [_radix : P1Radix gs]
    (bank : List (List (List Bool))) (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (family gs bank)).length^100 ≤ 2^s)
    (hw : ∀ rows∈bank,rows.length ≤ 2^w) :
    (EquationRow.request (input s Q w gs bank hs hg hw)).p=
      (P1Radix.bits gs)*(gs.length*Q)+Q+1 := rfl

theorem count_modEq (s Q w : ℕ) (gs : List (ExactThresholdGate ((s+1)/2+s/2))) [_radix : P1Radix gs]
    (bank : List (List (List Bool))) (hs : 67 ≤ s)
    (hg : (RowBinLift.batch Q (family gs bank)).length^100 ≤ 2^s)
    (hw : ∀ rows∈bank,rows.length ≤ 2^w)
    (i j : Fin (EquationRow.request (input s Q w gs bank hs hg hw)).U) :
    Int.ModEq ((2 : ℤ)^Q)
      (SupplierPrinter.weightedDominance
        (leftScore (EquationRow.request (input s Q w gs bank hs hg hw)))
        (rightScore (EquationRow.request (input s Q w gs bank hs hg hw)))
        (weight (EquationRow.request (input s Q w gs bank hs hg hw))) i j)
      (CompetitorCountTable.rowValues (family gs bank) (input s Q w gs bank hs hg hw) i j) :=
  CompetitorRowCountMeaning.request_modEq_perm (P1Radix.bits gs) Q
    (family gs bank) (input s Q w gs bank hs hg hw) (input_perm s Q w gs bank hs hg hw)
    (family_fit gs bank) i j

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSharedInput

/-! Coarse preparation bounds for the actual positional enumerator and
cut consumer. Only the digit exponent contains the monomial population;
native cache and matrix widths occur polynomially outside that exponent. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def scale (n p F w N Q : ℕ) := n+p+F+w+N+Q+1
def capacity (n p F w N Q : ℕ) :=
  4096*(scale n p F w N Q)^4*2^(w*(Q+1))
def tupleEnvelope (n N p F w M k : ℕ) :=
  2*RowTupleCursorReady.capacity N w M k+N*k+
    P1CompactRowCommonFixedCapacity.budget n F+2*F+4*p+30

theorem tuple_budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w M : ℕ) (rows : List (List Bool)) (ds : List ℕ)
    (hl : ∀ row∈rows,row.length=gs.length) (hd : ∀ d∈ds,d<rows.length) :
    P1CompactRowTupleCutBody.budget gs p F w M rows ds+2 ≤ tupleEnvelope n gs.length p F w M ds.length := by
  have hc := P1CompactRowTupleEquationBounds.count_le gs.length rows ds hl hd
  unfold P1CompactRowTupleCutBody.budget P1CompactRowTupleFramedBody.budget P1CompactRowTupleCursorBody.budget
    P1CompactRowTupleCursorEquation.budget RowTupleMaskReady.budget RowTupleMaskReady.capacity tupleEnvelope
    RowTupleCursorReady.capacity
  omega

theorem tuple_envelope_le (n N p F w M k U S : ℕ)
    (hn : n ≤ S) (hN : N ≤ S) (hp : p ≤ S) (hF : F ≤ S)
    (hw : w ≤ S) (hk : k ≤ S) (hM : M ≤ U) (hU : 1 ≤ U) (hS : 1 ≤ S) :
    tupleEnvelope n N p F w M k ≤ 1024*U*S^3 := by
  unfold tupleEnvelope RowTupleCursorReady.capacity RowTupleMaskLoop.budget RowTupleMaskBody.budget
    RowMaskLookupReusable.capacity RowMaskLookup.budget P1CompactRowCommonFixedCapacity.budget
  calc
    _ ≤ 2*(S*(2*(U*(2*S+8*S+15)+8*S+14+S*(4*S+21)+2*S+4*S+8)+4*S+5+3)+3)+
        S*S+((S+1)*(4*S+2*S+20)+3)+2*S+4*S+30 := by gcongr
    _ ≤ 1024*U*S^3 := by
      have h12 : S ≤ S^2 := by nlinarith
      have h23 : S^2 ≤ S^3 := by nlinarith [Nat.mul_le_mul_left S h12]
      have hu0 : U ≤ U*S^3 := by nlinarith [Nat.mul_le_mul_left U (hS.trans (h12.trans h23))]
      have hu1 : U*S ≤ U*S^3 := Nat.mul_le_mul_left U (h12.trans h23)
      have hu2 : U*S^2 ≤ U*S^3 := Nat.mul_le_mul_left U h23
      have h3u : S^3 ≤ U*S^3 := by nlinarith [Nat.mul_le_mul_right (S^3) hU]
      nlinarith

theorem enumeration_le (w k Q S : ℕ) (hw : w ≤ S) (hk : k ≤ S)
    (hQ : k ≤ Q) (hS : 1 ≤ S) :
    RowTupleEnumerationReady.budget w k ≤ 1024*2^(w*Q)*S^2 := by
  have he : 2^(w*k) ≤ 2^(w*Q) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left w hQ)
  have hE : 1 ≤ 2^(w*Q) := Nat.one_le_two_pow
  unfold RowTupleEnumerationReady.budget RowTupleDerivedEnumeration.budget
    RowTupleDerivedEnumeration.metadataTime RowTupleDerivedEnumeration.productTime RowTupleLimit.budget
    RowTupleColdEnumeration.budget RowTupleColdFields.time RowTupleEnumeration.time
  calc
    _ ≤ 2*(2*(S*(2*S+3)+2)+2+1+(10*(S*S)+45)+1+
        ((8*S+4*(S*S)+18)+1+(2^(w*Q)*(S*(52*S+68)+40)+1+2)))+2 := by gcongr
    _ ≤ 1024*2^(w*Q)*S^2 := by
      have h12 : S ≤ S^2 := by nlinarith
      have hu0 : 2^(w*Q) ≤ 2^(w*Q)*S^2 := by
        nlinarith [Nat.mul_le_mul_left (2^(w*Q)) (hS.trans h12)]
      have hu1 : 2^(w*Q)*S ≤ 2^(w*Q)*S^2 := Nat.mul_le_mul_left _ h12
      have h2u : S^2 ≤ 2^(w*Q)*S^2 := by nlinarith [Nat.mul_le_mul_right (S^2) hE]
      nlinarith

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparationBounds

/-! One concrete preparation capacity covers every degree of every
polynomial whose monomial count fits the shared digit width. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparationFits
open P1CompactCloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scale_fields (n p F w N Q : ℕ) :
    1 ≤ scale n p F w N Q ∧ n ≤ scale n p F w N Q ∧ p ≤ scale n p F w N Q ∧
      F ≤ scale n p F w N Q ∧ w ≤ scale n p F w N Q ∧ N ≤ scale n p F w N Q ∧
      Q+1 ≤ scale n p F w N Q := by unfold scale; omega

theorem selected_length (w M k : ℕ) : (RowTupleSubsets.selected w M k).length ≤ 2^(w*k) := by
  have h := List.length_filter_le (RowTupleSubsets.valid M) (RowTupleDigits.candidates w k)
  simpa only [RowTupleSubsets.selected,RowTupleDigits.candidates,List.length_map,List.length_range] using h

theorem list_budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w k S : ℕ) (rows : List (List Bool))
    (hl : ∀ row∈rows,row.length=gs.length) (hM : rows.length ≤ 2^w)
    (hn : n ≤ S) (hN : gs.length ≤ S) (hp : p ≤ S) (hF : F ≤ S)
    (hw : w ≤ S) (hk : k ≤ S) (hS : 1 ≤ S) :
    P1CompactRowTupleCutList.budget gs p F w rows.length rows (RowTupleSubsets.selected w rows.length k) ≤
      2^(w*k)*(1024*2^w*S^3)+1 := by
  have hb : ∀ ds∈RowTupleSubsets.selected w rows.length k,
      P1CompactRowTupleCutBody.budget gs p F w rows.length rows ds+2 ≤ 1024*2^w*S^3 := by
    intro ds hd
    obtain ⟨hlen,hvalid⟩ := P1CompactRowTupleSelectedList.selected_fields w rows.length k ds hd
    have h := tuple_budget gs p F w rows.length rows ds hl hvalid
    rw [hlen] at h
    exact h.trans (tuple_envelope_le n gs.length p F w rows.length k (2^w) S
      hn hN hp hF hw hk hM Nat.one_le_two_pow hS)
  have hs := RowBinLift.sum_le_length_mul
    ((RowTupleSubsets.selected w rows.length k).map (fun ds=>P1CompactRowTupleCutBody.budget gs p F w rows.length rows ds+2))
    (1024*2^w*S^3) (by
      intro x hx
      obtain ⟨ds,hd,rfl⟩ := List.mem_map.mp hx
      exact hb ds hd)
  rw [List.length_map] at hs
  unfold P1CompactRowTupleCutList.budget
  exact Nat.add_le_add_right (hs.trans (Nat.mul_le_mul_right _ (selected_length w rows.length k))) 1

theorem computed_fits {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w j : ℕ) (rows : List (List Bool))
    (hl : ∀ row∈rows,row.length=gs.length) (hM : rows.length ≤ 2^w) (hj : j<Q) :
    P1CompactCloseoutRowsComputedCuts.budget gs p F w j rows+1 ≤ capacity n p F w gs.length Q := by
  let S := scale n p F w gs.length Q
  obtain ⟨hS,hn,hp,hF,hw,hN,hQ⟩ := scale_fields n p F w gs.length Q
  have hk : j+1 ≤ S := by dsimp only [S]; omega
  have hE : 1 ≤ 2^(w*Q) := Nat.one_le_two_pow
  have hU : 1 ≤ 2^w := Nat.one_le_two_pow
  have he := enumeration_le w (j+1) Q S hw hk (by omega) hS
  have hlb := list_budget gs p F w (j+1) S rows hl hM hn hN hp hF hw hk hS
  have hpow : 2^(w*(j+1)) ≤ 2^(w*Q) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left w (by omega))
  have hlist := hlb.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hpow) 1)
  have h24 : S^2 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  have h34 : S^3 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  have h14 : S ≤ S^4 := by simpa only [pow_one] using Nat.pow_le_pow_right hS (show 1 ≤ 4 by decide)
  have hp1 : S ≤ 2^(w*Q)*2^w*S^4 := by
    calc
      S ≤ S^4 := h14
      _ ≤ 2^(w*Q)*2^w*S^4 := by nlinarith [Nat.mul_le_mul_right (S^4) (Nat.mul_le_mul hE hU)]
  have hp2 : 2^(w*Q)*S^2 ≤ 2^(w*Q)*2^w*S^4 := by
    calc
      _ ≤ 2^(w*Q)*S^4 := Nat.mul_le_mul_left _ h24
      _ ≤ 2^(w*Q)*2^w*S^4 := by nlinarith [Nat.mul_le_mul_left (2^(w*Q)*S^4) hU]
  have hp3 : 2^(w*Q)*2^w*S^3 ≤ 2^(w*Q)*2^w*S^4 := Nat.mul_le_mul_left _ h34
  have hcap : capacity n p F w gs.length Q=4096*(2^(w*Q)*2^w*S^4) := by
    unfold capacity
    rw [Nat.mul_add,Nat.mul_one,pow_add]
    dsimp only [S]
    ring
  rw [hcap]
  change (6*j+8*p+43)+1+(RowTupleEnumerationReady.budget w (j+1)+1+
    P1CompactRowTupleCutList.budget gs p F w rows.length rows (RowTupleSubsets.selected w rows.length (j+1)))+1 ≤ _
  change p ≤ S at hp
  change 1 ≤ S at hS
  nlinarith

theorem cursor_fits (n p F w N Q M k : ℕ)
    (hM : M ≤ 2^w) (hk : k ≤ Q+1) :
    RowTupleCursorReady.capacity N w M k ≤ capacity n p F w N Q := by
  let S := scale n p F w N Q
  obtain ⟨hS,hn,hp,hF,hw,hN,hQ⟩ := scale_fields n p F w N Q
  have h := tuple_envelope_le n N p F w M k (2^w) S hn hN hp hF hw
    (hk.trans hQ) hM Nat.one_le_two_pow hS
  have hbase : RowTupleCursorReady.capacity N w M k ≤ tupleEnvelope n N p F w M k := by unfold tupleEnvelope; omega
  have h34 : S^3 ≤ S^4 := Nat.pow_le_pow_right hS (by decide)
  have he : 2^w ≤ 2^(w*(Q+1)) := Nat.pow_le_pow_right (by decide) (by nlinarith)
  calc
    _ ≤ 1024*2^w*S^3 := hbase.trans h
    _ ≤ 4096*2^(w*(Q+1))*S^4 := by gcongr; omega
    _ = capacity n p F w N Q := by unfold capacity; dsimp only [S]; ring

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparationFits

/-! The concrete shared preparation capacity discharges the actual native
metadata and every selected initial work-tape extent. The growing output
prefix is absent from all of these bounds. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparationInput
open P1CompactCloseoutRowsPreparationBounds P1CompactCloseoutRowsPreparationFits
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem small_fits (n p F w N Q : ℕ) :
    16*scale n p F w N Q ≤ capacity n p F w N Q := by
  have hS := (scale_fields n p F w N Q).1
  have hpow : scale n p F w N Q ≤ (scale n p F w N Q)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hS (show 1 ≤ 4 by decide)
  have he : 1 ≤ 2^(w*(Q+1)) := Nat.one_le_two_pow
  unfold capacity
  nlinarith [Nat.mul_le_mul_right ((scale n p F w N Q)^4) he]

theorem metadata_fits (n p F w N Q j : ℕ) (hj : j<Q) :
    4*w+3 ≤ capacity n p F w N Q ∧ 2*w+p+j+3 ≤ capacity n p F w N Q := by
  have h := small_fits n p F w N Q
  unfold scale at h
  omega

theorem native_fits {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w j : ℕ) (rows : List (List Bool)) (hM : rows.length ≤ 2^w) (hj : j<Q)
    (out : List Bool) (i : Fin 49) (hi : CloseoutRowsDegreeReset.selected (i.castAdd 54)=true) :
    ((rawInput gs p F w j rows out).tapes (i.castAdd 54)).length ≤ capacity n p F w gs.length Q := by
  have hc := cursor_fits n p F w gs.length Q rows.length (j+1) hM (by omega)
  have hm := (metadata_fits n p F w gs.length Q j hj).2
  have h : i.val=44 ∨ i.val=47 ∨ i.val=48 ∨ 49 ≤ i.val := by
    simpa [CloseoutRowsDegreeReset.selected,Fin.ext_iff] using hi
  rcases h with h | h | h | h
  · have he : i=44 := Fin.ext h
    subst i
    simp [rawInput,P1CompactCloseoutRowsComputedCuts.input,P1CompactCloseoutRowsComputedCuts.body,
      P1CompactCloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,P1CompactCloseoutRowsEnumeratedCuts.core,
      P1CompactRowTupleCursorBody.padding,P1CompactRowTupleCursorLayout.data,Fin.addCases,ZeroPadding.pad]
  · have he : i=47 := Fin.ext h
    subst i
    simpa [rawInput,P1CompactCloseoutRowsComputedCuts.input,P1CompactCloseoutRowsComputedCuts.body,
      P1CompactCloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,P1CompactCloseoutRowsEnumeratedCuts.core,
      P1CompactRowTupleCursorBody.padding,P1CompactRowTupleCursorLayout.data,Fin.addCases,ZeroPadding.pad] using hc
  · have he : i=48 := Fin.ext h
    subst i
    simp [rawInput,P1CompactCloseoutRowsComputedCuts.input,Fin.addCases]
  · have hb:=i.isLt
    omega

theorem enum_fits {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w j : ℕ) (rows : List (List Bool)) (hj : j<Q)
    (out : List Bool) (i : Fin 40) :
    ((rawInput gs p F w j rows out).tapes ((i.natAdd 49).castAdd 14)).length ≤ capacity n p F w gs.length Q := by
  have hm := (metadata_fits n p F w gs.length Q j hj).2
  have hi : (i.natAdd 49 : Fin 89)≠48 := by
    intro h
    have hv:=congrArg Fin.val h
    change 49+i.val=48 at hv
    omega
  simp only [rawInput,P1CompactCloseoutRowsComputedCuts.input,Fin.addCases_left,Function.update_of_ne hi,
    P1CompactCloseoutRowsComputedCuts.body,P1CompactCloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,Fin.addCases_right]
  simp only [P1CompactRowTupleEnumeratedEquations.extra]
  split_ifs <;> simp [CompareMachine.word,frame_length,SignedSortKey.binary_length] <;> omega

theorem coefficient_fits {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w j : ℕ) (rows : List (List Bool)) (hj : j<Q)
    (out : List Bool) (i : Fin 14) :
    ((rawInput gs p F w j rows out).tapes (i.natAdd 89)).length ≤ capacity n p F w gs.length Q := by
  have hm := (metadata_fits n p F w gs.length Q j hj).2
  simp only [rawInput,P1CompactCloseoutRowsComputedCuts.input,Fin.addCases_right]
  fin_cases i <;> simp [CloseoutRowsDegreeCoefficient.input] <;> omega

theorem selected_fits {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w j : ℕ) (rows : List (List Bool)) (hM : rows.length ≤ 2^w) (hj : j<Q) :
    ∀ out i,CloseoutRowsDegreeReset.selected i=true →
      ((rawInput gs p F w j rows out).tapes i).length ≤ capacity n p F w gs.length Q := by
  intro out i
  refine Fin.addCases (m:=89) (n:=14) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=49) (n:=40) (fun b=>?_) (fun b=>?_) a
    · exact native_fits gs p F Q w j rows hM hj out b
    · intro _
      exact enum_fits gs p F Q w j rows hj out b
  · intro _
    exact coefficient_fits gs p F Q w j rows hj out a

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparationInput

/-! The complete polynomial program starts its added scratch suffixes
blank. Reverse zero-padding simulation preserves every transition and the
actual output bytes. Only the true C driver remains a required native field. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsColdScratch
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extraCaps (C : ℕ) : Fin 9→ℕ :=
  Fin.addCases (m:=3) (n:=6) (motive:=fun _=>ℕ) ![C,0,C+1] (fun _=>0)
def capacities (C : ℕ) : Fin 113→ℕ :=
  Fin.addCases (m:=112) (n:=1) (motive:=fun _=>ℕ)
    (Fin.addCases (m:=103) (n:=9) (motive:=fun _=>ℕ) (CloseoutRowsDegreeReset.caps C) (extraCaps C))
    (fun _=>0)
def coldExtra (p w M C : ℕ) : Fin 9→List Bool :=
  Fin.addCases (m:=3) (n:=6) (motive:=fun _=>List Bool)
    ![[],List.replicate C true,[]] (templates p w M 0)
noncomputable def coldTapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w C : ℕ) (rows : List (List Bool)) (out : List Bool) : Fin 112→List Bool :=
  Fin.addCases (m:=103) (n:=9) (motive:=fun _=>List Bool)
    (rawInput gs p F w 0 rows out).tapes (coldExtra p w rows.length C)
noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  RepeatMachine.cfg 0
    (⟨P1CompactCloseoutRowsPolynomial.body.start,inputHeads gs p F w 0 rows out,coldTapes gs p F w C rows out⟩ :
      Configuration 112 _) Q 1

theorem padded_input {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    ZeroPadding.config (capacities C) (input gs p F Q w C rows out)=
      P1CompactCloseoutRowsPolynomial.input gs p F Q w C rows out := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (m:=112) (n:=1) (fun a=>?_) (fun a=>?_) i
    · simp only [ZeroPadding.config,input,P1CompactCloseoutRowsPolynomial.input,RepeatMachine.cfg,
        controlConfig,TapeEmbedding.config,Fin.addCases_left,P1CompactCloseoutRowsDegreeLoop.entry]
      refine Fin.addCases (m:=103) (n:=9) (fun b=>?_) (fun b=>?_) a
      · simp only [capacities,coldTapes,inputTapes,Fin.addCases_left]
      · fin_cases b <;> simp [capacities,extraCaps,coldTapes,coldExtra,inputTapes,extra,
          Fin.addCases,ZeroPadding.pad]
    · fin_cases a
      exact ZeroPadding.pad_zero _

theorem from_receipt {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C fuel : ℕ) (rows : List (List Bool)) (out : List Bool)
    (source : ExecutionReceipt 113 _)
    (hr : runFrom P1CompactCloseoutRowsPolynomial.machine fuel
      (P1CompactCloseoutRowsPolynomial.input gs p F Q w C rows out)=some source) :
    ∃ actual,runFrom P1CompactCloseoutRowsPolynomial.machine fuel (input gs p F Q w C rows out)=some actual ∧
      actual.final.heads=source.final.heads ∧
      actual.final.tapes 31=source.final.tapes 31 ∧
      actual.final.tapes 112=source.final.tapes 112 ∧
      actual.steps=source.steps ∧ actual.peakTapeCells ≤ source.peakTapeCells := by
  rw [←padded_input gs p F Q w C rows out] at hr
  obtain ⟨actual,ha,hf,hs,hp⟩ := ZeroPadding.run_unpad P1CompactCloseoutRowsPolynomial.machine
    (capacities C) fuel (input gs p F Q w C rows out) source hr
  refine ⟨actual,ha,?_,?_,?_,hs,hp⟩
  · have hh := congrArg Configuration.heads hf
    exact hh
  · have h := congrArg (fun c=>c.tapes 31) hf
    change ZeroPadding.pad 0 (actual.final.tapes 31)=source.final.tapes 31 at h
    simpa only [ZeroPadding.pad_zero] using h
  · have h := congrArg (fun c=>c.tapes 112) hf
    change ZeroPadding.pad 0 (actual.final.tapes 112)=source.final.tapes 112 at h
    simpa only [ZeroPadding.pad_zero] using h

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsColdScratch

/-! One whole polynomial executes at the actual common preparation capacity.
All degree, scratch, cursor and metadata inequalities are discharged here.
The enclosing bank still supplies the native source data and true C driver. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparedPolynomial
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsLoopBoundary
open P1CompactCloseoutRowsPreparationBounds P1CompactCloseoutRowsPreparationFits P1CompactCloseoutRowsPreparationInput
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem polynomial_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (p F Q w : ℕ) (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hQp : Q ≤ p)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q ≤ p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F) :
    ∃ actual,runFrom P1CompactCloseoutRowsPolynomial.machine
      (P1CompactCloseoutRowsDegreeLoop.budget Q (capacity (l+r) p F w gs.length Q))
      (P1CompactCloseoutRowsColdScratch.input gs p F Q w (capacity (l+r) p F w gs.length Q) rows out)=some actual ∧
      actual.final.tapes 31=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p) ∧
      actual.final.heads 31=(out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)).length ∧
      actual.final.tapes 112=CompareMachine.word Q ∧ actual.final.heads 112=1 ∧
      actual.steps ≤ P1CompactCloseoutRowsDegreeLoop.budget Q (capacity (l+r) p F w gs.length Q) := by
  let C := capacity (l+r) p F w gs.length Q
  have hcopy : 4*w+3 ≤ C := by
    have h := small_fits (l+r) p F w gs.length Q
    unfold scale at h
    dsimp only [C]
    omega
  obtain ⟨source,hs,sf,ss⟩ := P1CompactCloseoutRowsDegreeLoop.degrees_run gs p F Q w C rows out hl hM hw hQp hp hF
    (fun j hj=>computed_fits gs p F Q w j rows hl hw.le hj)
    (fun j hj=>selected_fits gs p F Q w j rows hw.le hj) hcopy
    (fun j hj=>(metadata_fits (l+r) p F w gs.length Q j hj).2)
    (fun j hj=>cursor_fits (l+r) p F w gs.length Q rows.length (j+2) hw.le (by omega))
  obtain ⟨actual,ha,ah,atape,ad,asteps,_⟩ := P1CompactCloseoutRowsColdScratch.from_receipt gs p F Q w C _ rows out source hs
  have hout := P1CompactCloseoutRowsSharedDigits.emitted_word gs p Q w rows
  refine ⟨actual,ha,?_,?_,?_,?_,asteps.le.trans ss⟩
  · rw [atape,sf]
    change inputTapes gs p F w Q C rows (out++(List.range Q).flatMap (fun j=>emitted gs p w j rows)) 31=_
    rw [(P1CompactCloseoutRowsPolynomial.output_fields gs p F w Q C rows _).1,hout]
  · rw [ah,sf]
    change inputHeads gs p F w Q rows (out++(List.range Q).flatMap (fun j=>emitted gs p w j rows)) 31=_
    rw [(P1CompactCloseoutRowsPolynomial.output_fields gs p F w Q C rows _).2,hout]
  · rw [ad,sf]
    rfl
  · rw [ah,sf]
    rfl

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPreparedPolynomial

/-! The enclosing family controller has one fixed head pattern and one
common native-port extent. Neither contains the accumulated cut prefix. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsBankFields
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsPreparationBounds
open P1CompactCloseoutRowsPreparationFits P1CompactCloseoutRowsPreparationInput
open RepairSource.VerifierDecoding RepairRepresentation RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raised (i : Fin 113) : Bool :=
  decide (i=15 ∨ i=18 ∨ i=24 ∨ i=35 ∨ i=37 ∨ i=38 ∨ i=45 ∨ i=46 ∨ i=112)
def heads (out : List Bool) (i : Fin 113) := if i=31 then out.length else if raised i then 1 else 0

theorem native_heads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w j : ℕ) (rows : List (List Bool)) (out : List Bool) :
    inputHeads gs p F w j rows out = fun i=>heads out (i.castAdd 1) := by
  funext i
  fin_cases i <;> rfl

theorem polynomial_heads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    (P1CompactCloseoutRowsPolynomial.input gs p F Q w C rows out).heads=heads out := by
  funext i
  refine Fin.addCases (m:=112) (n:=1) (fun j=>?_) (fun j=>?_) i
  · simpa only [P1CompactCloseoutRowsPolynomial.input,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      Fin.addCases_left,P1CompactCloseoutRowsDegreeLoop.entry] using congrFun (native_heads gs p F w 0 rows out) j
  · fin_cases j
    rfl

theorem cache_bounds {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p F Q : ℕ)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F) :
    (exactListWord gs).length+1 ≤ F ∧
      RowCachedCoordinateBounds.inner (P1Radix.bits gs)+1 ≤ F ∧
      RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) ≤ F := by
  have hlarge : 16384*RowCachedCoordinateBounds.size gs (P1Radix.bits gs) ≤ F := by
    unfold P1CompactRowCommonBounds.capacity at hF
    have hmono := Nat.mul_le_mul_right (16384*RowCachedCoordinateBounds.size gs (P1Radix.bits gs))
      (show 1 ≤ gs.length*Q+1 by omega)
    nlinarith
  refine ⟨?_,?_,(P1CompactRowCommonBounds.inner_fits gs (gs.length*Q) p).trans hF⟩
  · unfold RowCachedCoordinateBounds.size P1Radix.bits at hlarge
    omega
  · unfold RowCachedCoordinateBounds.size at hlarge
    unfold RowCachedCoordinateBounds.inner
    omega

theorem common_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w : ℕ) (out : List Bool) (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (i : Fin 35) (hi : i≠31) :
    (P1CompactRowCommonReusable.data gs 0 p F [] out [] i).length ≤ capacity n p F w gs.length Q := by
  obtain ⟨hcache,hinner,houter⟩ := cache_bounds gs p F Q hF
  have hsmall := small_fits n p F w gs.length Q
  have hbits : P1Radix.bits gs ≤ F := by
    unfold RowCachedCoordinateBounds.inner at hinner
    omega
  unfold scale at hsmall
  fin_cases i <;> first | contradiction |
    simp [P1CompactRowCommonReusable.data,P1CompactRowOccurrenceLoop.word,CompareMachine.word,UnaryTemplate.tape]
  all_goals omega

theorem native_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w j : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : rows.length ≤ 2^w) (hj : j ≤ Q)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (i : Fin 49) (hi : i≠31) :
    ((rawInput gs p F w j rows out).tapes (i.castAdd 54)).length ≤ capacity n p F w gs.length Q := by
  let C := capacity n p F w gs.length Q
  have hsmall := small_fits n p F w gs.length Q
  have hcursor := cursor_fits n p F w gs.length Q rows.length (j+1) hM (by omega)
  have hlookup : RowMaskLookupReusable.capacity gs.length w rows.length ≤ C := by
    change RowMaskLookupReusable.capacity gs.length w rows.length ≤ capacity n p F w gs.length Q
    unfold RowTupleCursorReady.capacity RowTupleMaskLoop.budget RowTupleMaskBody.budget at hcursor
    nlinarith
  have hflat : rows.flatten.length=rows.length*gs.length := by
    clear hM hcursor hlookup
    induction rows with
    | nil => simp
    | cons row rows ih =>
      rw [List.flatten_cons,List.length_append,hl row (by simp),ih (fun x hx=>hl x (by simp [hx]))]
      simp [Nat.add_mul,Nat.add_comm]
  have hmflat : rows.flatten.length ≤ C := by
    rw [hflat]
    have hc := cursor_fits n p F w gs.length Q rows.length 1 hM (by omega)
    unfold RowTupleCursorReady.capacity RowTupleMaskLoop.budget RowTupleMaskBody.budget
      RowMaskLookupReusable.capacity RowMaskLookup.budget at hc
    dsimp only [C]
    nlinarith
  unfold scale at hsmall
  simp only [List.length_flatten] at hmflat
  revert hi
  refine Fin.addCases (m:=48) (n:=1) (fun a=>?_) (fun a=>?_) i
  · intro hi
    have ha : (a.castAdd 41 : Fin 89)≠48 := by
      intro he
      have hv:=congrArg (fun k : Fin 89=>k.val) he
      change a.val=48 at hv
      have hb:=a.isLt
      omega
    change ((rawInput gs p F w j rows out).tapes ((a.castAdd 41).castAdd 14)).length ≤ C
    simp only [rawInput,P1CompactCloseoutRowsComputedCuts.input,Fin.addCases_left]
    rw [Function.update_of_ne ha]
    change ((P1CompactCloseoutRowsComputedCuts.body (0 : Fin 1) gs p F w j rows out).tapes
      ((a.castAdd 1).castAdd 40)).length ≤ C
    simp only [P1CompactCloseoutRowsComputedCuts.body,P1CompactCloseoutRowsEnumeratedCuts.input,
      TapeEmbedding.config,Fin.addCases_left,P1CompactCloseoutRowsEnumeratedCuts.core]
    rw [ZeroPadding.pad_length]
    apply max_le
    · unfold P1CompactRowTupleCursorBody.padding
      split_ifs <;> omega
    · revert hi
      refine Fin.addCases (m:=36) (n:=12) (fun b=>?_) (fun b=>?_) a
      · refine Fin.addCases (m:=35) (n:=1) (fun d=>?_) (fun d=>?_) b
        · intro hi
          simpa only [P1CompactRowTupleCursorLayout.data,Fin.addCases_left] using
            common_bound gs p F Q w out hF d (by intro he; subst d; exact hi rfl)
        · intro _
          fin_cases d
          change (CompareMachine.word (n+1)).length ≤ C
          simp only [CompareMachine.word,List.length_cons,List.length_replicate]
          dsimp only [C]
          omega
      · intro _
        fin_cases b <;> simp [P1CompactRowTupleCursorLayout.data,Fin.addCases,CompareMachine.word,UnaryTemplate.tape,
          frame_length,SignedSortKey.binary_length]
        all_goals change _ ≤ C
        all_goals dsimp only [C] at *
        all_goals omega
  · intro _
    fin_cases a
    simp [rawInput,P1CompactCloseoutRowsComputedCuts.input,Fin.addCases]

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsBankFields

/-! One common C bounds every native port at both ends of a polynomial.
The global append output is excluded, and the erase log has exactly C+1 cells. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsBankCapacity
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsPreparationBounds
open P1CompactCloseoutRowsPreparationFits P1CompactCloseoutRowsPreparationInput P1CompactCloseoutRowsBankFields
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacities (C : ℕ) (i : Fin 113) := if i=31 then 0 else if i=105 then C+1 else C

theorem enum_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w j : ℕ) (rows : List (List Bool)) (out : List Bool) (hj : j ≤ Q) (i : Fin 40) :
    ((rawInput gs p F w j rows out).tapes ((i.natAdd 49).castAdd 14)).length ≤ capacity n p F w gs.length Q := by
  have hm := small_fits n p F w gs.length Q
  unfold scale at hm
  have hi : (i.natAdd 49 : Fin 89)≠48 := by
    intro h
    have hv:=congrArg Fin.val h
    change 49+i.val=48 at hv
    omega
  simp only [rawInput,P1CompactCloseoutRowsComputedCuts.input,Fin.addCases_left,Function.update_of_ne hi,
    P1CompactCloseoutRowsComputedCuts.body,P1CompactCloseoutRowsEnumeratedCuts.input,TapeEmbedding.config,Fin.addCases_right]
  simp only [P1CompactRowTupleEnumeratedEquations.extra]
  split_ifs <;> simp [CompareMachine.word,frame_length,SignedSortKey.binary_length] <;> omega

theorem coefficient_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w j : ℕ) (rows : List (List Bool)) (out : List Bool) (hj : j ≤ Q) (i : Fin 14) :
    ((rawInput gs p F w j rows out).tapes (i.natAdd 89)).length ≤ capacity n p F w gs.length Q := by
  have hm := small_fits n p F w gs.length Q
  unfold scale at hm
  simp only [rawInput,P1CompactCloseoutRowsComputedCuts.input,Fin.addCases_right]
  fin_cases i <;> simp [CloseoutRowsDegreeCoefficient.input] <;> omega

theorem raw_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w j : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : rows.length ≤ 2^w) (hj : j ≤ Q)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (i : Fin 103) (hi : i≠31) :
    ((rawInput gs p F w j rows out).tapes i).length ≤ capacity n p F w gs.length Q := by
  revert hi
  refine Fin.addCases (m:=89) (n:=14) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=49) (n:=40) (fun b=>?_) (fun b=>?_) a
    · intro hi
      exact native_bound gs p F Q w j rows out hl hM hj hF b (by intro he; subst b; exact hi rfl)
    · intro _
      exact enum_bound gs p F Q w j rows out hj b
  · intro _
    exact coefficient_bound gs p F Q w j rows out hj a

theorem input_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w j : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : rows.length ≤ 2^w) (hj : j ≤ Q)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (i : Fin 112) (hi : i≠31) (hlog : i≠105) :
    (inputTapes gs p F w j (capacity n p F w gs.length Q) rows out i).length ≤ capacity n p F w gs.length Q := by
  have hm := small_fits n p F w gs.length Q
  unfold scale at hm
  revert hi hlog
  refine Fin.addCases (m:=103) (n:=9) (fun a=>?_) (fun a=>?_) i
  · intro hi _
    simp only [inputTapes,Fin.addCases_left,ZeroPadding.pad_length]
    apply max_le
    · unfold CloseoutRowsDegreeReset.caps
      split_ifs <;> omega
    · exact raw_bound gs p F Q w j rows out hl hM hj hF a (by intro he; subst a; exact hi rfl)
  · intro _ hlog
    fin_cases a <;> first | (exact False.elim (hlog rfl)) |
      simp [inputTapes,extra,templates,Fin.addCases,CompareMachine.word,frame_length,SignedSortKey.binary_length]
    all_goals omega

theorem loop_heads {s n : ℕ} (body : Machine 112 s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (phase : Fin 5) (p F Q w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    (RepeatMachine.cfg phase (P1CompactCloseoutRowsDegreeLoop.entry body gs p F w j C rows out) Q 1).heads=heads out := by
  funext i
  refine Fin.addCases (m:=112) (n:=1) (fun a=>?_) (fun a=>?_) i
  · simpa only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left,P1CompactCloseoutRowsDegreeLoop.entry]
      using congrFun (native_heads gs p F w j rows out) a
  · fin_cases a
    rfl

theorem loop_bound {s n : ℕ} (body : Machine 112 s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (phase : Fin 5) (p F Q w j : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : rows.length ≤ 2^w) (hj : j ≤ Q)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F)
    (i : Fin 113) (hi : i≠31) (hlog : i≠105) :
    ((RepeatMachine.cfg phase (P1CompactCloseoutRowsDegreeLoop.entry body gs p F w j
      (capacity n p F w gs.length Q) rows out) Q 1).tapes i).length ≤ capacity n p F w gs.length Q := by
  revert hi hlog
  refine Fin.addCases (m:=112) (n:=1) (fun a=>?_) (fun a=>?_) i
  · intro hi hlog
    simpa only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,Fin.addCases_left,P1CompactCloseoutRowsDegreeLoop.entry]
      using input_bound gs p F Q w j rows out hl hM hj hF a
        (by intro he; subst a; exact hi rfl) (by intro he; subst a; exact hlog rfl)
  · intro _ _
    fin_cases a
    change (CompareMachine.word Q).length ≤ capacity n p F w gs.length Q
    have hm := small_fits n p F w gs.length Q
    unfold scale at hm
    simp only [CompareMachine.word,List.length_cons,List.length_replicate]
    omega

theorem loop_driver {s n : ℕ} (body : Machine 112 s) (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (phase : Fin 5) (p F Q w j C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    (RepeatMachine.cfg phase (P1CompactCloseoutRowsDegreeLoop.entry body gs p F w j C rows out) Q 1).tapes 104=
      List.replicate C true ∧
    (RepeatMachine.cfg phase (P1CompactCloseoutRowsDegreeLoop.entry body gs p F w j C rows out) Q 1).tapes 105=
      List.replicate (C+1) false := by constructor <;> rfl

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsBankCapacity

/-! A complete polynomial call returns to the enclosing bank's erased
native ports. Every transition and sweep is paid; the growing output stays live. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsBankPolynomial
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout P1CompactCloseoutRowsLoopBoundary
open P1CompactCloseoutRowsPreparationBounds P1CompactCloseoutRowsPreparationFits P1CompactCloseoutRowsPreparationInput
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def input {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  ZeroPadding.config (P1CompactCloseoutRowsBankCapacity.capacities C)
    (P1CompactCloseoutRowsPolynomial.input gs p F Q w C rows out)

theorem padded_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (p F Q w : ℕ) (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hQp : Q ≤ p)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q ≤ p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F) :
    let C:=capacity (l+r) p F w gs.length Q
    let word:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
    ∃ actual,runFrom P1CompactCloseoutRowsPolynomial.machine (P1CompactCloseoutRowsDegreeLoop.budget Q C)
      (input gs p F Q w C rows out)=some actual ∧
      actual.final.heads=P1CompactCloseoutRowsBankFields.heads word ∧ actual.final.tapes 31=word ∧
      actual.final.tapes 104=List.replicate C true ∧ actual.final.tapes 105=List.replicate (C+1) false ∧
      (∀ i,i≠31 → i≠105 → (actual.final.tapes i).length ≤ C) ∧
      actual.steps ≤ P1CompactCloseoutRowsDegreeLoop.budget Q C := by
  dsimp only
  let C:=capacity (l+r) p F w gs.length Q
  have hcopy : 4*w+3 ≤ C := by
    have h:=small_fits (l+r) p F w gs.length Q
    unfold scale at h
    dsimp only [C]
    omega
  obtain ⟨source,hs,sf,ss⟩ := P1CompactCloseoutRowsDegreeLoop.degrees_run gs p F Q w C rows out hl hM hw hQp hp hF
    (fun j hj=>computed_fits gs p F Q w j rows hl hw.le hj)
    (fun j hj=>selected_fits gs p F Q w j rows hw.le hj) hcopy
    (fun j hj=>(metadata_fits (l+r) p F w gs.length Q j hj).2)
    (fun j hj=>cursor_fits (l+r) p F w gs.length Q rows.length (j+2) hw.le (by omega))
  obtain ⟨actual,ha,af,asteps,_⟩ := ZeroPadding.run_config P1CompactCloseoutRowsPolynomial.machine
    (P1CompactCloseoutRowsBankCapacity.capacities C) _ _ source hs
  have hout := P1CompactCloseoutRowsSharedDigits.emitted_word gs p Q w rows
  have he : (List.range Q).flatMap (fun j=>emitted gs p w j rows)=
      (P1CompactCloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p) := hout
  rw [he] at sf
  refine ⟨actual,ha,?_,?_,?_,?_,?_,asteps.le.trans ss⟩
  · rw [af,sf]
    exact P1CompactCloseoutRowsBankCapacity.loop_heads _ gs 3 p F Q w Q C rows _
  · rw [af,sf]
    change ZeroPadding.pad 0 (inputTapes gs p F w Q C rows _ 31)=_
    rw [ZeroPadding.pad_zero,(P1CompactCloseoutRowsPolynomial.output_fields gs p F w Q C rows _).1]
  · rw [af,sf]
    change ZeroPadding.pad C (List.replicate C true)=_
    simp [ZeroPadding.pad,C]
  · rw [af,sf]
    change ZeroPadding.pad (C+1) (List.replicate (C+1) false)=_
    simp [ZeroPadding.pad,C]
  · intro i hi hlog
    rw [af,sf]
    change (ZeroPadding.pad (P1CompactCloseoutRowsBankCapacity.capacities C i) _).length ≤ C
    rw [ZeroPadding.pad_length]
    apply max_le
    · simp only [P1CompactCloseoutRowsBankCapacity.capacities,hi,hlog,↓reduceIte,le_refl]
    · exact P1CompactCloseoutRowsBankCapacity.loop_bound _ gs 3 p F Q w Q rows _ hl hw.le le_rfl hF i hi hlog

noncomputable def machine := Composition.machine P1CompactCloseoutRowsPolynomial.machine CloseoutRowsBankClear.machine
def budget (Q C : ℕ) := P1CompactCloseoutRowsDegreeLoop.budget Q C+1+CloseoutRowsBankClear.budget C
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  Composition.leftConfig 6 (input gs p F Q w C rows out)

theorem polynomial_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (p F Q w : ℕ) (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hQp : Q ≤ p)
    (hp : P1CompactRowTupleFixedCapacity.width gs Q ≤ p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p ≤ F) :
    let C:=capacity (l+r) p F w gs.length Q
    let word:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
    ∃ actual,runFrom machine (budget Q C) (entry gs p F Q w C rows out)=some actual ∧
      actual.final.heads=CloseoutRowsBankClear.zeroHeads word ∧ actual.final.tapes 31=word ∧
      (∀ i,actual.final.tapes (CloseoutRowsBankClear.slots i)=CloseoutRowsBankClear.erased C i) ∧
      actual.steps ≤ budget Q C := by
  dsimp only
  let C:=capacity (l+r) p F w gs.length Q
  let word:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
  obtain ⟨a,ha,ah,aout,ad,al,ab,_⟩ := padded_run gs p F Q w rows out hl hM hw hQp hp hF
  obtain ⟨b,hb,bh,bt,bout,_⟩ := CloseoutRowsBankClear.clear_run C word a.final.tapes ab ad al
  have he : Composition.restart a.final CloseoutRowsBankClear.machine.start=
      ⟨CloseoutRowsBankClear.machine.start,CloseoutRowsBankFields.heads word,a.final.tapes⟩ := by
    apply configuration_ext
    · rfl
    · exact ah
    · rfl
  rw [←he] at hb
  have whole := Composition.run_join P1CompactCloseoutRowsPolynomial.machine CloseoutRowsBankClear.machine _ _ _ a b ha hb
  exact ⟨Composition.joinedReceipt a b,whole,bh,bout.trans aout,bt,runFrom_steps_le machine _ _ _ whole⟩

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsBankPolynomial

namespace NearCubicWires.RepairOrdinary
theorem P1CompactCloseoutRowsBankPolynomial_machine_unchanged : @P1CompactCloseoutRowsBankPolynomial.machine = @CloseoutRowsBankPolynomial.machine := rfl
end NearCubicWires.RepairOrdinary

/-! The same paper load pays the generated cut family and all executed
BinLift driver/degree/clear costs plus the fixed110-port loading allowance.
This cost is added to table work; it is not internal-syntax Tprep. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSourceLoad
open CloseoutRowsSourceDigits P1CompactCloseoutRowsCacheInput
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem cuts_bound {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (ps : List (MvPolynomial (Fin gs.length) (ZMod 2))) (K : ℕ)
    (hbank : ps.length ≤ 2^K) :
    ((bank ps).flatMap (P1CompactCloseoutRowsSharedDigits.cuts gs (K+1) (width ps))).length ≤
      2^load K (degree ps) gs.length := by
  let D:=degree ps*Nat.clog 2 (gs.length+1)
  have hp := P1CompactCloseoutRowsSharedDigits.batch_perm gs (K+1) (width ps) (bank ps)
    (fun rs hr=>(bank_width ps rs hr).le)
  rw [hp.length_eq,RowPowerBinLift.batch_length]
  have hm : ∀ ms∈family gs (bank ps),ms.length ≤ 2^D := by
    intro ms hms
    obtain ⟨rs,hrs,rfl⟩ := List.mem_map.mp hms
    obtain ⟨P,hP,rfl⟩ := List.mem_map.mp hrs
    simpa only [polynomial,List.length_map] using binary_support ps P hP
  have hb:=RowBinLift.batch_length_bound (K+1) (2^D) (family gs (bank ps)) hm
  have hq : K+1 ≤ 2^Nat.clog 2 (K+2) :=
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have he : 1 ≤ 2^D := Nat.one_le_two_pow
  rw [max_eq_right he] at hb
  have hfamily : (family gs (bank ps)).length ≤ 2^K := by
    simpa only [family,bank,List.length_map] using hbank
  calc
    _ ≤ 2^K*(2^Nat.clog 2 (K+2))*(2^D)^(K+1) :=
      hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul hfamily hq))
    _ = 2^(K+Nat.clog 2 (K+2)+(K+1)*D) := by
      rw [←pow_add,←pow_mul,←pow_add,Nat.mul_comm D (K+1)]
    _ ≤ 2^load K (degree ps) gs.length := by
      apply Nat.pow_le_pow_right (by decide)
      dsimp [D,load]
      nlinarith

theorem cuts_gate {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (ps : List (MvPolynomial (Fin gs.length) (ZMod 2))) (K s : ℕ)
    (hbank : ps.length ≤ 2^K) (hload : 200*load K (degree ps) gs.length ≤ s) :
    ((bank ps).flatMap (P1CompactCloseoutRowsSharedDigits.cuts gs (K+1) (width ps))).length^100 ≤ 2^s := by
  calc
    _ ≤ (2^load K (degree ps) gs.length)^100 :=
      Nat.pow_le_pow_left (cuts_bound gs ps K hbank) 100
    _ = 2^(100*load K (degree ps) gs.length) := by rw [←pow_mul,Nat.mul_comm]
    _ ≤ 2^s := Nat.pow_le_pow_right (by decide) (by omega)

def oneCost (Q C : ℕ) := P1CompactCloseoutRowsBankPolynomial.budget Q C+110*(3*C+3)+8

theorem one_bound (S R Q : ℕ) (hQ : Q ≤ S) :
    oneCost Q (4096*S^4*2^R) ≤ 2000000*2^R*(S+1)^5 := by
  have hl := CloseoutRowsCapacityBudget.loop_bound S R Q hQ
  change P1CompactCloseoutRowsDegreeLoop.budget Q (4096*S^4*2^R) ≤ _ at hl
  have hs : S^4 ≤ (S+1)^5 :=
    (Nat.pow_le_pow_left (Nat.le_succ S) 4).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have hc : 4096*S^4*2^R ≤ 4096*2^R*(S+1)^5 := by
    nlinarith [Nat.mul_le_mul_left (4096*2^R) hs]
  have ht : 1 ≤ (S+1)^5 := Nat.one_le_pow 5 (S+1) (by omega)
  have he : 1 ≤ 2^R := Nat.one_le_two_pow
  have hu : 1 ≤ 2^R*(S+1)^5 := by nlinarith
  unfold oneCost P1CompactCloseoutRowsBankPolynomial.budget CloseoutRowsBankClear.budget
  nlinarith

theorem bank_bound (S R K s : ℕ) (hQ : K+1 ≤ S) (hload : K+R ≤ s) :
    CloseoutRowsCapacityDriver.budget S R+2^K*oneCost (K+1) (4096*S^4*2^R) ≤
      3000000*2^s*(S+1)^5*(R+1) := by
  have hd:=CloseoutRowsCapacityBudget.driver_bound S R
  have ho:=one_bound S R (K+1) hQ
  have hR : 2^R ≤ 2^s := Nat.pow_le_pow_right (by decide) (by omega)
  have hKR : 2^K*2^R ≤ 2^s := by
    rw [←pow_add]
    exact Nat.pow_le_pow_right (by decide) hload
  have hd' : CloseoutRowsCapacityDriver.budget S R ≤ 1000000*2^s*(S+1)^5*(R+1) :=
    hd.trans (by gcongr)
  have ho' : 2^K*oneCost (K+1) (4096*S^4*2^R) ≤ 2000000*2^s*(S+1)^5*(R+1) := by
    calc
      _ ≤ 2^K*(2000000*2^R*(S+1)^5) := Nat.mul_le_mul_left _ ho
      _ = 2000000*(2^K*2^R)*(S+1)^5 := by ring
      _ ≤ 2000000*2^s*(S+1)^5 := by gcongr
      _ ≤ _ := by nlinarith
  nlinarith

theorem source_bank_bound {B : ℕ} (ps : List (MvPolynomial (Fin B) (ZMod 2)))
    (K s S : ℕ) (hQ : K+1 ≤ S) (hload : 200*load K (degree ps) B ≤ s) :
    CloseoutRowsCapacityDriver.budget S (width ps*(K+2))+
        2^K*oneCost (K+1) (4096*S^4*2^(width ps*(K+2))) ≤
      3000000*2^s*(S+1)^5*(width ps*(K+2)+1) := by
  apply bank_bound S _ K s hQ
  have h:=digit_margin ps K s hload
  omega

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsSourceLoad

/-! One actual packet load, head positioning, complete polynomial call and
native clear compose into the reusable enclosing bank body. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPacketPolynomial
open LocalBitMultitape P1CompactCloseoutRowsPreparationBounds CloseoutRowsBankPacket
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def data {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  (P1CompactCloseoutRowsPolynomial.input gs p F Q w C rows out).tapes
noncomputable def native := Composition.machine (CloseoutRowsBankClear.position true) P1CompactCloseoutRowsBankPolynomial.machine
def nativeBudget (Q C : ℕ) := 2+P1CompactCloseoutRowsBankPolynomial.budget Q C

theorem data_fields {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    data gs p F Q w C rows out 31=out ∧
      data gs p F Q w C rows out 104=List.replicate C true ∧
      data gs p F Q w C rows out 105=List.replicate (C+1) false := by
  refine ⟨?_,rfl,rfl⟩
  exact (P1CompactCloseoutRowsPolynomial.output_fields gs p F w 0 C rows out).1

theorem data_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w : ℕ) (rows : List (List Bool)) (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hw : rows.length≤2^w)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    ∀ i,i≠31 → i≠105 →
      (data gs p F Q w (capacity n p F w gs.length Q) rows out i).length≤capacity n p F w gs.length Q := by
  exact P1CompactCloseoutRowsBankCapacity.loop_bound P1CompactCloseoutRowsPolynomial.body gs 0 p F Q w 0 rows out
    hl hw (Nat.zero_le _) hF

theorem native_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (p F Q w : ℕ) (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (out : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hQp : Q≤p) (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    let C:=capacity (l+r) p F w gs.length Q
    let result:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
    ∃ actual,runFrom native (nativeBudget Q C)
      ⟨native.start,CloseoutRowsBankClear.zeroHeads out,padded C (data gs p F Q w C rows out)⟩=some actual ∧
      actual.final.heads=CloseoutRowsBankClear.zeroHeads result ∧
      actual.final.tapes=CloseoutRowsBankClear.blank C result := by
  dsimp only
  let C:=capacity (l+r) p F w gs.length Q
  let result:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
  obtain ⟨a,ha,af,_⟩:=CloseoutRowsBankClear.position_run true out (padded C (data gs p F Q w C rows out))
  obtain ⟨b,hb,bh,bo,bt,_⟩:=P1CompactCloseoutRowsBankPolynomial.polynomial_run gs p F Q w rows out hl hM hw hQp hp hF
  have he : Composition.restart a.final P1CompactCloseoutRowsBankPolynomial.machine.start=
      P1CompactCloseoutRowsBankPolynomial.entry gs p F Q w C rows out := by
    rw [af]
    apply configuration_ext
    · rfl
    · exact (P1CompactCloseoutRowsBankCapacity.loop_heads P1CompactCloseoutRowsPolynomial.body gs 0 p F Q w 0 C rows out).symm
    · rfl
  rw [←he] at hb
  have hwhole:=Composition.run_join (CloseoutRowsBankClear.position true) P1CompactCloseoutRowsBankPolynomial.machine _ _ _ a b ha hb
  have ht:=CloseoutRowsBankPorts.erased_store C result b.final.tapes bo bt
  exact ⟨Composition.joinedReceipt a b,hwhole,bh,ht⟩

noncomputable def last := TapeEmbedding.machine 1 native
noncomputable def machine := Composition.machine CloseoutRowsBankPacket.machine last
noncomputable def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :=
  CloseoutRowsBankPacket.budget (data gs p F Q w C rows out)+1+nativeBudget Q C

theorem packet_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (p F Q w : ℕ) (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (out pre tail : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hM : 0<rows.length)
    (hw : rows.length<2^w) (hQp : Q≤p) (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    let C:=capacity (l+r) p F w gs.length Q
    let packet:=word (data gs p F Q w C rows out)
    let result:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
    ∃ actual,runFrom machine (budget gs p F Q w C rows out)
      ⟨machine.start,heads out pre.length,tapes C out (pre++packet++tail)⟩=some actual ∧
      actual.final.heads=heads result (pre.length+packet.length) ∧
      actual.final.tapes=tapes C result (pre++packet++tail) ∧
      actual.steps≤P1CompactCloseoutRowsBankPolynomial.budget Q C+110*(3*C+3)+3 := by
  dsimp only
  let C:=capacity (l+r) p F w gs.length Q
  let inputData:=data gs p F Q w C rows out
  let packet:=word inputData
  let result:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
  have df:=data_fields gs p F Q w C rows out
  have db:=data_bound gs p F Q w rows out hl hw.le hF
  obtain ⟨a,ha,ah,atape,_⟩:=load_run C inputData out pre tail df.1 df.2.1 df.2.2 db
  obtain ⟨b,hb,bh,bt⟩:=native_run gs p F Q w rows out hl hM hw hQp hp hF
  let e:=TapeEmbedding.receipt (fun _ : Fin 1=>pre.length+packet.length) (fun _=>pre++packet++tail) b
  have he:=TapeEmbedding.run_embed native
    (fun _ : Fin 1=>pre.length+packet.length) (fun _=>pre++packet++tail) _ _ b hb
  have ef : e.final=TapeEmbedding.config (fun _ : Fin 1=>pre.length+packet.length)
      (fun _=>pre++packet++tail) b.final := rfl
  have eh : TapeEmbedding.config (fun _ : Fin 1=>pre.length+packet.length)
      (fun _=>pre++packet++tail)
      (⟨native.start,CloseoutRowsBankClear.zeroHeads out,padded C inputData⟩ : Configuration 113 _)=
        Composition.restart a.final last.start := by
    apply configuration_ext
    · rfl
    · exact ah.symm
    · exact atape.symm
  rw [eh] at he
  have whole:=Composition.run_join CloseoutRowsBankPacket.machine last _ _ _ a e ha he
  refine ⟨Composition.joinedReceipt a e,whole,?_,?_,?_⟩
  · change e.final.heads=_
    rw [ef]
    change extend b.final.heads (pre.length+packet.length)=_
    rw [bh]
    rfl
  · change e.final.tapes=_
    rw [ef]
    change extend b.final.tapes (pre++packet++tail)=_
    rw [bt]
    rfl
  · have hs:=runFrom_steps_le machine _ _ _ whole
    have hpkt:=CloseoutRowsBankPacket.budget_bound C inputData db
    unfold nativeBudget at hs
    omega

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPacketPolynomial

namespace NearCubicWires.RepairOrdinary
theorem P1CompactCloseoutRowsPacketPolynomial_machine_unchanged : @P1CompactCloseoutRowsPacketPolynomial.machine = @CloseoutRowsPacketPolynomial.machine := rfl
end NearCubicWires.RepairOrdinary

/-! Native packets depend only on their source polynomial and fixed row
metadata. The accumulated cut output is absent from every packet field. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPacketIndependent
open P1CompactCloseoutRowsPacketPolynomial CloseoutRowsBankPacket CloseoutRowsBankPorts
open LocalBitMultitape P1CompactCloseoutRowsLoopLayout RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

private theorem vector_away {α : Type} (a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a32 a33 a34 x y : α)
    (i : Fin 35) (hi : i≠31) :
    (![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27,a28,a29,a30,x,a32,a33,a34] : Fin 35→α) i=![a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16,a17,a18,a19,a20,a21,a22,a23,a24,a25,a26,a27,a28,a29,a30,y,a32,a33,a34] i := by
  fin_cases i <;> simp_all

private theorem common_out {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F : ℕ) (out : List Bool) (i : Fin 35) (hi : i≠31) :
    P1CompactRowCommonReusable.data gs 0 p F [] out [] i=P1CompactRowCommonReusable.data gs 0 p F [] [] [] i := by
  unfold P1CompactRowCommonReusable.data
  exact vector_away _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ i hi

private theorem cursor_out {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w : ℕ) (rows : List (List Bool)) (out : List Bool) (i : Fin 48) (hi : i≠31) :
    P1CompactRowTupleCursorLayout.data gs 0 p F w rows.length 1 rows [] out 0 [] i=
      P1CompactRowTupleCursorLayout.data gs 0 p F w rows.length 1 rows [] [] 0 [] i := by
  revert hi
  refine Fin.addCases (m:=36) (n:=12) (fun a=>?_) (fun a=>?_) i
  · refine Fin.addCases (m:=35) (n:=1) (fun b=>?_) (fun b=>?_) a
    · intro hi
      simp only [P1CompactRowTupleCursorLayout.data,Fin.addCases_left]
      exact common_out gs p F out b (by intro he; subst b; exact hi rfl)
    · intro _
      simp only [P1CompactRowTupleCursorLayout.data,Fin.addCases_left,Fin.addCases_right]
  · intro _
    simp only [P1CompactRowTupleCursorLayout.data,Fin.addCases_right]

private theorem raw_out {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F w : ℕ) (rows : List (List Bool)) (out : List Bool) (i : Fin 103) (hi : i≠31) :
    (rawInput gs p F w 0 rows out).tapes i=(rawInput gs p F w 0 rows []).tapes i := by
  revert hi
  refine Fin.addCases (m:=89) (n:=14) (fun a=>?_) (fun a=>?_) i
  · simp only [rawInput,P1CompactCloseoutRowsComputedCuts.input,Fin.addCases_left]
    by_cases ha : a=48
    · subst a
      intro _
      rw [Function.update_self,Function.update_self]
    rw [Function.update_of_ne ha,Function.update_of_ne ha]
    simp only [P1CompactCloseoutRowsComputedCuts.body,P1CompactCloseoutRowsEnumeratedCuts.input,TapeEmbedding.config]
    refine Fin.addCases (m:=49) (n:=40) (fun b=>?_) (fun b=>?_) a
    · simp only [Fin.addCases_left,P1CompactCloseoutRowsEnumeratedCuts.core]
      refine Fin.addCases (m:=48) (n:=1) (fun c=>?_) (fun c=>?_) b
      · intro hi
        simp only [Fin.addCases_left]
        apply congrArg (ZeroPadding.pad _)
        exact cursor_out gs p F w rows out c (by intro he; subst c; exact hi rfl)
      · intro _
        simp only [Fin.addCases_right]
    · intro _
      simp only [Fin.addCases_right]
  · intro _
    simp only [rawInput,P1CompactCloseoutRowsComputedCuts.input,Fin.addCases_right]

theorem data_out {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) (i : Fin 113) (hi : i≠31) :
    data gs p F Q w C rows out i=data gs p F Q w C rows [] i := by
  revert hi
  refine Fin.addCases (m:=112) (n:=1) (fun a=>?_) (fun a=>?_) i
  · simp only [data,P1CompactCloseoutRowsPolynomial.input,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      Fin.addCases_left,P1CompactCloseoutRowsDegreeLoop.entry]
    refine Fin.addCases (m:=103) (n:=9) (fun b=>?_) (fun b=>?_) a
    · intro hi
      simp only [inputTapes,Fin.addCases_left]
      apply congrArg (ZeroPadding.pad _)
      exact raw_out gs p F w rows out b (by intro he; subst b; exact hi rfl)
    · intro _
      simp only [inputTapes,Fin.addCases_right]
  · intro _
    simp only [data,P1CompactCloseoutRowsPolynomial.input,RepeatMachine.cfg,controlConfig,TapeEmbedding.config,
      Fin.addCases_right]

theorem word_congr (left right : Fin 113→List Bool)
    (h : ∀ i,i≠31 → left i=right i) : word left=word right := by
  unfold word CloseoutRowsPacketLoad.stream
  apply List.flatMap_congr
  intro j hj
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
  simp only [fields,extend,port,Fin.addCases_left]
  exact congrArg frame (h _ (CloseoutRowsBankClear.work_avoids i).1)

theorem word_out {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (rows : List (List Bool)) (out : List Bool) :
    word (data gs p F Q w C rows out)=word (data gs p F Q w C rows []) := by
  exact word_congr _ _ (data_out gs p F Q w C rows out)

theorem packet_length (C : ℕ) (native : Fin 113→List Bool)
    (hb : ∀ i,i≠31 → i≠105 → (native i).length≤C) :
    (word native).length≤110*(2*C+1) := by
  have hh : ∀ js : List (Fin 114), (∀ j∈js,(fields native j).length≤C) →
      (CloseoutRowsPacketLoad.stream (fields native) js).length≤js.length*(2*C+1) := by
    intro js
    induction js with
    | nil => simp [CloseoutRowsPacketLoad.stream]
    | cons j js ih =>
      intro hj
      have h0:=hj j (by simp)
      have h1:=ih (fun k hk=>hj k (by simp [hk]))
      simp only [CloseoutRowsPacketLoad.stream,List.flatMap_cons,List.length_append,frame_length,List.length_cons] at *
      nlinarith
  have h:=hh ports (field_bound C native hb)
  simpa only [word,ports,List.length_map,List.length_finRange] using h

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPacketIndependent

/-! One enclosing polynomial packet, including the physical zero-monomial
skip, has a uniform receipt for the outer live-family loop. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPacketOptional
open LocalBitMultitape CloseoutRowsBankPacket P1CompactCloseoutRowsPreparationBounds
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def packet {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (rows : List (List Bool)) : List Bool :=
  if rows=[] then [false] else
    true::word (P1CompactCloseoutRowsPacketPolynomial.data gs p F Q w C rows [])
noncomputable def machine :=
  CloseoutRowsPacketBranch.machine (113 : Fin 114) P1CompactCloseoutRowsPacketPolynomial.machine
def cost (Q C : ℕ) := P1CompactCloseoutRowsBankPolynomial.budget Q C+110*(3*C+3)+6

theorem cuts_nil {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs] (Q w : ℕ) :
    P1CompactCloseoutRowsSharedDigits.cuts gs Q w []=[] := by
  have hd : ∀ j,P1CompactCloseoutRowsCutMeaning.degreeCuts gs w j []=[] := fun j=>
    P1CompactCloseoutRowsDegreeRange.degree_nil gs w j [] (by simp) (by simp)
  simp [P1CompactCloseoutRowsSharedDigits.cuts,hd]

theorem optional_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (p F Q w : ℕ) (rows : List (List Bool)) [_masks : P1MaskDegree gs rows] (out pre tail : List Bool)
    (hl : ∀ row∈rows,row.length=gs.length) (hw : rows.length<2^w)
    (hQp : Q≤p) (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    let C:=capacity (l+r) p F w gs.length Q
    let pkt:=packet gs p F Q w C rows
    let result:=out++(P1CompactCloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p)
    ∃ actual,runFrom machine (cost Q C)
      ⟨machine.start,heads out pre.length,tapes C out (pre++pkt++tail)⟩=some actual ∧
      actual.final.heads=heads result (pre.length+pkt.length) ∧
      actual.final.tapes=tapes C result (pre++pkt++tail) ∧ actual.steps≤cost Q C := by
  dsimp only
  let C:=capacity (l+r) p F w gs.length Q
  by_cases he : rows=[]
  · subst rows
    obtain ⟨a,ha,ah,atape,asteps⟩ := CloseoutRowsPacketBranch.absent_run (113 : Fin 114)
      P1CompactCloseoutRowsPacketPolynomial.machine (heads out pre.length)
      (tapes C out (pre++[false]++tail))
      (by change readTapeBit ((pre++[false])++tail) pre.length=false; simp [List.append_assoc,Streaming.read_append])
    have hb : 2≤cost Q C := by unfold cost; omega
    have more:=runFrom_moreFuel machine 2 (cost Q C-2) _ a ha
    rw [Nat.add_sub_of_le hb] at more
    refine ⟨a,?_,?_,?_,?_⟩
    · simpa only [machine,packet,↓reduceIte,C] using more
    · rw [ah]
      change Function.update (heads out pre.length) (113 : Fin 114) (pre.length+1)=_
      rw [CloseoutRowsPacketFlag.advanced]
      simp only [cuts_nil,List.flatMap_nil,List.append_nil,packet,↓reduceIte,List.length_singleton]
    · simpa only [cuts_nil,List.flatMap_nil,List.append_nil,packet,↓reduceIte,C] using atape
    · change a.steps≤cost Q C
      omega
  · have hM : 0<rows.length := List.length_pos_iff.mpr he
    let raw:=word (P1CompactCloseoutRowsPacketPolynomial.data gs p F Q w C rows [])
    let tt:=tapes C out (pre++true::(raw++tail))
    obtain ⟨base,hbase,bh,bt,_⟩ := P1CompactCloseoutRowsPacketPolynomial.packet_run gs p F Q w rows out
      (pre++[true]) tail hl hM hw hQp hp hF
    have hwrd:=P1CompactCloseoutRowsPacketIndependent.word_out gs p F Q w C rows out
    rw [hwrd] at hbase bh bt
    have hsource :
        (⟨P1CompactCloseoutRowsPacketPolynomial.machine.start,
          Function.update (heads out pre.length) (113 : Fin 114) (heads out pre.length 113+1),tt⟩ :
          Configuration 114 _)=
        ⟨P1CompactCloseoutRowsPacketPolynomial.machine.start,heads out (pre++[true]).length,
          tapes C out ((pre++[true])++raw++tail)⟩ := by
      apply configuration_ext
      · rfl
      · change Function.update (heads out pre.length) (113 : Fin 114) (pre.length+1)=_
        rw [CloseoutRowsPacketFlag.advanced]
        simp only [List.length_append,List.length_singleton]
      · simp only [tt,List.append_assoc,List.cons_append,List.nil_append]
    rw [←hsource] at hbase
    obtain ⟨a,ha,ah,atape,asteps⟩:=CloseoutRowsPacketBranch.present_run (113 : Fin 114)
      P1CompactCloseoutRowsPacketPolynomial.machine (heads out pre.length) tt _
      (by change readTapeBit (pre++true::(raw++tail)) pre.length=true; simp [Streaming.read_append]) base hbase
    have db:=P1CompactCloseoutRowsPacketPolynomial.data_bound gs p F Q w rows out hl hw.le hF
    have hb:=CloseoutRowsBankPacket.budget_bound C
      (P1CompactCloseoutRowsPacketPolynomial.data gs p F Q w C rows out) db
    have hcost : P1CompactCloseoutRowsPacketPolynomial.budget gs p F Q w C rows out+3≤cost Q C := by
      unfold P1CompactCloseoutRowsPacketPolynomial.budget P1CompactCloseoutRowsPacketPolynomial.nativeBudget cost
      omega
    have more:=runFrom_moreFuel machine _ (cost Q C-(P1CompactCloseoutRowsPacketPolynomial.budget gs p F Q w C rows out+3)) _ a ha
    rw [Nat.add_sub_of_le hcost] at more
    refine ⟨a,?_,?_,?_,asteps.trans hcost⟩
    · simpa only [machine,tt,raw,C,packet,he,↓reduceIte,List.cons_append,List.append_assoc] using more
    · rw [ah,bh]
      simp only [packet,he,↓reduceIte,List.length_append,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_assoc,Nat.add_comm 1,C]
    · rw [atape,bt]
      simp only [packet,he,↓reduceIte,List.append_assoc,List.cons_append,List.nil_append,C]

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsPacketOptional

namespace NearCubicWires.RepairOrdinary
theorem P1CompactCloseoutRowsPacketOptional_machine_unchanged : @P1CompactCloseoutRowsPacketOptional.machine = @CloseoutRowsPacketOptional.machine := rfl
end NearCubicWires.RepairOrdinary

/-! The actual outer family loop consumes every polynomial packet once,
including empty polynomials, and rewinds its literal family driver. -/
namespace NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsFamilyLoop
open LocalBitMultitape CloseoutRowsBankPacket P1CompactCloseoutRowsPreparationBounds
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem flatMap_index {α β : Type} (xs : List α) (default : α) (f : α→List β) :
    (List.range xs.length).flatMap (fun j=>f (xs.getD j default))=xs.flatMap f := by
  have he : (List.range xs.length).map (fun j=>xs.getD j default)=xs := by
    apply List.ext_getElem
    · simp
    · intro i _ hi
      simp only [List.getElem_map,List.getElem_range]
      exact List.getD_eq_getElem xs default hi
  rw [←List.flatMap_map,he]

theorem split_word {α β : Type} (xs : List α) (default : α) (f : α→List β)
    (j : ℕ) (hj : j<xs.length) :
    xs.flatMap f=(xs.take j).flatMap f++f (xs.getD j default)++(xs.drop (j+1)).flatMap f := by
  have h:=congrArg (List.flatMap f) (List.take_append_drop (j+1) xs)
  rw [List.take_succ_eq_append_getElem hj] at h
  simpa only [List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,
    List.getD_eq_getElem xs default hj] using h.symm

theorem next_word {α β : Type} (xs : List α) (default : α) (f : α→List β)
    (j : ℕ) (hj : j<xs.length) :
    ((xs.take (j+1)).flatMap f).length=
      ((xs.take j).flatMap f).length+(f (xs.getD j default)).length := by
  simp only [List.take_succ_eq_append_getElem hj,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,List.length_append,List.getD_eq_getElem xs default hj]

noncomputable def machine := P1CompactCloseoutRowsDegreeLoop.machine P1CompactCloseoutRowsPacketOptional.machine
noncomputable def stream {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (bank : List (List (List Bool))) :=
  bank.flatMap (P1CompactCloseoutRowsPacketOptional.packet gs p F Q w C)
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (p F Q w C : ℕ) (bank : List (List (List Bool))) (pre tail : List Bool)
    (j : ℕ) (out : List Bool) :=
  (⟨P1CompactCloseoutRowsPacketOptional.machine.start,
    heads out (pre.length+(stream gs p F Q w C (bank.take j)).length),
    tapes C out (pre++stream gs p F Q w C bank++tail)⟩ : Configuration 114 _)
def budget (N Q C : ℕ) := N*(P1CompactCloseoutRowsPacketOptional.cost Q C+3)+3

theorem family_run {l r : ℕ} (gs : List (ExactThresholdGate (l+r))) [_radix : P1Radix gs]
    (p F Q w : ℕ) (bank : List (List (List Bool))) [_masks : P1BankDegree gs bank] (out pre tail : List Bool)
    (hl : ∀ rows∈bank,∀ row∈rows,row.length=gs.length)
    (hw : ∀ rows∈bank,rows.length<2^w)
    (hQp : Q≤p) (hp : P1CompactRowTupleFixedCapacity.width gs Q≤p)
    (hF : P1CompactRowCommonBounds.capacity gs (gs.length*Q) p≤F) :
    let C:=capacity (l+r) p F w gs.length Q
    let result:=out++(bank.flatMap (P1CompactCloseoutRowsSharedDigits.cuts gs Q w)).flatMap (MatrixScoreBatch.cutWord p)
    ∃ actual,runFrom machine (budget bank.length Q C)
      (RepeatMachine.cfg 0 (entry gs p F Q w C bank pre tail 0 out) bank.length 1)=some actual ∧
      actual.final=RepeatMachine.cfg 3
        (entry gs p F Q w C bank pre tail bank.length result) bank.length 1 ∧
      actual.steps≤budget bank.length Q C := by
  dsimp only
  let C:=capacity (l+r) p F w gs.length Q
  let f:=P1CompactCloseoutRowsPacketOptional.packet gs p F Q w C
  let emit:=fun j=>(P1CompactCloseoutRowsSharedDigits.cuts gs Q w (bank.getD j [])).flatMap (MatrixScoreBatch.cutWord p)
  have supplier : ∀ j<bank.length,∀ acc,∃ actual,
      runFrom P1CompactCloseoutRowsPacketOptional.machine (P1CompactCloseoutRowsPacketOptional.cost Q C)
        (entry gs p F Q w C bank pre tail j acc)=some actual ∧
      actual.final.heads=(entry gs p F Q w C bank pre tail (j+1) (acc++emit j)).heads ∧
      actual.final.tapes=(entry gs p F Q w C bank pre tail (j+1) (acc++emit j)).tapes ∧
      actual.steps≤P1CompactCloseoutRowsPacketOptional.cost Q C := by
    intro j hj acc
    have hmem : bank.getD j []∈bank := by
      rw [List.getD_eq_getElem bank [] hj]
      exact List.getElem_mem hj
    let packetPre:=pre++(bank.take j).flatMap f
    let packetTail:=(bank.drop (j+1)).flatMap f++tail
    obtain ⟨a,ha,ah,atape,asteps⟩:=P1CompactCloseoutRowsPacketOptional.optional_run gs p F Q w
      (bank.getD j []) acc packetPre packetTail (hl _ hmem) (hw _ hmem) hQp hp hF
    have hs : packetPre++f (bank.getD j [])++packetTail=pre++stream gs p F Q w C bank++tail := by
      rw [stream,split_word bank [] f j hj]
      simp only [packetPre,packetTail,List.append_assoc]
    have hinput :
        (⟨P1CompactCloseoutRowsPacketOptional.machine.start,heads acc packetPre.length,
          tapes C acc (packetPre++f (bank.getD j [])++packetTail)⟩ : Configuration 114 _)=
        entry gs p F Q w C bank pre tail j acc := by
      rw [hs]
      apply configuration_ext
      · rfl
      · simp only [packetPre,List.length_append,entry,stream,f]
      · rfl
    rw [hinput] at ha
    refine ⟨a,ha,?_,?_,asteps⟩
    · rw [ah]
      change heads (acc++emit j) (packetPre.length+(f (bank.getD j [])).length)=
        heads (acc++emit j) (pre.length+((bank.take (j+1)).flatMap f).length)
      rw [next_word bank [] f j hj]
      simp only [packetPre,List.length_append,Nat.add_assoc]
    · rw [atape]
      change tapes C (acc++emit j) (packetPre++f (bank.getD j [])++packetTail)=_
      rw [hs]
      rfl
  obtain ⟨actual,ha,hf,ht⟩:=P1CompactCloseoutRowsDegreeLoop.loop_run P1CompactCloseoutRowsPacketOptional.machine
    (entry gs p F Q w C bank pre tail) emit (P1CompactCloseoutRowsPacketOptional.cost Q C) bank.length
    (by intro j hj acc; rfl) supplier out
  have hout : (List.range bank.length).flatMap emit=
      (bank.flatMap (P1CompactCloseoutRowsSharedDigits.cuts gs Q w)).flatMap (MatrixScoreBatch.cutWord p) := by
    rw [List.flatMap_assoc]
    simpa only [emit] using flatMap_index bank []
      (fun rows=>(P1CompactCloseoutRowsSharedDigits.cuts gs Q w rows).flatMap (MatrixScoreBatch.cutWord p))
  rw [hout] at hf
  exact ⟨actual,ha,hf,ht⟩

end NearCubicWires.RepairOrdinary.P1CompactCloseoutRowsFamilyLoop

namespace NearCubicWires.RepairOrdinary
theorem P1CompactCloseoutRowsFamilyLoop_machine_unchanged : @P1CompactCloseoutRowsFamilyLoop.machine = @CloseoutRowsFamilyLoop.machine := rfl
end NearCubicWires.RepairOrdinary

