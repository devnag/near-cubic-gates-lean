import Proof.MachineModel.ClosureRadix
import Proof.Supplier.RowOccurrenceLoop
import Proof.Supplier.RowOccurrenceMeaning
import Proof.Supplier.RowCachedEquationMeaning
import Proof.Supplier.RowCoefficientLoopReset
import Proof.Supplier.RowCoefficientDock
import Proof.Supplier.RowCoefficientWhole
import Proof.Supplier.RowCoefficientStream
import Proof.Supplier.RowCoefficientStreamReset
import Proof.Supplier.RowCoefficientStreamClear
import Proof.Supplier.RowCoefficientReusable
import Proof.Supplier.RowCoefficientBounds
import Proof.Supplier.RowCoordinateBody
import Proof.Supplier.RowCoordinateLoop
import Proof.Supplier.RowCoordinateMeaning
import Proof.Supplier.RowCommonCoefficient
import Proof.Supplier.RowCommonReset
import Proof.Supplier.RowCommonClear
import Proof.Supplier.RowCommonReusable
import Proof.Supplier.RowCommonBounds
import Proof.Supplier.RowCommonCoordinateBody
import Proof.Supplier.RowCommonCoordinateLoop

/-! The fixed ordinary loop consumes an ordered list of actual cached-child
occurrences and assembles one signed coefficient. Indices are never deduplicated.
The physical counter and every call/return/rewind are included in the run. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowOccurrenceLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RepeatMachine.machine RowOccurrenceReusable.machine (fun _ _=>true)
def word {N : ℕ} (indices : List (Fin N)) := indices.flatMap (fun i=>RowIndexField.word i.val)
def value {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n) (i : Fin gs.length) :=
  RowCachedCoordinateAppend.value gs i.val i.isLt j hj
def emitted {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n)
    (negative : Bool) (indices : List (Fin gs.length)) :=
  indices.flatMap (fun i=>marks (RowPowerNativeReusable.block
    (P1Radix.bits gs) (value gs j hj i) negative))
def callBudget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n) (i : Fin gs.length) :=
  RowOccurrenceReusable.budget gs i.val i.isLt j hj (P1Radix.bits gs)
    (RowCachedCoordinateBounds.inner (P1Radix.bits gs))
    (RowCachedCoordinateBounds.outer gs (P1Radix.bits gs))
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n)
    (indices : List (Fin gs.length)) := (indices.map (callBudget gs j hj)).sum+3*indices.length+3
noncomputable def data {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ)
    (source : List Bool) (pos : ℕ) (positive negative : List Bool) :=
  RowOccurrenceReusable.entry gs j (P1Radix.bits gs)
    (RowCachedCoordinateBounds.inner (P1Radix.bits gs))
    (RowCachedCoordinateBounds.outer gs (P1Radix.bits gs)) source pos positive negative
noncomputable def cfg {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (phase : Fin 5)
    (source : List Bool) (pos : ℕ) (positive negative : List Bool) (total driver : ℕ) :=
  RepeatMachine.cfg phase (data gs j source pos positive negative) total driver

theorem index_fits {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (i : Fin gs.length) :
    i.val+2≤RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) := by
  have hi := i.isLt
  unfold RowCachedCoordinateBounds.outer RowCachedCoordinateBounds.size
  nlinarith

theorem call_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n)
    (i : Fin gs.length) (pre tail positive negative : List Bool) :
    let source := pre++RowIndexField.word i.val++tail
    let P := positive++emitted gs j hj false [i]
    let N := negative++emitted gs j hj true [i]
    ∃ r,runFrom RowOccurrenceReusable.machine (callBudget gs j hj i)
      (data gs j source pre.length positive negative)=some r ∧
      r.final.heads=(data gs j source (pre.length+i.val+1) P N).heads ∧
      r.final.tapes=(data gs j source (pre.length+i.val+1) P N).tapes ∧ r.steps=callBudget gs j hj i := by
  have hw := P1Radix.value_width gs i.val i.isLt j hj
  simpa only [emitted,List.flatMap_cons,List.flatMap_nil,List.append_nil,value,data,callBudget] using
    RowOccurrenceReusable.reusable_run gs i.val i.isLt j hj (P1Radix.bits gs)
      (RowCachedCoordinateBounds.inner (P1Radix.bits gs))
      (RowCachedCoordinateBounds.outer gs (P1Radix.bits gs)) pre tail positive negative
      (RowCachedCoordinateBounds.inner_fits _ _ hw)
      (RowCachedCoordinateBounds.outer_fits gs i.val i.isLt j hj _ hw) (index_fits gs i)

theorem cfg_eq {t s : ℕ} (phase : Fin 5) (a b : Configuration t s) (total driver : ℕ)
    (hh : a.heads=b.heads) (ht : a.tapes=b.tapes) :
    RepeatMachine.cfg phase a total driver=RepeatMachine.cfg phase b total driver := by
  simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh,ht]

theorem remaining {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n)
    (pre tail positive negative : List Bool) (indices : List (Fin gs.length)) (total done : ℕ)
    (hn : done+indices.length=total) :
    Timed machine ((indices.map (callBudget gs j hj)).sum+2*indices.length+total+3)
      (cfg gs j 0 (pre++word indices++tail) pre.length positive negative total (done+1))
      (cfg gs j 3 (pre++word indices++tail) (pre.length+(word indices).length)
        (positive++emitted gs j hj false indices) (negative++emitted gs j hj true indices) total 1) := by
  induction indices generalizing pre positive negative done with
  | nil =>
    have hd : done=total := by simpa using hn
    subst done
    simpa [machine,cfg,word,emitted] using RepeatMachine.exhaust RowOccurrenceReusable.machine
      (fun _ _=>true) (data gs j (pre++tail) pre.length positive negative) total
  | cons i indices ih =>
    obtain ⟨r,hr,rh,rt,rs⟩ := call_run gs j hj i pre (word indices++tail) positive negative
    have hiter := RepeatMachine.iteration RowOccurrenceReusable.machine (fun _ _=>true)
      (data gs j (pre++RowIndexField.word i.val++(word indices++tail)) pre.length positive negative)
      total done r (by rfl) (by simp only [List.length_cons] at hn; omega) hr
    rw [rs] at hiter
    simp only [↓reduceIte] at hiter
    have he := cfg_eq 0 r.final
      (data gs j (pre++RowIndexField.word i.val++(word indices++tail)) (pre.length+i.val+1)
        (positive++emitted gs j hj false [i]) (negative++emitted gs j hj true [i])) total (done+2) rh rt
    rw [he] at hiter
    have ht := ih (pre++RowIndexField.word i.val)
      (positive++emitted gs j hj false [i]) (negative++emitted gs j hj true [i]) (done+1)
      (by simp only [List.length_cons] at hn; omega)
    have hs : (pre++RowIndexField.word i.val)++word indices++tail=
        pre++RowIndexField.word i.val++(word indices++tail) := by simp [List.append_assoc]
    rw [hs,List.length_append] at ht
    have hlen : (RowIndexField.word i.val).length=i.val+1 := by simp [RowIndexField.word]
    rw [hlen] at ht
    have hpos : pre.length+(i.val+1)=pre.length+i.val+1 := by omega
    rw [hpos] at ht
    have hdone : done+1+1=done+2 := by omega
    rw [hdone] at ht
    have whole := hiter.trans ht
    have htime : (callBudget gs j hj i+2)+
        ((indices.map (callBudget gs j hj)).sum+2*indices.length+total+3)=
        (((i::indices).map (callBudget gs j hj)).sum+2*(i::indices).length+total+3) := by
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega
    rw [htime] at whole
    simpa [machine,cfg,word,emitted,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,
      RowIndexField.word] using whole

theorem list_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n)
    (pre tail positive negative : List Bool) (indices : List (Fin gs.length)) :
    ∃ r,runFrom machine (budget gs j hj indices)
      (cfg gs j 0 (pre++word indices++tail) pre.length positive negative indices.length 1)=some r ∧
      r.final=cfg gs j 3 (pre++word indices++tail) (pre.length+(word indices).length)
        (positive++emitted gs j hj false indices) (negative++emitted gs j hj true indices) indices.length 1 ∧
      r.steps=budget gs j hj indices := by
  have h := remaining gs j hj pre tail positive negative indices indices.length 0 (by omega)
  have ht : (indices.map (callBudget gs j hj)).sum+2*indices.length+indices.length+3=budget gs j hj indices := by
    unfold budget
    omega
  rw [ht] at h
  exact h.run (by simp [machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])

end NearCubicWires.RepairOrdinary.P1CompactRowOccurrenceLoop

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowOccurrenceLoop_machine_unchanged : P1CompactRowOccurrenceLoop.machine = RowOccurrenceLoop.machine := rfl
end NearCubicWires.RepairOrdinary

/-! Physical output and uniform cost of one completed occurrence-coordinate
loop. The two produced frames denote the signed Horner coefficient. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowOccurrenceLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem call_budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n) (i : Fin gs.length) :
    callBudget gs j hj i≤2048*RowCachedCoordinateBounds.size gs (P1Radix.bits gs) := by
  have hw := P1Radix.value_width gs i.val i.isLt j hj
  have h := RowCachedCoordinateBounds.reusable_budget gs i.val i.isLt j hj _ hw
  have hs : gs.length+1≤RowCachedCoordinateBounds.size gs (P1Radix.bits gs) := by
    unfold RowCachedCoordinateBounds.size
    nlinarith
  have hi := i.isLt
  unfold callBudget RowOccurrenceReusable.budget RowOccurrenceAppend.budget RowCachedCoordinateBounds.outer
  unfold RowCachedCoordinateBounds.outer at h
  omega

theorem budget_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n)
    (indices : List (Fin gs.length)) :
    budget gs j hj indices ≤ indices.length*
      (2048*RowCachedCoordinateBounds.size gs (P1Radix.bits gs)+3)+3 := by
  have h : (indices.map (callBudget gs j hj)).sum ≤ indices.length*
      (2048*RowCachedCoordinateBounds.size gs (P1Radix.bits gs)) := by
    induction indices with
    | nil => simp
    | cons i indices ih =>
      have hi := call_budget gs j hj i
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
  unfold budget
  nlinarith

def values {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n)
    (indices : List (Fin gs.length)) := indices.map (value gs j hj)

theorem values_fit {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n)
    (indices : List (Fin gs.length)) (z : ℤ) (hz : z∈values gs j hj indices) :
    natBitLength z.natAbs≤P1Radix.bits gs := by
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
  exact P1Radix.value_width gs i.val i.isLt j hj

theorem emitted_blocks {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n)
    (negative : Bool) (indices : List (Fin gs.length)) :
    emitted gs j hj negative indices=marks (RowPowerNativeReusable.blocks
      (P1Radix.bits gs) negative (values gs j hj indices)) := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    simpa [emitted,values,RowPowerNativeReusable.blocks,marks,List.flatMap_append] using ih

theorem coefficient_value {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n)
    (indices : List (Fin gs.length)) :
    (RadixSemantics.value (RowPowerNativeReusable.blocks (P1Radix.bits gs) false
        (values gs j hj indices)) : ℤ)-
      RadixSemantics.value (RowPowerNativeReusable.blocks (P1Radix.bits gs) true
        (values gs j hj indices))=
      RowPowerNativeReusable.horner ((2 : ℤ)^(P1Radix.bits gs)) (values gs j hj indices) :=
  RowPowerNativeReusable.blocks_value _ _ (values_fit gs j hj indices)

theorem cfg_outputs {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (source : List Bool)
    (pos : ℕ) (positive negative : List Bool) (total driver : ℕ) (phase : Fin 5) :
    (cfg gs j phase source pos positive negative total driver).tapes 10=positive++[false] ∧
    (cfg gs j phase source pos positive negative total driver).tapes 11=negative++[false] ∧
    (cfg gs j phase source pos positive negative total driver).heads 10=positive.length ∧
    (cfg gs j phase source pos positive negative total driver).heads 11=negative.length := by
  simp [cfg,data,RepeatMachine.cfg,controlConfig,RowOccurrenceReusable.entry,
    RowOccurrenceAppend.entry,RowOccurrenceAppend.blank,RowOccurrenceAppend.ready,
    RowCachedCoordinateReusable.entry,RowCachedCoordinateReusable.extended,
    Composition.leftConfig,Composition.restart,TapeEmbedding.config,ZeroPadding.config,
    RowCachedCoordinateReset.entry,Rewind.recording,Rewind.config,RowCachedCoordinateAppend.entry,
    RowCachedCoordinateAppend.ready,RowNativeCoordinateAppend.ready,RowPowerNativeReusable.heads,
    RowPowerNativeReusable.tapes,RowCachedCoordinateReset.caps,RowOccurrenceReusable.caps,
    Fin.addCases,ZeroPadding.pad]

theorem coefficient_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :
    ∃ r,runFrom machine (budget gs j hj indices)
      (cfg gs j 0 (pre++word indices++tail) pre.length [] [] indices.length 1)=some r ∧
      r.final.tapes 10=frame (RowPowerNativeReusable.blocks (P1Radix.bits gs) false
        (values gs j hj indices)) ∧
      r.final.tapes 11=frame (RowPowerNativeReusable.blocks (P1Radix.bits gs) true
        (values gs j hj indices)) ∧
      r.final.heads 10=2*P1Radix.bits gs*indices.length ∧
      r.final.heads 11=2*P1Radix.bits gs*indices.length ∧
      r.steps ≤ indices.length*(2048*RowCachedCoordinateBounds.size gs (P1Radix.bits gs)+3)+3 := by
  obtain ⟨r,hr,rf,rs⟩ := list_run gs j hj pre tail [] [] indices
  obtain ⟨hp,hn,hph,hnh⟩ := cfg_outputs gs j (pre++word indices++tail) (pre.length+(word indices).length)
    ([]++emitted gs j hj false indices) ([]++emitted gs j hj true indices) indices.length 1 3
  have hp := (congrArg (fun c=>c.tapes 10) rf).trans hp
  have hn := (congrArg (fun c=>c.tapes 11) rf).trans hn
  have hph := (congrArg (fun c=>c.heads 10) rf).trans hph
  have hnh := (congrArg (fun c=>c.heads 11) rf).trans hnh
  simp only [emitted_blocks] at hp hn hph hnh
  simp only [List.nil_append,marks_length,RowPowerNativeReusable.blocks_length,values,List.length_map] at hp hn hph hnh
  refine ⟨r,hr,?_,?_,?_,?_,rs.le.trans (budget_bound gs j hj indices)⟩
  · have hf (bits : List Bool) : marks bits++[false]=frame bits := by
      simpa only [List.append_nil,frame] using (frame_append bits []).symm
    simpa only [hf,values] using hp
  · have hf (bits : List Bool) : marks bits++[false]=frame bits := by
      simpa only [List.append_nil,frame] using (frame_append bits []).symm
    simpa only [hf,values] using hn
  · rw [hph]; ring
  · rw [hnh]; ring

end NearCubicWires.RepairOrdinary.P1CompactRowOccurrenceLoop

/-! The executed occurrence-coordinate loop assembles the power-radix stack
of actual native child equations. The radix is safe by their native bytes;
only the conjunction is identified with the canonical equation stack. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCachedEquation
open LocalBitMultitape RepairRepresentation SupplierPipeline SupplierPrime SupplierEstimator ThresholdCompiler
open P1CompactRowOccurrenceLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def equation {n : ℕ} (g : ExactThresholdGate n) : LabelledEquation (Fin n) := ⟨g.weight,g.target⟩
def equations {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length)) :=
  indices.map (fun i=>equation gs[i.val])

theorem native_abs_sum (zs : List ℤ) :
    (zs.map Int.natAbs).sum<2^(zs.flatMap intWord).length := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
    have hk : natBitLength z.natAbs≤(intWord z).length := by
      simp only [DecompositionSource.intWord_length,intBitLength,natBitLength]
      omega
    have hz : z.natAbs<2^(intWord z).length :=
      (Nat.lt_pow_succ_log_self (by decide : 1<2) z.natAbs).trans_le
        (Nat.pow_le_pow_right (by decide) hk)
    have hp := Nat.mul_le_mul (Nat.succ_le_of_lt hz) (Nat.succ_le_of_lt ih)
    simp only [Nat.succ_eq_add_one] at hp
    have hn : 0≤z.natAbs*(zs.map Int.natAbs).sum := Nat.zero_le _
    simp only [List.map_cons,List.sum_cons,List.flatMap_cons,List.length_append,pow_add]
    nlinarith

theorem equation_magnitude {n : ℕ} (g : ExactThresholdGate n) :
    equationMagnitudeBound (equation g)<2^(exactWord g).length := by
  have h := native_abs_sum (RowNativeCoordinate.fields g)
  rw [←RowNativeCoordinate.word_fields] at h
  simpa [equationMagnitudeBound,equation,RowNativeCoordinate.fields,List.map_ofFn,List.sum_ofFn] using h

theorem cache_radix_safe {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (i : Fin gs.length) :
    equationMagnitudeBound (equation gs[i.val])<2^(P1Radix.bits gs) := P1Radix.safe i

theorem coordinate_weight {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : Fin n) (i : Fin gs.length) :
    value gs j.val j.isLt.le i=(equation gs[i.val]).weights j :=
  RowNativeCoordinate.field_weight gs[i.val] j

theorem coordinate_target {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (i : Fin gs.length) :
    value gs n le_rfl i=(equation gs[i.val]).target :=
  RowNativeCoordinate.field_target gs[i.val]

theorem stack_weight {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : Fin n)
    (indices : List (Fin gs.length)) :
    RowPowerNativeReusable.horner ((2 : ℤ)^(P1Radix.bits gs))
      (values gs j.val j.isLt.le indices)=
      (RowPowerBinLift.stack (P1Radix.bits gs) (equations gs indices)).weights j := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    simpa only [values,List.map_cons,RowPowerNativeReusable.horner,equations,RowPowerBinLift.stack,
      stackEquations,coordinate_weight] using congrArg
        (fun z=>(equation gs[i.val]).weights j+(2 : ℤ)^(P1Radix.bits gs)*z) ih

theorem stack_target {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length)) :
    RowPowerNativeReusable.horner ((2 : ℤ)^(P1Radix.bits gs))
      (values gs n le_rfl indices)=
      (RowPowerBinLift.stack (P1Radix.bits gs) (equations gs indices)).target := by
  induction indices with
  | nil => rfl
  | cons i indices ih =>
    simpa only [values,List.map_cons,RowPowerNativeReusable.horner,equations,RowPowerBinLift.stack,
      stackEquations,coordinate_target] using congrArg
        (fun z=>(equation gs[i.val]).target+(2 : ℤ)^(P1Radix.bits gs)*z) ih

theorem same_conjunction {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (indices : List (Fin gs.length)) (input : Fin n → Bool) :
    (RowPowerBinLift.stack (P1Radix.bits gs) (equations gs indices)).Holds input ↔
      (canonicalEquationStack (equations gs indices)).Holds input := by
  apply RowPowerBinLift.same_conjunction
  intro e he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
  exact cache_radix_safe gs i

end NearCubicWires.RepairOrdinary.P1CompactRowCachedEquation

/-! Execute the complete occurrence loop and physically rewind just its two
coefficient heads. The cache, index-stream cursor and loop counter survive;
the paid rewind log supplies real allocated normalization workspace. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientLoopReset
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 25) : Bool := decide (i=10 ∨ i=11)
noncomputable def machine := MaskedReset.machine P1CompactRowOccurrenceLoop.machine selected
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :=
  Rewind.recording (P1CompactRowOccurrenceLoop.cfg gs j 0 (pre++P1CompactRowOccurrenceLoop.word indices++tail)
    pre.length [] [] indices.length 1) 0
noncomputable def loopFinal {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :=
  P1CompactRowOccurrenceLoop.cfg gs j 3 (pre++P1CompactRowOccurrenceLoop.word indices++tail)
    (pre.length+(P1CompactRowOccurrenceLoop.word indices).length)
    (P1CompactRowOccurrenceLoop.emitted gs j hj false indices) (P1CompactRowOccurrenceLoop.emitted gs j hj true indices)
    indices.length 1
def finish {s : ℕ} (c : Configuration 25 s) (steps : ℕ) :=
  SelectiveReset.finished (s:=s) (fun i=>if selected i then 0 else c.heads i) c.tapes steps
noncomputable def output {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :=
  finish (loopFinal gs j hj pre tail indices) (P1CompactRowOccurrenceLoop.budget gs j hj indices)

theorem loop_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :
    ∃ r,runFrom machine (2*P1CompactRowOccurrenceLoop.budget gs j hj indices+2)
      (entry gs j pre tail indices)=some r ∧
      r.final=output gs j hj pre tail indices ∧ r.steps=2*P1CompactRowOccurrenceLoop.budget gs j hj indices+2 := by
  obtain ⟨r,hr,rf,rs⟩ := P1CompactRowOccurrenceLoop.list_run gs j hj pre tail [] [] indices
  have start := P1CompactRowOccurrenceLoop.cfg_outputs gs j (pre++P1CompactRowOccurrenceLoop.word indices++tail)
    pre.length [] [] indices.length 1 0
  have hh : ∀ i,selected i=true → r.final.heads i ≤ r.steps := by
    intro i hi
    have h := SelectiveReset.prefix_head (prefix_of_run P1CompactRowOccurrenceLoop.machine _ _ r hr).1 i
    have hs : (P1CompactRowOccurrenceLoop.cfg gs j 0 (pre++P1CompactRowOccurrenceLoop.word indices++tail)
        pre.length [] [] indices.length 1).heads i=0 := by
      have ht : i=10 ∨ i=11 := by simpa only [selected,decide_eq_true_eq] using hi
      rcases ht with rfl | rfl
      · exact start.2.2.1
      · exact start.2.2.2
    simpa only [hs,zero_add] using h
  obtain ⟨a,ha,af,asteps,_⟩ := MaskedReset.reset_run P1CompactRowOccurrenceLoop.machine selected _ _ r hr hh
  rw [rs] at ha asteps
  have hfinal : r.final=loopFinal gs j hj pre tail indices := by
    simpa only [loopFinal,List.nil_append] using rf
  rw [hfinal,rs] at af
  exact ⟨a,ha,af,asteps⟩

end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientLoopReset

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowCoefficientLoopReset_machine_unchanged : P1CompactRowCoefficientLoopReset.machine = RowCoefficientLoopReset.machine := rfl
end NearCubicWires.RepairOrdinary

/-! The actual loop endpoint supplies the seven normalization tapes. The
same normalizer accepts the physically retained zero padding in its flag
and magnitude slots; only its two output tapes are fresh. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientDock
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (D : ℕ) (i : Fin 7) := if i=2 ∨ i=3 then D else 0
def padded (D : ℕ) (tapes : Fin 7 → List Bool) := fun i=>ZeroPadding.pad (caps D i) (tapes i)
def slots : Fin 7 → Fin 28 := ![10,11,19,16,25,26,27]
theorem slots_injective : Function.Injective slots := by decide
def extend {s : ℕ} (c : Configuration 26 s) :=
  TapeEmbedding.config (fun _ : Fin 2=>0) (fun _=>[]) c
noncomputable def dock {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :=
  extend (P1CompactRowCoefficientLoopReset.output gs j hj pre tail indices)
def bits {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (negative : Bool) (indices : List (Fin gs.length)) :=
  RowPowerNativeReusable.blocks (P1Radix.bits gs) negative
    (P1CompactRowOccurrenceLoop.values gs j hj indices)

theorem bits_length {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (negative : Bool) (indices : List (Fin gs.length)) :
    (bits gs j hj negative indices).length=P1Radix.bits gs*indices.length := by
  simp [bits,RowPowerNativeReusable.blocks_length,P1CompactRowOccurrenceLoop.values]

theorem padded_ready (w p n cap D : ℕ) (hp : p<2^w) (hn : n<2^w) :
    ReadyRun RowCoefficientField.machine (12*w+21)
      (padded D (RowCoefficientField.input w p n cap 0))
      (padded D (RowCoefficientField.output w p n cap 0)) := by
  obtain ⟨r,hr,rt,rh,rs⟩ := RowCoefficientField.field_ready w p n cap 0 hp hn
  obtain ⟨a,ha,af,asteps,_⟩ := ZeroPadding.run_config RowCoefficientField.machine (caps D) _ _ r hr
  refine ⟨a,ha,?_,?_,asteps.trans rs⟩
  · rw [af]; change padded D r.final.tapes=_; rw [rt]
  · intro i; rw [af]; exact rh i

theorem scratch {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (source : List Bool)
    (pos : ℕ) (positive negative : List Bool) (total driver : ℕ) (phase : Fin 5) :
    let c := P1CompactRowOccurrenceLoop.cfg gs j phase source pos positive negative total driver
    let D := RowCachedCoordinateBounds.outer gs (P1Radix.bits gs)
    c.heads 19=0 ∧ c.heads 16=0 ∧ c.tapes 19=List.replicate D false ∧ c.tapes 16=List.replicate D false := by
  simp [P1CompactRowOccurrenceLoop.cfg,P1CompactRowOccurrenceLoop.data,RepeatMachine.cfg,controlConfig,
    RowOccurrenceReusable.entry,RowOccurrenceAppend.entry,RowOccurrenceAppend.blank,
    RowOccurrenceAppend.ready,RowCachedCoordinateReusable.entry,RowCachedCoordinateReusable.extended,
    Composition.leftConfig,Composition.restart,TapeEmbedding.config,ZeroPadding.config,
    RowCachedCoordinateReset.entry,Rewind.recording,Rewind.config,RowCachedCoordinateAppend.entry,
    RowCachedCoordinateAppend.ready,RowNativeCoordinateAppend.ready,
    RowNativeCoordinateAppend.extraHeads,RowNativeCoordinateAppend.extraTapes,
    RowCachedCoordinateReset.caps,RowOccurrenceReusable.caps,
    Fin.addCases,ZeroPadding.pad]

theorem dock_heads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :
    ∀ i,(dock gs j hj pre tail indices).heads (slots i)=0 := by
  have h := scratch gs j (pre++P1CompactRowOccurrenceLoop.word indices++tail)
    (pre.length+(P1CompactRowOccurrenceLoop.word indices).length)
    (P1CompactRowOccurrenceLoop.emitted gs j hj false indices) (P1CompactRowOccurrenceLoop.emitted gs j hj true indices)
    indices.length 1 3
  have h19 : (P1CompactRowCoefficientLoopReset.loopFinal gs j hj pre tail indices).heads 19=0 := h.1
  have h16 : (P1CompactRowCoefficientLoopReset.loopFinal gs j hj pre tail indices).heads 16=0 := h.2.1
  intro i
  simp only [dock,extend,P1CompactRowCoefficientLoopReset.output,P1CompactRowCoefficientLoopReset.finish,
    SelectiveReset.finished,Rewind.config,TapeEmbedding.config]
  fin_cases i <;> simp [slots,Fin.addCases,P1CompactRowCoefficientLoopReset.selected,h19,h16]

theorem dock_input {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :
    ∀ i,(dock gs j hj pre tail indices).tapes (slots i)=
      padded (RowCachedCoordinateBounds.outer gs (P1Radix.bits gs))
        (RowCoefficientField.input (P1Radix.bits gs*indices.length)
          (RadixSemantics.value (bits gs j hj false indices))
          (RadixSemantics.value (bits gs j hj true indices))
          (P1CompactRowOccurrenceLoop.budget gs j hj indices) 0) i := by
  have h := scratch gs j (pre++P1CompactRowOccurrenceLoop.word indices++tail)
    (pre.length+(P1CompactRowOccurrenceLoop.word indices).length)
    (P1CompactRowOccurrenceLoop.emitted gs j hj false indices) (P1CompactRowOccurrenceLoop.emitted gs j hj true indices)
    indices.length 1 3
  have h19 : (P1CompactRowCoefficientLoopReset.loopFinal gs j hj pre tail indices).tapes 19=
      List.replicate (RowCachedCoordinateBounds.outer gs (P1Radix.bits gs)) false := h.2.2.1
  have h16 : (P1CompactRowCoefficientLoopReset.loopFinal gs j hj pre tail indices).tapes 16=
      List.replicate (RowCachedCoordinateBounds.outer gs (P1Radix.bits gs)) false := h.2.2.2
  have ho := P1CompactRowOccurrenceLoop.cfg_outputs gs j (pre++P1CompactRowOccurrenceLoop.word indices++tail)
    (pre.length+(P1CompactRowOccurrenceLoop.word indices).length)
    (P1CompactRowOccurrenceLoop.emitted gs j hj false indices) (P1CompactRowOccurrenceLoop.emitted gs j hj true indices)
    indices.length 1 3
  have hp : (P1CompactRowCoefficientLoopReset.loopFinal gs j hj pre tail indices).tapes 10=frame (bits gs j hj false indices) := by
    unfold P1CompactRowCoefficientLoopReset.loopFinal
    rw [ho.1,P1CompactRowOccurrenceLoop.emitted_blocks]
    simpa only [List.append_nil,frame,bits] using (frame_append (bits gs j hj false indices) []).symm
  have hn : (P1CompactRowCoefficientLoopReset.loopFinal gs j hj pre tail indices).tapes 11=frame (bits gs j hj true indices) := by
    unfold P1CompactRowCoefficientLoopReset.loopFinal
    rw [ho.2.1,P1CompactRowOccurrenceLoop.emitted_blocks]
    simpa only [List.append_nil,frame,bits] using (frame_append (bits gs j hj true indices) []).symm
  have hb (negative : Bool) : SignedSortKey.binary (P1Radix.bits gs*indices.length)
      (RadixSemantics.value (bits gs j hj negative indices))=bits gs j hj negative indices := by
    simpa only [bits_length] using BoundedCounter.binary_of_value (bits gs j hj negative indices)
  have hD : 1 ≤ RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) := by
    unfold RowCachedCoordinateBounds.outer RowCachedCoordinateBounds.size
    omega
  intro i
  simp only [dock,extend,P1CompactRowCoefficientLoopReset.output,P1CompactRowCoefficientLoopReset.finish,
    SelectiveReset.finished,Rewind.config,TapeEmbedding.config]
  fin_cases i <;> simp [slots,Fin.addCases,padded,caps,RowCoefficientField.input,
    RowCoefficientNormalize.input,RowCoefficientNormalize.data,RowCoefficientField.extra,
    hp,hn,h19,h16,hb,ZeroPadding.pad]
  rw [←List.replicate_succ]
  congr 1

end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientDock

/-! One fixed ordinary program consumes the retained cache and the actual
ordered occurrence stream, computes one stacked coefficient, physically
rewinds its P/N words, and emits its final normalized signed field. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientWhole
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding P1CompactRowCoefficientDock
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 2 P1CompactRowCoefficientLoopReset.machine
noncomputable def last := RecoveryFocus.machine slots RowCoefficientField.machine
noncomputable def machine := Composition.machine first last
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :=
  Composition.restart (extend (P1CompactRowCoefficientLoopReset.entry gs j pre tail indices)) machine.start
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :=
  2*P1CompactRowOccurrenceLoop.budget gs j hj indices+12*(P1Radix.bits gs*indices.length)+24
noncomputable def result {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :=
  install slots (dock gs j hj pre tail indices).tapes
    (padded (RowCachedCoordinateBounds.outer gs (P1Radix.bits gs))
      (RowCoefficientField.output (P1Radix.bits gs*indices.length)
        (RadixSemantics.value (bits gs j hj false indices))
        (RadixSemantics.value (bits gs j hj true indices))
        (P1CompactRowOccurrenceLoop.budget gs j hj indices) 0))

theorem whole_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :
    ∃ r,runFrom machine (budget gs j hj indices) (entry gs j pre tail indices)=some r ∧
      r.final.heads=(dock gs j hj pre tail indices).heads ∧
      r.final.tapes=result gs j hj pre tail indices ∧ r.steps=budget gs j hj indices := by
  obtain ⟨a,ha,af,asteps⟩ := P1CompactRowCoefficientLoopReset.loop_run gs j hj pre tail indices
  have hr := TapeEmbedding.run_embed P1CompactRowCoefficientLoopReset.machine (fun _ : Fin 2=>0)
    (fun _=>[]) _ _ a ha
  let ar := TapeEmbedding.receipt (fun _ : Fin 2=>0) (fun _=>[]) a
  have arf : ar.final=dock gs j hj pre tail indices := by
    change extend a.final=extend (P1CompactRowCoefficientLoopReset.output gs j hj pre tail indices)
    rw [af]
  have hp := RadixSemantics.value_lt (bits gs j hj false indices)
  have hn := RadixSemantics.value_lt (bits gs j hj true indices)
  rw [bits_length] at hp hn
  have h := padded_ready _ _ _ (P1CompactRowOccurrenceLoop.budget gs j hj indices)
    (RowCachedCoordinateBounds.outer gs (P1Radix.bits gs)) hp hn
  obtain ⟨b,hb,bh,bt,bs⟩ := h.focus_at slots slots_injective
    (dock gs j hj pre tail indices).heads (dock gs j hj pre tail indices).tapes
    (dock_input gs j hj pre tail indices) (dock_heads gs j hj pre tail indices)
  have he : (⟨RowCoefficientField.machine.start,(dock gs j hj pre tail indices).heads,
      (dock gs j hj pre tail indices).tapes⟩)=Composition.restart ar.final last.start := by
    rw [arf]; rfl
  rw [he] at hb
  have whole := Composition.run_join first last _ _ _ ar b hr hb
  have ht : (2*P1CompactRowOccurrenceLoop.budget gs j hj indices+2)+1+
      (12*(P1Radix.bits gs*indices.length)+21)=budget gs j hj indices := by
    unfold budget
    omega
  rw [ht] at whole
  refine ⟨Composition.joinedReceipt ar b,whole,bh,bt,?_⟩
  change a.steps+1+b.steps=_
  rw [asteps,bs,ht]

theorem result_field {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :
    result gs j hj pre tail indices 26=frame (MatrixScoreBatch.signMagnitude
      (P1Radix.bits gs*indices.length)
      (RowPowerNativeReusable.horner ((2 : ℤ)^P1Radix.bits gs)
        (P1CompactRowOccurrenceLoop.values gs j hj indices))) := by
  have h := install_slot slots slots_injective (dock gs j hj pre tail indices).tapes
    (padded (RowCachedCoordinateBounds.outer gs (P1Radix.bits gs))
      (RowCoefficientField.output (P1Radix.bits gs*indices.length)
        (RadixSemantics.value (bits gs j hj false indices))
        (RadixSemantics.value (bits gs j hj true indices))
        (P1CompactRowOccurrenceLoop.budget gs j hj indices) 0)) 5
  change result gs j hj pre tail indices 26=_ at h
  simpa only [padded,caps,show ¬((5 : Fin 7)=2 ∨ (5 : Fin 7)=3) by decide,if_false,
    ZeroPadding.pad_zero,RowCoefficientField.field_output,bits,
    P1CompactRowOccurrenceLoop.coefficient_value] using h

theorem budget_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :
    budget gs j hj indices ≤ 8192*indices.length*
      RowCachedCoordinateBounds.size gs (P1Radix.bits gs)+30 := by
  have hb := P1CompactRowOccurrenceLoop.budget_bound gs j hj indices
  have hw : P1Radix.bits gs+1 ≤
      RowCachedCoordinateBounds.size gs (P1Radix.bits gs) := by
    unfold RowCachedCoordinateBounds.size
    omega
  have hm := Nat.mul_le_mul_left indices.length hw
  unfold budget
  nlinarith

end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientWhole

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowCoefficientWhole_machine_unchanged : P1CompactRowCoefficientWhole.machine = RowCoefficientWhole.machine := rfl
end NearCubicWires.RepairOrdinary

/-! Whole retained-cache coefficient computation followed by its physical
append to the live row stream. The field and its emitter log are reused by
the cursor-restoring copier; the row-output head remains advanced. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientStream
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 1 P1CompactRowCoefficientWhole.machine
noncomputable def last := RowCoefficientAppendCall.machine
noncomputable def machine := Composition.machine first last
def extend {s : ℕ} (out : List Bool) (c : Configuration 28 s) :=
  TapeEmbedding.config (fun _ : Fin 1=>out.length) (fun _=>out) c
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ)
    (pre tail out : List Bool) (indices : List (Fin gs.length)) :=
  Composition.restart (extend out (P1CompactRowCoefficientWhole.entry gs j pre tail indices)) machine.start
def field {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) := MatrixScoreBatch.signMagnitude
      (P1Radix.bits gs*indices.length)
      (RowPowerNativeReusable.horner ((2 : ℤ)^P1Radix.bits gs)
        (P1CompactRowOccurrenceLoop.values gs j hj indices))
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) := P1CompactRowCoefficientWhole.budget gs j hj indices+4*(field gs j hj indices).length+5
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (pre tail out : List Bool) (indices : List (Fin gs.length)) :=
  Fin.addCases (m:=28) (n:=1) (motive:=fun _=>ℕ)
    (P1CompactRowCoefficientDock.dock gs j hj pre tail indices).heads (fun _=>out.length)
noncomputable def tapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (pre tail out : List Bool) (indices : List (Fin gs.length)) :=
  Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool)
    (P1CompactRowCoefficientWhole.result gs j hj pre tail indices) (fun _=>out)

theorem field_length {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :
    (field gs j hj indices).length=P1Radix.bits gs*indices.length+1 := by
  simp [field,MatrixScoreBatch.signMagnitude,SignedSortKey.binary_length]

theorem whole_log {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :
    P1CompactRowCoefficientWhole.result gs j hj pre tail indices 27=
      List.replicate (2*(P1Radix.bits gs*indices.length)+4) false := by
  have h := install_slot P1CompactRowCoefficientDock.slots P1CompactRowCoefficientDock.slots_injective
    (P1CompactRowCoefficientDock.dock gs j hj pre tail indices).tapes
    (P1CompactRowCoefficientDock.padded (RowCachedCoordinateBounds.outer gs (P1Radix.bits gs))
      (RowCoefficientField.output (P1Radix.bits gs*indices.length)
        (RadixSemantics.value (P1CompactRowCoefficientDock.bits gs j hj false indices))
        (RadixSemantics.value (P1CompactRowCoefficientDock.bits gs j hj true indices))
        (P1CompactRowOccurrenceLoop.budget gs j hj indices) 0)) 6
  change P1CompactRowCoefficientWhole.result gs j hj pre tail indices 27=_ at h
  simpa only [P1CompactRowCoefficientDock.padded,P1CompactRowCoefficientDock.caps,
    show ¬((6 : Fin 7)=2 ∨ (6 : Fin 7)=3) by decide,if_false,ZeroPadding.pad_zero,
    RowCoefficientAppendCall.field_log] using h

theorem stream_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (pre tail out : List Bool) (indices : List (Fin gs.length)) :
    ∃ r,runFrom machine (budget gs j hj indices) (entry gs j pre tail out indices)=some r ∧
      r.final.heads=heads gs j hj pre tail (out++frame (field gs j hj indices)) indices ∧
      r.final.tapes=tapes gs j hj pre tail (out++frame (field gs j hj indices)) indices ∧
      r.steps ≤ budget gs j hj indices := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := P1CompactRowCoefficientWhole.whole_run gs j hj pre tail indices
  let a := TapeEmbedding.receipt (fun _ : Fin 1=>out.length) (fun _=>out) base
  have ha := TapeEmbedding.run_embed P1CompactRowCoefficientWhole.machine (fun _ : Fin 1=>out.length)
    (fun _=>out) _ _ base hbase
  have ah : a.final.heads=heads gs j hj pre tail out indices := by
    change Fin.addCases (m:=28) (n:=1) (motive:=fun _=>ℕ) base.final.heads (fun _=>out.length)=_
    rw [bh]; rfl
  have atapes : a.final.tapes=tapes gs j hj pre tail out indices := by
    change Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool) base.final.tapes (fun _=>out)=_
    rw [bt]; rfl
  have h26 : a.final.heads 26=0 := by
    rw [ah]
    exact P1CompactRowCoefficientDock.dock_heads gs j hj pre tail indices 5
  have h27 : a.final.heads 27=0 := by
    rw [ah]
    exact P1CompactRowCoefficientDock.dock_heads gs j hj pre tail indices 6
  have t26 : a.final.tapes 26=frame (field gs j hj indices) := by
    rw [atapes]
    exact P1CompactRowCoefficientWhole.result_field gs j hj pre tail indices
  have t27 : a.final.tapes 27=List.replicate
      (2*(P1Radix.bits gs*indices.length)+4) false := by
    rw [atapes]
    exact whole_log gs j hj pre tail indices
  obtain ⟨b,hb,bh',bt',bs'⟩ := RowCoefficientAppendCall.append_run (field gs j hj indices) out
    (2*(P1Radix.bits gs*indices.length)+4) a.final.heads a.final.tapes
    (by rw [field_length]; omega) h26 (by rw [ah]; rfl) h27 t26 (by rw [atapes]; rfl) t27
  have whole := Composition.run_join first last _ _ _ a b ha hb
  have htime : P1CompactRowCoefficientWhole.budget gs j hj indices+1+(4*(field gs j hj indices).length+4)=
      budget gs j hj indices := by unfold budget; omega
  rw [htime] at whole
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,?_⟩
  · change b.final.heads=_
    rw [bh',ah]
    funext i
    refine Fin.addCases (m:=28) (n:=1) (fun a=>?_) (fun a=>?_) i
    · have hn : a.castAdd 1 ≠ (28 : Fin 29) := by
        intro h; have hv:=congrArg (fun j : Fin 29=>j.val) h; simp only [Fin.val_castAdd] at hv; omega
      simp only [Function.update_of_ne hn,heads,Fin.addCases_left]
    · fin_cases a; simp [heads,Fin.addCases]
  · change b.final.tapes=_
    rw [bt',atapes]
    funext i
    refine Fin.addCases (m:=28) (n:=1) (fun a=>?_) (fun a=>?_) i
    · have hn : a.castAdd 1 ≠ (28 : Fin 29) := by
        intro h; have hv:=congrArg (fun j : Fin 29=>j.val) h; simp only [Fin.val_castAdd] at hv; omega
      simp only [Function.update_of_ne hn,tapes,Fin.addCases_left]
    · fin_cases a; simp [tapes,Fin.addCases]
  · change base.steps+1+b.steps ≤ _
    rw [bs]
    unfold budget
    omega

theorem budget_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :
    budget gs j hj indices ≤ 8192*indices.length*
      RowCachedCoordinateBounds.size gs (P1Radix.bits gs)+39 := by
  have hb := P1CompactRowOccurrenceLoop.budget_bound gs j hj indices
  have hw : P1Radix.bits gs+1 ≤
      RowCachedCoordinateBounds.size gs (P1Radix.bits gs) := by
    unfold RowCachedCoordinateBounds.size
    omega
  have hm := Nat.mul_le_mul_left indices.length hw
  unfold budget P1CompactRowCoefficientWhole.budget
  rw [field_length]
  nlinarith

end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientStream

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowCoefficientStream_machine_unchanged : P1CompactRowCoefficientStream.machine = RowCoefficientStream.machine := rfl
end NearCubicWires.RepairOrdinary

/-! Restore the dedicated occurrence-stream cursor after a coefficient
append, with paid recording and retained scratch padding for the next call.
The global row-output cursor is deliberately preserved by this machine. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientStreamReset
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlots : Fin 7 → Fin 29 := ![10,11,16,19,25,26,27]
def work (i : Fin 29) : Bool := decide (i=10 ∨ i=11 ∨ i=16 ∨ i=19 ∨ i=25 ∨ i=26 ∨ i=27)
def selected (i : Fin 29) := decide (i=23)
def caps (F : ℕ) : Fin 30 → ℕ :=
  Fin.addCases (m:=29) (n:=1) (motive:=fun _=>ℕ) (fun i=>if work i then F else 0) (fun _=>F)
noncomputable def machine := MaskedReset.machine P1CompactRowCoefficientStream.machine selected
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  ZeroPadding.config (caps F) (Rewind.recording (P1CompactRowCoefficientStream.entry gs j [] tail out indices) 0)
def outputHeads (h : Fin 29 → ℕ) :=
  Fin.addCases (m:=29) (n:=1) (motive:=fun _=>ℕ) (fun i=>if selected i then 0 else h i) (fun _=>0)
def outputTapes (F : ℕ) (a : Fin 29 → List Bool) :=
  Fin.addCases (m:=29) (n:=1) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (if work i then F else 0) (a i)) (fun _=>List.replicate F false)

theorem start_head {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (k : Fin 7) :
    (P1CompactRowCoefficientStream.entry gs j [] tail out indices).heads (workSlots k)=0 := by
  fin_cases k <;> rfl

theorem start_support {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hF : 1 ≤ F) (hD : RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) ≤ F)
    (k : Fin 7) : ( (P1CompactRowCoefficientStream.entry gs j [] tail out indices).tapes (workSlots k)).length ≤ F := by
  have hs := P1CompactRowCoefficientDock.scratch gs j (P1CompactRowOccurrenceLoop.word indices++tail) 0 [] [] indices.length 1 0
  have ho := P1CompactRowOccurrenceLoop.cfg_outputs gs j (P1CompactRowOccurrenceLoop.word indices++tail) 0 [] [] indices.length 1 0
  simp only [P1CompactRowCoefficientStream.entry,Composition.restart,P1CompactRowCoefficientStream.extend,TapeEmbedding.config,
    P1CompactRowCoefficientWhole.entry,P1CompactRowCoefficientDock.extend,P1CompactRowCoefficientLoopReset.entry,Rewind.recording,Rewind.config,
    List.nil_append,List.length_nil]
  fin_cases k <;> simp [workSlots,Fin.addCases,ho.1,ho.2.1,hs.2.2.1,hs.2.2.2,hF,hD]

theorem reset_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hF : P1CompactRowCoefficientStream.budget gs j hj indices+1 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) ≤ F) :
    ∃ r,runFrom machine (2*P1CompactRowCoefficientStream.budget gs j hj indices+2)
      (entry gs j F tail out indices)=some r ∧
      r.final.heads=outputHeads (P1CompactRowCoefficientStream.heads gs j hj [] tail
        (out++frame (P1CompactRowCoefficientStream.field gs j hj indices)) indices) ∧
      r.final.tapes=outputTapes F (P1CompactRowCoefficientStream.tapes gs j hj [] tail
        (out++frame (P1CompactRowCoefficientStream.field gs j hj indices)) indices) ∧
      r.steps ≤ 2*P1CompactRowCoefficientStream.budget gs j hj indices+2 ∧
      (∀ k : Fin 7,(r.final.tapes ((workSlots k).castAdd 1)).length ≤ F) ∧
      (r.final.tapes 29).length ≤ F := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := P1CompactRowCoefficientStream.stream_run gs j hj [] tail out indices
  have hh : ∀ i,selected i=true → base.final.heads i ≤ base.steps := by
    intro i hi
    have he : i=23 := by simpa only [selected,decide_eq_true_eq] using hi
    subst i
    have h := SelectiveReset.prefix_head (prefix_of_run _ _ _ _ hbase).1 23
    have h0 : (P1CompactRowCoefficientStream.entry gs j [] tail out indices).heads 23=0 := rfl
    simpa only [h0,zero_add] using h
  obtain ⟨reset,hr,rf,rs,_⟩ := MaskedReset.reset_run P1CompactRowCoefficientStream.machine selected _ _ base hbase hh
  obtain ⟨r,hrun,rfinal,rsteps,_⟩ := ZeroPadding.run_config machine (caps F) _ _ reset hr
  have hsmall : base.steps ≤ F := by omega
  have ht : r.final.tapes=outputTapes F base.final.tapes := by
    rw [rfinal,rf]
    funext i
    refine Fin.addCases (m:=29) (n:=1) (fun a=>?_) (fun a=>?_) i
    · simp only [ZeroPadding.config,caps,SelectiveReset.finished,Rewind.config,outputTapes,Fin.addCases_left]
    · fin_cases a
      change ZeroPadding.pad F (List.replicate base.steps false)=List.replicate F false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le hsmall]
  have extra := runFrom_moreFuel machine (2*base.steps+2)
    ((2*P1CompactRowCoefficientStream.budget gs j hj indices+2)-(2*base.steps+2)) _ r hrun
  have hbudget : 2*base.steps+2 ≤ 2*P1CompactRowCoefficientStream.budget gs j hj indices+2 := by omega
  rw [Nat.add_sub_of_le hbudget] at extra
  refine ⟨r,extra,?_,ht.trans (congrArg (outputTapes F) bt),?_,?_,?_⟩
  · rw [rfinal,rf]
    change outputHeads base.final.heads=_
    rw [bh]
  · rw [rsteps,rs]; omega
  · intro k
    rw [ht]
    simp only [outputTapes,Fin.addCases_left]
    have hk : work (workSlots k)=true := by fin_cases k <;> decide
    simp only [hk,↓reduceIte,ZeroPadding.pad_length]
    apply max_le le_rfl
    have h := PCPSerializerReuse.tape_support P1CompactRowCoefficientStream.machine _ _ base hbase (workSlots k) F 0
      (start_head gs j tail out indices k).le
      ((start_support gs j F tail out indices (by omega) hD k).trans (Nat.le_max_left _ _))
    simp only [zero_add] at h
    exact h.trans (max_le le_rfl (by omega))
  · rw [ht]; simp [outputTapes,Fin.addCases]

end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientStreamReset

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowCoefficientStreamReset_machine_unchanged : P1CompactRowCoefficientStreamReset.machine = RowCoefficientStreamReset.machine := rfl
end NearCubicWires.RepairOrdinary

/-! Whole coefficient append with a physical erase of all coefficient work.
The native cache, width/arity drivers, occurrence list and row output survive.
The same retained allocation can be used by subsequent coordinate calls. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientStreamClear
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlots : Fin 8 → Fin 32 := ![10,11,16,19,25,26,27,29]
def eraseSlots : Fin 10 → Fin 32 := Fin.addCases (m:=9) (n:=1) (motive:=fun _=>Fin 32)
  (Fin.addCases (m:=8) (n:=1) (motive:=fun _=>Fin 32) workSlots (fun _=>30)) (fun _=>31)
theorem injective : Function.Injective eraseSlots := by decide
def eraseInput (F : ℕ) (backing : Fin 8 → List Bool) :=
  Fin.addCases (m:=9) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=8) (n:=1) (motive:=fun _=>List Bool) backing (fun _=>List.replicate F true))
    (fun _=>List.replicate (F+1) false)
noncomputable def cleared (F : ℕ) (a : Fin 32 → List Bool) :=
  install eraseSlots a (eraseInput F (fun _=>List.replicate F false))
noncomputable def first := TapeEmbedding.machine 2 P1CompactRowCoefficientStreamReset.machine
noncomputable def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 8)
noncomputable def machine := Composition.machine first last
def extra (F : ℕ) : Fin 2 → List Bool := ![List.replicate F true,List.replicate (F+1) false]
def extend {s : ℕ} (F : ℕ) (c : Configuration 30 s) := TapeEmbedding.config (fun _=>0) (extra F) c
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Composition.restart (extend F (P1CompactRowCoefficientStreamReset.entry gs j F tail out indices)) machine.start
noncomputable def resultHeads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Fin.addCases (m:=30) (n:=2) (motive:=fun _=>ℕ)
    (P1CompactRowCoefficientStreamReset.outputHeads (P1CompactRowCoefficientStream.heads gs j hj [] tail out indices)) (fun _=>0)
noncomputable def resetTapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (F : ℕ) (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Fin.addCases (m:=30) (n:=2) (motive:=fun _=>List Bool)
    (P1CompactRowCoefficientStreamReset.outputTapes F (P1CompactRowCoefficientStream.tapes gs j hj [] tail out indices)) (extra F)

theorem clear_run (F : ℕ) (heads : Fin 32 → ℕ) (a : Fin 32 → List Bool)
    (hh : ∀ i,heads (eraseSlots i)=0) (ht : ∀ i,(a (workSlots i)).length ≤ F)
    (hd : a 30=List.replicate F true) (hl : a 31=List.replicate (F+1) false) :
    ∃ r,runFrom last (2*F+4) ⟨last.start,heads,a⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=cleared F a ∧ r.steps=2*F+4 := by
  have h := RecoveryScratchErase.erase_ready F (F+1) (fun i=>a (workSlots i)) ht
  simp only [max_self] at h
  apply h.focus_at eraseSlots injective heads a _ hh
  intro i
  refine Fin.addCases (m:=9) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=8) (n:=1) (fun k=>?_) (fun k=>?_) j
    · simp only [eraseSlots,Fin.addCases_left]
    · simpa only [eraseSlots,Fin.addCases_left,Fin.addCases_right] using hd
  · simpa only [eraseSlots,Fin.addCases_right] using hl

theorem result_zero {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    ∀ i,resultHeads gs j hj tail out indices (eraseSlots i)=0 := by
  have h := P1CompactRowCoefficientDock.dock_heads gs j hj [] tail indices
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6
  change (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads 10=0 at h0
  change (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads 11=0 at h1
  change (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads 19=0 at h2
  change (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads 16=0 at h3
  change (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads 25=0 at h4
  change (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads 26=0 at h5
  change (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads 27=0 at h6
  intro i
  simp only [resultHeads,P1CompactRowCoefficientStreamReset.outputHeads,P1CompactRowCoefficientStream.heads]
  fin_cases i <;> simp [eraseSlots,workSlots,Fin.addCases,P1CompactRowCoefficientStreamReset.selected,
    h0,h1,h2,h3,h4,h5,h6]

theorem cleared_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hF : P1CompactRowCoefficientStream.budget gs j hj indices+1 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) ≤ F) :
    ∃ r,runFrom machine (2*P1CompactRowCoefficientStream.budget gs j hj indices+2*F+7)
      (entry gs j F tail out indices)=some r ∧
      r.final.heads=resultHeads gs j hj tail (out++frame (P1CompactRowCoefficientStream.field gs j hj indices)) indices ∧
      r.final.tapes=cleared F (resetTapes gs j hj F tail (out++frame (P1CompactRowCoefficientStream.field gs j hj indices)) indices) ∧
      r.steps ≤ 2*P1CompactRowCoefficientStream.budget gs j hj indices+2*F+7 := by
  obtain ⟨base,hbase,bh,bt,bs,bwork,blog⟩ := P1CompactRowCoefficientStreamReset.reset_run gs j hj F tail out indices hF hD
  let a := TapeEmbedding.receipt (fun _ : Fin 2=>0) (extra F) base
  have ha := TapeEmbedding.run_embed P1CompactRowCoefficientStreamReset.machine (fun _ : Fin 2=>0) (extra F) _ _ base hbase
  have ah : a.final.heads=resultHeads gs j hj tail (out++frame (P1CompactRowCoefficientStream.field gs j hj indices)) indices := by
    change Fin.addCases (m:=30) (n:=2) (motive:=fun _=>ℕ) base.final.heads (fun _=>0)=_
    rw [bh]; rfl
  have atapes : a.final.tapes=resetTapes gs j hj F tail (out++frame (P1CompactRowCoefficientStream.field gs j hj indices)) indices := by
    change Fin.addCases (m:=30) (n:=2) (motive:=fun _=>List Bool) base.final.tapes (extra F)=_
    rw [bt]; rfl
  have hw : ∀ i,(a.final.tapes (workSlots i)).length ≤ F := by
    intro i
    fin_cases i
    · exact bwork 0
    · exact bwork 1
    · exact bwork 2
    · exact bwork 3
    · exact bwork 4
    · exact bwork 5
    · exact bwork 6
    · exact blog
  obtain ⟨b,hb,bh',bt',bs'⟩ := clear_run F a.final.heads a.final.tapes
    (by rw [ah]; exact result_zero gs j hj tail _ indices) hw rfl rfl
  have whole := Composition.run_join first last _ _ _ a b ha hb
  have htime : (2*P1CompactRowCoefficientStream.budget gs j hj indices+2)+1+(2*F+4)=
      2*P1CompactRowCoefficientStream.budget gs j hj indices+2*F+7 := by omega
  rw [htime] at whole
  refine ⟨Composition.joinedReceipt a b,whole,bh'.trans ah,?_,?_⟩
  · change b.final.tapes=_
    rw [bt',atapes]
  · change base.steps+1+b.steps ≤ _
    rw [bs']; omega

end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientStreamClear

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowCoefficientStreamClear_machine_unchanged : P1CompactRowCoefficientStreamClear.machine = RowCoefficientStreamClear.machine := rfl
end NearCubicWires.RepairOrdinary

/-! Exact same-bank endpoint for one coefficient. Rewinding and erasure
restore the original allocated entry, with only the row stream extended. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientReusable
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem erase_pick (i : Fin 32) : RecoveryFocus.pick P1CompactRowCoefficientStreamClear.eraseSlots i=
    (if i=10 then some 0 else if i=11 then some 1 else if i=16 then some 2 else if i=19 then some 3
      else if i=25 then some 4 else if i=26 then some 5 else if i=27 then some 6 else if i=29 then some 7
      else if i=30 then some 8 else if i=31 then some 9 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientStreamClear.injective 0
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientStreamClear.injective 1
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientStreamClear.injective 2
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientStreamClear.injective 3
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientStreamClear.injective 4
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientStreamClear.injective 5
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientStreamClear.injective 6
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientStreamClear.injective 7
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientStreamClear.injective 8
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientStreamClear.injective 9
    | decide

theorem field_pick (i : Fin 28) : RecoveryFocus.pick P1CompactRowCoefficientDock.slots i=
    (if i=10 then some 0 else if i=11 then some 1 else if i=19 then some 2 else if i=16 then some 3
      else if i=25 then some 4 else if i=26 then some 5 else if i=27 then some 6 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientDock.slots_injective 0
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientDock.slots_injective 1
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientDock.slots_injective 2
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientDock.slots_injective 3
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientDock.slots_injective 4
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientDock.slots_injective 5
    | exact RecoveryFocus.pick_slot _ P1CompactRowCoefficientDock.slots_injective 6
    | decide

theorem heads_restore {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    P1CompactRowCoefficientStreamClear.resultHeads gs j hj tail out indices=
      (P1CompactRowCoefficientStreamClear.entry gs j F tail out indices).heads := by
  funext i
  fin_cases i <;> rfl

def data {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) : Fin 32 → List Bool :=
  let w := P1Radix.bits gs
  let C := RowCachedCoordinateBounds.inner w
  let D := RowCachedCoordinateBounds.outer gs w
  let zC := List.replicate C false
  let zD := List.replicate D false
  let zF := List.replicate F false
  ![exactListWord gs,zC,zC,zC,zC,zC,zC,zC,zC,List.replicate w true,zF,zF,zC,
    List.replicate C true,List.replicate (C+1) false,UnaryTemplate.tape j,zF,zD,UnaryTemplate.tape n,
    zF,zD,List.replicate D true,List.replicate (D+1) false,P1CompactRowOccurrenceLoop.word indices++tail,
    CompareMachine.word indices.length,zF,zF,zF,out,zF,List.replicate F true,List.replicate (F+1) false]

theorem entry_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (hF : 1 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) ≤ F) :
    (P1CompactRowCoefficientStreamClear.entry gs j F tail out indices).tapes=data gs j F tail out indices := by
  funext i
  dsimp only [P1CompactRowCoefficientStreamClear.entry,P1CompactRowCoefficientStreamClear.extend,Composition.restart,
    TapeEmbedding.config,P1CompactRowCoefficientStreamReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,
    P1CompactRowCoefficientStream.entry,P1CompactRowCoefficientStream.extend,P1CompactRowCoefficientWhole.entry,P1CompactRowCoefficientDock.extend,
    P1CompactRowCoefficientLoopReset.entry,
    P1CompactRowOccurrenceLoop.cfg,P1CompactRowOccurrenceLoop.data,RepeatMachine.cfg,controlConfig,
    RowOccurrenceReusable.entry,RowOccurrenceAppend.entry,RowOccurrenceAppend.blank,RowOccurrenceAppend.ready,
    RowCachedCoordinateReusable.entry,RowCachedCoordinateReusable.extended,RowCachedCoordinateReusable.extra,
    Composition.leftConfig,Composition.restart,RowCachedCoordinateReset.entry,ZeroPadding.config,
    Rewind.recording,Rewind.config,TapeEmbedding.config,RowCachedCoordinateAppend.entry,
    RowCachedCoordinateAppend.ready,RowCachedCoordinateAppend.extra,RowNativeCoordinateAppend.ready,
    RowNativeCoordinateAppend.extraTapes,RowPowerNativeReusable.tapes]
  fin_cases i <;> simp [data,P1CompactRowCoefficientStreamClear.extra,P1CompactRowCoefficientStreamReset.caps,
    P1CompactRowCoefficientStreamReset.work,RowCachedCoordinateReset.caps,RowOccurrenceReusable.caps,
    Fin.addCases,ZeroPadding.pad,Nat.add_sub_of_le hD]
  all_goals rw [←List.replicate_succ]
  all_goals congr 1
  all_goals omega

def nativeData {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ)
    (source positive negative : List Bool) (total : ℕ) : Fin 25 → List Bool :=
  let w := P1Radix.bits gs
  let C := RowCachedCoordinateBounds.inner w
  let D := RowCachedCoordinateBounds.outer gs w
  let zC := List.replicate C false
  let zD := List.replicate D false
  ![exactListWord gs,zC,zC,zC,zC,zC,zC,zC,zC,List.replicate w true,
    positive++[false],negative++[false],zC,List.replicate C true,List.replicate (C+1) false,
    UnaryTemplate.tape j,zD,zD,UnaryTemplate.tape n,zD,zD,List.replicate D true,
    List.replicate (D+1) false,source,CompareMachine.word total]

theorem cfg_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (phase : Fin 5)
    (source : List Bool) (pos : ℕ) (positive negative : List Bool) (total driver : ℕ) :
    (P1CompactRowOccurrenceLoop.cfg gs j phase source pos positive negative total driver).tapes=
      nativeData gs j source positive negative total := by
  funext i
  dsimp only [
    P1CompactRowOccurrenceLoop.cfg,P1CompactRowOccurrenceLoop.data,RepeatMachine.cfg,controlConfig,
    RowOccurrenceReusable.entry,RowOccurrenceAppend.entry,RowOccurrenceAppend.blank,RowOccurrenceAppend.ready,
    RowCachedCoordinateReusable.entry,RowCachedCoordinateReusable.extended,RowCachedCoordinateReusable.extra,
    Composition.leftConfig,Composition.restart,RowCachedCoordinateReset.entry,ZeroPadding.config,
    Rewind.recording,Rewind.config,TapeEmbedding.config,RowCachedCoordinateAppend.entry,
    RowCachedCoordinateAppend.ready,RowCachedCoordinateAppend.extra,RowNativeCoordinateAppend.ready,
    RowNativeCoordinateAppend.extraTapes,RowPowerNativeReusable.tapes]
  fin_cases i <;> simp [nativeData,RowCachedCoordinateReset.caps,RowOccurrenceReusable.caps,
    Fin.addCases,ZeroPadding.pad]

theorem cleared_low {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (i : Fin 16) :
    P1CompactRowCoefficientStreamClear.cleared F (P1CompactRowCoefficientStreamClear.resetTapes gs j hj F tail out indices) (i.castAdd 16)=
      data gs j F tail out indices (i.castAdd 16) := by
  simp only [P1CompactRowCoefficientStreamClear.cleared,install,erase_pick]
  fin_cases i <;> simp [P1CompactRowCoefficientStreamClear.eraseInput,data,
    P1CompactRowCoefficientStreamClear.resetTapes,
    P1CompactRowCoefficientStreamReset.outputTapes,P1CompactRowCoefficientStreamReset.work,P1CompactRowCoefficientStream.tapes,
    P1CompactRowCoefficientWhole.result,install,field_pick,P1CompactRowCoefficientDock.dock,P1CompactRowCoefficientDock.extend,
    P1CompactRowCoefficientLoopReset.output,P1CompactRowCoefficientLoopReset.finish,SelectiveReset.finished,
    P1CompactRowCoefficientLoopReset.loopFinal,
    cfg_tapes,nativeData,Rewind.config,TapeEmbedding.config,
    Fin.addCases,ZeroPadding.pad]

theorem cleared_high {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (i : Fin 16) :
    P1CompactRowCoefficientStreamClear.cleared F (P1CompactRowCoefficientStreamClear.resetTapes gs j hj F tail out indices) (i.natAdd 16)=
      data gs j F tail out indices (i.natAdd 16) := by
  simp only [P1CompactRowCoefficientStreamClear.cleared,install,erase_pick]
  fin_cases i <;> simp [P1CompactRowCoefficientStreamClear.eraseInput,data,
    P1CompactRowCoefficientStreamClear.resetTapes,
    P1CompactRowCoefficientStreamReset.outputTapes,P1CompactRowCoefficientStreamReset.work,P1CompactRowCoefficientStream.tapes,
    P1CompactRowCoefficientWhole.result,install,field_pick,P1CompactRowCoefficientDock.dock,P1CompactRowCoefficientDock.extend,
    P1CompactRowCoefficientLoopReset.output,P1CompactRowCoefficientLoopReset.finish,SelectiveReset.finished,
    P1CompactRowCoefficientLoopReset.loopFinal,
    cfg_tapes,nativeData,Rewind.config,TapeEmbedding.config,
    Fin.addCases,ZeroPadding.pad]

theorem cleared_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    P1CompactRowCoefficientStreamClear.cleared F (P1CompactRowCoefficientStreamClear.resetTapes gs j hj F tail out indices)=
      data gs j F tail out indices := by
  funext i
  exact Fin.addCases (m:=16) (n:=16)
    (motive:=fun k=>P1CompactRowCoefficientStreamClear.cleared F
      (P1CompactRowCoefficientStreamClear.resetTapes gs j hj F tail out indices) k=data gs j F tail out indices k)
    (cleared_low gs j hj F tail out indices) (cleared_high gs j hj F tail out indices) i

theorem tapes_restore {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (hF : 1 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) ≤ F) :
    P1CompactRowCoefficientStreamClear.cleared F (P1CompactRowCoefficientStreamClear.resetTapes gs j hj F tail out indices)=
      (P1CompactRowCoefficientStreamClear.entry gs j F tail out indices).tapes :=
  (cleared_tapes gs j hj F tail out indices).trans (entry_tapes gs j F tail out indices hF hD).symm

theorem reusable_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hF : P1CompactRowCoefficientStream.budget gs j hj indices+1 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) ≤ F) :
    ∃ r,runFrom P1CompactRowCoefficientStreamClear.machine (2*P1CompactRowCoefficientStream.budget gs j hj indices+2*F+7)
      (P1CompactRowCoefficientStreamClear.entry gs j F tail out indices)=some r ∧
      r.final.heads=(P1CompactRowCoefficientStreamClear.entry gs j F tail
        (out++frame (P1CompactRowCoefficientStream.field gs j hj indices)) indices).heads ∧
      r.final.tapes=(P1CompactRowCoefficientStreamClear.entry gs j F tail
        (out++frame (P1CompactRowCoefficientStream.field gs j hj indices)) indices).tapes ∧
      r.steps ≤ 2*P1CompactRowCoefficientStream.budget gs j hj indices+2*F+7 := by
  obtain ⟨r,hr,rh,rt,rs⟩ := P1CompactRowCoefficientStreamClear.cleared_run gs j hj F tail out indices hF hD
  exact ⟨r,hr,rh.trans (heads_restore gs j hj F tail _ indices),
    rt.trans (tapes_restore gs j hj F tail _ indices (by omega) hD),rs⟩

end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientReusable

/-! One uniform local coefficient workspace and budget, derived from actual
cache bytes, native arity, cached child count and ordered occurrence count.
This removes the local capacity premise; cold driver production is separate. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoefficientBounds
open LocalBitMultitape RepairRepresentation Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (m : ℕ) :=
  16384*(m+1)*RowCachedCoordinateBounds.size gs (P1Radix.bits gs)+40

theorem call_fits {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :
    P1CompactRowCoefficientStream.budget gs j hj indices+1 ≤ capacity gs indices.length := by
  have h := P1CompactRowCoefficientStream.budget_bound gs j hj indices
  unfold capacity
  nlinarith

theorem inner_fits {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (m : ℕ) :
    RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) ≤ capacity gs m := by
  unfold RowCachedCoordinateBounds.outer capacity
  nlinarith

theorem budget_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :
    2*P1CompactRowCoefficientStream.budget gs j hj indices+2*capacity gs indices.length+7 ≤
      65536*(indices.length+1)*RowCachedCoordinateBounds.size gs (P1Radix.bits gs)+165 := by
  have h := P1CompactRowCoefficientStream.budget_bound gs j hj indices
  unfold capacity
  nlinarith

theorem reusable_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    ∃ r,runFrom P1CompactRowCoefficientStreamClear.machine
      (2*P1CompactRowCoefficientStream.budget gs j hj indices+2*capacity gs indices.length+7)
      (P1CompactRowCoefficientStreamClear.entry gs j (capacity gs indices.length) tail out indices)=some r ∧
      r.final.heads=(P1CompactRowCoefficientStreamClear.entry gs j (capacity gs indices.length) tail
        (out++frame (P1CompactRowCoefficientStream.field gs j hj indices)) indices).heads ∧
      r.final.tapes=(P1CompactRowCoefficientStreamClear.entry gs j (capacity gs indices.length) tail
        (out++frame (P1CompactRowCoefficientStream.field gs j hj indices)) indices).tapes ∧
      r.steps ≤ 65536*(indices.length+1)*
        RowCachedCoordinateBounds.size gs (P1Radix.bits gs)+165 := by
  obtain ⟨r,hr,rh,rt,rs⟩ := P1CompactRowCoefficientReusable.reusable_run gs j hj (capacity gs indices.length)
    tail out indices (call_fits gs j hj indices) (inner_fits gs indices.length)
  exact ⟨r,hr,rh,rt,rs.trans (budget_bound gs j hj indices)⟩

end NearCubicWires.RepairOrdinary.P1CompactRowCoefficientBounds

/-! One actual coordinate-loop body computes and appends the stacked field,
restores its coefficient bank, then advances its own coordinate template.
All values used by the next call are physically present in the same bank. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoordinateBody
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := P1CompactRowCoefficientStreamClear.machine
noncomputable def last := RowCoordinateIncrement.focused
noncomputable def machine := Composition.machine first last
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Composition.restart (P1CompactRowCoefficientStreamClear.entry gs j (P1CompactRowCoefficientBounds.capacity gs indices.length)
    tail out indices) machine.start
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :=
  2*P1CompactRowCoefficientStream.budget gs j hj indices+2*P1CompactRowCoefficientBounds.capacity gs indices.length+2*j+17

theorem coordinate_heads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j k F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    (P1CompactRowCoefficientStreamClear.entry gs j F tail out indices).heads=
      (P1CompactRowCoefficientStreamClear.entry gs k F tail out indices).heads := by
  funext i
  dsimp only [P1CompactRowCoefficientStreamClear.entry,P1CompactRowCoefficientStreamClear.extend,Composition.restart,
    TapeEmbedding.config,P1CompactRowCoefficientStreamReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,
    P1CompactRowCoefficientStream.entry,P1CompactRowCoefficientStream.extend,P1CompactRowCoefficientWhole.entry,P1CompactRowCoefficientDock.extend,
    P1CompactRowCoefficientLoopReset.entry,P1CompactRowOccurrenceLoop.cfg,P1CompactRowOccurrenceLoop.data,RepeatMachine.cfg,controlConfig,
    RowOccurrenceReusable.entry,RowOccurrenceAppend.entry,RowOccurrenceAppend.blank,RowOccurrenceAppend.ready,
    RowCachedCoordinateReusable.entry,RowCachedCoordinateReusable.extended,Composition.leftConfig,
    RowCachedCoordinateReset.entry,RowCachedCoordinateAppend.entry,RowCachedCoordinateAppend.ready,
    RowNativeCoordinateAppend.ready]

theorem coordinate_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    Function.update (P1CompactRowCoefficientStreamClear.entry gs j (P1CompactRowCoefficientBounds.capacity gs indices.length)
      tail out indices).tapes 15 (UnaryTemplate.tape (j+1))=
      (P1CompactRowCoefficientStreamClear.entry gs (j+1) (P1CompactRowCoefficientBounds.capacity gs indices.length) tail out indices).tapes := by
  have hF : 1 ≤ P1CompactRowCoefficientBounds.capacity gs indices.length := by unfold P1CompactRowCoefficientBounds.capacity; omega
  rw [P1CompactRowCoefficientReusable.entry_tapes gs j _ tail out indices hF (P1CompactRowCoefficientBounds.inner_fits gs _),
    P1CompactRowCoefficientReusable.entry_tapes gs (j+1) _ tail out indices hF (P1CompactRowCoefficientBounds.inner_fits gs _)]
  funext i
  fin_cases i <;> simp [P1CompactRowCoefficientReusable.data]

theorem body_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    ∃ r,runFrom machine (budget gs j hj indices) (entry gs j tail out indices)=some r ∧
      r.final.heads=(entry gs (j+1) tail (out++frame (P1CompactRowCoefficientStream.field gs j hj indices)) indices).heads ∧
      r.final.tapes=(entry gs (j+1) tail (out++frame (P1CompactRowCoefficientStream.field gs j hj indices)) indices).tapes ∧
      r.steps ≤ budget gs j hj indices := by
  obtain ⟨a,ha,ah,atapes,asteps⟩ := P1CompactRowCoefficientReusable.reusable_run gs j hj
    (P1CompactRowCoefficientBounds.capacity gs indices.length) tail out indices
    (P1CompactRowCoefficientBounds.call_fits gs j hj indices) (P1CompactRowCoefficientBounds.inner_fits gs _)
  have hhead : a.final.heads 15=1 := by rw [ah]; rfl
  have htape : a.final.tapes 15=UnaryTemplate.tape j := by
    rw [atapes,P1CompactRowCoefficientReusable.entry_tapes gs j _ tail _ indices
      (by unfold P1CompactRowCoefficientBounds.capacity; omega) (P1CompactRowCoefficientBounds.inner_fits gs _)]
    rfl
  obtain ⟨b,hb,bh,bt,bs⟩ := RowCoordinateIncrement.focused_run j a.final.heads a.final.tapes hhead htape
  have whole := Composition.run_join first last _ _ _ a b ha hb
  have htime : (2*P1CompactRowCoefficientStream.budget gs j hj indices+2*P1CompactRowCoefficientBounds.capacity gs indices.length+7)+1+
      (2*j+9)=budget gs j hj indices := by unfold budget; omega
  rw [htime] at whole
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,?_⟩
  · change b.final.heads=_
    rw [bh,ah]
    exact coordinate_heads gs j (j+1) _ tail _ indices
  · change b.final.tapes=_
    rw [bt,atapes]
    exact coordinate_tapes gs j tail _ indices
  · change a.steps+1+b.steps ≤ _
    rw [bs]
    unfold budget
    omega

theorem budget_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :
    budget gs j hj indices ≤ 65536*(indices.length+1)*
      RowCachedCoordinateBounds.size gs (P1Radix.bits gs)+2*n+175 := by
  have h := P1CompactRowCoefficientBounds.budget_bound gs j hj indices
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.P1CompactRowCoordinateBody

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowCoordinateBody_machine_unchanged : P1CompactRowCoordinateBody.machine = RowCoordinateBody.machine := rfl
end NearCubicWires.RepairOrdinary

/-! A literal native-arity driver executes all weight coordinates and the
target. Each body restores its coefficient bank and increments its actual
coordinate template. The resulting row is an ordered stream of fields. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoordinateLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RepeatMachine.machine P1CompactRowCoordinateBody.machine (fun _ _=>true)
def field {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length)) (j : ℕ) :=
  if hj : j ≤ n then P1CompactRowCoefficientStream.field gs j hj indices else []
def word {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length)) : ℕ → ℕ → List Bool
  | _,0=>[]
  | j,k+1=>frame (field gs indices j)++word gs indices (j+1) k
def bodyBudget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length)) :=
  65536*(indices.length+1)*RowCachedCoordinateBounds.size gs (P1Radix.bits gs)+2*n+175
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length)) :=
  (n+1)*(bodyBudget gs indices+3)+3
noncomputable def cfg {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length))
    (phase : Fin 5) (j driver : ℕ) (tail out : List Bool) :=
  RepeatMachine.cfg phase (P1CompactRowCoordinateBody.entry gs j tail out indices) (n+1) driver

theorem remaining {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length))
    (j count : ℕ) (hj : j+count=n+1) (tail out : List Bool) :
    ∃ time,time ≤ count*(bodyBudget gs indices+2)+(n+1)+3 ∧
      Timed machine time (cfg gs indices 0 j (j+1) tail out)
        (cfg gs indices 3 (n+1) 1 tail (out++word gs indices j count)) := by
  induction count generalizing j out with
  | zero =>
    have he : j=n+1 := by omega
    subst j
    refine ⟨n+1+3,by omega,?_⟩
    simpa only [machine,cfg,word,List.append_nil] using
      RepeatMachine.exhaust P1CompactRowCoordinateBody.machine (fun _ _=>true)
        (P1CompactRowCoordinateBody.entry gs (n+1) tail out indices) (n+1)
  | succ count ih =>
    have hjn : j ≤ n := by omega
    obtain ⟨r,hr,rh,rt,rs⟩ := P1CompactRowCoordinateBody.body_run gs j hjn tail out indices
    have hbudget := P1CompactRowCoordinateBody.budget_bound gs j hjn indices
    have hs : r.steps ≤ bodyBudget gs indices := rs.trans hbudget
    have ht := RepeatMachine.iteration P1CompactRowCoordinateBody.machine (fun _ _=>true)
      (P1CompactRowCoordinateBody.entry gs j tail out indices) (n+1) j r (by rfl) (by omega) hr
    simp only [↓reduceIte] at ht
    have he := P1CompactRowOccurrenceLoop.cfg_eq 0 r.final
      (P1CompactRowCoordinateBody.entry gs (j+1) tail (out++frame (P1CompactRowCoefficientStream.field gs j hjn indices)) indices)
      (n+1) (j+2) rh rt
    rw [he] at ht
    obtain ⟨time,hbound,htail⟩ := ih (j+1) (by omega)
      (out++frame (P1CompactRowCoefficientStream.field gs j hjn indices))
    have hdriver : j+1+1=j+2 := by omega
    rw [hdriver] at htail
    have whole := ht.trans htail
    refine ⟨r.steps+2+time,?_,?_⟩
    · nlinarith
    · simpa only [machine,cfg,word,field,dif_pos hjn,List.append_assoc] using whole

theorem row_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length))
    (tail out : List Bool) :
    ∃ r,runFrom machine (budget gs indices) (cfg gs indices 0 0 1 tail out)=some r ∧
      r.final=cfg gs indices 3 (n+1) 1 tail (out++word gs indices 0 (n+1)) ∧
      r.steps ≤ budget gs indices := by
  obtain ⟨time,hb,ht⟩ := remaining gs indices 0 (n+1) (by omega) tail out
  have hbudget : time ≤ budget gs indices := by unfold budget; nlinarith
  obtain ⟨r,hr,rf,rs⟩ := ht.run
    (by simp [machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have hmore := runFrom_moreFuel machine time (budget gs indices-time) _ r hr
  rw [Nat.add_sub_of_le hbudget] at hmore
  exact ⟨r,hmore,rf,rs.le.trans hbudget⟩

end NearCubicWires.RepairOrdinary.P1CompactRowCoordinateLoop

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowCoordinateLoop_machine_unchanged : P1CompactRowCoordinateLoop.machine = RowCoordinateLoop.machine := rfl
end NearCubicWires.RepairOrdinary

/-! The actual coordinate stream is the weight-and-target encoding of the
power-radix stack. The canonical radix is related only by its conjunction. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCoordinateLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open SupplierPipeline SupplierPrime SupplierEstimator ThresholdCompiler
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length)) :=
  P1Radix.bits gs*indices.length
def equation {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length)) :=
  RowPowerBinLift.stack (P1Radix.bits gs) (P1CompactRowCachedEquation.equations gs indices)
def equationWord {n : ℕ} (p : ℕ) (e : LabelledEquation (Fin n)) :=
  EquationWidenLoop.stream p (List.ofFn e.weights++[e.target])

theorem field_weight {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (indices : List (Fin gs.length)) (j : Fin n) :
    field gs indices j.val=MatrixScoreBatch.signMagnitude (width gs indices) ((equation gs indices).weights j) := by
  simp only [field,dif_pos j.isLt.le,P1CompactRowCoefficientStream.field,width,equation,
    P1CompactRowCachedEquation.stack_weight]

theorem field_target {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (indices : List (Fin gs.length)) :
    field gs indices n=MatrixScoreBatch.signMagnitude (width gs indices) (equation gs indices).target := by
  simp only [field,dif_pos le_rfl,P1CompactRowCoefficientStream.field,width,equation,
    P1CompactRowCachedEquation.stack_target]

theorem word_add {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length))
    (j a b : ℕ) : word gs indices j (a+b)=word gs indices j a++word gs indices (j+a) b := by
  induction a generalizing j with
  | zero => simp [word]
  | succ a ih =>
    rw [Nat.succ_add,word,word,ih,List.append_assoc]
    rw [show j+1+a=j+(a+1) by omega]

theorem word_ofFn {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length))
    (j count : ℕ) : word gs indices j count=
      (List.ofFn (fun i : Fin count=>frame (field gs indices (j+i.val)))).flatten := by
  induction count generalizing j with
  | zero => simp [word]
  | succ count ih =>
    rw [word,List.ofFn_succ,List.flatten_cons,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    have h : (fun i : Fin count=>frame (field gs indices (j+1+i.val)))=
        (fun i : Fin count=>frame (field gs indices (j+(i.val+1)))) := by
      funext i
      rw [show j+1+i.val=j+(i.val+1) by omega]
    rw [h]

theorem word_equation {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length)) :
    word gs indices 0 (n+1)=equationWord (width gs indices) (equation gs indices) := by
  rw [word_add,word_ofFn]
  simp only [Nat.zero_add,word,List.append_nil,field_target]
  simp only [equationWord,EquationWidenLoop.stream,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,field_weight]
  congr 1
  rw [List.flatMap]
  simp only [List.map_ofFn,Function.comp_def]

theorem equation_magnitude {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (indices : List (Fin gs.length)) :
    equationMagnitudeBound (equation gs indices)<2^(width gs indices) := by
  have h := RowPowerBinLift.stack_width (P1Radix.bits gs)
    (P1CompactRowCachedEquation.equations gs indices) (by
      intro e he
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
      exact P1CompactRowCachedEquation.cache_radix_safe gs i)
  simpa only [P1CompactRowCachedEquation.equations,List.length_map,width,equation] using h

theorem equation_holds {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (indices : List (Fin gs.length)) (input : Fin n→Bool) :
    (equation gs indices).Holds input ↔
      (canonicalEquationStack (P1CompactRowCachedEquation.equations gs indices)).Holds input :=
  P1CompactRowCachedEquation.same_conjunction gs indices input

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length))
    (tail out : List Bool) :
    ∃ r,runFrom machine (budget gs indices) (cfg gs indices 0 0 1 tail out)=some r ∧
      r.final=cfg gs indices 3 (n+1) 1 tail
        (out++equationWord (width gs indices) (equation gs indices)) ∧
      r.steps ≤ budget gs indices := by
  simpa only [word_equation] using row_run gs indices tail out

end NearCubicWires.RepairOrdinary.P1CompactRowCoordinateLoop

/-! The native occurrence coefficient is normalized once, widened directly
to the common cut width, and physically appended. No canonical-radix
coefficient equality or implicit change of the emitted width is used. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonCoefficient
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (F : ℕ) (i : Fin 28) := if P1CompactRowCoefficientStreamReset.work (i.castAdd 1) then F else 0
def extraHeads (out : List Bool) : Fin 4→ℕ := ![0,0,0,out.length]
def extra (p F : ℕ) (out : List Bool) : Fin 4→List Bool :=
  ![List.replicate F false,CompareMachine.word (p+1),List.replicate F false,out]
def extend {s : ℕ} (p F : ℕ) (out : List Bool) (c : Configuration 28 s) :=
  TapeEmbedding.config (extraHeads out) (extra p F out) (ZeroPadding.config (caps F) c)
def fieldSlots : Fin 5→Fin 32 := ![26,28,29,30,31]
theorem field_injective : Function.Injective fieldSlots := by decide
theorem field_pick (i : Fin 32) : RecoveryFocus.pick fieldSlots i=
    (if i=26 then some 0 else if i=28 then some 1 else if i=29 then some 2
      else if i=30 then some 3 else if i=31 then some 4 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot fieldSlots field_injective 0
    | exact RecoveryFocus.pick_slot fieldSlots field_injective 1
    | exact RecoveryFocus.pick_slot fieldSlots field_injective 2
    | exact RecoveryFocus.pick_slot fieldSlots field_injective 3
    | exact RecoveryFocus.pick_slot fieldSlots field_injective 4
    | decide
noncomputable def first := TapeEmbedding.machine 4 P1CompactRowCoefficientWhole.machine
noncomputable def last := RecoveryFocus.machine fieldSlots RowFieldPaddingAppend.machine
noncomputable def machine := Composition.machine first last
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Composition.restart (extend p F out (P1CompactRowCoefficientWhole.entry gs j [] tail indices)) machine.start
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Fin.addCases (m:=28) (n:=4) (motive:=fun _=>ℕ)
    (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads (extraHeads out)
noncomputable def middle {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Fin.addCases (m:=28) (n:=4) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (caps F i) (P1CompactRowCoefficientWhole.result gs j hj [] tail indices i)) (extra p F out)
def value {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :=
  RowPowerNativeReusable.horner ((2 : ℤ)^P1Radix.bits gs)
    (P1CompactRowOccurrenceLoop.values gs j hj indices)
noncomputable def result {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  install fieldSlots (middle gs j hj p F tail out indices)
    (RowFieldPaddingAppend.output (P1CompactRowCoordinateLoop.width gs indices) p F (value gs j hj indices) out)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (p : ℕ)
    (indices : List (Fin gs.length)) := P1CompactRowCoefficientWhole.budget gs j hj indices+8*p+22

theorem value_fits {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) : (value gs j hj indices).natAbs<2^(P1CompactRowCoordinateLoop.width gs indices) := by
  by_cases h : j<n
  · have he := P1CompactRowCachedEquation.stack_weight gs ⟨j,h⟩ indices
    have hm := P1CompactRowCoordinateLoop.equation_magnitude gs indices
    have hw : ((P1CompactRowCoordinateLoop.equation gs indices).weights ⟨j,h⟩).natAbs ≤
        SupplierPrime.equationMagnitudeBound (P1CompactRowCoordinateLoop.equation gs indices) := by
      unfold SupplierPrime.equationMagnitudeBound
      exact (Finset.single_le_sum (f:=fun i : Fin n=>(P1CompactRowCoordinateLoop.equation gs indices).weights i |>.natAbs)
        (fun i _=>Nat.zero_le _) (Finset.mem_univ (⟨j,h⟩ : Fin n))).trans (Nat.le_add_right _ _)
    change (RowPowerNativeReusable.horner _ _).natAbs<_
    rw [he]
    exact hw.trans_lt hm
  · have he : j=n := by omega
    subst j
    have hm := P1CompactRowCoordinateLoop.equation_magnitude gs indices
    have ht : (P1CompactRowCoordinateLoop.equation gs indices).target.natAbs ≤
        SupplierPrime.equationMagnitudeBound (P1CompactRowCoordinateLoop.equation gs indices) := by
      unfold SupplierPrime.equationMagnitudeBound
      omega
    simpa only [value,P1CompactRowCachedEquation.stack_target,P1CompactRowCoordinateLoop.equation] using ht.trans_lt hm

theorem field_input {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (i : Fin 5) :
    middle gs j hj p F tail out indices (fieldSlots i)=
      RowFieldPaddingAppend.input (P1CompactRowCoordinateLoop.width gs indices) p F (value gs j hj indices) out i := by
  fin_cases i
  · change ZeroPadding.pad F (P1CompactRowCoefficientWhole.result gs j hj [] tail indices 26)=_
    rw [P1CompactRowCoefficientWhole.result_field]
    rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem field_heads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (tail out : List Bool) (indices : List (Fin gs.length)) (i : Fin 5) :
    heads gs j hj tail out indices (fieldSlots i)=RowFieldPaddingAppend.heads out i := by
  fin_cases i
  · exact P1CompactRowCoefficientDock.dock_heads gs j hj [] tail indices 5
  · rfl
  · rfl
  · rfl
  · rfl

theorem whole_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : P1CompactRowCoordinateLoop.width gs indices ≤ p) (hF : 2*p+5 ≤ F) :
    ∃ r,runFrom machine (budget gs j hj p indices) (entry gs j p F tail out indices)=some r ∧
      r.final.heads=heads gs j hj tail (out++frame (MatrixScoreBatch.signMagnitude p (value gs j hj indices))) indices ∧
      r.final.tapes=result gs j hj p F tail (out++frame (MatrixScoreBatch.signMagnitude p (value gs j hj indices))) indices ∧
      r.steps ≤ budget gs j hj p indices := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := P1CompactRowCoefficientWhole.whole_run gs j hj [] tail indices
  obtain ⟨pad,hpad,pf,ps,_⟩ := ZeroPadding.run_config P1CompactRowCoefficientWhole.machine (caps F) _ _ base hbase
  let a := TapeEmbedding.receipt (extraHeads out) (extra p F out) pad
  have ha := TapeEmbedding.run_embed P1CompactRowCoefficientWhole.machine (extraHeads out) (extra p F out) _ _ pad hpad
  have ah : a.final.heads=heads gs j hj tail out indices := by
    change Fin.addCases (m:=28) (n:=4) (motive:=fun _=>ℕ) pad.final.heads (extraHeads out)=_
    rw [pf]
    change Fin.addCases (m:=28) (n:=4) (motive:=fun _=>ℕ) base.final.heads (extraHeads out)=_
    rw [bh]; rfl
  have atapes : a.final.tapes=middle gs j hj p F tail out indices := by
    change Fin.addCases (m:=28) (n:=4) (motive:=fun _=>List Bool) pad.final.tapes (extra p F out)=_
    rw [pf]
    change Fin.addCases (m:=28) (n:=4) (motive:=fun _=>List Bool)
      (fun i=>ZeroPadding.pad (caps F i) (base.final.tapes i)) (extra p F out)=_
    rw [bt]; rfl
  obtain ⟨b0,hb0,bh0,bt0,bs0⟩ := RowFieldPaddingAppend.field_run (P1CompactRowCoordinateLoop.width gs indices) p F
    (value gs j hj indices) out hp (value_fits gs j hj indices) hF
  obtain ⟨b,hb,bf,bstep⟩ := RecoveryFocus.run_config fieldSlots field_injective RowFieldPaddingAppend.machine
    a.final.heads a.final.tapes _ _ b0 hb0
  have hi : RecoveryFocus.config fieldSlots a.final.heads a.final.tapes
      ⟨RowFieldPaddingAppend.machine.start,RowFieldPaddingAppend.heads out,
        RowFieldPaddingAppend.input (P1CompactRowCoordinateLoop.width gs indices) p F (value gs j hj indices) out⟩=
      Composition.restart a.final last.start := by
    apply WilliamsSourceCrop.focus_same fieldSlots (Composition.restart a.final last.start)
    · intro i; change a.final.heads (fieldSlots i)=_; rw [ah]; exact field_heads gs j hj tail out indices i
    · intro i; change a.final.tapes (fieldSlots i)=_; rw [atapes]; exact field_input gs j hj p F tail out indices i
  rw [hi] at hb
  have h := Composition.run_join first last _ _ _ a b ha hb
  have htime : P1CompactRowCoefficientWhole.budget gs j hj indices+1+(8*p+21)=budget gs j hj p indices := by unfold budget; omega
  rw [htime] at h
  refine ⟨Composition.joinedReceipt a b,h,?_,?_,?_⟩
  · change b.final.heads=_
    rw [bf]
    simp only [RecoveryFocus.config,bh0,ah,field_pick]
    funext i
    have h26 := P1CompactRowCoefficientDock.dock_heads gs j hj [] tail indices 5
    change (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads 26=0 at h26
    fin_cases i <;> simp [heads,RowFieldPaddingAppend.heads,extraHeads,Fin.addCases,h26]
  · change b.final.tapes=_
    rw [bf]
    change install fieldSlots a.final.tapes b0.final.tapes=_
    rw [bt0,atapes]
    unfold result
    funext i
    simp only [install,field_pick]
    fin_cases i <;> simp [middle,Fin.addCases]
  · change pad.steps+1+b.steps ≤ _
    rw [ps,bs,bstep]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.P1CompactRowCommonCoefficient

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowCommonCoefficient_machine_unchanged : P1CompactRowCommonCoefficient.machine = RowCommonCoefficient.machine := rfl
end NearCubicWires.RepairOrdinary

/-! Restore the dedicated occurrence cursor after the common-width append.
All scratch lengths are bounded using the executed prefix, and the physical
reset log is retained at the same paid allocation for subsequent erasure. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonReset
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlots : Fin 9→Fin 32 := ![10,11,16,19,25,26,27,28,30]
def selected (i : Fin 32) := decide (i=23)
def caps (F : ℕ) (i : Fin 33) := if i=32 then F else 0
noncomputable def machine := MaskedReset.machine P1CompactRowCommonCoefficient.machine selected
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  ZeroPadding.config (caps F) (Rewind.recording (P1CompactRowCommonCoefficient.entry gs j p F tail out indices) 0)
def outputHeads (h : Fin 32→ℕ) :=
  Fin.addCases (m:=32) (n:=1) (motive:=fun _=>ℕ) (fun i=>if selected i then 0 else h i) (fun _=>0)
def outputTapes (F : ℕ) (a : Fin 32→List Bool) :=
  Fin.addCases (m:=32) (n:=1) (motive:=fun _=>List Bool) a (fun _=>List.replicate F false)

theorem start_head {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (k : Fin 9) :
    (P1CompactRowCommonCoefficient.entry gs j p F tail out indices).heads (workSlots k)=0 := by
  fin_cases k <;> rfl

theorem start_support {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hF : 1 ≤ F) (hD : RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) ≤ F)
    (k : Fin 9) : ((P1CompactRowCommonCoefficient.entry gs j p F tail out indices).tapes (workSlots k)).length ≤ F := by
  have h := P1CompactRowCoefficientStreamReset.start_support gs j F tail [] indices hF hD
  dsimp only [P1CompactRowCommonCoefficient.entry,P1CompactRowCommonCoefficient.extend,Composition.restart,
    TapeEmbedding.config,ZeroPadding.config]
  dsimp only [P1CompactRowCoefficientStream.entry,P1CompactRowCoefficientStream.extend,Composition.restart,
    TapeEmbedding.config] at h
  fin_cases k
  · change (ZeroPadding.pad F ((P1CompactRowCoefficientWhole.entry gs j [] tail indices).tapes 10)).length ≤ F
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (h 0)
  · change (ZeroPadding.pad F ((P1CompactRowCoefficientWhole.entry gs j [] tail indices).tapes 11)).length ≤ F
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (h 1)
  · change (ZeroPadding.pad F ((P1CompactRowCoefficientWhole.entry gs j [] tail indices).tapes 16)).length ≤ F
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (h 2)
  · change (ZeroPadding.pad F ((P1CompactRowCoefficientWhole.entry gs j [] tail indices).tapes 19)).length ≤ F
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (h 3)
  · change (ZeroPadding.pad F ((P1CompactRowCoefficientWhole.entry gs j [] tail indices).tapes 25)).length ≤ F
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (h 4)
  · change (ZeroPadding.pad F ((P1CompactRowCoefficientWhole.entry gs j [] tail indices).tapes 26)).length ≤ F
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (h 5)
  · change (ZeroPadding.pad F ((P1CompactRowCoefficientWhole.entry gs j [] tail indices).tapes 27)).length ≤ F
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (h 6)
  · simp [P1CompactRowCommonCoefficient.extra,workSlots,Fin.addCases]
  · simp [P1CompactRowCommonCoefficient.extra,workSlots,Fin.addCases]

theorem reset_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : P1CompactRowCoordinateLoop.width gs indices ≤ p)
    (hcall : P1CompactRowCommonCoefficient.budget gs j hj p indices+1 ≤ F)
    (hF : 2*p+5 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) ≤ F) :
    ∃ r,runFrom machine (2*P1CompactRowCommonCoefficient.budget gs j hj p indices+2)
      (entry gs j p F tail out indices)=some r ∧
      r.final.heads=outputHeads (P1CompactRowCommonCoefficient.heads gs j hj tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices) ∧
      r.final.tapes=outputTapes F (P1CompactRowCommonCoefficient.result gs j hj p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices) ∧
      r.steps ≤ 2*P1CompactRowCommonCoefficient.budget gs j hj p indices+2 ∧
      (∀ k : Fin 9,(r.final.tapes ((workSlots k).castAdd 1)).length ≤ F) ∧
      (r.final.tapes 32).length ≤ F := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := P1CompactRowCommonCoefficient.whole_run gs j hj p F tail out indices hp hF
  have hh : ∀ i,selected i=true → base.final.heads i ≤ base.steps := by
    intro i hi
    have he : i=23 := by simpa only [selected,decide_eq_true_eq] using hi
    subst i
    have h := SelectiveReset.prefix_head (prefix_of_run _ _ _ _ hbase).1 23
    have h0 : (P1CompactRowCommonCoefficient.entry gs j p F tail out indices).heads 23=0 := rfl
    simpa only [h0,zero_add] using h
  obtain ⟨reset,hr,rf,rs,_⟩ := MaskedReset.reset_run P1CompactRowCommonCoefficient.machine selected _ _ base hbase hh
  obtain ⟨r,hrun,rfinal,rsteps,_⟩ := ZeroPadding.run_config machine (caps F) _ _ reset hr
  have hsmall : base.steps ≤ F := by omega
  have ht : r.final.tapes=outputTapes F base.final.tapes := by
    rw [rfinal,rf]
    funext i
    refine Fin.addCases (m:=32) (n:=1) (fun a=>?_) (fun a=>?_) i
    · have hn : a.castAdd 1≠(32 : Fin 33) := by
        intro he; have hv:=congrArg (fun j : Fin 33=>j.val) he
        simp only [Fin.val_castAdd] at hv
        omega
      simp only [ZeroPadding.config,caps,hn,if_false,SelectiveReset.finished,Rewind.config,
        outputTapes,Fin.addCases_left,ZeroPadding.pad_zero]
    · fin_cases a
      change ZeroPadding.pad F (List.replicate base.steps false)=List.replicate F false
      simp [ZeroPadding.pad,Nat.add_sub_of_le hsmall]
  have hb : 2*base.steps+2 ≤ 2*P1CompactRowCommonCoefficient.budget gs j hj p indices+2 := by omega
  have more := runFrom_moreFuel machine (2*base.steps+2)
    ((2*P1CompactRowCommonCoefficient.budget gs j hj p indices+2)-(2*base.steps+2)) _ r hrun
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,?_,ht.trans (congrArg (outputTapes F) bt),?_,?_,?_⟩
  · rw [rfinal,rf]
    change outputHeads base.final.heads=_
    rw [bh]
  · rw [rsteps,rs]; omega
  · intro k
    rw [ht]
    simp only [outputTapes,Fin.addCases_left]
    have h := PCPSerializerReuse.tape_support P1CompactRowCommonCoefficient.machine _ _ base hbase (workSlots k) F 0
      (start_head gs j p F tail out indices k).le
      ((start_support gs j p F tail out indices (by omega) hD k).trans (Nat.le_max_left _ _))
    simp only [zero_add] at h
    exact h.trans (max_le le_rfl (by omega))
  · rw [ht]; simp [outputTapes,Fin.addCases]

end NearCubicWires.RepairOrdinary.P1CompactRowCommonReset

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowCommonReset_machine_unchanged : P1CompactRowCommonReset.machine = RowCommonReset.machine := rfl
end NearCubicWires.RepairOrdinary

/-! Physically erase the common-width coefficient scratch, preserving the
native cache, occurrence stream, dimensions and live cut-output cursor. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonClear
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlots : Fin 10→Fin 35 := ![10,11,16,19,25,26,27,28,30,32]
def eraseSlots : Fin 12→Fin 35 := Fin.addCases (m:=11) (n:=1) (motive:=fun _=>Fin 35)
  (Fin.addCases (m:=10) (n:=1) (motive:=fun _=>Fin 35) workSlots (fun _=>33)) (fun _=>34)
theorem injective : Function.Injective eraseSlots := by decide
def eraseInput (F : ℕ) (backing : Fin 10→List Bool) :=
  Fin.addCases (m:=11) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=10) (n:=1) (motive:=fun _=>List Bool) backing (fun _=>List.replicate F true))
    (fun _=>List.replicate (F+1) false)
noncomputable def cleared (F : ℕ) (a : Fin 35→List Bool) :=
  install eraseSlots a (eraseInput F (fun _=>List.replicate F false))
noncomputable def first := TapeEmbedding.machine 2 P1CompactRowCommonReset.machine
noncomputable def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 10)
noncomputable def machine := Composition.machine first last
def extra (F : ℕ) : Fin 2→List Bool := ![List.replicate F true,List.replicate (F+1) false]
def extend {s : ℕ} (F : ℕ) (c : Configuration 33 s) := TapeEmbedding.config (fun _=>0) (extra F) c
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Composition.restart (extend F (P1CompactRowCommonReset.entry gs j p F tail out indices)) machine.start
noncomputable def resultHeads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Fin.addCases (m:=33) (n:=2) (motive:=fun _=>ℕ)
    (P1CompactRowCommonReset.outputHeads (P1CompactRowCommonCoefficient.heads gs j hj tail out indices)) (fun _=>0)
noncomputable def resetTapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (p F : ℕ) (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Fin.addCases (m:=33) (n:=2) (motive:=fun _=>List Bool)
    (P1CompactRowCommonReset.outputTapes F (P1CompactRowCommonCoefficient.result gs j hj p F tail out indices)) (extra F)

theorem clear_run (F : ℕ) (heads : Fin 35→ℕ) (a : Fin 35→List Bool)
    (hh : ∀ i,heads (eraseSlots i)=0) (ht : ∀ i,(a (workSlots i)).length ≤ F)
    (hd : a 33=List.replicate F true) (hl : a 34=List.replicate (F+1) false) :
    ∃ r,runFrom last (2*F+4) ⟨last.start,heads,a⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=cleared F a ∧ r.steps=2*F+4 := by
  have h := RecoveryScratchErase.erase_ready F (F+1) (fun i=>a (workSlots i)) ht
  simp only [max_self] at h
  apply h.focus_at eraseSlots injective heads a _ hh
  intro i
  refine Fin.addCases (m:=11) (n:=1) (fun j=>?_) (fun j=>?_) i
  · refine Fin.addCases (m:=10) (n:=1) (fun k=>?_) (fun k=>?_) j
    · simp only [eraseSlots,Fin.addCases_left]
    · simpa only [eraseSlots,Fin.addCases_left,Fin.addCases_right] using hd
  · simpa only [eraseSlots,Fin.addCases_right] using hl

theorem result_zero {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    ∀ i,resultHeads gs j hj tail out indices (eraseSlots i)=0 := by
  have h := P1CompactRowCoefficientDock.dock_heads gs j hj [] tail indices
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6
  change (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads 10=0 at h0
  change (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads 11=0 at h1
  change (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads 19=0 at h2
  change (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads 16=0 at h3
  change (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads 25=0 at h4
  change (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads 26=0 at h5
  change (P1CompactRowCoefficientDock.dock gs j hj [] tail indices).heads 27=0 at h6
  intro i
  simp only [resultHeads,P1CompactRowCommonReset.outputHeads,P1CompactRowCommonCoefficient.heads]
  fin_cases i <;> simp [eraseSlots,workSlots,Fin.addCases,P1CompactRowCommonReset.selected,
    P1CompactRowCommonCoefficient.extraHeads,h0,h1,h2,h3,h4,h5,h6]

theorem cleared_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : P1CompactRowCoordinateLoop.width gs indices ≤ p)
    (hcall : P1CompactRowCommonCoefficient.budget gs j hj p indices+1 ≤ F)
    (hF : 2*p+5 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) ≤ F) :
    ∃ r,runFrom machine (2*P1CompactRowCommonCoefficient.budget gs j hj p indices+2*F+7)
      (entry gs j p F tail out indices)=some r ∧
      r.final.heads=resultHeads gs j hj tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices ∧
      r.final.tapes=cleared F (resetTapes gs j hj p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices) ∧
      r.steps ≤ 2*P1CompactRowCommonCoefficient.budget gs j hj p indices+2*F+7 := by
  obtain ⟨base,hbase,bh,bt,bs,bwork,blog⟩ := P1CompactRowCommonReset.reset_run gs j hj p F tail out indices hp hcall hF hD
  let a := TapeEmbedding.receipt (fun _ : Fin 2=>0) (extra F) base
  have ha := TapeEmbedding.run_embed P1CompactRowCommonReset.machine (fun _ : Fin 2=>0) (extra F) _ _ base hbase
  have ah : a.final.heads=resultHeads gs j hj tail
      (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices := by
    change Fin.addCases (m:=33) (n:=2) (motive:=fun _=>ℕ) base.final.heads (fun _=>0)=_
    rw [bh]; rfl
  have atapes : a.final.tapes=resetTapes gs j hj p F tail
      (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices := by
    change Fin.addCases (m:=33) (n:=2) (motive:=fun _=>List Bool) base.final.tapes (extra F)=_
    rw [bt]; rfl
  have hw : ∀ i,(a.final.tapes (workSlots i)).length ≤ F := by
    intro i
    fin_cases i
    · exact bwork 0
    · exact bwork 1
    · exact bwork 2
    · exact bwork 3
    · exact bwork 4
    · exact bwork 5
    · exact bwork 6
    · exact bwork 7
    · exact bwork 8
    · exact blog
  obtain ⟨b,hb,bh',bt',bs'⟩ := clear_run F a.final.heads a.final.tapes
    (by rw [ah]; exact result_zero gs j hj tail _ indices) hw rfl rfl
  have whole := Composition.run_join first last _ _ _ a b ha hb
  have ht : (2*P1CompactRowCommonCoefficient.budget gs j hj p indices+2)+1+(2*F+4)=
      2*P1CompactRowCommonCoefficient.budget gs j hj p indices+2*F+7 := by omega
  rw [ht] at whole
  refine ⟨Composition.joinedReceipt a b,whole,bh'.trans ah,?_,?_⟩
  · change b.final.tapes=_
    rw [bt',atapes]
  · change base.steps+1+b.steps ≤ _
    rw [bs']; omega

end NearCubicWires.RepairOrdinary.P1CompactRowCommonClear

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowCommonClear_machine_unchanged : P1CompactRowCommonClear.machine = RowCommonClear.machine := rfl
end NearCubicWires.RepairOrdinary

/-! The exact common-width bank is restored after each executed coefficient.
Only the live output contains the appended common-width signed field. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonReusable
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) : Fin 35→List Bool :=
  let w := P1Radix.bits gs
  let C := RowCachedCoordinateBounds.inner w
  let D := RowCachedCoordinateBounds.outer gs w
  let zC := List.replicate C false
  let zD := List.replicate D false
  let zF := List.replicate F false
  ![exactListWord gs,zC,zC,zC,zC,zC,zC,zC,zC,List.replicate w true,zF,zF,zC,
    List.replicate C true,List.replicate (C+1) false,UnaryTemplate.tape j,zF,zD,UnaryTemplate.tape n,
    zF,zD,List.replicate D true,List.replicate (D+1) false,P1CompactRowOccurrenceLoop.word indices++tail,
    CompareMachine.word indices.length,zF,zF,zF,zF,CompareMachine.word (p+1),zF,out,zF,
    List.replicate F true,List.replicate (F+1) false]

theorem entry_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (hF : 1 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) ≤ F) :
    (P1CompactRowCommonClear.entry gs j p F tail out indices).tapes=data gs j p F tail out indices := by
  funext i
  dsimp only [P1CompactRowCommonClear.entry,P1CompactRowCommonClear.extend,Composition.restart,TapeEmbedding.config,
    P1CompactRowCommonReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,P1CompactRowCommonCoefficient.entry,
    P1CompactRowCommonCoefficient.extend,P1CompactRowCoefficientWhole.entry,P1CompactRowCoefficientDock.extend,P1CompactRowCoefficientLoopReset.entry]
  simp only [P1CompactRowCoefficientReusable.cfg_tapes,List.nil_append,List.length_nil]
  fin_cases i <;> simp [data,P1CompactRowCommonClear.extra,P1CompactRowCommonReset.caps,P1CompactRowCommonCoefficient.caps,
    P1CompactRowCommonCoefficient.extra,P1CompactRowCoefficientStreamReset.work,P1CompactRowCoefficientReusable.nativeData,
    Fin.addCases,ZeroPadding.pad,Nat.add_sub_of_le hD]
  all_goals rw [←List.replicate_succ]
  all_goals congr 1
  all_goals omega

theorem erase_pick (i : Fin 35) : RecoveryFocus.pick P1CompactRowCommonClear.eraseSlots i=
    (if i=10 then some 0 else if i=11 then some 1 else if i=16 then some 2 else if i=19 then some 3
      else if i=25 then some 4 else if i=26 then some 5 else if i=27 then some 6 else if i=28 then some 7
      else if i=30 then some 8 else if i=32 then some 9 else if i=33 then some 10 else if i=34 then some 11 else none) := by
  fin_cases i
  all_goals first
    | exact RecoveryFocus.pick_slot _ P1CompactRowCommonClear.injective 0
    | exact RecoveryFocus.pick_slot _ P1CompactRowCommonClear.injective 1
    | exact RecoveryFocus.pick_slot _ P1CompactRowCommonClear.injective 2
    | exact RecoveryFocus.pick_slot _ P1CompactRowCommonClear.injective 3
    | exact RecoveryFocus.pick_slot _ P1CompactRowCommonClear.injective 4
    | exact RecoveryFocus.pick_slot _ P1CompactRowCommonClear.injective 5
    | exact RecoveryFocus.pick_slot _ P1CompactRowCommonClear.injective 6
    | exact RecoveryFocus.pick_slot _ P1CompactRowCommonClear.injective 7
    | exact RecoveryFocus.pick_slot _ P1CompactRowCommonClear.injective 8
    | exact RecoveryFocus.pick_slot _ P1CompactRowCommonClear.injective 9
    | exact RecoveryFocus.pick_slot _ P1CompactRowCommonClear.injective 10
    | exact RecoveryFocus.pick_slot _ P1CompactRowCommonClear.injective 11
    | decide

theorem cleared_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    P1CompactRowCommonClear.cleared F (P1CompactRowCommonClear.resetTapes gs j hj p F tail out indices)=
      data gs j p F tail out indices := by
  funext i
  simp only [P1CompactRowCommonClear.cleared,install,erase_pick]
  fin_cases i <;> simp [P1CompactRowCommonClear.eraseInput,data,P1CompactRowCommonClear.resetTapes,
    P1CompactRowCommonReset.outputTapes,P1CompactRowCommonCoefficient.result,install,P1CompactRowCommonCoefficient.field_pick,
    RowFieldPaddingAppend.output,RowFieldPaddingAppend.extend,RowFieldPadding.output,
    P1CompactRowCommonCoefficient.middle,P1CompactRowCommonCoefficient.caps,P1CompactRowCoefficientStreamReset.work,
    P1CompactRowCoefficientWhole.result,P1CompactRowCoefficientReusable.field_pick,P1CompactRowCoefficientDock.dock,P1CompactRowCoefficientDock.extend,
    P1CompactRowCoefficientLoopReset.output,P1CompactRowCoefficientLoopReset.finish,SelectiveReset.finished,
    P1CompactRowCoefficientLoopReset.loopFinal,P1CompactRowCoefficientReusable.cfg_tapes,P1CompactRowCoefficientReusable.nativeData,
    Rewind.config,TapeEmbedding.config,Fin.addCases,ZeroPadding.pad]

theorem heads_restore {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    P1CompactRowCommonClear.resultHeads gs j hj tail out indices=
      (P1CompactRowCommonClear.entry gs j p F tail out indices).heads := by
  funext i
  fin_cases i <;> rfl

theorem reusable_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : P1CompactRowCoordinateLoop.width gs indices ≤ p)
    (hcall : P1CompactRowCommonCoefficient.budget gs j hj p indices+1 ≤ F)
    (hF : 2*p+5 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) ≤ F) :
    ∃ r,runFrom P1CompactRowCommonClear.machine (2*P1CompactRowCommonCoefficient.budget gs j hj p indices+2*F+7)
      (P1CompactRowCommonClear.entry gs j p F tail out indices)=some r ∧
      r.final.heads=(P1CompactRowCommonClear.entry gs j p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices).heads ∧
      r.final.tapes=(P1CompactRowCommonClear.entry gs j p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices).tapes ∧
      r.steps ≤ 2*P1CompactRowCommonCoefficient.budget gs j hj p indices+2*F+7 := by
  obtain ⟨r,hr,rh,rt,rs⟩ := P1CompactRowCommonClear.cleared_run gs j hj p F tail out indices hp hcall hF hD
  refine ⟨r,hr,rh.trans (heads_restore gs j hj p F tail _ indices),?_,rs⟩
  rw [rt,cleared_tapes,entry_tapes gs j p F tail _ indices (by omega) hD]

end NearCubicWires.RepairOrdinary.P1CompactRowCommonReusable

/-! A single explicit allocation pays the common-width coefficient and its
complete physical cleanup. The remaining cold caller must produce these
raw counters; no local capacity inequality survives this endpoint. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonBounds
open LocalBitMultitape RepairRepresentation RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (m p : ℕ) :=
  16384*(m+1)*RowCachedCoordinateBounds.size gs (P1Radix.bits gs)+16*p+64
def bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (m p : ℕ) :=
  65536*(m+1)*RowCachedCoordinateBounds.size gs (P1Radix.bits gs)+64*p+256

theorem call_fits {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (p : ℕ)
    (indices : List (Fin gs.length)) :
    P1CompactRowCommonCoefficient.budget gs j hj p indices+1 ≤ capacity gs indices.length p := by
  have h := P1CompactRowCoefficientWhole.budget_bound gs j hj indices
  unfold P1CompactRowCommonCoefficient.budget capacity
  nlinarith

theorem padding_fits {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (m p : ℕ) :
    2*p+5 ≤ capacity gs m p := by unfold capacity; omega

theorem inner_fits {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (m p : ℕ) :
    RowCachedCoordinateBounds.outer gs (P1Radix.bits gs) ≤ capacity gs m p := by
  unfold RowCachedCoordinateBounds.outer capacity
  nlinarith

theorem budget_bound {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (p : ℕ)
    (indices : List (Fin gs.length)) :
    2*P1CompactRowCommonCoefficient.budget gs j hj p indices+2*capacity gs indices.length p+7 ≤
      bound gs indices.length p := by
  have h := P1CompactRowCoefficientWhole.budget_bound gs j hj indices
  unfold P1CompactRowCommonCoefficient.budget capacity bound
  nlinarith

theorem reusable_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j ≤ n) (p : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : P1CompactRowCoordinateLoop.width gs indices ≤ p) :
    ∃ r,runFrom P1CompactRowCommonClear.machine (bound gs indices.length p)
      (P1CompactRowCommonClear.entry gs j p (capacity gs indices.length p) tail out indices)=some r ∧
      r.final.heads=(P1CompactRowCommonClear.entry gs j p (capacity gs indices.length p) tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices).heads ∧
      r.final.tapes=(P1CompactRowCommonClear.entry gs j p (capacity gs indices.length p) tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices).tapes ∧
      r.steps ≤ bound gs indices.length p := by
  obtain ⟨r,hr,rh,rt,rs⟩ := P1CompactRowCommonReusable.reusable_run gs j hj p (capacity gs indices.length p)
    tail out indices hp (call_fits gs j hj p indices) (padding_fits gs indices.length p)
    (inner_fits gs indices.length p)
  have hb := budget_bound gs j hj p indices
  have more := runFrom_moreFuel P1CompactRowCommonClear.machine _
    (bound gs indices.length p-(2*P1CompactRowCommonCoefficient.budget gs j hj p indices+2*capacity gs indices.length p+7)) _ r hr
  rw [Nat.add_sub_of_le hb] at more
  exact ⟨r,more,rh,rt,rs.trans hb⟩

end NearCubicWires.RepairOrdinary.P1CompactRowCommonBounds

/-! The actual common-width row consumer: append one coefficient at the
shared cut width, restore its bank, and advance the coordinate on tape15. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonCoordinateBody
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 1→Fin 35 := fun _=>15
theorem injective : Function.Injective slots := by intro a b _; exact Subsingleton.elim _ _
noncomputable def increment := RecoveryFocus.machine slots RowCoordinateIncrement.machine
noncomputable def machine := Composition.machine P1CompactRowCommonClear.machine increment
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j p : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Composition.restart (P1CompactRowCommonClear.entry gs j p (P1CompactRowCommonBounds.capacity gs indices.length p)
    tail out indices) machine.start
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j p : ℕ)
    (indices : List (Fin gs.length)) := P1CompactRowCommonBounds.bound gs indices.length p+2*j+10

theorem pick (i : Fin 35) : RecoveryFocus.pick slots i=(if i=15 then some 0 else none) := by
  fin_cases i
  all_goals first | exact RecoveryFocus.pick_slot slots injective 0 | decide

theorem increment_run (j : ℕ) (heads : Fin 35→ℕ) (tapes : Fin 35→List Bool)
    (hh : heads 15=1) (ht : tapes 15=UnaryTemplate.tape j) :
    ∃ r,runFrom increment (2*j+9) ⟨increment.start,heads,tapes⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=Function.update tapes 15 (UnaryTemplate.tape (j+1)) ∧
      r.steps=2*j+9 := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := RowCoordinateIncrement.increment_run j
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config slots injective RowCoordinateIncrement.machine
    heads tapes _ _ base hbase
  have he : RecoveryFocus.config slots heads tapes
      (RowCoordinateIncrement.cfg RowCoordinateIncrement.machine.start 1 (UnaryTemplate.tape j))=
      (⟨increment.start,heads,tapes⟩ : Configuration 35 9) := by
    apply WilliamsSourceCrop.focus_same slots (⟨increment.start,heads,tapes⟩ : Configuration 35 9)
    · intro i; exact hh
    · intro i; exact ht
  rw [he] at hr
  refine ⟨r,hr,?_,?_,rs.trans bs⟩
  · rw [rf]
    simp only [RecoveryFocus.config,bh]
    funext i
    by_cases hi : i=15
    · subst i; simp [pick,hh]
    · simp [pick,hi]
  · rw [rf]
    change install slots tapes base.final.tapes=_
    rw [bt]
    funext i
    by_cases hi : i=15
    · subst i; simp [install,pick]
    · simp [install,pick,hi]

theorem coordinate_heads {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j k p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    (P1CompactRowCommonClear.entry gs j p F tail out indices).heads=
      (P1CompactRowCommonClear.entry gs k p F tail out indices).heads := by
  funext i
  dsimp only [P1CompactRowCommonClear.entry,P1CompactRowCommonClear.extend,Composition.restart,
    TapeEmbedding.config,P1CompactRowCommonReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,
    P1CompactRowCommonCoefficient.entry,P1CompactRowCommonCoefficient.extend,P1CompactRowCoefficientWhole.entry,P1CompactRowCoefficientDock.extend,
    P1CompactRowCoefficientLoopReset.entry,P1CompactRowOccurrenceLoop.cfg,P1CompactRowOccurrenceLoop.data,RepeatMachine.cfg,controlConfig,
    RowOccurrenceReusable.entry,RowOccurrenceAppend.entry,RowOccurrenceAppend.blank,RowOccurrenceAppend.ready,
    RowCachedCoordinateReusable.entry,RowCachedCoordinateReusable.extended,Composition.leftConfig,
    RowCachedCoordinateReset.entry,RowCachedCoordinateAppend.entry,RowCachedCoordinateAppend.ready,
    RowNativeCoordinateAppend.ready]

theorem coordinate_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j p : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    Function.update (P1CompactRowCommonClear.entry gs j p (P1CompactRowCommonBounds.capacity gs indices.length p)
      tail out indices).tapes 15 (UnaryTemplate.tape (j+1))=
      (P1CompactRowCommonClear.entry gs (j+1) p (P1CompactRowCommonBounds.capacity gs indices.length p)
        tail out indices).tapes := by
  have hF : 1≤P1CompactRowCommonBounds.capacity gs indices.length p := by unfold P1CompactRowCommonBounds.capacity; omega
  rw [P1CompactRowCommonReusable.entry_tapes gs j p _ tail out indices hF (P1CompactRowCommonBounds.inner_fits gs _ p),
    P1CompactRowCommonReusable.entry_tapes gs (j+1) p _ tail out indices hF (P1CompactRowCommonBounds.inner_fits gs _ p)]
  funext i
  fin_cases i <;> simp [P1CompactRowCommonReusable.data]

theorem body_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (j : ℕ) (hj : j≤n) (p : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : P1CompactRowCoordinateLoop.width gs indices≤p) :
    ∃ r,runFrom machine (budget gs j p indices) (entry gs j p tail out indices)=some r ∧
      r.final.heads=(entry gs (j+1) p tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices).heads ∧
      r.final.tapes=(entry gs (j+1) p tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices))) indices).tapes ∧
      r.steps≤budget gs j p indices := by
  obtain ⟨a,ha,ah,atapes,asteps⟩ := P1CompactRowCommonBounds.reusable_run gs j hj p tail out indices hp
  have hhead : a.final.heads 15=1 := by rw [ah]; rfl
  have htape : a.final.tapes 15=UnaryTemplate.tape j := by
    rw [atapes,P1CompactRowCommonReusable.entry_tapes gs j p _ tail _ indices
      (by unfold P1CompactRowCommonBounds.capacity; omega) (P1CompactRowCommonBounds.inner_fits gs _ p)]
    rfl
  obtain ⟨b,hb,bh,bt,bs⟩ := increment_run j a.final.heads a.final.tapes hhead htape
  have whole := Composition.run_join P1CompactRowCommonClear.machine increment _ _ _ a b ha hb
  have htime : P1CompactRowCommonBounds.bound gs indices.length p+1+(2*j+9)=budget gs j p indices := by
    unfold budget; omega
  rw [htime] at whole
  refine ⟨Composition.joinedReceipt a b,whole,?_,?_,?_⟩
  · change b.final.heads=_
    rw [bh,ah]
    exact coordinate_heads gs j (j+1) p _ tail _ indices
  · change b.final.tapes=_
    rw [bt,atapes]
    exact coordinate_tapes gs j p tail _ indices
  · change a.steps+1+b.steps≤_
    rw [bs]
    unfold budget
    omega

end NearCubicWires.RepairOrdinary.P1CompactRowCommonCoordinateBody

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowCommonCoordinateBody_machine_unchanged : P1CompactRowCommonCoordinateBody.machine = RowCommonCoordinateBody.machine := rfl
end NearCubicWires.RepairOrdinary

/-! All weights and the target are emitted at the one common cut width.
The native arity driver executes the coordinate loop and restores itself. -/
namespace NearCubicWires.RepairOrdinary.P1CompactRowCommonCoordinateLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RepeatMachine.machine P1CompactRowCommonCoordinateBody.machine (fun _ _=>true)
def field {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length)) (p j : ℕ) :=
  if hj : j≤n then MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hj indices) else []
def word {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length)) (p : ℕ) : ℕ→ℕ→List Bool
  | _,0=>[]
  | j,k+1=>frame (field gs indices p j)++word gs indices p (j+1) k
def bodyBudget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p : ℕ) (indices : List (Fin gs.length)) :=
  P1CompactRowCommonBounds.bound gs indices.length p+2*n+10
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p : ℕ) (indices : List (Fin gs.length)) :=
  (n+1)*(bodyBudget gs p indices+3)+3
noncomputable def cfg {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p : ℕ) (indices : List (Fin gs.length))
    (phase : Fin 5) (j driver : ℕ) (tail out : List Bool) :=
  RepeatMachine.cfg phase (P1CompactRowCommonCoordinateBody.entry gs j p tail out indices) (n+1) driver

theorem remaining {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p : ℕ) (indices : List (Fin gs.length))
    (j count : ℕ) (hj : j+count=n+1) (tail out : List Bool)
    (hp : P1CompactRowCoordinateLoop.width gs indices≤p) :
    ∃ time,time≤count*(bodyBudget gs p indices+2)+(n+1)+3 ∧
      Timed machine time (cfg gs p indices 0 j (j+1) tail out)
        (cfg gs p indices 3 (n+1) 1 tail (out++word gs indices p j count)) := by
  induction count generalizing j out with
  | zero =>
    have he : j=n+1 := by omega
    subst j
    refine ⟨n+1+3,by omega,?_⟩
    simpa only [machine,cfg,word,List.append_nil] using
      RepeatMachine.exhaust P1CompactRowCommonCoordinateBody.machine (fun _ _=>true)
        (P1CompactRowCommonCoordinateBody.entry gs (n+1) p tail out indices) (n+1)
  | succ count ih =>
    have hjn : j≤n := by omega
    obtain ⟨r,hr,rh,rt,rs⟩ := P1CompactRowCommonCoordinateBody.body_run gs j hjn p tail out indices hp
    have hs : r.steps≤bodyBudget gs p indices := by
      unfold bodyBudget P1CompactRowCommonCoordinateBody.budget at *
      omega
    have ht := RepeatMachine.iteration P1CompactRowCommonCoordinateBody.machine (fun _ _=>true)
      (P1CompactRowCommonCoordinateBody.entry gs j p tail out indices) (n+1) j r (by rfl) (by omega) hr
    simp only [↓reduceIte] at ht
    have he := P1CompactRowOccurrenceLoop.cfg_eq 0 r.final
      (P1CompactRowCommonCoordinateBody.entry gs (j+1) p tail
        (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hjn indices))) indices)
      (n+1) (j+2) rh rt
    rw [he] at ht
    obtain ⟨time,hbound,htail⟩ := ih (j+1) (by omega)
      (out++frame (MatrixScoreBatch.signMagnitude p (P1CompactRowCommonCoefficient.value gs j hjn indices)))
    have hdriver : j+1+1=j+2 := by omega
    rw [hdriver] at htail
    have whole := ht.trans htail
    refine ⟨r.steps+2+time,?_,?_⟩
    · nlinarith
    · simpa only [machine,cfg,word,field,dif_pos hjn,List.append_assoc] using whole

theorem row_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p : ℕ) (indices : List (Fin gs.length))
    (tail out : List Bool) (hp : P1CompactRowCoordinateLoop.width gs indices≤p) :
    ∃ r,runFrom machine (budget gs p indices) (cfg gs p indices 0 0 1 tail out)=some r ∧
      r.final=cfg gs p indices 3 (n+1) 1 tail (out++word gs indices p 0 (n+1)) ∧
      r.steps≤budget gs p indices := by
  obtain ⟨time,hb,ht⟩ := remaining gs p indices 0 (n+1) (by omega) tail out hp
  have hbudget : time≤budget gs p indices := by unfold budget; nlinarith
  obtain ⟨r,hr,rf,rs⟩ := ht.run
    (by simp [machine,cfg,RepeatMachine.machine,RepeatMachine.cfg,controlConfig,RepeatMachine.phaseCode])
  have hmore := runFrom_moreFuel machine time (budget gs p indices-time) _ r hr
  rw [Nat.add_sub_of_le hbudget] at hmore
  exact ⟨r,hmore,rf,rs.le.trans hbudget⟩

theorem field_weight {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (indices : List (Fin gs.length)) (p : ℕ) (j : Fin n) :
    field gs indices p j.val=MatrixScoreBatch.signMagnitude p ((P1CompactRowCoordinateLoop.equation gs indices).weights j) := by
  simp only [field,dif_pos j.isLt.le,P1CompactRowCommonCoefficient.value,P1CompactRowCoordinateLoop.equation,
    P1CompactRowCachedEquation.stack_weight]

theorem field_target {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (indices : List (Fin gs.length)) (p : ℕ) :
    field gs indices p n=MatrixScoreBatch.signMagnitude p (P1CompactRowCoordinateLoop.equation gs indices).target := by
  simp only [field,dif_pos le_rfl,P1CompactRowCommonCoefficient.value,P1CompactRowCoordinateLoop.equation,
    P1CompactRowCachedEquation.stack_target]

theorem word_add {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length))
    (p j a b : ℕ) : word gs indices p j (a+b)=word gs indices p j a++word gs indices p (j+a) b := by
  induction a generalizing j with
  | zero => simp [word]
  | succ a ih =>
    rw [Nat.succ_add,word,word,ih,List.append_assoc]
    rw [show j+1+a=j+(a+1) by omega]

theorem word_ofFn {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (indices : List (Fin gs.length))
    (p j count : ℕ) : word gs indices p j count=
      (List.ofFn (fun i : Fin count=>frame (field gs indices p (j+i.val)))).flatten := by
  induction count generalizing j with
  | zero => simp [word]
  | succ count ih =>
    rw [word,List.ofFn_succ,List.flatten_cons,ih]
    simp only [Fin.val_zero,Nat.add_zero,Fin.val_succ]
    have h : (fun i : Fin count=>frame (field gs indices p (j+1+i.val)))=
        (fun i : Fin count=>frame (field gs indices p (j+(i.val+1)))) := by
      funext i
      rw [show j+1+i.val=j+(i.val+1) by omega]
    rw [h]

theorem word_equation {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs]
    (indices : List (Fin gs.length)) (p : ℕ) :
    word gs indices p 0 (n+1)=P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs indices) := by
  rw [word_add,word_ofFn]
  simp only [Nat.zero_add,word,List.append_nil,field_target]
  simp only [P1CompactRowCoordinateLoop.equationWord,EquationWidenLoop.stream,List.flatMap_append,List.flatMap_cons,
    List.flatMap_nil,List.append_nil,field_weight]
  congr 1
  rw [List.flatMap]
  simp only [List.map_ofFn,Function.comp_def]

theorem equation_run {n : ℕ} (gs : List (ExactThresholdGate n)) [_radix : P1Radix gs] (p : ℕ)
    (indices : List (Fin gs.length)) (tail out : List Bool) (hp : P1CompactRowCoordinateLoop.width gs indices≤p) :
    ∃ r,runFrom machine (budget gs p indices) (cfg gs p indices 0 0 1 tail out)=some r ∧
      r.final=cfg gs p indices 3 (n+1) 1 tail
        (out++P1CompactRowCoordinateLoop.equationWord p (P1CompactRowCoordinateLoop.equation gs indices)) ∧
      r.steps≤budget gs p indices := by
  simpa only [word_equation] using row_run gs p indices tail out hp

end NearCubicWires.RepairOrdinary.P1CompactRowCommonCoordinateLoop

namespace NearCubicWires.RepairOrdinary
theorem P1CompactRowCommonCoordinateLoop_machine_unchanged : P1CompactRowCommonCoordinateLoop.machine = RowCommonCoordinateLoop.machine := rfl
end NearCubicWires.RepairOrdinary

