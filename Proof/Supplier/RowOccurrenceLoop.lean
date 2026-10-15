import Proof.Supplier.RowOccurrenceReusable

/-! The fixed ordinary loop consumes an ordered list of actual cached-child
occurrences and assembles one signed coefficient. Indices are never deduplicated.
The physical counter and every call/return/rewind are included in the run. -/
namespace NearCubicWires.RepairOrdinary.RowOccurrenceLoop
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine := RepeatMachine.machine RowOccurrenceReusable.machine (fun _ _=>true)
def word {N : ℕ} (indices : List (Fin N)) := indices.flatMap (fun i=>RowIndexField.word i.val)
def value {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n) (i : Fin gs.length) :=
  RowCachedCoordinateAppend.value gs i.val i.isLt j hj
def emitted {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n)
    (negative : Bool) (indices : List (Fin gs.length)) :=
  indices.flatMap (fun i=>marks (RowPowerNativeReusable.block
    (RowCachedCoordinateBounds.width gs) (value gs j hj i) negative))
def callBudget {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n) (i : Fin gs.length) :=
  RowOccurrenceReusable.budget gs i.val i.isLt j hj (RowCachedCoordinateBounds.width gs)
    (RowCachedCoordinateBounds.inner (RowCachedCoordinateBounds.width gs))
    (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs))
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n)
    (indices : List (Fin gs.length)) := (indices.map (callBudget gs j hj)).sum+3*indices.length+3
noncomputable def data {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ)
    (source : List Bool) (pos : ℕ) (positive negative : List Bool) :=
  RowOccurrenceReusable.entry gs j (RowCachedCoordinateBounds.width gs)
    (RowCachedCoordinateBounds.inner (RowCachedCoordinateBounds.width gs))
    (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)) source pos positive negative
noncomputable def cfg {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (phase : Fin 5)
    (source : List Bool) (pos : ℕ) (positive negative : List Bool) (total driver : ℕ) :=
  RepeatMachine.cfg phase (data gs j source pos positive negative) total driver

theorem index_fits {n : ℕ} (gs : List (ExactThresholdGate n)) (i : Fin gs.length) :
    i.val+2≤RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) := by
  have hi := i.isLt
  unfold RowCachedCoordinateBounds.outer RowCachedCoordinateBounds.size
  nlinarith

theorem call_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n)
    (i : Fin gs.length) (pre tail positive negative : List Bool) :
    let source := pre++RowIndexField.word i.val++tail
    let P := positive++emitted gs j hj false [i]
    let N := negative++emitted gs j hj true [i]
    ∃ r,runFrom RowOccurrenceReusable.machine (callBudget gs j hj i)
      (data gs j source pre.length positive negative)=some r ∧
      r.final.heads=(data gs j source (pre.length+i.val+1) P N).heads ∧
      r.final.tapes=(data gs j source (pre.length+i.val+1) P N).tapes ∧ r.steps=callBudget gs j hj i := by
  have hw := RowCachedCoordinateBounds.value_width gs i.val i.isLt j hj
  simpa only [emitted,List.flatMap_cons,List.flatMap_nil,List.append_nil,value,data,callBudget] using
    RowOccurrenceReusable.reusable_run gs i.val i.isLt j hj (RowCachedCoordinateBounds.width gs)
      (RowCachedCoordinateBounds.inner (RowCachedCoordinateBounds.width gs))
      (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs)) pre tail positive negative
      (RowCachedCoordinateBounds.inner_fits _ _ hw)
      (RowCachedCoordinateBounds.outer_fits gs i.val i.isLt j hj _ hw) (index_fits gs i)

theorem cfg_eq {t s : ℕ} (phase : Fin 5) (a b : Configuration t s) (total driver : ℕ)
    (hh : a.heads=b.heads) (ht : a.tapes=b.tapes) :
    RepeatMachine.cfg phase a total driver=RepeatMachine.cfg phase b total driver := by
  simp only [RepeatMachine.cfg,controlConfig,TapeEmbedding.config,hh,ht]

theorem remaining {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n)
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

theorem list_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n)
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

end NearCubicWires.RepairOrdinary.RowOccurrenceLoop
