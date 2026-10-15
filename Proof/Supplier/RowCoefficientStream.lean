import Proof.Supplier.RowCoefficientAppendCall

/-! Whole retained-cache coefficient computation followed by its physical
append to the live row stream. The field and its emitter log are reused by
the cursor-restoring copier; the row-output head remains advanced. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientStream
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def first := TapeEmbedding.machine 1 RowCoefficientWhole.machine
noncomputable def last := RowCoefficientAppendCall.machine
noncomputable def machine := Composition.machine first last
def extend {s : ℕ} (out : List Bool) (c : Configuration 28 s) :=
  TapeEmbedding.config (fun _ : Fin 1=>out.length) (fun _=>out) c
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ)
    (pre tail out : List Bool) (indices : List (Fin gs.length)) :=
  Composition.restart (extend out (RowCoefficientWhole.entry gs j pre tail indices)) machine.start
def field {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) := MatrixScoreBatch.signMagnitude
      (RowCachedCoordinateBounds.width gs*indices.length)
      (RowPowerNativeReusable.horner ((2 : ℤ)^RowCachedCoordinateBounds.width gs)
        (RowOccurrenceLoop.values gs j hj indices))
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) := RowCoefficientWhole.budget gs j hj indices+4*(field gs j hj indices).length+5
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (pre tail out : List Bool) (indices : List (Fin gs.length)) :=
  Fin.addCases (m:=28) (n:=1) (motive:=fun _=>ℕ)
    (RowCoefficientDock.dock gs j hj pre tail indices).heads (fun _=>out.length)
noncomputable def tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (pre tail out : List Bool) (indices : List (Fin gs.length)) :=
  Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool)
    (RowCoefficientWhole.result gs j hj pre tail indices) (fun _=>out)

theorem field_length {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :
    (field gs j hj indices).length=RowCachedCoordinateBounds.width gs*indices.length+1 := by
  simp [field,MatrixScoreBatch.signMagnitude,SignedSortKey.binary_length]

theorem whole_log {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (pre tail : List Bool) (indices : List (Fin gs.length)) :
    RowCoefficientWhole.result gs j hj pre tail indices 27=
      List.replicate (2*(RowCachedCoordinateBounds.width gs*indices.length)+4) false := by
  have h := install_slot RowCoefficientDock.slots RowCoefficientDock.slots_injective
    (RowCoefficientDock.dock gs j hj pre tail indices).tapes
    (RowCoefficientDock.padded (RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs))
      (RowCoefficientField.output (RowCachedCoordinateBounds.width gs*indices.length)
        (RadixSemantics.value (RowCoefficientDock.bits gs j hj false indices))
        (RadixSemantics.value (RowCoefficientDock.bits gs j hj true indices))
        (RowOccurrenceLoop.budget gs j hj indices) 0)) 6
  change RowCoefficientWhole.result gs j hj pre tail indices 27=_ at h
  simpa only [RowCoefficientDock.padded,RowCoefficientDock.caps,
    show ¬((6 : Fin 7)=2 ∨ (6 : Fin 7)=3) by decide,if_false,ZeroPadding.pad_zero,
    RowCoefficientAppendCall.field_log] using h

theorem stream_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (pre tail out : List Bool) (indices : List (Fin gs.length)) :
    ∃ r,runFrom machine (budget gs j hj indices) (entry gs j pre tail out indices)=some r ∧
      r.final.heads=heads gs j hj pre tail (out++frame (field gs j hj indices)) indices ∧
      r.final.tapes=tapes gs j hj pre tail (out++frame (field gs j hj indices)) indices ∧
      r.steps ≤ budget gs j hj indices := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := RowCoefficientWhole.whole_run gs j hj pre tail indices
  let a := TapeEmbedding.receipt (fun _ : Fin 1=>out.length) (fun _=>out) base
  have ha := TapeEmbedding.run_embed RowCoefficientWhole.machine (fun _ : Fin 1=>out.length)
    (fun _=>out) _ _ base hbase
  have ah : a.final.heads=heads gs j hj pre tail out indices := by
    change Fin.addCases (m:=28) (n:=1) (motive:=fun _=>ℕ) base.final.heads (fun _=>out.length)=_
    rw [bh]; rfl
  have atapes : a.final.tapes=tapes gs j hj pre tail out indices := by
    change Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool) base.final.tapes (fun _=>out)=_
    rw [bt]; rfl
  have h26 : a.final.heads 26=0 := by
    rw [ah]
    exact RowCoefficientDock.dock_heads gs j hj pre tail indices 5
  have h27 : a.final.heads 27=0 := by
    rw [ah]
    exact RowCoefficientDock.dock_heads gs j hj pre tail indices 6
  have t26 : a.final.tapes 26=frame (field gs j hj indices) := by
    rw [atapes]
    exact RowCoefficientWhole.result_field gs j hj pre tail indices
  have t27 : a.final.tapes 27=List.replicate
      (2*(RowCachedCoordinateBounds.width gs*indices.length)+4) false := by
    rw [atapes]
    exact whole_log gs j hj pre tail indices
  obtain ⟨b,hb,bh',bt',bs'⟩ := RowCoefficientAppendCall.append_run (field gs j hj indices) out
    (2*(RowCachedCoordinateBounds.width gs*indices.length)+4) a.final.heads a.final.tapes
    (by rw [field_length]; omega) h26 (by rw [ah]; rfl) h27 t26 (by rw [atapes]; rfl) t27
  have whole := Composition.run_join first last _ _ _ a b ha hb
  have htime : RowCoefficientWhole.budget gs j hj indices+1+(4*(field gs j hj indices).length+4)=
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

theorem budget_bound {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :
    budget gs j hj indices ≤ 8192*indices.length*
      RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs)+39 := by
  have hb := RowOccurrenceLoop.budget_bound gs j hj indices
  have hw : RowCachedCoordinateBounds.width gs+1 ≤
      RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs) := by
    unfold RowCachedCoordinateBounds.size
    omega
  have hm := Nat.mul_le_mul_left indices.length hw
  unfold budget RowCoefficientWhole.budget
  rw [field_length]
  nlinarith

end NearCubicWires.RepairOrdinary.RowCoefficientStream
