import Proof.Supplier.RowCoefficientStream

/-! Restore the dedicated occurrence-stream cursor after a coefficient
append, with paid recording and retained scratch padding for the next call.
The global row-output cursor is deliberately preserved by this machine. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientStreamReset
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
noncomputable def machine := MaskedReset.machine RowCoefficientStream.machine selected
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (j F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  ZeroPadding.config (caps F) (Rewind.recording (RowCoefficientStream.entry gs j [] tail out indices) 0)
def outputHeads (h : Fin 29 → ℕ) :=
  Fin.addCases (m:=29) (n:=1) (motive:=fun _=>ℕ) (fun i=>if selected i then 0 else h i) (fun _=>0)
def outputTapes (F : ℕ) (a : Fin 29 → List Bool) :=
  Fin.addCases (m:=29) (n:=1) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (if work i then F else 0) (a i)) (fun _=>List.replicate F false)

theorem start_head {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (k : Fin 7) :
    (RowCoefficientStream.entry gs j [] tail out indices).heads (workSlots k)=0 := by
  fin_cases k <;> rfl

theorem start_support {n : ℕ} (gs : List (ExactThresholdGate n)) (j F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hF : 1 ≤ F) (hD : RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) ≤ F)
    (k : Fin 7) : ( (RowCoefficientStream.entry gs j [] tail out indices).tapes (workSlots k)).length ≤ F := by
  have hs := RowCoefficientDock.scratch gs j (RowOccurrenceLoop.word indices++tail) 0 [] [] indices.length 1 0
  have ho := RowOccurrenceLoop.cfg_outputs gs j (RowOccurrenceLoop.word indices++tail) 0 [] [] indices.length 1 0
  simp only [RowCoefficientStream.entry,Composition.restart,RowCoefficientStream.extend,TapeEmbedding.config,
    RowCoefficientWhole.entry,RowCoefficientDock.extend,RowCoefficientLoopReset.entry,Rewind.recording,Rewind.config,
    List.nil_append,List.length_nil]
  fin_cases k <;> simp [workSlots,Fin.addCases,ho.1,ho.2.1,hs.2.2.1,hs.2.2.2,hF,hD]

theorem reset_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hF : RowCoefficientStream.budget gs j hj indices+1 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) ≤ F) :
    ∃ r,runFrom machine (2*RowCoefficientStream.budget gs j hj indices+2)
      (entry gs j F tail out indices)=some r ∧
      r.final.heads=outputHeads (RowCoefficientStream.heads gs j hj [] tail
        (out++frame (RowCoefficientStream.field gs j hj indices)) indices) ∧
      r.final.tapes=outputTapes F (RowCoefficientStream.tapes gs j hj [] tail
        (out++frame (RowCoefficientStream.field gs j hj indices)) indices) ∧
      r.steps ≤ 2*RowCoefficientStream.budget gs j hj indices+2 ∧
      (∀ k : Fin 7,(r.final.tapes ((workSlots k).castAdd 1)).length ≤ F) ∧
      (r.final.tapes 29).length ≤ F := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := RowCoefficientStream.stream_run gs j hj [] tail out indices
  have hh : ∀ i,selected i=true → base.final.heads i ≤ base.steps := by
    intro i hi
    have he : i=23 := by simpa only [selected,decide_eq_true_eq] using hi
    subst i
    have h := SelectiveReset.prefix_head (prefix_of_run _ _ _ _ hbase).1 23
    have h0 : (RowCoefficientStream.entry gs j [] tail out indices).heads 23=0 := rfl
    simpa only [h0,zero_add] using h
  obtain ⟨reset,hr,rf,rs,_⟩ := MaskedReset.reset_run RowCoefficientStream.machine selected _ _ base hbase hh
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
    ((2*RowCoefficientStream.budget gs j hj indices+2)-(2*base.steps+2)) _ r hrun
  have hbudget : 2*base.steps+2 ≤ 2*RowCoefficientStream.budget gs j hj indices+2 := by omega
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
    have h := PCPSerializerReuse.tape_support RowCoefficientStream.machine _ _ base hbase (workSlots k) F 0
      (start_head gs j tail out indices k).le
      ((start_support gs j F tail out indices (by omega) hD k).trans (Nat.le_max_left _ _))
    simp only [zero_add] at h
    exact h.trans (max_le le_rfl (by omega))
  · rw [ht]; simp [outputTapes,Fin.addCases]

end NearCubicWires.RepairOrdinary.RowCoefficientStreamReset
