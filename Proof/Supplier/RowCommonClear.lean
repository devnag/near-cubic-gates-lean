import Proof.Supplier.RowCommonReset

/-! Physically erase the common-width coefficient scratch, preserving the
native cache, occurrence stream, dimensions and live cut-output cursor. -/
namespace NearCubicWires.RepairOrdinary.RowCommonClear
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
noncomputable def first := TapeEmbedding.machine 2 RowCommonReset.machine
noncomputable def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 10)
noncomputable def machine := Composition.machine first last
def extra (F : ℕ) : Fin 2→List Bool := ![List.replicate F true,List.replicate (F+1) false]
def extend {s : ℕ} (F : ℕ) (c : Configuration 33 s) := TapeEmbedding.config (fun _=>0) (extra F) c
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Composition.restart (extend F (RowCommonReset.entry gs j p F tail out indices)) machine.start
noncomputable def resultHeads {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Fin.addCases (m:=33) (n:=2) (motive:=fun _=>ℕ)
    (RowCommonReset.outputHeads (RowCommonCoefficient.heads gs j hj tail out indices)) (fun _=>0)
noncomputable def resetTapes {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (p F : ℕ) (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Fin.addCases (m:=33) (n:=2) (motive:=fun _=>List Bool)
    (RowCommonReset.outputTapes F (RowCommonCoefficient.result gs j hj p F tail out indices)) (extra F)

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

theorem result_zero {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    ∀ i,resultHeads gs j hj tail out indices (eraseSlots i)=0 := by
  have h := RowCoefficientDock.dock_heads gs j hj [] tail indices
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  have h4 := h 4; have h5 := h 5; have h6 := h 6
  change (RowCoefficientDock.dock gs j hj [] tail indices).heads 10=0 at h0
  change (RowCoefficientDock.dock gs j hj [] tail indices).heads 11=0 at h1
  change (RowCoefficientDock.dock gs j hj [] tail indices).heads 19=0 at h2
  change (RowCoefficientDock.dock gs j hj [] tail indices).heads 16=0 at h3
  change (RowCoefficientDock.dock gs j hj [] tail indices).heads 25=0 at h4
  change (RowCoefficientDock.dock gs j hj [] tail indices).heads 26=0 at h5
  change (RowCoefficientDock.dock gs j hj [] tail indices).heads 27=0 at h6
  intro i
  simp only [resultHeads,RowCommonReset.outputHeads,RowCommonCoefficient.heads]
  fin_cases i <;> simp [eraseSlots,workSlots,Fin.addCases,RowCommonReset.selected,
    RowCommonCoefficient.extraHeads,h0,h1,h2,h3,h4,h5,h6]

theorem cleared_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : RowCoordinateLoop.width gs indices ≤ p)
    (hcall : RowCommonCoefficient.budget gs j hj p indices+1 ≤ F)
    (hF : 2*p+5 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) ≤ F) :
    ∃ r,runFrom machine (2*RowCommonCoefficient.budget gs j hj p indices+2*F+7)
      (entry gs j p F tail out indices)=some r ∧
      r.final.heads=resultHeads gs j hj tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices ∧
      r.final.tapes=cleared F (resetTapes gs j hj p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices) ∧
      r.steps ≤ 2*RowCommonCoefficient.budget gs j hj p indices+2*F+7 := by
  obtain ⟨base,hbase,bh,bt,bs,bwork,blog⟩ := RowCommonReset.reset_run gs j hj p F tail out indices hp hcall hF hD
  let a := TapeEmbedding.receipt (fun _ : Fin 2=>0) (extra F) base
  have ha := TapeEmbedding.run_embed RowCommonReset.machine (fun _ : Fin 2=>0) (extra F) _ _ base hbase
  have ah : a.final.heads=resultHeads gs j hj tail
      (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices := by
    change Fin.addCases (m:=33) (n:=2) (motive:=fun _=>ℕ) base.final.heads (fun _=>0)=_
    rw [bh]; rfl
  have atapes : a.final.tapes=resetTapes gs j hj p F tail
      (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices := by
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
  have ht : (2*RowCommonCoefficient.budget gs j hj p indices+2)+1+(2*F+4)=
      2*RowCommonCoefficient.budget gs j hj p indices+2*F+7 := by omega
  rw [ht] at whole
  refine ⟨Composition.joinedReceipt a b,whole,bh'.trans ah,?_,?_⟩
  · change b.final.tapes=_
    rw [bt',atapes]
  · change base.steps+1+b.steps ≤ _
    rw [bs']; omega

end NearCubicWires.RepairOrdinary.RowCommonClear
