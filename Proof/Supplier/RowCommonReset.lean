import Proof.Supplier.RowCommonCoefficient

/-! Restore the dedicated occurrence cursor after the common-width append.
All scratch lengths are bounded using the executed prefix, and the physical
reset log is retained at the same paid allocation for subsequent erasure. -/
namespace NearCubicWires.RepairOrdinary.RowCommonReset
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlots : Fin 9→Fin 32 := ![10,11,16,19,25,26,27,28,30]
def selected (i : Fin 32) := decide (i=23)
def caps (F : ℕ) (i : Fin 33) := if i=32 then F else 0
noncomputable def machine := MaskedReset.machine RowCommonCoefficient.machine selected
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  ZeroPadding.config (caps F) (Rewind.recording (RowCommonCoefficient.entry gs j p F tail out indices) 0)
def outputHeads (h : Fin 32→ℕ) :=
  Fin.addCases (m:=32) (n:=1) (motive:=fun _=>ℕ) (fun i=>if selected i then 0 else h i) (fun _=>0)
def outputTapes (F : ℕ) (a : Fin 32→List Bool) :=
  Fin.addCases (m:=32) (n:=1) (motive:=fun _=>List Bool) a (fun _=>List.replicate F false)

theorem start_head {n : ℕ} (gs : List (ExactThresholdGate n)) (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (k : Fin 9) :
    (RowCommonCoefficient.entry gs j p F tail out indices).heads (workSlots k)=0 := by
  fin_cases k <;> rfl

theorem start_support {n : ℕ} (gs : List (ExactThresholdGate n)) (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hF : 1 ≤ F) (hD : RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) ≤ F)
    (k : Fin 9) : ((RowCommonCoefficient.entry gs j p F tail out indices).tapes (workSlots k)).length ≤ F := by
  have h := RowCoefficientStreamReset.start_support gs j F tail [] indices hF hD
  dsimp only [RowCommonCoefficient.entry,RowCommonCoefficient.extend,Composition.restart,
    TapeEmbedding.config,ZeroPadding.config]
  dsimp only [RowCoefficientStream.entry,RowCoefficientStream.extend,Composition.restart,
    TapeEmbedding.config] at h
  fin_cases k
  · change (ZeroPadding.pad F ((RowCoefficientWhole.entry gs j [] tail indices).tapes 10)).length ≤ F
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (h 0)
  · change (ZeroPadding.pad F ((RowCoefficientWhole.entry gs j [] tail indices).tapes 11)).length ≤ F
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (h 1)
  · change (ZeroPadding.pad F ((RowCoefficientWhole.entry gs j [] tail indices).tapes 16)).length ≤ F
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (h 2)
  · change (ZeroPadding.pad F ((RowCoefficientWhole.entry gs j [] tail indices).tapes 19)).length ≤ F
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (h 3)
  · change (ZeroPadding.pad F ((RowCoefficientWhole.entry gs j [] tail indices).tapes 25)).length ≤ F
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (h 4)
  · change (ZeroPadding.pad F ((RowCoefficientWhole.entry gs j [] tail indices).tapes 26)).length ≤ F
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (h 5)
  · change (ZeroPadding.pad F ((RowCoefficientWhole.entry gs j [] tail indices).tapes 27)).length ≤ F
    rw [ZeroPadding.pad_length]
    exact max_le le_rfl (h 6)
  · simp [RowCommonCoefficient.extra,workSlots,Fin.addCases]
  · simp [RowCommonCoefficient.extra,workSlots,Fin.addCases]

theorem reset_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : RowCoordinateLoop.width gs indices ≤ p)
    (hcall : RowCommonCoefficient.budget gs j hj p indices+1 ≤ F)
    (hF : 2*p+5 ≤ F)
    (hD : RowCachedCoordinateBounds.outer gs (RowCachedCoordinateBounds.width gs) ≤ F) :
    ∃ r,runFrom machine (2*RowCommonCoefficient.budget gs j hj p indices+2)
      (entry gs j p F tail out indices)=some r ∧
      r.final.heads=outputHeads (RowCommonCoefficient.heads gs j hj tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices) ∧
      r.final.tapes=outputTapes F (RowCommonCoefficient.result gs j hj p F tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices) ∧
      r.steps ≤ 2*RowCommonCoefficient.budget gs j hj p indices+2 ∧
      (∀ k : Fin 9,(r.final.tapes ((workSlots k).castAdd 1)).length ≤ F) ∧
      (r.final.tapes 32).length ≤ F := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := RowCommonCoefficient.whole_run gs j hj p F tail out indices hp hF
  have hh : ∀ i,selected i=true → base.final.heads i ≤ base.steps := by
    intro i hi
    have he : i=23 := by simpa only [selected,decide_eq_true_eq] using hi
    subst i
    have h := SelectiveReset.prefix_head (prefix_of_run _ _ _ _ hbase).1 23
    have h0 : (RowCommonCoefficient.entry gs j p F tail out indices).heads 23=0 := rfl
    simpa only [h0,zero_add] using h
  obtain ⟨reset,hr,rf,rs,_⟩ := MaskedReset.reset_run RowCommonCoefficient.machine selected _ _ base hbase hh
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
  have hb : 2*base.steps+2 ≤ 2*RowCommonCoefficient.budget gs j hj p indices+2 := by omega
  have more := runFrom_moreFuel machine (2*base.steps+2)
    ((2*RowCommonCoefficient.budget gs j hj p indices+2)-(2*base.steps+2)) _ r hrun
  rw [Nat.add_sub_of_le hb] at more
  refine ⟨r,more,?_,ht.trans (congrArg (outputTapes F) bt),?_,?_,?_⟩
  · rw [rfinal,rf]
    change outputHeads base.final.heads=_
    rw [bh]
  · rw [rsteps,rs]; omega
  · intro k
    rw [ht]
    simp only [outputTapes,Fin.addCases_left]
    have h := PCPSerializerReuse.tape_support RowCommonCoefficient.machine _ _ base hbase (workSlots k) F 0
      (start_head gs j p F tail out indices k).le
      ((start_support gs j p F tail out indices (by omega) hD k).trans (Nat.le_max_left _ _))
    simp only [zero_add] at h
    exact h.trans (max_le le_rfl (by omega))
  · rw [ht]; simp [outputTapes,Fin.addCases]

end NearCubicWires.RepairOrdinary.RowCommonReset
