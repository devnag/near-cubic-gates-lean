import Proof.Supplier.RowFieldPaddingAppend

/-! The native occurrence coefficient is normalized once, widened directly
to the common cut width, and physically appended. No canonical-radix
coefficient equality or implicit change of the emitted width is used. -/
namespace NearCubicWires.RepairOrdinary.RowCommonCoefficient
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (F : ℕ) (i : Fin 28) := if RowCoefficientStreamReset.work (i.castAdd 1) then F else 0
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
noncomputable def first := TapeEmbedding.machine 4 RowCoefficientWhole.machine
noncomputable def last := RecoveryFocus.machine fieldSlots RowFieldPaddingAppend.machine
noncomputable def machine := Composition.machine first last
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (j p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Composition.restart (extend p F out (RowCoefficientWhole.entry gs j [] tail indices)) machine.start
noncomputable def heads {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Fin.addCases (m:=28) (n:=4) (motive:=fun _=>ℕ)
    (RowCoefficientDock.dock gs j hj [] tail indices).heads (extraHeads out)
noncomputable def middle {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Fin.addCases (m:=28) (n:=4) (motive:=fun _=>List Bool)
    (fun i=>ZeroPadding.pad (caps F i) (RowCoefficientWhole.result gs j hj [] tail indices i)) (extra p F out)
def value {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) :=
  RowPowerNativeReusable.horner ((2 : ℤ)^RowCachedCoordinateBounds.width gs)
    (RowOccurrenceLoop.values gs j hj indices)
noncomputable def result {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  install fieldSlots (middle gs j hj p F tail out indices)
    (RowFieldPaddingAppend.output (RowCoordinateLoop.width gs indices) p F (value gs j hj indices) out)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (p : ℕ)
    (indices : List (Fin gs.length)) := RowCoefficientWhole.budget gs j hj indices+8*p+22

theorem value_fits {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (indices : List (Fin gs.length)) : (value gs j hj indices).natAbs<2^(RowCoordinateLoop.width gs indices) := by
  by_cases h : j<n
  · have he := RowCachedEquation.stack_weight gs ⟨j,h⟩ indices
    have hm := RowCoordinateLoop.equation_magnitude gs indices
    have hw : ((RowCoordinateLoop.equation gs indices).weights ⟨j,h⟩).natAbs ≤
        SupplierPrime.equationMagnitudeBound (RowCoordinateLoop.equation gs indices) := by
      unfold SupplierPrime.equationMagnitudeBound
      exact (Finset.single_le_sum (f:=fun i : Fin n=>(RowCoordinateLoop.equation gs indices).weights i |>.natAbs)
        (fun i _=>Nat.zero_le _) (Finset.mem_univ (⟨j,h⟩ : Fin n))).trans (Nat.le_add_right _ _)
    change (RowPowerNativeReusable.horner _ _).natAbs<_
    rw [he]
    exact hw.trans_lt hm
  · have he : j=n := by omega
    subst j
    have hm := RowCoordinateLoop.equation_magnitude gs indices
    have ht : (RowCoordinateLoop.equation gs indices).target.natAbs ≤
        SupplierPrime.equationMagnitudeBound (RowCoordinateLoop.equation gs indices) := by
      unfold SupplierPrime.equationMagnitudeBound
      omega
    simpa only [value,RowCachedEquation.stack_target,RowCoordinateLoop.equation] using ht.trans_lt hm

theorem field_input {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) (i : Fin 5) :
    middle gs j hj p F tail out indices (fieldSlots i)=
      RowFieldPaddingAppend.input (RowCoordinateLoop.width gs indices) p F (value gs j hj indices) out i := by
  fin_cases i
  · change ZeroPadding.pad F (RowCoefficientWhole.result gs j hj [] tail indices 26)=_
    rw [RowCoefficientWhole.result_field]
    rfl
  · rfl
  · rfl
  · rfl
  · rfl

theorem field_heads {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n)
    (tail out : List Bool) (indices : List (Fin gs.length)) (i : Fin 5) :
    heads gs j hj tail out indices (fieldSlots i)=RowFieldPaddingAppend.heads out i := by
  fin_cases i
  · exact RowCoefficientDock.dock_heads gs j hj [] tail indices 5
  · rfl
  · rfl
  · rfl
  · rfl

theorem whole_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j ≤ n) (p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : RowCoordinateLoop.width gs indices ≤ p) (hF : 2*p+5 ≤ F) :
    ∃ r,runFrom machine (budget gs j hj p indices) (entry gs j p F tail out indices)=some r ∧
      r.final.heads=heads gs j hj tail (out++frame (MatrixScoreBatch.signMagnitude p (value gs j hj indices))) indices ∧
      r.final.tapes=result gs j hj p F tail (out++frame (MatrixScoreBatch.signMagnitude p (value gs j hj indices))) indices ∧
      r.steps ≤ budget gs j hj p indices := by
  obtain ⟨base,hbase,bh,bt,bs⟩ := RowCoefficientWhole.whole_run gs j hj [] tail indices
  obtain ⟨pad,hpad,pf,ps,_⟩ := ZeroPadding.run_config RowCoefficientWhole.machine (caps F) _ _ base hbase
  let a := TapeEmbedding.receipt (extraHeads out) (extra p F out) pad
  have ha := TapeEmbedding.run_embed RowCoefficientWhole.machine (extraHeads out) (extra p F out) _ _ pad hpad
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
  obtain ⟨b0,hb0,bh0,bt0,bs0⟩ := RowFieldPaddingAppend.field_run (RowCoordinateLoop.width gs indices) p F
    (value gs j hj indices) out hp (value_fits gs j hj indices) hF
  obtain ⟨b,hb,bf,bstep⟩ := RecoveryFocus.run_config fieldSlots field_injective RowFieldPaddingAppend.machine
    a.final.heads a.final.tapes _ _ b0 hb0
  have hi : RecoveryFocus.config fieldSlots a.final.heads a.final.tapes
      ⟨RowFieldPaddingAppend.machine.start,RowFieldPaddingAppend.heads out,
        RowFieldPaddingAppend.input (RowCoordinateLoop.width gs indices) p F (value gs j hj indices) out⟩=
      Composition.restart a.final last.start := by
    apply WilliamsSourceCrop.focus_same fieldSlots (Composition.restart a.final last.start)
    · intro i; change a.final.heads (fieldSlots i)=_; rw [ah]; exact field_heads gs j hj tail out indices i
    · intro i; change a.final.tapes (fieldSlots i)=_; rw [atapes]; exact field_input gs j hj p F tail out indices i
  rw [hi] at hb
  have h := Composition.run_join first last _ _ _ a b ha hb
  have htime : RowCoefficientWhole.budget gs j hj indices+1+(8*p+21)=budget gs j hj p indices := by unfold budget; omega
  rw [htime] at h
  refine ⟨Composition.joinedReceipt a b,h,?_,?_,?_⟩
  · change b.final.heads=_
    rw [bf]
    simp only [RecoveryFocus.config,bh0,ah,field_pick]
    funext i
    have h26 := RowCoefficientDock.dock_heads gs j hj [] tail indices 5
    change (RowCoefficientDock.dock gs j hj [] tail indices).heads 26=0 at h26
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

end NearCubicWires.RepairOrdinary.RowCommonCoefficient
