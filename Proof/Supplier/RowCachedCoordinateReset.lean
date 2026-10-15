import Proof.Supplier.RowCachedCoordinateAppend

/-! Paid reset of the original cache cursor and the two positioner scratch
heads after a selected coordinate append. Existing width/selection drivers
and both live P/N append cursors are retained exactly. -/
namespace NearCubicWires.RepairOrdinary.RowCachedCoordinateReset
open LocalBitMultitape RepairRepresentation RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 20) := decide (i=0 ∨ i=16 ∨ i=17)
noncomputable def machine := MaskedReset.machine RowCachedCoordinateAppend.machine selected
def caps (D : ℕ) (i : Fin 21) : ℕ := if i=16 ∨ i=17 ∨ i=20 then D else 0
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (i j w C D : ℕ)
    (positive negative : List Bool) :=
  ZeroPadding.config (caps D) (Rewind.recording
    (RowCachedCoordinateAppend.entry gs i j w C positive negative) 0)
def outputHeads (h : Fin 20 → ℕ) : Fin 21 → ℕ :=
  Fin.addCases (m:=20) (n:=1) (motive:=fun _=>ℕ)
    (fun i => if selected i then 0 else h i) (fun _=>0)
def outputTapes (D : ℕ) (a : Fin 20 → List Bool) : Fin 21 → List Bool :=
  Fin.addCases (m:=20) (n:=1) (motive:=fun _=>List Bool)
    (fun i => ZeroPadding.pad (if i=16 ∨ i=17 then D else 0) (a i))
    (fun _=>List.replicate D false)

theorem initial_head {n : ℕ} (gs : List (ExactThresholdGate n)) (i j w C : ℕ)
    (positive negative : List Bool) (a : Fin 20) (ha : selected a=true) :
    (RowCachedCoordinateAppend.entry gs i j w C positive negative).heads a=0 := by
  simp only [selected,decide_eq_true_eq] at ha
  rcases ha with rfl|rfl|rfl <;> rfl
theorem initial_scratch {n : ℕ} (gs : List (ExactThresholdGate n)) (i j w C : ℕ)
    (positive negative : List Bool) (a : Fin 20) (ha : a=16 ∨ a=17) :
    (RowCachedCoordinateAppend.entry gs i j w C positive negative).tapes a=[] := by
  rcases ha with rfl|rfl <;> rfl

theorem reset_run {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) (positive negative : List Bool) (w C D : ℕ)
    (hC : RowPowerNativeReset.rawTime (RowCachedCoordinateAppend.value gs i hi j hj) w+1≤C)
    (hD : RowCachedCoordinateAppend.budget gs i hi j hj w C+1≤D) :
    let P := positive++marks (RowPowerNativeReusable.block w (RowCachedCoordinateAppend.value gs i hi j hj) false)
    let N := negative++marks (RowPowerNativeReusable.block w (RowCachedCoordinateAppend.value gs i hi j hj) true)
    let result := RowCachedCoordinateAppend.ready gs i j (RowCachedCoordinateAppend.endPos gs i hi j hj)
      w C P N (RowCachedCoordinateAppend.afterBacking gs i hi j) (RowCachedChildFields.prior gs i)
    ∃ r,runFrom machine (2*RowCachedCoordinateAppend.budget gs i hi j hj w C+2)
      (entry gs i j w C D positive negative)=some r ∧
      r.final.heads=outputHeads result.heads ∧ r.final.tapes=outputTapes D result.tapes ∧
      r.steps=2*RowCachedCoordinateAppend.budget gs i hi j hj w C+2 ∧
      (∀ a : Fin 21,a=16 ∨ a=17 ∨ a=20 → (r.final.tapes a).length≤D) := by
  dsimp only
  obtain ⟨raw,hr,rh,rt,rs⟩ := RowCachedCoordinateAppend.append_run gs i hi j hj positive negative w C hC
  have hheads : ∀ a,selected a=true → raw.final.heads a≤raw.steps := by
    intro a ha
    have hp := SelectiveReset.prefix_head (prefix_of_run _ _ _ _ hr).1 a
    simpa only [initial_head gs i j w C positive negative a ha,Nat.zero_add] using hp
  obtain ⟨reset,hreset,rf,rsteps,_⟩ := MaskedReset.reset_run
    RowCachedCoordinateAppend.machine selected _ _ raw hr hheads
  obtain ⟨result,hresult,resultFinal,resultSteps,_⟩ := ZeroPadding.run_config machine
    (caps D) _ _ reset hreset
  rw [rs] at hresult
  have hd : raw.steps≤D := by rw [rs]; omega
  have htapes : result.final.tapes=outputTapes D raw.final.tapes := by
    rw [resultFinal,rf]
    funext a
    refine Fin.addCases (m:=20) (n:=1) (fun b=>?_) (fun b=>?_) a
    · simp only [ZeroPadding.config,SelectiveReset.finished,Rewind.config,
        Fin.addCases_left,outputTapes]
      congr 2
      have hn : b.castAdd 1≠(20 : Fin 21) := by intro he; have hv:=congrArg Fin.val he; simp at hv; omega
      have h16 : b.castAdd 1=(16 : Fin 21) ↔ b=16 := by simp only [Fin.ext_iff,Fin.val_castAdd]; rfl
      have h17 : b.castAdd 1=(17 : Fin 21) ↔ b=17 := by simp only [Fin.ext_iff,Fin.val_castAdd]; rfl
      simp only [caps,hn,h16,h17,or_false]
    · fin_cases b
      change ZeroPadding.pad D (List.replicate raw.steps false)=List.replicate D false
      simp only [ZeroPadding.pad,List.length_replicate,←List.replicate_add,Nat.add_sub_of_le hd]
  refine ⟨result,hresult,?_,htapes.trans (congrArg (outputTapes D) rt),?_,?_⟩
  · rw [resultFinal,rf]
    change outputHeads raw.final.heads=_
    rw [rh]
  · rw [resultSteps,rsteps,rs]
  · intro a ha
    rw [htapes]
    rcases ha with rfl|rfl|rfl
    · change (ZeroPadding.pad D (raw.final.tapes 16)).length≤D
      rw [ZeroPadding.pad_length]
      apply max_le le_rfl
      have h := PCPSerializerReuse.tape_support RowCachedCoordinateAppend.machine _ _ raw hr 16 0 0
        (initial_head gs i j w C positive negative 16 (by decide)).le
        (by rw [initial_scratch gs i j w C positive negative 16 (by simp)]; simp)
      simp only [Nat.zero_add,max_eq_right (Nat.zero_le _),rs] at h
      omega
    · change (ZeroPadding.pad D (raw.final.tapes 17)).length≤D
      rw [ZeroPadding.pad_length]
      apply max_le le_rfl
      have h := PCPSerializerReuse.tape_support RowCachedCoordinateAppend.machine _ _ raw hr 17 0 0
        (initial_head gs i j w C positive negative 17 (by decide)).le
        (by rw [initial_scratch gs i j w C positive negative 17 (by simp)]; simp)
      simp only [Nat.zero_add,max_eq_right (Nat.zero_le _),rs] at h
      omega
    · simp [outputTapes,Fin.addCases]

end NearCubicWires.RepairOrdinary.RowCachedCoordinateReset
