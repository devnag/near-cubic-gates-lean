import Proof.Supplier.RowCachedCoordinateReset
import Proof.Amplification.RecoveryRowLookupTapes

/-! Complete reusable selected-child coordinate call. Both scratch banks are
physically cleared, the original cache returns to head0, and each P/N cursor
stays at the newly appended delimiter. The two capacity tapes are real inputs. -/
namespace NearCubicWires.RepairOrdinary.RowCachedCoordinateReusable
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlots : Fin 3 → Fin 23 := ![16,17,20]
def eraseSlots : Fin 5 → Fin 23 := ![16,17,20,21,22]
theorem erase_injective : Function.Injective eraseSlots := by decide
def extra (D : ℕ) : Fin 2 → List Bool := ![List.replicate D true,List.replicate (D+1) false]
def erasedInput (D : ℕ) (b : Fin 3 → List Bool) : Fin 5 → List Bool :=
  Fin.addCases (m:=4) (n:=1) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=3) (n:=1) (motive:=fun _=>List Bool) b (fun _=>List.replicate D true))
    (fun _=>List.replicate (D+1) false)
noncomputable def cleared (D : ℕ) (a : Fin 23 → List Bool) :=
  install eraseSlots a (erasedInput D (fun _=>List.replicate D false))
noncomputable def first := TapeEmbedding.machine 2 RowCachedCoordinateReset.machine
noncomputable def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 3)
noncomputable def machine := Composition.machine first last
noncomputable def extended {n : ℕ} (gs : List (ExactThresholdGate n)) (i j w C D : ℕ)
    (positive negative : List Bool) :=
  TapeEmbedding.config (fun _ : Fin 2=>0) (extra D)
    (RowCachedCoordinateReset.entry gs i j w C D positive negative)
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (i j w C D : ℕ)
    (positive negative : List Bool) := Composition.leftConfig 4 (extended gs i j w C D positive negative)
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) (w C D : ℕ) := 2*RowCachedCoordinateAppend.budget gs i hi j hj w C+2*D+7

theorem clear_run (D : ℕ) (heads : Fin 23 → ℕ) (a : Fin 23 → List Bool)
    (hh : ∀ k,heads (eraseSlots k)=0) (hb : ∀ k,(a (workSlots k)).length≤D)
    (hd : a 21=List.replicate D true) (hl : a 22=List.replicate (D+1) false) :
    ∃ r,runFrom last (2*D+4) ⟨last.start,heads,a⟩=some r ∧
      r.final.heads=heads ∧ r.final.tapes=cleared D a ∧ r.steps=2*D+4 := by
  have h := RecoveryScratchErase.erase_ready D (D+1) (fun k=>a (workSlots k)) hb
  simp only [max_self] at h
  apply h.focus_at eraseSlots erase_injective heads a
  · intro k
    fin_cases k <;> first | rfl | exact hd | exact hl
  · exact hh

theorem restored_heads {n : ℕ} (gs : List (ExactThresholdGate n)) (i j pos w C D : ℕ)
    (positive negative backing out : List Bool) :
    RowCachedCoordinateReset.outputHeads
      (RowCachedCoordinateAppend.ready gs i j pos w C positive negative backing out).heads=
      (RowCachedCoordinateReset.entry gs i j w C D positive negative).heads := by
  funext a
  fin_cases a <;> simp [RowCachedCoordinateReset.outputHeads,RowCachedCoordinateReset.selected,
    RowCachedCoordinateReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,
    RowCachedCoordinateAppend.entry,RowCachedCoordinateAppend.ready,
    Composition.leftConfig,TapeEmbedding.config,RowNativeCoordinateAppend.ready,
    RowNativeCoordinateAppend.extraHeads,RowPowerNativeReusable.heads,Fin.addCases]

theorem cleared_pick (k : Fin 23) : RecoveryFocus.pick eraseSlots k=
    (![none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,none,
      some 0,some 1,none,none,some 2,some 3,some 4] : Fin 23 → Option (Fin 5)) k := by
  fin_cases k
  all_goals first
    | exact RecoveryFocus.pick_slot eraseSlots erase_injective 0
    | exact RecoveryFocus.pick_slot eraseSlots erase_injective 1
    | exact RecoveryFocus.pick_slot eraseSlots erase_injective 2
    | exact RecoveryFocus.pick_slot eraseSlots erase_injective 3
    | exact RecoveryFocus.pick_slot eraseSlots erase_injective 4
    | decide

theorem restored_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (i j pos w C D : ℕ)
    (positive negative backing out : List Bool) :
    cleared D (Fin.addCases (m:=21) (n:=2) (motive:=fun _=>List Bool)
      (RowCachedCoordinateReset.outputTapes D
        (RowCachedCoordinateAppend.ready gs i j pos w C positive negative backing out).tapes)
      (extra D))=(extended gs i j w C D positive negative).tapes := by
  funext a
  fin_cases a <;> simp [cleared,install,cleared_pick,erasedInput,extended,extra,
    RowCachedCoordinateReset.outputTapes,RowCachedCoordinateReset.entry,
    RowCachedCoordinateReset.caps,ZeroPadding.config,Rewind.recording,Rewind.config,
    RowCachedCoordinateAppend.entry,RowCachedCoordinateAppend.ready,
    Composition.leftConfig,TapeEmbedding.config,RowNativeCoordinateAppend.ready,
    RowNativeCoordinateAppend.extraTapes,RowPowerNativeReusable.tapes,Fin.addCases,ZeroPadding.pad]

theorem reusable_run {n : ℕ} (gs : List (ExactThresholdGate n)) (i : ℕ) (hi : i<gs.length)
    (j : ℕ) (hj : j≤n) (positive negative : List Bool) (w C D : ℕ)
    (hC : RowPowerNativeReset.rawTime (RowCachedCoordinateAppend.value gs i hi j hj) w+1≤C)
    (hD : RowCachedCoordinateAppend.budget gs i hi j hj w C+1≤D) :
    let P := positive++marks (RowPowerNativeReusable.block w (RowCachedCoordinateAppend.value gs i hi j hj) false)
    let N := negative++marks (RowPowerNativeReusable.block w (RowCachedCoordinateAppend.value gs i hi j hj) true)
    ∃ r,runFrom machine (budget gs i hi j hj w C D) (entry gs i j w C D positive negative)=some r ∧
      r.final.heads=(entry gs i j w C D P N).heads ∧
      r.final.tapes=(entry gs i j w C D P N).tapes ∧ r.steps=budget gs i hi j hj w C D := by
  dsimp only
  obtain ⟨reset,hr,rh,rt,rs,support⟩ := RowCachedCoordinateReset.reset_run gs i hi j hj positive negative w C D hC hD
  let firstRun := TapeEmbedding.receipt (fun _ : Fin 2=>0) (extra D) reset
  have hfirst := TapeEmbedding.run_embed RowCachedCoordinateReset.machine
    (fun _ : Fin 2=>0) (extra D) _ _ reset hr
  have hh : ∀ k,firstRun.final.heads (eraseSlots k)=0 := by
    intro k
    fin_cases k <;> simp [firstRun,TapeEmbedding.receipt,TapeEmbedding.config,eraseSlots,
      Fin.addCases,rh,RowCachedCoordinateReset.outputHeads,RowCachedCoordinateReset.selected]
  have hb : ∀ k,(firstRun.final.tapes (workSlots k)).length≤D := by
    intro k
    fin_cases k <;> apply support <;> decide
  obtain ⟨erase,he,eh,et,es⟩ := clear_run D firstRun.final.heads firstRun.final.tapes hh hb rfl rfl
  have whole := Composition.run_join first last _ _ _ firstRun erase hfirst he
  have time : (2*RowCachedCoordinateAppend.budget gs i hi j hj w C+2)+1+(2*D+4)=budget gs i hi j hj w C D := by
    unfold budget
    omega
  rw [time] at whole
  refine ⟨Composition.joinedReceipt firstRun erase,whole,?_,?_,?_⟩
  · change erase.final.heads=_
    rw [eh]
    dsimp only [firstRun,TapeEmbedding.receipt,TapeEmbedding.config]
    rw [rh,restored_heads gs i j _ w C D]
    rfl
  · change erase.final.tapes=_
    rw [et]
    dsimp only [firstRun,TapeEmbedding.receipt,TapeEmbedding.config]
    rw [rt,restored_tapes gs i j _ w C D]
    rfl
  · change reset.steps+1+erase.steps=_
    rw [rs,es,time]

end NearCubicWires.RepairOrdinary.RowCachedCoordinateReusable
