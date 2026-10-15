import Proof.Supplier.RowCommonBounds

/-! The actual common-width row consumer: append one coefficient at the
shared cut width, restore its bank, and advance the coordinate on tape15. -/
namespace NearCubicWires.RepairOrdinary.RowCommonCoordinateBody
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 1→Fin 35 := fun _=>15
theorem injective : Function.Injective slots := by intro a b _; exact Subsingleton.elim _ _
noncomputable def increment := RecoveryFocus.machine slots RowCoordinateIncrement.machine
noncomputable def machine := Composition.machine RowCommonClear.machine increment
noncomputable def entry {n : ℕ} (gs : List (ExactThresholdGate n)) (j p : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :=
  Composition.restart (RowCommonClear.entry gs j p (RowCommonBounds.capacity gs indices.length p)
    tail out indices) machine.start
def budget {n : ℕ} (gs : List (ExactThresholdGate n)) (j p : ℕ)
    (indices : List (Fin gs.length)) := RowCommonBounds.bound gs indices.length p+2*j+10

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

theorem coordinate_heads {n : ℕ} (gs : List (ExactThresholdGate n)) (j k p F : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    (RowCommonClear.entry gs j p F tail out indices).heads=
      (RowCommonClear.entry gs k p F tail out indices).heads := by
  funext i
  dsimp only [RowCommonClear.entry,RowCommonClear.extend,Composition.restart,
    TapeEmbedding.config,RowCommonReset.entry,ZeroPadding.config,Rewind.recording,Rewind.config,
    RowCommonCoefficient.entry,RowCommonCoefficient.extend,RowCoefficientWhole.entry,RowCoefficientDock.extend,
    RowCoefficientLoopReset.entry,RowOccurrenceLoop.cfg,RowOccurrenceLoop.data,RepeatMachine.cfg,controlConfig,
    RowOccurrenceReusable.entry,RowOccurrenceAppend.entry,RowOccurrenceAppend.blank,RowOccurrenceAppend.ready,
    RowCachedCoordinateReusable.entry,RowCachedCoordinateReusable.extended,Composition.leftConfig,
    RowCachedCoordinateReset.entry,RowCachedCoordinateAppend.entry,RowCachedCoordinateAppend.ready,
    RowNativeCoordinateAppend.ready]

theorem coordinate_tapes {n : ℕ} (gs : List (ExactThresholdGate n)) (j p : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length)) :
    Function.update (RowCommonClear.entry gs j p (RowCommonBounds.capacity gs indices.length p)
      tail out indices).tapes 15 (UnaryTemplate.tape (j+1))=
      (RowCommonClear.entry gs (j+1) p (RowCommonBounds.capacity gs indices.length p)
        tail out indices).tapes := by
  have hF : 1≤RowCommonBounds.capacity gs indices.length p := by unfold RowCommonBounds.capacity; omega
  rw [RowCommonReusable.entry_tapes gs j p _ tail out indices hF (RowCommonBounds.inner_fits gs _ p),
    RowCommonReusable.entry_tapes gs (j+1) p _ tail out indices hF (RowCommonBounds.inner_fits gs _ p)]
  funext i
  fin_cases i <;> simp [RowCommonReusable.data]

theorem body_run {n : ℕ} (gs : List (ExactThresholdGate n)) (j : ℕ) (hj : j≤n) (p : ℕ)
    (tail out : List Bool) (indices : List (Fin gs.length))
    (hp : RowCoordinateLoop.width gs indices≤p) :
    ∃ r,runFrom machine (budget gs j p indices) (entry gs j p tail out indices)=some r ∧
      r.final.heads=(entry gs (j+1) p tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices).heads ∧
      r.final.tapes=(entry gs (j+1) p tail
        (out++frame (MatrixScoreBatch.signMagnitude p (RowCommonCoefficient.value gs j hj indices))) indices).tapes ∧
      r.steps≤budget gs j p indices := by
  obtain ⟨a,ha,ah,atapes,asteps⟩ := RowCommonBounds.reusable_run gs j hj p tail out indices hp
  have hhead : a.final.heads 15=1 := by rw [ah]; rfl
  have htape : a.final.tapes 15=UnaryTemplate.tape j := by
    rw [atapes,RowCommonReusable.entry_tapes gs j p _ tail _ indices
      (by unfold RowCommonBounds.capacity; omega) (RowCommonBounds.inner_fits gs _ p)]
    rfl
  obtain ⟨b,hb,bh,bt,bs⟩ := increment_run j a.final.heads a.final.tapes hhead htape
  have whole := Composition.run_join RowCommonClear.machine increment _ _ _ a b ha hb
  have htime : RowCommonBounds.bound gs indices.length p+1+(2*j+9)=budget gs j p indices := by
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

end NearCubicWires.RepairOrdinary.RowCommonCoordinateBody
