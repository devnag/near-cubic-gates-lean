import Proof.Amplification.RecoveryRawViewCount

/-! Exact counter-clearing boundary for raw-view reuse. The old counter
is bounded by the already retained unpair erase driver. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawView
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def resetInner (x : RecoveryRawLiteralBound.State) (capacity : Nat) : RecoveryRawLiteralBound.State :=
  {x with stream:={x.stream with data:={x.stream.data with
    data:={x.stream.data.data with capacity:=capacity}}}}
def cleared (x : State) : State :=
  {x with count:=0,inner:=resetInner x.inner (max x.inner.stream.data.data.capacity (x.capacity+1))}
def counterHeads {s : Nat} (x : State) (q : Fin s) : Fin 65→Nat := Function.update (x.cfg q).heads 35 0

def moveCounter (direction : HeadMove) : Machine 65 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then
    some ⟨1,fun _=>none,fun i=>if i=35 then direction else .stay⟩ else none
noncomputable def clearFront := Composition.machine (moveCounter .left) eraseMachine
noncomputable def clearMachine := Composition.machine clearFront (moveCounter .right)
def clearCost (x : State) := 2*x.capacity+8

theorem reset_inner_tapes {s : Nat} (x : RecoveryRawLiteralBound.State) (capacity : Nat) (q : Fin s) :
    ((resetInner x capacity).cfg q).tapes=Function.update (x.cfg q).tapes 22 (List.replicate capacity false) := by
  have h28 := reset_core_tapes x.stream.data.data capacity
  have h29 : (resetInner x capacity).stream.data.tapes=
      Function.update x.stream.data.tapes 22 (List.replicate capacity false) := by
    change Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool)
      ({x.stream.data.data with capacity:=capacity} : RecoveryClauseState.State).tapes
      (fun _=>[x.stream.data.present])=_
    rw [h28,bank_update_left]
    rfl
  have h31 : ((resetInner x capacity).stream.cfg q).tapes=
      Function.update (x.stream.cfg q).tapes 22 (List.replicate capacity false) := by
    change Fin.addCases (m:=29) (n:=2) (motive:=fun _=>List Bool)
      (resetInner x capacity).stream.data.tapes x.stream.extra=_
    rw [h29,bank_update_left]
    rfl
  change Fin.addCases (m:=31) (n:=4) (motive:=fun _=>List Bool)
    ((resetInner x capacity).stream.cfg q).tapes x.extra=_
  rw [h31,bank_update_left]
  rfl

theorem cleared_tapes {s : Nat} (x : State) (q : Fin s) :
    ((cleared x).cfg q).tapes=Function.update (Function.update (x.cfg q).tapes 35 (List.replicate x.capacity false))
      22 (List.replicate (max x.inner.stream.data.data.capacity (x.capacity+1)) false) := by
  have h35 := reset_inner_tapes x.inner (max x.inner.stream.data.data.capacity (x.capacity+1)) q
  have hc : 1 ≤ x.capacity := (by omega : 1 ≤ 3*(x.width+1)+1).trans (capacity_large x)
  have hdr : (fun _ : Fin 1=>List.replicate x.capacity false)=
      Function.update (fun _ : Fin 1=>ZeroPadding.pad x.capacity (CompareMachine.word x.count)) 0
        (List.replicate x.capacity false) := by funext i; fin_cases i; rfl
  change Fin.addCases (m:=36) (n:=29) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=35) (n:=1) (motive:=fun _=>List Bool)
      ((resetInner x.inner (max x.inner.stream.data.data.capacity (x.capacity+1))).cfg q).tapes
      (fun _=>ZeroPadding.pad x.capacity (CompareMachine.word 0))) x.extra=_
  rw [RecoveryCertificateCount.empty_driver x.capacity hc,h35,hdr,
    bank_update_left,bank_update_right,bank_update_left,bank_update_left]
  rfl

theorem counter_length {s : Nat} (x : State) (q : Fin s) (hx : x.Valid) :
    ((x.cfg q).tapes 35).length ≤ x.capacity := by
  change (ZeroPadding.pad x.capacity (CompareMachine.word x.count)).length ≤ x.capacity
  rw [ZeroPadding.pad_length]
  apply Nat.max_le.mpr
  constructor
  · exact Nat.le_refl _
  · simp only [CompareMachine.word,List.length_cons,List.length_replicate]
    have h := capacity_large x
    have hn := hx.2.2.2.1
    have hl := hx.2.2.2.2
    omega

theorem cleared_valid (x : State) (hx : x.Valid) : (cleared x).Valid :=
  ⟨hx.1,hx.2.1,hx.2.2.1,Nat.zero_le _,hx.2.2.2.2⟩

theorem move_run (direction : HeadMove) (heads : Fin 65→Nat) (tapes : Fin 65→List Bool) :
    ∃ r,runFrom (moveCounter direction) 1 ⟨0,heads,tapes⟩=some r ∧
      r.final=⟨1,Function.update heads 35 (direction.apply (heads 35)),tapes⟩ ∧ r.steps=1 := by
  have h : step (moveCounter direction) ⟨0,heads,tapes⟩=
      some (⟨1,Function.update heads 35 (direction.apply (heads 35)),tapes⟩ : Configuration 65 2) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      by_cases hi : i=35
      · subst i; simp [applyAction,HeadMove.apply]
      · simp [applyAction,hi,HeadMove.apply]
    · funext i; rfl
  exact (Timed.single (by rfl) h).run (by rfl)

theorem cleared_heads {s : Nat} (x : State) (q : Fin s) :
    ((cleared x).cfg q).heads=(x.cfg q).heads := by
  simp only [State.cfg,State.innerCfg,RecoveryBankPair.cfg,TapeEmbedding.config,
    RecoveryRawLiteralBound.State.cfg,RecoveryRawLiteralStream.State.cfg,
    RecoveryRawLiteralStream.State.extraHeads,cleared,resetInner]

theorem counter_restore (heads : Fin 65→Nat) (hh : heads 35=1) :
    Function.update (Function.update heads 35 0) 35 1=heads := by
  funext i
  by_cases hi : i=35
  · subst i; simp [hh]
  · simp [hi]

end NearCubicWires.RepairOrdinary.RecoveryRawView
