import Proof.Amplification.RecoveryRawClausePadded

/-! Shared workspace for one raw-view clause. The inner 36-tape bank keeps
its existing witness cursor and literal counter; the outer raw-list bank
retains the remaining formula code, and tape64 is the actual count cap. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  inner : RecoveryRawLiteralBound.State
  outer : RecoveryClauseState.State
  count : Nat
  limit : Nat

def State.width (x : State) := x.inner.stream.width
def State.capacity (x : State) := RecoveryReusableUnpair.capacity x.inner.stream.data.data.bits
def State.innerCfg {s : Nat} (x : State) (q : Fin s) :=
  TapeEmbedding.config (fun _ : Fin 1=>1)
    (fun _=>ZeroPadding.pad x.capacity (CompareMachine.word x.count)) (x.inner.cfg q)
def State.extra (x : State) : Fin 29→List Bool :=
  Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool) x.outer.tapes (fun _=>CompareMachine.word x.limit)
def State.extraHeads : Fin 29→Nat :=
  Fin.addCases (m:=28) (n:=1) (motive:=fun _=>Nat) (fun _=>0) (fun _=>1)
def State.cfg {s : Nat} (x : State) (q : Fin s) : Configuration 65 s :=
  RecoveryBankPair.cfg (x.innerCfg q).heads (x.innerCfg q).tapes State.extraHeads x.extra q
def State.Valid (x : State) : Prop :=
  x.inner.Valid ∧ x.outer.Valid ∧ x.outer.bits.length=x.width ∧
    x.count ≤ x.limit ∧ x.limit ≤ 3*(x.width+1)

def copySlots : Fin 4→Fin 65 := ![60,0,58,22]
def countSlots : Fin 3→Fin 65 := ![29,35,64]
def eraseSlots : Fin 3→Fin 65 := ![35,21,22]
theorem copySlots_injective : Function.Injective copySlots := by decide
theorem countSlots_injective : Function.Injective countSlots := by decide
theorem eraseSlots_injective : Function.Injective eraseSlots := by decide
noncomputable def copyMachine := RecoveryFocus.machine copySlots RecoveryRootRound.copyMachine
noncomputable def countMachine := RecoveryFocus.machine countSlots RecoveryCertificateCount.machine
noncomputable def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 1)
noncomputable def outerMachine := RecoveryBankPair.rightMachine (t:=36)
  (TapeEmbedding.machine 1 (RecoveryClauseState.machine 0))
noncomputable def clauseMachine := TapeEmbedding.machine 29 RecoveryRawClause.machine

def outerStep (x : State) : State := {x with outer:=x.outer.after 0}
def copied (x : State) (bits : List Bool) : State :=
  let innerCore := {x.inner.stream.data.data with
    bits := bits
    capacity := max x.inner.stream.data.data.capacity (4*bits.length+3)}
  let outerCore := {x.outer with capacity := max x.outer.capacity (2*bits.length+1)}
  { x with
    outer := outerCore
    inner := {x.inner with stream := {x.inner.stream with
      data := {x.inner.stream.data with data := innerCore}}} }

theorem capacity_large (x : State) : 3*(x.width+1)+1 ≤ x.capacity := by
  change 3*(x.width+1)+1 ≤ 8192*(x.width+1)^2
  nlinarith

theorem outer_step_valid (x : State) (hx : x.Valid) : (outerStep x).Valid := by
  exact ⟨hx.1,RecoveryClauseState.after_valid x.outer 0 hx.2.1,
    (RecoveryClauseState.after_length x.outer 0).trans hx.2.2.1,hx.2.2.2⟩

theorem inner_cfg_padded {s : Nat} (x : State) (q : Fin s) :
    x.innerCfg q=RecoveryRawClause.paddedCfg x.capacity x.inner x.count q := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    refine Fin.addCases (m:=35) (n:=1) (motive:=fun i=>
      (x.innerCfg q).tapes i=(RecoveryRawClause.paddedCfg x.capacity x.inner x.count q).tapes i) ?_ ?_ i
    · intro j
      have hj : j.castAdd 1≠(35 : Fin 36) := by intro h; have hv:=congrArg Fin.val h; simp at hv; omega
      simp only [State.innerCfg,TapeEmbedding.config,Fin.addCases_left,RecoveryRawClause.paddedCfg,
        ZeroPadding.config,RecoveryRawClause.driverCaps,if_neg hj,ZeroPadding.pad_zero,RecoveryRawClause.cfg]
    · intro j; fin_cases j; rfl

end NearCubicWires.RepairOrdinary.RecoveryRawView
