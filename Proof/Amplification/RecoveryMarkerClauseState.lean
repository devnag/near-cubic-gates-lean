import Proof.Amplification.RecoveryRawSATCorrected

/-! The marker replay has one retained original outer-code bank and one
reusable literal bank. The outer head is copied by the existing framed
copy machine before any literal inspection. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerClause
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStructure
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  inner : RecoveryRawLiteral.State
  outer : RecoveryClauseState.State

def State.width (x : State) := x.inner.data.bits.length
def State.tapes (x : State) : Fin 57→List Bool :=
  Fin.addCases (m:=29) (n:=28) (motive:=fun _=>List Bool) x.inner.tapes x.outer.tapes
def State.cfg {s : Nat} (x : State) (q : Fin s) : Configuration 57 s := ⟨q,fun _=>0,x.tapes⟩
def State.Valid (x : State) : Prop := x.inner.data.Valid ∧ x.outer.Valid ∧ x.outer.bits.length=x.width
def outerStep (x : State) : State := {x with outer:=x.outer.after 0}
def headWord (x : State) := RecoveryCellStore.headWord x.outer.bits
def copied (x : State) (bits : List Bool) : State :=
  let data := {x.inner.data with bits:=bits,capacity:=max x.inner.data.capacity (4*bits.length+3)}
  let inner := {x.inner with data:=data}
  let outer := {x.outer with capacity:=max x.outer.capacity (2*bits.length+1)}
  ⟨inner,outer⟩
def literalStep (x : State) : State := {x with inner:=RecoveryRawLiteral.output x.inner}
def emptyStep (x : State) : State := {x with inner:={x.inner with data:=x.inner.data.after 0}}

noncomputable def outerMachine := RecoveryBankPair.rightMachine (t:=29) (RecoveryClauseState.machine 0)
def copySlots : Fin 4→Fin 57 := ![53,0,51,22]
theorem copySlots_injective : Function.Injective copySlots := by decide
noncomputable def copyMachine := RecoveryFocus.machine copySlots RecoveryRootRound.copyMachine
noncomputable def literalMachine := TapeEmbedding.machine 28 RecoveryRawLiteral.machine
noncomputable def emptyMachine := TapeEmbedding.machine 28
  (TapeEmbedding.machine 1 (RecoveryClauseState.machine 0))

theorem outer_valid (x : State) (hx : x.Valid) : (outerStep x).Valid :=
  ⟨hx.1,RecoveryClauseState.after_valid x.outer 0 hx.2.1,
    (RecoveryClauseState.after_length x.outer 0).trans hx.2.2⟩
theorem literal_valid (x : State) (hx : x.Valid) : (literalStep x).Valid :=
  ⟨RecoveryRawLiteral.output_valid x.inner hx.1,hx.2.1,hx.2.2.trans (RecoveryRawLiteral.output_width x.inner).symm⟩
theorem empty_valid (x : State) (hx : x.Valid) : (emptyStep x).Valid :=
  ⟨RecoveryClauseState.after_valid x.inner.data 0 hx.1,hx.2.1,
    hx.2.2.trans (RecoveryClauseState.after_length x.inner.data 0).symm⟩
theorem copied_capacity (x : State) (bits : List Bool) (hw : bits.length=x.width) :
    RecoveryReusableUnpair.capacity bits=RecoveryReusableUnpair.capacity x.inner.data.bits := by
  change 8192*(bits.length+1)^2=8192*(x.width+1)^2
  rw [hw]
theorem copied_valid (x : State) (bits : List Bool) (hx : x.Valid) (hw : bits.length=x.width) :
    (copied x bits).Valid := by
  refine ⟨?_,hx.2.1,hx.2.2.trans hw.symm⟩
  constructor
  · intro i
    change (x.inner.data.backing i).length ≤ RecoveryReusableUnpair.capacity bits
    rw [copied_capacity x bits hw]
    exact hx.1.1 i
  · intro i
    change (x.inner.data.fields i).length ≤ 2*bits.length+1
    rw [hw]
    exact hx.1.2 i

theorem copied_tapes (x : State) (bits : List Bool) (hw : bits.length=x.width) :
    (copied x bits).tapes=
      Function.update (Function.update (Function.update x.tapes 51
        (List.replicate (max x.outer.capacity (2*bits.length+1)) false)) 0 (frame bits))
        22 (List.replicate (max x.inner.data.capacity (4*bits.length+3)) false) := by
  have hc := RecoveryRawView.replace_core_tapes x.inner.data bits
    (max x.inner.data.capacity (4*bits.length+3)) (copied_capacity x bits hw)
  have ho := RecoveryRawView.reset_core_tapes x.outer (max x.outer.capacity (2*bits.length+1))
  change Fin.addCases (m:=29) (n:=28) (motive:=fun _=>List Bool)
    (Fin.addCases (m:=28) (n:=1) (motive:=fun _=>List Bool)
      ({x.inner.data with bits:=bits,capacity:=max x.inner.data.capacity (4*bits.length+3)} : RecoveryClauseState.State).tapes
      (fun _=>[x.inner.present]))
    ({x.outer with capacity:=max x.outer.capacity (2*bits.length+1)} : RecoveryClauseState.State).tapes=_
  rw [hc,ho,bank_update_left,bank_update_left,bank_update_left,bank_update_left,bank_update_right]
  rfl

end NearCubicWires.RepairOrdinary.RecoveryMarkerClause
