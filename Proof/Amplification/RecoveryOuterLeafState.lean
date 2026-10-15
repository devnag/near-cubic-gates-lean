import Proof.Amplification.RecoveryRowStructureLeafFlag

/-! Outer rows retain a second lookup bank containing the already checked
inner table. The structural prior-prefix bank remains independent. -/
namespace NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryRowStream RecoveryRowStructure
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RepairSource.RecoveryOracle.BalancedCertificate
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  outer : Children
  inner : RecoveryRowLookupStream.Data
  total : Nat
  capacity : Nat

def State.view (x : State) : Children := {x.outer with bank:=x.inner,total:=x.total,lookupCapacity:=x.capacity}
noncomputable def State.extra (x : State) := RecoveryRowLookupTable.readyTapes x.inner x.total x.capacity
noncomputable def State.tapes (x : State) : Fin 84→List Bool :=
  Fin.addCases (m:=68) (n:=16) (motive:=fun _=>List Bool) x.outer.tapes x.extra
def State.heads (x : State) : Fin 84→Nat :=
  Fin.addCases (m:=68) (n:=16) (motive:=fun _=>Nat) x.outer.heads (fun _=>0)
noncomputable def State.cfg {s : Nat} (x : State) (q : Fin s) : Configuration 84 s := ⟨q,x.heads,x.tapes⟩
def State.Valid (x : State) (word outerBits innerBits : List Bool) :=
  x.outer.Valid word outerBits ∧ x.view.Valid word innerBits

def setBank (x : State) (bank : RecoveryRowLookupStream.Data) : State := {x with inner:=bank}
def keyed (x : State) : State := setBank x {x.inner with key:=x.outer.base.state.bits}
def output (x : State) (bits : List Bool) : State := setBank x (RecoveryRowLookupTable.output x.total x.inner bits)
def slots : Fin 16→Fin 84 := fun i=>i.natAdd 68
theorem slots_injective : Function.Injective slots := by intro a b h; exact Fin.ext (by have he:=congrArg Fin.val h; simp [slots] at he; omega)
noncomputable def lookupMachine := RecoveryFocus.machine slots RecoveryRowLookupTable.rewindMachine
def time (x : State) := bankTime x.view

theorem install_bank (x : State) (bank : RecoveryRowLookupStream.Data) :
    install slots x.tapes (RecoveryRowLookupTable.readyTapes bank x.total x.capacity)=(setBank x bank).tapes := by
  funext i
  refine Fin.addCases (m:=68) (n:=16) (motive:=fun j=>
    install slots x.tapes (RecoveryRowLookupTable.readyTapes bank x.total x.capacity) j=(setBank x bank).tapes j) ?_ ?_ i
  · intro j
    rw [install_other]
    · simp only [State.tapes,Fin.addCases_left]; rfl
    · intro k h
      have he:=congrArg Fin.val h
      simp [slots] at he
      omega
  · intro j
    change install slots x.tapes (RecoveryRowLookupTable.readyTapes bank x.total x.capacity) (slots j)=_
    rw [install_slot slots slots_injective]
    simp only [State.tapes,Fin.addCases_right]
    rfl

theorem keyed_tapes (x : State) : (keyed x).tapes=Function.update x.tapes 75 (frame x.outer.base.state.bits) := by
  have he : (keyed x).extra=Function.update x.extra 7 (frame x.outer.base.state.bits) := by
    exact lookup_key_tapes x.inner x.total x.capacity x.outer.base.state.bits
  unfold State.tapes
  rw [he,bank_update_right]
  rfl

theorem keyed_valid (x : State) (word outerBits innerBits : List Bool) (hx : x.Valid word outerBits innerBits) :
    (keyed x).Valid word outerBits innerBits :=
  ⟨hx.1,bankKey_valid x.view x.outer.base.state.bits word innerBits hx.2 rfl⟩

theorem output_valid (x : State) (word outerBits innerBits : List Bool) (hx : x.Valid word outerBits innerBits)
    (ha : (readMany (readRow x.inner.row.width) x.total innerBits).isSome=true) :
    (output x innerBits).Valid word outerBits innerBits :=
  ⟨hx.1,bank_output_valid x.view word innerBits hx.2 ha⟩

end NearCubicWires.RepairOrdinary.RecoveryOuterLeaf
