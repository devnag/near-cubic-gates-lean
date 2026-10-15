import Proof.Amplification.RecoveryRawLiteralStreamWhole

/-! The raw inspector accumulates natural-tag validity and the literal
index bound. The binary bound is produced from the original input length. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRawLiteralBound
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure State where
  stream : RecoveryRawLiteralStream.State
  bound : List Bool
  bad : Bool
  tags : Bool
  bounded : Bool

def State.extra (x : State) : Fin 4 → List Bool := ![frame x.bound,[x.bad],[x.tags],[x.bounded]]
def State.cfg {s : Nat} (x : State) (q : Fin s) : Configuration 35 s :=
  TapeEmbedding.config (fun _ : Fin 4=>0) x.extra (x.stream.cfg q)
def State.Valid (x : State) : Prop := x.stream.data.data.Valid ∧ x.bound.length=x.stream.width
def decoded (x : State) : State := {x with stream:=RecoveryRawLiteralStream.output x.stream}
def compared (x : State) (index : List Bool) : State := {x with bad:=decide (RadixSemantics.value x.bound ≤ RadixSemantics.value index)}
def marked (x : State) : State :=
  {x with tags:=x.tags && x.stream.data.data.result,bounded:=x.bounded && !x.bad}
def indexWord (x : State) := RecoveryChildSelection.word false (RecoveryRawLiteral.literal x.stream.data)
def output (x : State) := if (decoded x).stream.data.present then marked (compared (decoded x) (indexWord x)) else decoded x

def slots : Fin 4 → Fin 35 := ![31,24,32,22]
theorem slots_injective : Function.Injective slots := by decide
noncomputable def compareMachine := RecoveryFocus.machine slots RecoveryPrefixCompare.machine
noncomputable def streamMachine := TapeEmbedding.machine 4 RecoveryRawLiteralStream.machine
def markMachine : Machine 35 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q bits=>if q.val=0 then
    some ⟨1,fun i=>if i=33 then some (bits 33 && bits 27)
      else if i=34 then some (bits 34 && !bits 32) else none,fun _=>.stay⟩ else none
noncomputable def checkMachine := Composition.machine compareMachine markMachine
noncomputable def machine := RecoveryGatedSequence.machine streamMachine checkMachine 28
def cost (x : State) := RecoveryRawLiteralStream.cost x.stream+(4*x.bound.length+8+1+1)+2

theorem decoded_valid (x : State) (hx : x.Valid) : (decoded x).Valid := by
  constructor
  · rw [show (decoded x).stream.data=RecoveryRawLiteral.output x.stream.data from RecoveryRawLiteralStream.output_data x.stream]
    exact RecoveryRawLiteral.output_valid x.stream.data hx.1
  · exact hx.2.trans (RecoveryRawLiteralStream.output_width x.stream).symm

theorem decoded_field (x : State) (hx : (decoded x).stream.data.present=true) :
    (decoded x).stream.data.data.fields 0=frame (indexWord x) ∧
      (indexWord x).length=(decoded x).stream.width := by
  have hn : RadixSemantics.value x.stream.data.data.bits≠0 := by
    rw [show (decoded x).stream.data=RecoveryRawLiteral.output x.stream.data from RecoveryRawLiteralStream.output_data x.stream,
      RecoveryRawLiteral.output_present,decide_eq_true_eq] at hx
    exact hx
  constructor
  · rw [show (decoded x).stream.data=RecoveryRawLiteral.output x.stream.data from RecoveryRawLiteralStream.output_data x.stream]
    exact (RecoveryRawLiteral.output_variable x.stream.data hn).1
  · rw [show (decoded x).stream.width=x.stream.width from RecoveryRawLiteralStream.output_width x.stream]
    exact (RecoveryChildSelection.word_length false (RecoveryRawLiteral.literal x.stream.data)).trans
      (RecoveryCellStore.headWord_length x.stream.data.data.bits)

theorem decoded_capacity (x : State) (hx : (decoded x).stream.data.present=true) :
    2*(decoded x).stream.width+3 ≤ (decoded x).stream.data.data.capacity := by
  have hn : RadixSemantics.value x.stream.data.data.bits≠0 := by
    rw [show (decoded x).stream.data=RecoveryRawLiteral.output x.stream.data from RecoveryRawLiteralStream.output_data x.stream,
      RecoveryRawLiteral.output_present,decide_eq_true_eq] at hx
    exact hx
  have hp : (RecoveryRawLiteral.marked x.stream.data).present=true := by
    rw [RecoveryRawLiteral.marked_present]; exact decide_eq_true hn
  rw [show (decoded x).stream.data=RecoveryRawLiteral.output x.stream.data from RecoveryRawLiteralStream.output_data x.stream]
  rw [RecoveryRawLiteral.output,if_pos hp]
  have hl : (RecoveryRawLiteral.literal x.stream.data).length=(decoded x).stream.width := by
    rw [show (decoded x).stream.width=x.stream.width from RecoveryRawLiteralStream.output_width x.stream]
    exact RecoveryCellStore.headWord_length x.stream.data.data.bits
  have hb : RecoveryReusableUnpair.capacity (RecoveryRawLiteral.literal x.stream.data)+1 ≤
      (RecoveryRawLiteral.decoded x.stream.data).data.capacity := by
    exact (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
  change 8192*((RecoveryRawLiteral.literal x.stream.data).length+1)^2+1 ≤ _ at hb
  rw [hl] at hb
  nlinarith

end NearCubicWires.RepairOrdinary.RecoveryRawLiteralBound
