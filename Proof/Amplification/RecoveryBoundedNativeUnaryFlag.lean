import Proof.Amplification.RecoveryBoundedNativeLiteralStepRun

/-! The original unary-equality guard reads its actual value driver at the
current offset, then writes the literal's polarity cell in one paid step. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryFlag
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def negative (value pos : ℕ) : Bool := decide (¬pos<value)
def machine : Machine 2 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q bits=>if q.val=0 then
    some ⟨1,![some (!bits 1),none],fun _=>.stay⟩ else none
def cfg (q : Fin 2) (value pos : ℕ) (flag : Bool) : Configuration 2 2 :=
  ⟨q,![0,pos],![[flag],List.replicate value true]⟩

theorem flag_step (value pos : ℕ) (flag : Bool) :
    step machine (cfg 0 value pos flag)=some (cfg 1 value pos (negative value pos)) := by
  have hread:=ClockUnaryProduct.read_unary value pos
  have hneg : (!readTapeBit (List.replicate value true) pos)=negative value pos := by
    rw [hread]
    by_cases h : pos<value <;> simp [negative,h]
  change (some (applyAction (cfg 0 value pos flag)
    (⟨1,![some (!readTapeBit (List.replicate value true) pos),none],fun _=>.stay⟩ : Action 2 2)))=_
  rw [hneg]
  congr 1
  apply configuration_ext
  · rfl
  · rfl
  · funext i; fin_cases i <;> rfl

theorem flag_run (value pos : ℕ) (flag : Bool) :
    ∃ r, runFrom machine 1 (cfg 0 value pos flag)=some r ∧
      r.final=cfg 1 value pos (negative value pos) ∧ r.steps=1 :=
  (Timed.single (by rfl) (flag_step value pos flag)).run (by rfl)

def advance : Machine 1 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>none,fun _=>.right⟩ else none
theorem advance_run (pos : ℕ) (bits : List Bool) :
    ∃ r, runFrom advance 1 ⟨0,fun _=>pos,fun _=>bits⟩=some r ∧
      r.final=(⟨1,fun _=>pos+1,fun _=>bits⟩ : Configuration 1 2) ∧ r.steps=1 :=
  (Timed.single (by rfl) (show step advance (⟨0,fun _=>pos,fun _=>bits⟩ : Configuration 1 2)=
    some ⟨1,fun _=>pos+1,fun _=>bits⟩ from rfl)).run (by rfl)

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeUnaryFlag
