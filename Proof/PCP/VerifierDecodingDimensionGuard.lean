import Proof.PCP.VerifierDecodingTableRun

/-! Physical t≥2 and s>0 check at the prepared sentinel-counter boundary.
It reads the second tape-count mark and first state-count mark, then restores
the tape-count head. No table expansion precedes this two-transition guard. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.DimensionGuard
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 4 4 where
  descriptionBits := 0
  start := 0
  halted := fun q => 2≤q.val
  rule := fun q bits => if q.val=0 then
    some ⟨1,fun _ => none,fun i => if i=1 then .right else .stay⟩
    else if q.val=1 then
      some ⟨if bits 1 && bits 2 then 2 else 3,fun _ => none,fun i => if i=1 then .left else .stay⟩
    else none

def cfg (q : Fin 4) (word : List Bool) (pos t s tapeHead : ℕ) : Configuration 4 4 :=
  ⟨q,![pos,tapeHead,1,1],![frame word,CapMachine.counter word.length t,
    CapMachine.counter word.length s,CapMachine.counter word.length word.length]⟩

theorem first_step (word : List Bool) (pos t s : ℕ) :
    step machine (cfg 0 word pos t s 1)=some (cfg 1 word pos t s 2) := by
  simp [step,machine,cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem second_step (word : List Bool) (pos t s : ℕ) :
    step machine (cfg 1 word pos t s 2)=some (cfg (if 2≤t ∧ 0<s then 2 else 3) word pos t s 1) := by
  have ht : readTapeBit (CapMachine.counter word.length t) 2=decide (2≤t) := by
    rw [show 2=1+1 from rfl,CapMachine.counter_read]
    congr 1
  have hs : readTapeBit (CapMachine.counter word.length s) 1=decide (0<s) := by
    exact CapMachine.counter_read _ _ 0
  simp [step,machine,cfg,Configuration.scanned,ht,hs]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction,HeadMove.apply]
  · rfl

theorem guard_run (word : List Bool) (pos t s : ℕ) :
    ∃ r, runFrom machine 2 (cfg 0 word pos t s 1)=some r ∧
      r.final=cfg (if 2≤t ∧ 0<s then 2 else 3) word pos t s 1 ∧ r.steps=2 := by
  have hfirst := Timed.single (by rfl : machine.halted (0 : Fin 4)=false) (first_step word pos t s)
  have hsecond := Timed.single (by rfl : machine.halted (1 : Fin 4)=false) (second_step word pos t s)
  exact (hfirst.trans hsecond).run (by split <;> rfl)

end NearCubicWires.RepairSource.VerifierDecoding.DimensionGuard
