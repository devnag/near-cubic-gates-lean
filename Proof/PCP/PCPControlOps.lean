import Proof.PCP.PCPContinuation

/-! Constant-size physical branch and continuation operations for the counted
balanced traversal. Tests restore the count cursor; stack writes retain top. -/
namespace NearCubicWires.RepairOrdinary.PCPControlOps
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pushMachine : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q _ => if q.val=0 then some ⟨1,fun _ => some false,fun _ => .right⟩
    else if q.val=1 then some ⟨2,fun _ => some true,fun _ => .right⟩ else none
def pushCfg (q : Fin 3) (pre : List Bool) : Configuration 1 3 :=
  ⟨q,fun _ => pre.length,fun _ => pre⟩

theorem push_step (q next : Fin 3) (pre : List Bool) (b : Bool)
    (hr : pushMachine.rule q (pushCfg q pre).scanned=
      some ⟨next,fun _ => some b,fun _ => .right⟩) :
    step pushMachine (pushCfg q pre)=some (pushCfg next (pre++[b])) := by
  simp only [step,show (pushCfg q pre).control=q from rfl,hr]
  apply congrArg some
  apply configuration_ext
  · rfl
  · funext i
    simp [applyAction,pushCfg,HeadMove.apply]
  · funext i
    exact Streaming.write_append pre b

theorem push_run (pre : List Bool) (cap : ℕ) :
    ∃ r : ExecutionReceipt 1 3,
      runFrom pushMachine 2 (ZeroPadding.config (fun _ => cap) (pushCfg 0 pre))=some r ∧
      r.final=ZeroPadding.config (fun _ => cap) (pushCfg 2 (pre++[false,true])) ∧ r.steps=2 := by
  have h1 := Timed.single (by rfl : pushMachine.halted (0 : Fin 3)=false)
    (push_step 0 1 pre false (by rfl))
  have h2 := Timed.single (by rfl : pushMachine.halted (1 : Fin 3)=false)
    (push_step 1 2 (pre++[false]) true (by rfl))
  have ht := h1.trans h2
  simp only [List.append_assoc,List.singleton_append] at ht
  obtain ⟨base,hr,hf,hs⟩ := ht.run (by rfl)
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config pushMachine (fun _ => cap) 2 _ base hr
  exact ⟨r,hrun,by rw [hfinal,hf],hsteps.trans hs⟩

def testMachine : Machine 1 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => decide (2≤q.val)
  rule := fun q bits => if q.val=0 then some
      ⟨if bits 0 then 1 else 2,fun _ => none,fun _ => if bits 0 then .right else .stay⟩
    else if q.val=1 then some
      ⟨if bits 0 then 4 else 3,fun _ => none,fun _ => .left⟩ else none
def testCfg (q : Fin 5) (n pos : ℕ) : Configuration 1 5 :=
  ⟨q,fun _ => pos,fun _ => List.replicate n true⟩

theorem test_step (q next : Fin 5) (n pos : ℕ) (move : HeadMove)
    (hr : testMachine.rule q (testCfg q n pos).scanned=
      some ⟨next,fun _ => none,fun _ => move⟩) :
    step testMachine (testCfg q n pos)=some (testCfg next n (move.apply pos)) := by
  change Option.map (applyAction (testCfg q n pos))
    (testMachine.rule q (testCfg q n pos).scanned)=_
  rw [hr]
  rfl

def testCode (n : ℕ) : Fin 5 := if n=0 then 2 else if n=1 then 3 else 4
def testCost (n : ℕ) := if n=0 then 1 else 2

theorem test_timed (n : ℕ) :
    Timed testMachine (testCost n) (testCfg 0 n 0) (testCfg (testCode n) n 0) := by
  cases n with
  | zero =>
    exact Timed.single (by rfl) (test_step 0 2 0 0 .stay (by rfl))
  | succ n =>
    have h1 := test_step 0 1 (n+1) 0 .right (by simp [testMachine,testCfg,Configuration.scanned,readTapeBit,List.getD])
    have h2 := test_step 1 (if n=0 then 3 else 4) (n+1) 1 .left (by
      cases n <;> simp [testMachine,testCfg,Configuration.scanned,readTapeBit,List.getD])
    have ht := (Timed.single (by rfl : testMachine.halted (0 : Fin 5)=false) h1).trans
      (Timed.single (by rfl : testMachine.halted (1 : Fin 5)=false) h2)
    simpa [testCost,testCode,HeadMove.apply] using ht

theorem test_run (n cap : ℕ) :
    ∃ r : ExecutionReceipt 1 5,
      runFrom testMachine (testCost n)
        (ZeroPadding.config (fun _ => cap) (testCfg 0 n 0))=some r ∧
      r.final=ZeroPadding.config (fun _ => cap) (testCfg (testCode n) n 0) ∧ r.steps=testCost n := by
  obtain ⟨base,hr,hf,hs⟩ := (test_timed n).run (by
    by_cases h0 : n=0
    · simp [testMachine,testCode,testCfg,h0]
    · by_cases h1 : n=1 <;> simp [testMachine,testCode,testCfg,h0,h1])
  obtain ⟨r,hrun,hfinal,hsteps,_⟩ := ZeroPadding.run_config testMachine (fun _ => cap) _ _ base hr
  exact ⟨r,hrun,by rw [hfinal,hf],hsteps.trans hs⟩

end NearCubicWires.RepairOrdinary.PCPControlOps
