import Proof.CaseAnalysis.CloseoutScheduleCapacity
import Proof.Amplification.RecoveryPrefixLoopDock

/-! The existing two literal driver moves turn the finite schedule into a
zero-head ordinary call. Both moves and both composition handoffs are paid. -/
namespace NearCubicWires.RepairSource.CloseoutSchedule.Dock
open LocalBitMultitape RepairOrdinary RecoveryExecution VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def heads (t h : Nat) : Fin (t+1) → Nat :=
  fun i => Fin.addCases (fun _ : Fin t => 0) (fun _ : Fin 1 => h) i
def data {t : Nat} (native : Fin t → List Bool) (total : Nat) : Fin (t+1) → List Bool :=
  fun i => Fin.addCases native (fun _ : Fin 1 => CompareMachine.word total) i
def cfg {t : Nat} (q : Fin 2) (h : Nat) (store : Fin (t+1) → List Bool) : Configuration (t+1) 2 :=
  ⟨q,heads t h,store⟩

theorem heads_zero (t : Nat) : heads t 0 = fun _ => 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [heads]

theorem shift_run (t : Nat) (move : HeadMove) (h : Nat) (store : Fin (t+1) → List Bool) :
    ∃ r, runFrom (RecoveryPrefixLoopDock.shift t move) 1 (cfg 0 h store) = some r ∧
      r.final = cfg 1 (move.apply h) store ∧ r.steps = 1 := by
  have hs : step (RecoveryPrefixLoopDock.shift t move) (cfg 0 h store) =
      some (cfg 1 (move.apply h) store) := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
        simp [applyAction,cfg,heads,HeadMove.apply]
    · rfl
  exact (Timed.single (by rfl) hs).run (by rfl)

def machine {t states : Nat} (body : Machine t states) :=
  Composition.machine
    (Composition.machine (RecoveryPrefixLoopDock.shift t .right)
      (RepeatMachine.machine body (fun _ _ => true)))
    (RecoveryPrefixLoopDock.shift t .left)

theorem ready {t states : Nat} (body : Machine t states) (total cost : Nat)
    (input output : Fin t → List Bool)
    (h : ∃ r, runFrom (RepeatMachine.machine body (fun _ _ => true)) cost
      (RepeatMachine.cfg 0 (initialConfiguration body input) total 1) = some r ∧
      r.steps ≤ cost ∧ r.final = RepeatMachine.cfg 3 (initialConfiguration body output) total 1) :
    ClockJoin.ReadyRun (machine body) (cost+4) (data input total) (data output total) := by
  obtain ⟨a,ha,haf,has⟩ := shift_run t .right 0 (data input total)
  obtain ⟨b,hb,hbs,hbf⟩ := h
  have he : Composition.restart a.final (RepeatMachine.machine body (fun _ _ => true)).start =
      RepeatMachine.cfg 0 (initialConfiguration body input) total 1 := by
    rw [haf]
    rfl
  rw [←he] at hb
  have hab := Composition.run_join (RecoveryPrefixLoopDock.shift t .right)
    (RepeatMachine.machine body (fun _ _ => true)) 1 cost _ a b ha hb
  obtain ⟨c,hc,hcf,hcs⟩ := shift_run t .left 1 (data output total)
  have heout : Composition.restart (Composition.joinedReceipt a b).final
      (RecoveryPrefixLoopDock.shift t .left).start = cfg 0 1 (data output total) := by
    change Composition.restart (Composition.rightConfig 2 b.final) _ = _
    rw [hbf]
    rfl
  rw [←heout] at hc
  have hall := Composition.run_join
    (Composition.machine (RecoveryPrefixLoopDock.shift t .right) (RepeatMachine.machine body (fun _ _ => true)))
    (RecoveryPrefixLoopDock.shift t .left) (1+1+cost) 1 _ (Composition.joinedReceipt a b) c hab hc
  have hi : Composition.leftConfig 2
      (Composition.leftConfig (Fintype.card (RepeatMachine.Control states)) (cfg 0 0 (data input total))) =
      initialConfiguration (machine body) (data input total) := by
    apply configuration_ext
    · rfl
    · exact heads_zero t
    · rfl
  rw [hi,show 1+1+cost+1+1 = cost+4 by omega] at hall
  refine ⟨_,hall,?_,?_,?_⟩
  · change c.final.tapes = _
    rw [hcf]
    rfl
  · intro i
    change c.final.heads i = 0
    rw [hcf]
    exact congrFun (heads_zero t) i
  · change (a.steps+1+b.steps)+1+c.steps ≤ cost+4
    omega

theorem schedule_ready (sources : EightSources) (k D copies : Nat)
    (clock : OrdinaryClock (fun n => n^(k+2))) (C n : Nat) (hD : 1 ≤ D)
    (hn : n+3 ≤ C) (hN : 2^n+3 ≤ C)
    (hcost : ∀ s, s ≤ n → Test.budget sources k D copies clock s n+1 ≤ C) :
    ClockJoin.ReadyRun (machine (Step.machine sources k D copies clock)) (n*(16*C+67)+7)
      (data (Loop.input sources k D copies clock C n 0) n)
      (data (Loop.input sources k D copies clock C n n) n) := by
  have h := ready (Step.machine sources k D copies clock) n (n*(16*C+67)+3) _ _
    (Loop.loop_run sources k D copies clock C n hD hn hN hcost)
  simpa only [Nat.add_assoc] using h

end
end NearCubicWires.RepairSource.CloseoutSchedule.Dock
