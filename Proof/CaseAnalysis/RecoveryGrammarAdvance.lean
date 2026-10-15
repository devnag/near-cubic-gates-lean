import Proof.CaseAnalysis.RecoveryGrammarScalarBank

/-! Physically advance the original row's three description offsets and
its predecessor bound exactly once. No scalar tape is supplied by meaning. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarAdvance
open LocalBitMultitape RecoveryRootRound BoundedOracleStructuralCircuit OuterPCPRecovery
open RecoveryBoundedGrammarCold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=Composition.machine (Composition.machine (Composition.machine
  (add 0 21) (add 1 21)) (add 2 21)) (add 19 11)
def budget (B : ℕ):=64*(B+2)

theorem ready {W C D L S B P : ℕ} (room : Room W C D L S B P)
    (q bound row : ℕ) (extra : Fin 12→List Bool)
    (width : extra 0=RecoveryBoundedGrammarScalarAdd.unary B (rowWidth q bound))
    (hindex : (row+1)*rowWidth q bound+6+boundedCircuitFieldLimit q bound≤W)
    (hrow : row+1≤W) :
    ClockJoin.ReadyRun machine (budget B) (bank B (metadata q bound row C B extra))
      (bank B (metadata q bound (row+1) C B extra)) := by
  rw [Nat.add_mul,Nat.one_mul] at hindex
  have hcap:=room.reference
  let c0:=metadata q bound row C B extra
  let c1:=Function.update c0 0 (RecoveryBoundedGrammarScalarAdd.unary B
    (row*rowWidth q bound+rowWidth q bound))
  let c2:=Function.update c1 1 (RecoveryBoundedGrammarScalarAdd.unary B
    (row*rowWidth q bound+6+rowWidth q bound))
  let c3:=Function.update c2 2 (RecoveryBoundedGrammarScalarAdd.unary B
    (row*rowWidth q bound+6+boundedCircuitFieldLimit q bound+rowWidth q bound))
  let c4:=Function.update c3 19 (RecoveryBoundedGrammarScalarAdd.unary B (row+1))
  have r0:=add_ready 0 21 (by decide) (row*rowWidth q bound) (rowWidth q bound) B c0
    rfl width (by omega)
  change ClockJoin.ReadyRun (add 0 21) _ (bank B c0) (bank B c1) at r0
  have r1:=add_ready 1 21 (by decide) (row*rowWidth q bound+6) (rowWidth q bound) B c1
    (by simp only [c1,Function.update_of_ne (by decide : (1 : Fin 33)≠0)];rfl)
    (by simp only [c1,Function.update_of_ne (by decide : (21 : Fin 33)≠0)];exact width) (by omega)
  change ClockJoin.ReadyRun (add 1 21) _ (bank B c1) (bank B c2) at r1
  have r2:=add_ready 2 21 (by decide) (row*rowWidth q bound+6+boundedCircuitFieldLimit q bound)
    (rowWidth q bound) B c2
    (by simp only [c2,c1,Function.update_of_ne (by decide : (2 : Fin 33)≠1),
        Function.update_of_ne (by decide : (2 : Fin 33)≠0)];rfl)
    (by simp only [c2,c1,Function.update_of_ne (by decide : (21 : Fin 33)≠1),
        Function.update_of_ne (by decide : (21 : Fin 33)≠0)];exact width) (by omega)
  change ClockJoin.ReadyRun (add 2 21) _ (bank B c2) (bank B c3) at r2
  have r3:=add_ready 19 11 (by decide) row 1 B c3
    (by simp only [c3,c2,c1,Function.update_of_ne (by decide : (19 : Fin 33)≠2),
        Function.update_of_ne (by decide : (19 : Fin 33)≠1),
        Function.update_of_ne (by decide : (19 : Fin 33)≠0)];rfl)
    (by simp only [c3,c2,c1,Function.update_of_ne (by decide : (11 : Fin 33)≠2),
        Function.update_of_ne (by decide : (11 : Fin 33)≠1),
        Function.update_of_ne (by decide : (11 : Fin 33)≠0)];rfl) (by omega)
  change ClockJoin.ReadyRun (add 19 11) _ (bank B c3) (bank B c4) at r3
  have joined:=ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ r0 r1) r2) r3
  have final : c4=metadata q bound (row+1) C B extra := by
    funext i
    fin_cases i <;> simp [c4,c3,c2,c1,c0,metadata,numbers,RecoveryBoundedGrammarScalarAdd.unary,
      Fin.addCases,Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
  rw [final] at joined
  apply ClockJoin.enlarge _ _ (budget B) _ _ joined
  unfold RecoveryBoundedGrammarScalarAdd.budget budget
  have wb:=room.wB
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedGrammarAdvance
