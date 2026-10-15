import Proof.CaseAnalysis.RecoveryFixedRowsReuse
import Proof.CaseAnalysis.RecoveryGrammarAdvance

/-! Restore only the four row-dependent original grammar scalars. The
same paid erase and unary-add workers retain every constant and candidate. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedCountScalarReset
open LocalBitMultitape RecoveryRootRound BoundedOracleStructuralCircuit
open RecoveryBoundedGrammarCold RecoveryBoundedGrammarAdvance
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 6→Fin 37:=![0,1,2,19,35,36]
def values (cold : Fin 33→List Bool) : Fin 4→List Bool:=![cold 0,cold 1,cold 2,cold 19]
def input (B : ℕ) (cold : Fin 33→List Bool) : Fin 6→List Bool:=
  ![cold 0,cold 1,cold 2,cold 19,List.replicate B true,List.replicate (B+1) false]
def output (B : ℕ) : Fin 6→List Bool:=
  ![List.replicate B false,List.replicate B false,List.replicate B false,List.replicate B false,
    List.replicate B true,List.replicate (B+1) false]
def zeroed (B : ℕ) (cold : Fin 33→List Bool) (i : Fin 33):=
  if i=0 ∨ i=1 ∨ i=2 ∨ i=19 then List.replicate B false else cold i
noncomputable def erase:=RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 4)

theorem erase_ready (B : ℕ) (cold : Fin 33→List Bool) (h : ∀ i,(values cold i).length≤B) :
    ClockJoin.ReadyRun erase (2*B+4) (bank B cold) (bank B (zeroed B cold)) := by
  obtain ⟨r,rr,rt,rh,rs⟩:=RecoveryScratchErase.erase_ready B (B+1) (values cold) h
  have hin : (Fin.addCases (m:=5) (n:=1) (motive:=fun _ : Fin 6=>List Bool)
      (Fin.addCases (m:=4) (n:=1) (motive:=fun _ : Fin 5=>List Bool)
        (values cold) (fun _=>List.replicate B true))
      (fun _=>List.replicate (B+1) false))=input B cold := by
    funext i;fin_cases i <;> rfl
  rw [hin] at rr
  have localRun : ClockJoin.ReadyRun (RecoveryScratchErase.resetMachine 4) (2*B+4) (input B cold) (output B) := by
    refine ⟨r,rr,?_,rh,rs.le⟩
    rw [rt,Nat.max_self]
    funext i;fin_cases i <;> rfl
  have focused:=localRun.focus slots (by decide) (bank B cold) (by intro j;fin_cases j <;> rfl)
  have he : install slots (bank B cold) (output B)=bank B (zeroed B cold) := by
    apply HierarchyWidth.install_eq slots (by decide)
    · intro j;fin_cases j <;> rfl
    · intro i hi
      fin_cases i
      all_goals first
        | exact False.elim (hi 0 rfl)
        | exact False.elim (hi 1 rfl)
        | exact False.elim (hi 2 rfl)
        | exact False.elim (hi 3 rfl)
        | exact False.elim (hi 4 rfl)
        | exact False.elim (hi 5 rfl)
        | rfl
  rw [he] at focused
  exact focused

noncomputable def machine:=Composition.machine (Composition.machine (Composition.machine erase
  (add 1 16)) (add 2 16)) (add 2 5)
def budget (B : ℕ):=64*(B+2)

theorem ready (q bound row C B : ℕ) (extra : Fin 12→List Bool)
    (hindex : row*rowWidth q bound+6+OuterPCPRecovery.boundedCircuitFieldLimit q bound≤B)
    (hrow : row≤B) (hF : 6+OuterPCPRecovery.boundedCircuitFieldLimit q bound+2≤B) :
    ClockJoin.ReadyRun machine (budget B) (bank B (metadata q bound row C B extra))
      (bank B (metadata q bound 0 C B extra)) := by
  let old:=metadata q bound row C B extra
  let c0:=zeroed B old
  let c1:=Function.update c0 1 (RecoveryBoundedGrammarScalarAdd.unary B 6)
  let c2:=Function.update c1 2 (RecoveryBoundedGrammarScalarAdd.unary B 6)
  let c3:=Function.update c2 2 (RecoveryBoundedGrammarScalarAdd.unary B
    (6+OuterPCPRecovery.boundedCircuitFieldLimit q bound))
  have padded (value : ℕ) (hv : value≤B) :
      (ZeroPadding.pad B (List.replicate value true)).length≤B := by
    simp only [ZeroPadding.pad_length,List.length_replicate]
    omega
  have r0:=erase_ready B old (by
    intro j
    fin_cases j
    · exact padded (row*rowWidth q bound) (by omega)
    · exact padded (row*rowWidth q bound+6) (by omega)
    · exact padded (row*rowWidth q bound+6+OuterPCPRecovery.boundedCircuitFieldLimit q bound) hindex
    · exact padded row hrow)
  change ClockJoin.ReadyRun erase _ (bank B old) (bank B c0) at r0
  have r1:=add_ready 1 16 (by decide) 0 6 B c0
    (by simp [c0,zeroed,RecoveryBoundedGrammarScalarAdd.unary,ZeroPadding.pad]) rfl (by omega)
  change ClockJoin.ReadyRun (add 1 16) _ (bank B c0) (bank B c1) at r1
  have r2:=add_ready 2 16 (by decide) 0 6 B c1
    (by simp [c1,c0,zeroed,RecoveryBoundedGrammarScalarAdd.unary,ZeroPadding.pad])
    (by simp only [c1,Function.update_of_ne (by decide : (16 : Fin 33)≠1)];rfl) (by omega)
  change ClockJoin.ReadyRun (add 2 16) _ (bank B c1) (bank B c2) at r2
  have r3:=add_ready 2 5 (by decide) 6 (OuterPCPRecovery.boundedCircuitFieldLimit q bound) B c2
    (by simp only [c2,Function.update_self])
    (by simp only [c2,c1,Function.update_of_ne (by decide : (5 : Fin 33)≠2),
      Function.update_of_ne (by decide : (5 : Fin 33)≠1)];rfl) hF
  change ClockJoin.ReadyRun (add 2 5) _ (bank B c2) (bank B c3) at r3
  have joined:=ClockJoin.join _ _ _ _ _ _ _ (ClockJoin.join _ _ _ _ _ _ _
    (ClockJoin.join _ _ _ _ _ _ _ r0 r1) r2) r3
  have final : c3=metadata q bound 0 C B extra := by
    funext i
    fin_cases i <;> simp [c3,c2,c1,c0,old,zeroed,metadata,numbers,Fin.addCases,
      RecoveryBoundedGrammarScalarAdd.unary,ZeroPadding.pad]
  rw [final] at joined
  apply ClockJoin.enlarge _ _ (budget B) _ _ joined
  unfold RecoveryBoundedGrammarScalarAdd.budget budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedCountScalarReset
