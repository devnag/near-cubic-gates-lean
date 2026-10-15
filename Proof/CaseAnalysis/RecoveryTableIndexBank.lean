import Proof.CaseAnalysis.RecoveryTableIndexLoop

/-! Advance the retained first, second and tag indices using either the
actual field-limit driver or the already present six sentinel. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableIndexBank
open LocalBitMultitape RepairRepresentation
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (six : Bool) : Fin 5→Fin 55:=![46,44,52,32,if six then 53 else 35]
theorem slots_injective (six : Bool) : Function.Injective (slots six) := by cases six <;> decide
noncomputable def machine (six : Bool):=RecoveryFocus.machine (slots six) RecoveryBoundedTableIndexLoop.machine
def heads : Fin 5→ℕ:=![0,0,0,0,1]
def input (a b c C count : ℕ) : Fin 5→List Bool:=
  ![List.replicate a true,List.replicate b true,List.replicate c true,List.replicate C false,CompareMachine.word count]
def output (A : Fin 55→List Bool) (a b c count : ℕ) (i : Fin 55):=
  if i=46 then List.replicate (a+count) true else if i=44 then List.replicate (b+count) true
  else if i=52 then List.replicate (c+count) true else A i

theorem cfg_heads (phase : Fin 5) (a b c C count : ℕ) :
    (RepeatMachine.cfg phase (RecoveryBoundedTableIndexLoop.base a b c C) count 1).heads=heads := by
  funext i
  fin_cases i <;> rfl
theorem cfg_tapes (phase : Fin 5) (a b c C count : ℕ) :
    (RepeatMachine.cfg phase (RecoveryBoundedTableIndexLoop.base a b c C) count 1).tapes=input a b c C count := by
  funext i
  fin_cases i <;> rfl

theorem output_slot (six : Bool) (A : Fin 55→List Bool) (a b c count C total : ℕ)
    (hA : ∀ j,A (slots six j)=input a b c C total j) (j : Fin 5) :
    output A a b c count (slots six j)=input (a+count) (b+count) (c+count) C total j := by
  have hj:=hA j
  cases six <;> fin_cases j <;> first | rfl | exact hj

theorem index_run (six : Bool) (H : Fin 55→ℕ) (A : Fin 55→List Bool) (a b c count C W : ℕ)
    (hH : ∀ j,H (slots six j)=heads j) (hA : ∀ j,A (slots six j)=input a b c C count j)
    (ha : a+count ≤ W) (hb : b+count ≤ W) (hc : c+count ≤ W) (hC : W+1 ≤ C) :
    ∃ r,runFrom (machine six) (RecoveryBoundedTableIndexLoop.budget count W) ⟨(machine six).start,H,A⟩=some r ∧
      r.steps ≤ RecoveryBoundedTableIndexLoop.budget count W ∧ r.final.heads=H ∧
      r.final.tapes=output A a b c count := by
  obtain ⟨p,pr,ps,pf⟩:=RecoveryBoundedTableIndexLoop.loop_run a b c count C W ha hb hc hC
  obtain ⟨r,hr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock (slots six) (slots_injective six)
    RecoveryBoundedTableIndexLoop.machine _ H A
    (RepeatMachine.cfg 0 (RecoveryBoundedTableIndexLoop.base a b c C) count 1)
    (by rw [cfg_heads];exact hH) (by rw [cfg_tapes];exact hA) p pr
  refine ⟨r,hr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,slots six j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,pf,cfg_heads]
      exact (hH j).symm
    · exact (rkeep i (by intro j h;exact hi ⟨j,h⟩)).1
  · funext i
    by_cases hi : ∃ j,slots six j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pf,cfg_tapes]
      exact (output_slot six A a b c count C count hA j).symm
    · have h46 : i≠46:=fun h=>hi ⟨0,h.symm⟩
      have h44 : i≠44:=fun h=>hi ⟨1,h.symm⟩
      have h52 : i≠52:=fun h=>hi ⟨2,h.symm⟩
      rw [(rkeep i (by intro j h;exact hi ⟨j,h⟩)).2]
      simp only [output,if_neg h46,if_neg h44,if_neg h52]

theorem output_add (A : Fin 55→List Bool) (a b c d e : ℕ) :
    output (output A a b c d) (a+d) (b+d) (c+d) e=output A a b c (d+e) := by
  funext i
  simp only [output,Nat.add_assoc]
  split_ifs <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableIndexBank
