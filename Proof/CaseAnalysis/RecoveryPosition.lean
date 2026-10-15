import Proof.CaseAnalysis.RecoveryWork

/-! Two paid moves set the original bound/candidate/count scan cursors.
The randomness scan starts at two; all three other drivers start at one. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdPosition
open LocalBitMultitape RecoveryRootRound RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def raw : Machine 4 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>none,![.stay,.stay,.right,.stay]⟩
    else if q.val=1 then some ⟨2,fun _=>none,fun _=>.right⟩ else none
def slots : Fin 4→Fin 158:=![150,151,115,152]
def heads : Fin 4→ℕ:=![1,1,2,1]
def positioned (H : Fin 158→ℕ) (i : Fin 158):=
  if i=150 ∨ i=151 ∨ i=152 then 1 else if i=115 then 2 else H i
noncomputable def machine:=RecoveryFocus.machine slots raw

theorem raw_run (A : Fin 4→List Bool) :
    ∃ r,run raw 2 A=some r ∧ r.final.heads=heads ∧ r.final.tapes=A ∧ r.steps=2 := by
  let mid : Configuration 4 3:=⟨1,![0,0,1,0],A⟩
  let final : Configuration 4 3:=⟨2,heads,A⟩
  have ha : step raw (initialConfiguration raw A)=some mid := by
    simp only [step,raw,initialConfiguration,Fin.val_zero,↓reduceIte,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
  have hb : step raw mid=some final := by
    simp only [step,raw,mid,show (1 : Fin 3).val=1 from rfl,show ¬1=0 from by decide,↓reduceIte,Option.map_some]
    congr 1
    apply configuration_ext
    · rfl
    · funext i;fin_cases i <;> rfl
    · funext i;fin_cases i <;> rfl
  obtain ⟨r,hr,rf,rs⟩:=((Timed.single (by rfl) ha).trans (Timed.single (by rfl) hb)).run (by rfl)
  exact ⟨r,hr,congrArg Configuration.heads rf,congrArg Configuration.tapes rf,rs⟩

theorem position_run (A : Fin 158→List Bool) (H : Fin 158→ℕ) (hh : ∀ j,H (slots j)=0) :
    ∃ r,runFrom machine 2 ⟨machine.start,H,A⟩=some r ∧
      r.final.heads=positioned H ∧ r.final.tapes=A ∧ r.steps=2 := by
  obtain ⟨a,ha,ah,atapes,as⟩:=raw_run (fun j=>A (slots j))
  obtain ⟨r,rr,_,rs,rh,rt,keep⟩:=RecoveryFocus.dock slots (by decide) raw 2 H A
    (initialConfiguration raw (fun j=>A (slots j))) hh (by intro j;rfl) a ha
  refine ⟨r,rr,?_,?_,rs.trans as⟩
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [show positioned H (slots j)=heads j from by fin_cases j <;> rfl]
      exact (rh j).trans (congrFun ah j)
    · have hn : ∀ j,slots j≠i:=by simpa only [not_exists] using hi
      have h150 : i≠150:=Ne.symm (hn 0)
      have h151 : i≠151:=Ne.symm (hn 1)
      have h115 : i≠115:=Ne.symm (hn 2)
      have h152 : i≠152:=Ne.symm (hn 3)
      simp only [positioned,h150,h151,h115,h152,false_or,ite_false]
      exact (keep i hn).1
  · funext i
    by_cases hi : ∃ j,slots j=i
    · obtain ⟨j,rfl⟩:=hi
      exact (rt j).trans (congrFun atapes j)
    · exact (keep i (by simpa only [not_exists] using hi)).2

end NearCubicWires.RepairOrdinary.RecoveryBoundedColdPosition
