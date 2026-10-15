import Proof.PCP.PCPPNativeLiteralAppend
import Proof.PCP.PCPPNativeSumReusable
import Proof.PCP.PCPPRequestNodeSchema

/-! The projection-node caller retains both actual raw indices. Its
second sum call shares exactly the first call's reusable workspace. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeSumBinary
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def data (base left right C : ℕ) (out : List Bool) : Fin 25 → List Bool :=
  Fin.addCases (motive := fun _ : Fin 25 => List Bool)
    (PCPPNativeSumReusable.data base left C out) (fun _ : Fin 1 => List.replicate right true)
def heads (out : List Bool) : Fin 25 → ℕ :=
  Fin.addCases (motive := fun _ : Fin 25 => ℕ) (PCPPNativeSumReusable.heads out) (fun _ : Fin 1 => 0)
def rightSlots (i : Fin 24) : Fin 25 := if i=1 then 24 else i.castAdd 1
theorem right_injective : Function.Injective rightSlots := by decide
noncomputable def rightMachine := RecoveryFocus.machine rightSlots PCPPNativeSumReusable.machine
noncomputable def rightEntry (base left right C : ℕ) (out : List Bool) :=
  (⟨rightMachine.start,heads out,data base left right C out⟩ : Configuration 25 _)

theorem right_input (base left right C : ℕ) (out : List Bool) (i : Fin 24) :
    heads out (rightSlots i)=PCPPNativeSumReusable.heads out i ∧
      data base left right C out (rightSlots i)=PCPPNativeSumReusable.data base right C out i := by
  fin_cases i <;> simp [heads,data,rightSlots,PCPPNativeSumReusable.heads,
    PCPPNativeSumReusable.data,Fin.addCases]

theorem right_run (base left right C : ℕ) (out : List Bool)
    (hC : PCPPNativeSumAppend.budget base right+1 ≤ C) :
    ∃ r,runFrom rightMachine (PCPPNativeSumReusable.budget base right C)
      (rightEntry base left right C out)=some r ∧
      r.steps ≤ PCPPNativeSumReusable.budget base right C ∧
      r.final.heads=heads (out++natWord ((base+right))) ∧
      r.final.tapes=data base left right C (out++natWord ((base+right))) := by
  obtain ⟨raw,hr,rs,rh,rt⟩ := PCPPNativeSumReusable.append_run base right C out hC
  obtain ⟨r,hrun,_,steps,hh,ht,keep⟩ := RecoveryFocus.dock rightSlots right_injective
    PCPPNativeSumReusable.machine _ (heads out) (data base left right C out)
    (PCPPNativeSumReusable.entry base right C out)
    (fun i => (right_input base left right C out i).1)
    (fun i => (right_input base left right C out i).2) raw hr
  have keep1 := keep 1 (by
    intro i
    by_cases hi : i=1
    · subst i; decide
    · intro h
      have hv := congrArg Fin.val h
      simp only [rightSlots,hi,ite_false,Fin.val_castAdd] at hv
      exact hi (Fin.ext hv))
  have hhead (j : Fin 24) : r.final.heads (rightSlots j)=
      PCPPNativeSumReusable.heads (out++natWord ((base+right))) j := by
    rw [hh,rh]
  have htape (j : Fin 24) : r.final.tapes (rightSlots j)=
      PCPPNativeSumReusable.data base right C (out++natWord ((base+right))) j := by
    rw [ht,rt]
  refine ⟨r,hrun,by omega,?_,?_⟩
  · funext i
    fin_cases i
    all_goals first | exact hhead 0 | exact hhead 1 | exact hhead 2 | exact hhead 3 | exact hhead 4 | exact hhead 5 | exact hhead 6 | exact hhead 7 | exact hhead 8 | exact hhead 9 | exact hhead 10 | exact hhead 11 | exact hhead 12 | exact hhead 13 | exact hhead 14 | exact hhead 15 | exact hhead 16 | exact hhead 17 | exact hhead 18 | exact hhead 19 | exact hhead 20 | exact hhead 21 | exact hhead 22 | exact hhead 23 | exact keep1.1
  · funext i
    fin_cases i
    all_goals first | exact htape 0 | exact htape 1 | exact htape 2 | exact htape 3 | exact htape 4 | exact htape 5 | exact htape 6 | exact htape 7 | exact htape 8 | exact htape 9 | exact htape 10 | exact htape 11 | exact htape 12 | exact htape 13 | exact htape 14 | exact htape 15 | exact htape 16 | exact htape 17 | exact htape 18 | exact htape 19 | exact htape 20 | exact htape 21 | exact htape 22 | exact htape 23 | exact keep1.2

end NearCubicWires.RepairOrdinary.PCPPNativeSumBinary
