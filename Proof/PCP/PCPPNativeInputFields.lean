import Proof.PCP.PCPPNativeQueryHierarchyStream
import Proof.MachineModel.GeneratedAmplifierCopy

/-! The original compound native request is physically split into its two
raw fields. One paid reset restores all heads before hierarchy execution. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeInputFields
open LocalBitMultitape GeneratedAmplifier
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def leftSlots : Fin 2 → Fin 3 := ![0,1]
def rightSlots : Fin 2 → Fin 3 := ![0,2]
noncomputable def left := RecoveryFocus.machine leftSlots Copy.machine
noncomputable def right := RecoveryFocus.machine rightSlots Copy.machine
noncomputable def raw := Composition.machine left right
def word (a b : List Bool) := frame a++frame b
def input3 (a b : List Bool) : Fin 3 → List Bool := ![word a b,[],[]]
def output3 (a b : List Bool) : Fin 3 → List Bool := ![word a b,a,b]
def rawBudget (a b : List Bool) := 2*(a.length+b.length)+3

theorem raw_run (a b : List Bool) :
    ∃ result,run raw (rawBudget a b) (input3 a b)=some result ∧
      result.final.tapes=output3 a b ∧ result.steps=rawBudget a b := by
  obtain ⟨first,hfirst,firstFinal,firstSteps⟩ := Copy.copy_run [] a (frame b) []
  simp only [List.nil_append,List.length_nil,Nat.zero_add] at hfirst firstFinal
  obtain ⟨p,hp,_,ps,ph,pt,pk⟩ := RecoveryFocus.dock leftSlots (by decide) Copy.machine _
    (fun _ => 0) (input3 a b) _ (by intro j; fin_cases j <;> rfl)
    (by intro j; fin_cases j <;> rfl) first hfirst
  have pheads : p.final.heads=![2*a.length+1,a.length,0] := by
    funext i
    fin_cases i
    · exact (ph 0).trans (by rw [firstFinal]; rfl)
    · exact (ph 1).trans (by rw [firstFinal]; rfl)
    · exact (pk 2 (by decide)).1
  have pdata : p.final.tapes=![word a b,a,[]] := by
    funext i
    fin_cases i
    · exact (pt 0).trans (by rw [firstFinal]; rfl)
    · exact (pt 1).trans (by rw [firstFinal]; rfl)
    · exact (pk 2 (by decide)).2
  obtain ⟨last,hlast,lastFinal,lastSteps⟩ := Copy.copy_run (frame a) b [] []
  simp only [List.append_nil,List.nil_append] at hlast lastFinal
  obtain ⟨q,hq,_,qs,_qh,qt,qk⟩ := RecoveryFocus.dock rightSlots (by decide) Copy.machine _
    p.final.heads p.final.tapes _
    (by intro j; rw [pheads]; fin_cases j <;> simp [rightSlots,Copy.cfg,frame_length])
    (by intro j; rw [pdata]; fin_cases j <;> rfl) last hlast
  let result := Composition.joinedReceipt p q
  have hr := Composition.run_join left right _ _ _ p q hp hq
  have htime : (2*a.length+1)+1+(2*b.length+1)=rawBudget a b := by unfold rawBudget; omega
  rw [htime] at hr
  refine ⟨result,hr,?_,?_⟩
  · change q.final.tapes=output3 a b
    funext i
    fin_cases i
    · exact (qt 0).trans (by rw [lastFinal]; rfl)
    · exact ((qk 1 (by decide)).2).trans (congrFun pdata 1)
    · exact (qt 1).trans (by rw [lastFinal]; rfl)
  · change p.steps+1+q.steps=_
    rw [ps,qs,firstSteps,lastSteps,htime]

noncomputable def machine := Rewind.machine raw
def input (a b : List Bool) : Fin 4 → List Bool := ![word a b,[],[],[]]
def output (a b : List Bool) : Fin 4 → List Bool :=
  ![word a b,a,b,List.replicate (rawBudget a b) false]
def budget (a b : List Bool) := 4*(a.length+b.length)+8

theorem ready (a b : List Bool) :
    RecoveryRootRound.ReadyRun machine (budget a b) (input a b) (output a b) := by
  obtain ⟨first,hfirst,firstTapes,firstSteps⟩ := raw_run a b
  obtain ⟨result,hr,rt,rlog,rheads,rsteps,_⟩ := Rewind.Workspace.reset_workspace raw _ _ first hfirst 0
  have hi : Fin.addCases (motive := fun _ : Fin (3+1) => List Bool)
      (input3 a b) (fun _ : Fin 1 => List.replicate 0 false)=input a b := by
    funext i; fin_cases i <;> rfl
  have hb : 2*first.steps+2=budget a b := by rw [firstSteps]; unfold rawBudget budget; omega
  rw [hi,hb] at hr
  refine ⟨result,hr,?_,rheads,by rw [rsteps,hb]⟩
  funext i
  fin_cases i
  · exact (rt 0).trans (congrFun firstTapes 0)
  · exact (rt 1).trans (congrFun firstTapes 1)
  · exact (rt 2).trans (congrFun firstTapes 2)
  · change result.final.tapes 3=List.replicate (rawBudget a b) false
    rw [Nat.zero_max,firstSteps] at rlog
    exact rlog

end NearCubicWires.RepairOrdinary.PCPPNativeInputFields
