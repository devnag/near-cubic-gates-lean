import Proof.MachineModel.OrdinaryMatrixScoreConstantsEntry
import Proof.Hierarchy.HierarchyBinaryMultiplyEntry

/-! Every assignment physically erases its twelve scalar work tapes, then
copies the retained native constants into its two accumulators. Cold empty
work and a cold empty rewind tape are included in this reusable entry. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreInitialize
open LocalBitMultitape RecoveryRootRound SignedSortKey MatrixScoreWeight
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def clearSlots : Fin 14 → Fin 16 := fun i => i.castAdd 2
theorem clear_injective : Function.Injective clearSlots := by
  intro a b h
  exact Fin.ext (congrArg (fun i : Fin 16 => i.val) h)
def clearPick : Fin 16 → Option (Fin 14) :=
  ![some 0,some 1,some 2,some 3,some 4,some 5,some 6,some 7,some 8,some 9,some 10,some 11,some 12,some 13,none,none]
theorem pick_clear (i : Fin 16) : RecoveryFocus.pick clearSlots i=clearPick i := by
  fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 0
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 1
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 2
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 3
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 4
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 5
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 6
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 7
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 8
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 9
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 10
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 11
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 12
    | exact RecoveryFocus.pick_slot clearSlots clear_injective 13
def copySlots (negative : Bool) : Fin 4 → Fin 16 :=
  if negative then ![15,8,9,10] else ![14,7,9,10]
def copyPick (negative : Bool) : Fin 16 → Option (Fin 4) :=
  if negative then ![none,none,none,none,none,none,none,none,some 1,some 2,some 3,none,none,none,none,some 0]
  else ![none,none,none,none,none,none,none,some 1,none,some 2,some 3,none,none,none,some 0,none]
theorem pick_copy (negative : Bool) (i : Fin 16) : RecoveryFocus.pick (copySlots negative) i=copyPick negative i := by
  cases negative <;> fin_cases i
  all_goals first
    | decide
    | exact RecoveryFocus.pick_slot (copySlots false) (by decide) 0
    | exact RecoveryFocus.pick_slot (copySlots false) (by decide) 1
    | exact RecoveryFocus.pick_slot (copySlots false) (by decide) 2
    | exact RecoveryFocus.pick_slot (copySlots false) (by decide) 3
    | exact RecoveryFocus.pick_slot (copySlots true) (by decide) 0
    | exact RecoveryFocus.pick_slot (copySlots true) (by decide) 1
    | exact RecoveryFocus.pick_slot (copySlots true) (by decide) 2
    | exact RecoveryFocus.pick_slot (copySlots true) (by decide) 3
noncomputable def clear : Machine 16 4 := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 12)
noncomputable def copy (negative : Bool) : Machine 16 6 := RecoveryFocus.machine (copySlots negative) copyMachine
noncomputable def machine := Composition.machine (Composition.machine clear (copy false)) (copy true)
def tapes (c cap w x y : ℕ) (work : Fin 12 → List Bool) : Fin 16 → List Bool :=
  ![work 0,work 1,work 2,work 3,work 4,work 5,work 6,work 7,work 8,work 9,work 10,work 11,
    List.replicate c true,zeros cap,frame (binary w x),frame (binary w y)]
def prepared (c w x y : ℕ) (positive negative : Bool) : Fin 12 → List Bool := fun i =>
  if i=7 ∧ positive then scalar c w x else if i=8 ∧ negative then scalar c w y else zeros c

theorem native_copy (c w x : ℕ) (hc : 4*w+3≤c) :
    ReadyRun copyMachine (8*w+8)
      ![frame (binary w x),zeros c,zeros c,zeros c]
      ![frame (binary w x),scalar c w x,zeros c,zeros c] := by
  obtain ⟨base,hr,ht,hh,hs⟩ := copy_ready (binary w x) [] c c (by simp)
  simp only [binary_length] at hr ht hs
  have hc' : 2*w+1≤c := by omega
  simp only [max_eq_left hc',max_eq_left hc] at ht
  obtain ⟨actual,ha,hf,has,_⟩ := ZeroPadding.run_config copyMachine ![0,c,c,c] _ _ base hr
  have hi : ZeroPadding.config ![0,c,c,c]
      (initialConfiguration copyMachine ![frame (binary w x),[],zeros c,zeros c])=
      initialConfiguration copyMachine ![frame (binary w x),zeros c,zeros c,zeros c] := by
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> simp [ZeroPadding.config,initialConfiguration,zeros,ZeroPadding.pad]
  change runFrom copyMachine (8*w+8) (ZeroPadding.config ![0,c,c,c]
    (initialConfiguration copyMachine ![frame (binary w x),[],zeros c,zeros c]))=some actual at ha
  rw [hi] at ha
  refine ⟨actual,ha,?_,?_,has.trans hs⟩
  · rw [hf]
    funext i
    fin_cases i <;> simp [ZeroPadding.config,ht,scalar,zeros,Rewind.Workspace.pad_zeros]
  · intro i; rw [hf]; exact hh i

theorem clear_ready (c cap w x y : ℕ) (work : Fin 12 → List Bool)
    (hcap : cap≤c+1) (hb : ∀ i,(work i).length≤c) :
    ReadyRun clear (2*c+4) (tapes c cap w x y work)
      (tapes c (c+1) w x y (fun _ => zeros c)) := by
  have base := RecoveryScratchErase.erase_ready c cap work hb
  have focused := base.focus clearSlots clear_injective (tapes c cap w x y work) (by
      intro i; fin_cases i <;> rfl)
  have he : install clearSlots (tapes c cap w x y work)
      (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        (Fin.addCases (m := 12) (n := 1) (motive := fun _ => List Bool)
          (fun _ => zeros c) (fun _ => List.replicate c true))
        (fun _ => zeros (max cap (c+1))))=tapes c (c+1) w x y (fun _ => zeros c) := by
    rw [max_eq_right hcap]
    funext i
    fin_cases i <;> simp [install,pick_clear,clearPick,tapes,Fin.addCases]
  change ReadyRun clear (2*c+4) (tapes c cap w x y work)
    (install clearSlots (tapes c cap w x y work)
      (Fin.addCases (m := 13) (n := 1) (motive := fun _ => List Bool)
        (Fin.addCases (m := 12) (n := 1) (motive := fun _ => List Bool)
          (fun _ => zeros c) (fun _ => List.replicate c true))
        (fun _ => zeros (max cap (c+1))))) at focused
  rw [he] at focused
  exact focused

theorem copy_ready_stage (negative : Bool) (c w x y : ℕ) (hc : 4*w+3≤c) :
    ReadyRun (copy negative) (8*w+8)
      (tapes c (c+1) w x y (prepared c w x y negative false))
      (tapes c (c+1) w x y (prepared c w x y true negative)) := by
  have base := native_copy c w (if negative then y else x) hc
  have focused := base.focus (copySlots negative) (by cases negative <;> decide)
    (tapes c (c+1) w x y (prepared c w x y negative false)) (by
      intro i; cases negative <;> fin_cases i <;> rfl)
  have he : install (copySlots negative)
      (tapes c (c+1) w x y (prepared c w x y negative false))
      ![frame (binary w (if negative then y else x)),scalar c w (if negative then y else x),zeros c,zeros c]=
      tapes c (c+1) w x y (prepared c w x y true negative) := by
    funext i
    cases negative <;> fin_cases i <;> simp [install,pick_copy,copyPick,tapes,prepared]
  rw [he] at focused
  exact focused

theorem initialize_ready (c cap w x y : ℕ) (work : Fin 12 → List Bool)
    (hc : 4*w+3≤c) (hcap : cap≤c+1) (hb : ∀ i,(work i).length≤c) :
    ReadyRun machine (2*c+16*w+22) (tapes c cap w x y work)
      (tapes c (c+1) w x y (prepared c w x y true true)) := by
  have first := clear_ready c cap w x y work hcap hb
  have middle := copy_ready_stage false c w x y hc
  have he : (fun _ : Fin 12 => zeros c)=prepared c w x y false false := by
    funext i; simp [prepared]
  rw [he] at first
  have joined := HierarchyMultiplyEntry.join_exact clear (copy false) _ _ _ _ _ first middle
  have last := HierarchyMultiplyEntry.join_exact (Composition.machine clear (copy false)) (copy true)
    _ _ _ _ _ joined (copy_ready_stage true c w x y hc)
  have ht : ((2*c+4)+1+(8*w+8))+1+(8*w+8)=2*c+16*w+22 := by omega
  simpa only [machine,ht] using last

end NearCubicWires.RepairOrdinary.MatrixScoreInitialize
