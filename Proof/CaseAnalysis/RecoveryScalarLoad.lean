import Proof.PCP.PCPUnaryCopy
import Proof.PCP.PCPPairReusable
import Proof.Hierarchy.HierarchyWidth

/-! Five actual raw source scalars are copied into the metadata bank.
One paid B sweep allocates all destinations; the original scalars survive. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedColdScalarLoad
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def sourceSlot (j : Fin 5) : Fin 12:=j.castAdd 7
def targetSlot (j : Fin 5) : Fin 12:=(j.castAdd 2).natAdd 5
def copySlots (j : Fin 5) : Fin 3→Fin 12:=![sourceSlot j,targetSlot j,11]
def eraseSlots (j : Fin 7) : Fin 12:=j.natAdd 5
def bank (n : Fin 5→ℕ) (B done : ℕ) : Fin 12→List Bool:=
  Fin.addCases (m:=5) (n:=7) (fun j=>List.replicate (n j) true)
    (Fin.addCases (m:=5) (n:=2)
      (fun j=>if j.val<done then ZeroPadding.pad B (List.replicate (n j) true) else List.replicate B false)
      ![List.replicate B true,List.replicate (B+1) false])
def input (n : Fin 5→ℕ) (B : ℕ) : Fin 12→List Bool:=
  Fin.addCases (m:=5) (n:=7) (fun j=>List.replicate (n j) true)
    (Fin.addCases (m:=5) (n:=2) (fun _=>[]) ![List.replicate B true,List.replicate (B+1) false])
def localOutput (n B : ℕ) : Fin 3→List Bool:=
  ![List.replicate n true,ZeroPadding.pad B (List.replicate n true),List.replicate (B+1) false]

theorem copy_injective (j : Fin 5) : Function.Injective (copySlots j):=by
  intro a b h
  have hv:=congrArg Fin.val h
  have hj:=j.isLt
  fin_cases a <;>fin_cases b <;>simp [copySlots,sourceSlot,targetSlot] at hv ⊢ <;>omega
theorem erase_injective : Function.Injective eraseSlots:=by
  intro i j h
  exact Fin.ext (by have hv:=congrArg Fin.val h;change 5+i.val=5+j.val at hv;omega)
theorem bank_source (n : Fin 5→ℕ) (B done : ℕ) (j : Fin 5) :
    bank n B done (sourceSlot j)=List.replicate (n j) true := by
  simp only [bank,sourceSlot,Fin.addCases_left]
theorem bank_target (n : Fin 5→ℕ) (B done : ℕ) (j : Fin 5) :
    bank n B done (targetSlot j)=
      if j.val<done then ZeroPadding.pad B (List.replicate (n j) true) else List.replicate B false := by
  simp only [bank,targetSlot,Fin.addCases_right,Fin.addCases_left]
theorem bank_log (n : Fin 5→ℕ) (B done : ℕ) : bank n B done 11=List.replicate (B+1) false:=rfl

theorem install_step (n : Fin 5→ℕ) (B : ℕ) (j : Fin 5) :
    install (copySlots j) (bank n B j.val) (localOutput (n j) B)=bank n B (j.val+1) := by
  apply HierarchyWidth.install_eq (copySlots j) (copy_injective j)
  · intro i
    fin_cases i
    · exact bank_source n B _ j
    · exact (bank_target n B _ j).trans (if_pos (by omega))
    · exact bank_log n B _
  · intro i hi
    revert hi
    refine Fin.addCases (m:=5) (n:=7) (fun k=>?_) (fun k=>?_) i
    · intro _;simp only [bank,Fin.addCases_left]
    · refine Fin.addCases (m:=5) (n:=2) (fun k=>?_) (fun k=>?_) k
      · intro hi
        have hk : k≠j:=by intro h;subst k;exact hi 1 rfl
        have hkv : k.val≠j.val:=fun h=>hk (Fin.ext h)
        have he : (k.val<j.val)=(k.val<j.val+1):=propext (by omega)
        simp only [bank,Fin.addCases_right,Fin.addCases_left,he]
      · intro _;simp only [bank,Fin.addCases_right]

def copyProgram (j : Fin 5):=RecoveryFocus.machine (copySlots j) PCPUnaryCopy.machine
def eraseProgram:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 5)
def firstTwo:=Composition.machine (copyProgram 0) (copyProgram 1)
def firstThree:=Composition.machine firstTwo (copyProgram 2)
def firstFour:=Composition.machine firstThree (copyProgram 3)
def copies:=Composition.machine firstFour (copyProgram 4)
def machine:=Composition.machine eraseProgram copies
def copyBudget (n : Fin 5→ℕ):=(2*n 0+4)+1+(2*n 1+4)+1+(2*n 2+4)+1+(2*n 3+4)+1+(2*n 4+4)
def budget (B : ℕ):=16*(B+2)

theorem copy_ready (n : Fin 5→ℕ) (B : ℕ) (j : Fin 5) (hn : n j≤B) :
    ClockJoin.ReadyRun (copyProgram j) (2*n j+4) (bank n B j.val) (bank n B (j.val+1)) := by
  obtain ⟨r,rr,rt,rh,rs⟩:=PCPUnaryCopy.copy_ready (n j) 0 B (B+1)
  have hlocal : ClockJoin.ReadyRun PCPUnaryCopy.machine (2*n j+4)
      (![List.replicate (n j) true,List.replicate B false,List.replicate (B+1) false] : Fin 3→List Bool)
      (localOutput (n j) B) := by
    simp only [ZeroPadding.pad_zero,max_eq_left (by omega : n j+1≤B+1)] at rr rt
    exact ⟨r,rr,rt,rh,rs.le⟩
  have h:=hlocal.focus (copySlots j) (copy_injective j) (bank n B j.val) (by
    intro i;fin_cases i
    · exact bank_source n B _ j
    · exact (bank_target n B _ j).trans (if_neg (by omega))
    · exact bank_log n B _)
  rw [install_step] at h
  exact h

theorem erase_ready (n : Fin 5→ℕ) (B : ℕ) :
    ClockJoin.ReadyRun eraseProgram (2*B+4) (input n B) (bank n B 0) := by
  have h:= (RecoveryScratchErase.erase_ready B (B+1) (fun _ : Fin 5=>[]) (by simp)).focus
    eraseSlots erase_injective (input n B) (by
      intro i
      refine Fin.addCases (m:=6) (n:=1) (fun j=>?_) (fun j=>?_) i
      · refine Fin.addCases (m:=5) (n:=1) (fun k=>?_) (fun k=>?_) j
        · simp only [eraseSlots,input,Fin.addCases_right,Fin.addCases_left]
          change Fin.addCases (m:=5) (n:=2) (fun _=>[])
            ![List.replicate B true,List.replicate (B+1) false] (k.castAdd 2)=[]
          exact Fin.addCases_left k
        · fin_cases k;rfl
      · fin_cases j;rfl)
  have he : install eraseSlots (input n B)
      (Fin.addCases (m:=6) (n:=1)
        (Fin.addCases (m:=5) (n:=1) (fun _=>List.replicate B false) (fun _=>List.replicate B true))
        (fun _=>List.replicate (max (B+1) (B+1)) false))=bank n B 0 := by
    apply HierarchyWidth.install_eq eraseSlots erase_injective
    · intro i
      fin_cases i <;>simp [bank,eraseSlots,Fin.addCases]
    · intro i hi
      revert hi
      refine Fin.addCases (m:=5) (n:=7) (fun j=>?_) (fun j=>?_) i
      · intro _;simp only [input,bank,Fin.addCases_left]
      · intro hi;exact False.elim (hi j rfl)
  rw [he] at h
  obtain ⟨r,rr,rt,rh,rs⟩:=h
  exact ⟨r,rr,rt,rh,rs.le⟩

theorem load_ready (n : Fin 5→ℕ) (B : ℕ) (hn : ∀ j,n j≤B) :
    ClockJoin.ReadyRun machine (budget B) (input n B) (bank n B 5) := by
  have h01:=ClockJoin.join _ _ _ _ _ _ _ (copy_ready n B 0 (hn 0)) (copy_ready n B 1 (hn 1))
  have h012:=ClockJoin.join _ _ _ _ _ _ _ h01 (copy_ready n B 2 (hn 2))
  have h0123:=ClockJoin.join _ _ _ _ _ _ _ h012 (copy_ready n B 3 (hn 3))
  have hcopies:=ClockJoin.join _ _ _ _ _ _ _ h0123 (copy_ready n B 4 (hn 4))
  have hc : ClockJoin.ReadyRun copies (copyBudget n) (bank n B 0) (bank n B 5):=hcopies
  have h:=ClockJoin.join _ _ _ _ _ _ _ (erase_ready n B) hc
  apply ClockJoin.enlarge _ _ _ _ _ h
  have h0:=hn 0;have h1:=hn 1;have h2:=hn 2;have h3:=hn 3;have h4:=hn 4
  dsimp only [copyBudget,budget]
  omega

end
end NearCubicWires.RepairOrdinary.RecoveryBoundedColdScalarLoad
