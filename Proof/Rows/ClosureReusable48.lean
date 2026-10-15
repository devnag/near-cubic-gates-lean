import Proof.Assembly.RowProduction
import Proof.Amplification.RecoveryScratchErase
import Proof.Amplification.RecoveryRowLookupTapes

/-! Reuse the checked 48-tape restoration layout for the second physical
source worker, the X/C constant gate. All runtime templates remain inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.Reusable48
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch
open HardwireReusable hiding machine child input padded masters budget run

noncomputable def child {s : Nat} (p : Machine 48 s) :=
  RecoveryFocus.machine maskSlots (MaskedReset.machine p selected)
noncomputable def machine {s : Nat} (p : Machine 48 s) :=
  Composition.machine (Composition.machine (Composition.machine (child p) (move false)) restore) (move true)
def masters (A : List Bool → Fin 48 → List Bool) : Fin 47 → List Bool := fun j=>A [] (work j)
def padded (A : List Bool → Fin 48 → List Bool) (out : List Bool) (R : Nat) :=
  fun i=>ZeroPadding.pad (caps R i) (A out i)
def input (A : List Bool → Fin 48 → List Bool) (out : List Bool) (R : Nat) :=
  state (padded A out R) (masters A) R

theorem run {s : Nat} (p : Machine 48 s) (A : List Bool → Fin 48 → List Bool)
    (out next : List Bool) (n pos mpos R : Nat) (result : Fin 48 → List Bool)
    (hwork : ∀ a j,A a (work j)=A [] (work j)) (houtput : ∀ a,A a 34=a)
    (hr : Step p n (HardwireChild.heads out 0 0) (A out) (HardwireChild.heads next pos mpos) result)
    (hout : result 34=next)
    (hmaster : ∀ j,(masters A j).length≤R) (hR : n+2≤R) :
    Step (machine p) (2*n+4*R+16) (heads out 1) (input A out R)
      (heads next 1) (input A next R) := by
  have padded_work (a : List Bool) (j : Fin 47) :
      padded A a R (work j)=ZeroPadding.pad R (masters A j) := by
    have hcaps : caps R (work j)=R := by fin_cases j <;>rfl
    simp only [padded,hcaps,hwork,masters]
  have padded_out (a : List Bool) : padded A a R 34=a := by
    change ZeroPadding.pad 0 (A a 34)=a
    rw [ZeroPadding.pad_zero,houtput]
  let appended := next
  let resultP : Fin 48 → List Bool := fun i=>ZeroPadding.pad (caps R i) (result i)
  have hp := hr.pad (caps R)
  have fit : ∀ j,(resultP (work j)).length≤R := by
    intro j
    apply LocalSupport.step_fits hp (work j) R
    · change (padded A out R (work j)).length≤R
      rw [padded_work out j]
      rw [ZeroPadding.pad_length,Nat.max_eq_left (hmaster j)]
    · have hh : HardwireChild.heads out 0 0 (work j)≤1 := by fin_cases j <;> first | exact Nat.zero_le 1 | exact Nat.le_refl 1
      omega
  have reset := hp.mask selected (by
    intro i hi
    fin_cases i <;> first | rfl | contradiction) (by omega : n≤R)
  have hmask : ∀ j,heads out 1 (maskSlots j)=
      Fin.addCases (HardwireChild.heads out 0 0) (fun _ : Fin 1=>0) j := by
    intro j; fin_cases j <;> rfl
  have tmask : ∀ j,input A out R (maskSlots j)=
      Fin.addCases (padded A out R)
        (fun _ : Fin 1=>List.replicate R false) j := by
    intro j
    refine Fin.addCases (m:=48) (n:=1) (fun j=>?_) (fun j=>?_) j
    · simp only [maskSlots,input,state,Fin.addCases_left]
    · fin_cases j; rfl
  have rhead : dockH maskSlots (heads out 1)
      (Fin.addCases (m:=48) (n:=1) (motive:=fun _=>Nat) (fun i=>if selected i then 0 else HardwireChild.heads appended pos mpos i)
        (fun _ : Fin 1=>0)) = heads appended 1 := by
    funext i
    unfold dockH
    cases hi : RecoveryFocus.pick maskSlots i with
    | none =>
      have hn : i≠34 := by
        intro he
        subst i
        have hk : RecoveryFocus.pick maskSlots 34=some 34 :=
          RecoveryFocus.pick_slot maskSlots maskSlots_injective 34
        rw [hi] at hk
        contradiction
      simp only [heads,if_neg hn]
    | some j =>
      have he := RecoveryFocus.slot_of_pick maskSlots hi
      rw [←he]
      fin_cases j <;> rfl
  have rtapes : install maskSlots (input A out R)
      (Fin.addCases (m:=48) (n:=1) (motive:=fun _=>List Bool) resultP (fun _ : Fin 1=>List.replicate R false))=
      state resultP (masters A) R := by
    apply HierarchyAllocation.install_eq maskSlots maskSlots_injective
    · intro j
      refine Fin.addCases (m:=48) (n:=1) (fun j=>?_) (fun j=>?_) j
      · simp only [maskSlots,state,Fin.addCases_left]
      · fin_cases j; rfl
    · intro i hi
      exact Fin.addCases (m:=48) (n:=50)
        (fun j hj=>False.elim (hj (j.castAdd 1) (by simp only [maskSlots,Fin.addCases_left])))
        (fun _ _=>by simp only [input,state,Fin.addCases_right]) i hi
  have first := ((reset.focus maskSlots maskSlots_injective (heads out 1)
    (input A out R)).congr_in
      (dockH_existing _ _ _ hmask) (install_existing _ _ _ tmask)).congr rhead rtapes
  have resultOut : resultP 34=appended := by
    change ZeroPadding.pad 0 (result 34)=appended
    rw [ZeroPadding.pad_zero]
    exact hout
  have reload := restore_run resultP (padded A appended R)
    (masters A) appended R hmaster fit
    (padded_work appended)
    ((padded_out appended).trans resultOut.symm)
  have joined := ((first.seq (move_run false appended _)).seq reload).seq (move_run true appended _)
  convert joined using 1 <;> first | rfl | omega

end NearCubicWires.P1Closure.Reusable48
