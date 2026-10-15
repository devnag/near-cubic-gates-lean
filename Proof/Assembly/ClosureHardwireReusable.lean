import Proof.Assembly.ClosureHardwireBounds
import Proof.Assembly.ClosureTemplateRestore
import Proof.MachineModel.ClosureLocalSupport
import Proof.Circuits.DecompositionCountPosition

/-! The hardwired-child call restores every scratch template from the same
retained masters, leaving only its output append. The source and masks are
restored too; masters, capacity drivers and logs remain explicit inputs. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.HardwireReusable
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound
open RepairRepresentation RepairSource CloseoutFinal SupplierPipeline SupplierEstimator
open ExtIncidence
open scoped BigOperators

def work : Fin 47 → Fin 48 :=
  ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,35,36,37,38,39,40,41,42,43,44,45,46,47]
def caps (R : Nat) (i : Fin 48) := if i=34 then 0 else R
def selected (i : Fin 48) : Bool := decide (i≠34 ∧ i≠42 ∧ i≠46)
def maskSlots : Fin 49 → Fin 98 :=
  Fin.addCases (m:=48) (n:=1) (motive:=fun _=>Fin 98) (fun j : Fin 48=>j.castAdd 50) (fun _ : Fin 1=>95)
def restoreSlots : Fin 96 → Fin 98 :=
  Fin.addCases (m:=95) (n:=1) (motive:=fun _=>Fin 98)
    (Fin.addCases (m:=47) (n:=48) (motive:=fun _=>Fin 98) (fun j : Fin 47=>(j.castAdd 3).natAdd 48)
    (Fin.addCases (m:=47) (n:=1) (motive:=fun _=>Fin 98) (fun j : Fin 47=>(work j).castAdd 50) (fun _ : Fin 1=>96)))
    (fun _ : Fin 1=>97)
theorem maskSlots_injective : Function.Injective maskSlots := by decide
theorem restoreSlots_injective : Function.Injective restoreSlots := by decide

def heads (out : List Bool) (counter : Nat) (i : Fin 98) : Nat :=
  if i=34 then out.length else if i=42 ∨ i=46 then counter else 0
def state (child : Fin 48 → List Bool) (masters : Fin 47 → List Bool) (R : Nat) : Fin 98 → List Bool :=
  Fin.addCases (m:=48) (n:=50) (motive:=fun _=>List Bool) child
    (Fin.addCases (m:=47) (n:=3) (motive:=fun _=>List Bool) masters
    (![List.replicate R false,List.replicate R true,List.replicate (R+1) false] : Fin 3 → List Bool))
def directions (up : Bool) (i : Fin 98) : HeadMove :=
  if i=42 ∨ i=46 then if up then .right else .left else .stay
def move (up : Bool) := DecompositionCountPosition.move (directions up)
noncomputable def child := RecoveryFocus.machine maskSlots (MaskedReset.machine HardwireChild.machine selected)
noncomputable def restore := RecoveryFocus.machine restoreSlots (TemplateRestore.machine 47)
noncomputable def machine := Composition.machine (Composition.machine (Composition.machine child (move false)) restore) (move true)

theorem move_run (up : Bool) (out : List Bool) (A : Fin 98 → List Bool) :
    Step (move up) 1 (heads out (if up then 0 else 1)) A
      (heads out (if up then 1 else 0)) A := by
  obtain ⟨r,hr,hf,_⟩ := DecompositionCountPosition.move_run (directions up)
    (heads out (if up then 0 else 1)) A
  apply Step.of_run hr
  · rw [hf]
    funext i
    cases up <;> fin_cases i <;> rfl
  · rw [hf]

theorem restore_run (before after : Fin 48 → List Bool) (masters : Fin 47 → List Bool)
    (out : List Bool) (R : Nat)
    (hm : ∀ j,(masters j).length≤R) (hd : ∀ j,(before (work j)).length≤R)
    (ha : ∀ j,after (work j)=ZeroPadding.pad R (masters j))
    (hout : after 34=before 34) :
    Step restore (4*R+9) (heads out 0) (state before masters R)
      (heads out 0) (state after masters R) := by
  have hh : ∀ j,heads out 0 (restoreSlots j)=0 := by intro j; fin_cases j <;> rfl
  have hi : ∀ j,state before masters R (restoreSlots j)=
      TemplateRestore.input masters (fun j=>before (work j)) R j := by
    intro j
    refine Fin.addCases (m:=47+48) (n:=1) (fun j=>?_) (fun j=>?_) j
    · refine Fin.addCases (m:=47) (n:=48) (fun a=>?_) (fun a=>?_) j
      · simp only [restoreSlots,state,TemplateRestore.input,TemplateRestore.pack,TemplateRestore.localInput,
          Fin.addCases_left,Fin.addCases_right]
      · refine Fin.addCases (m:=47) (n:=1) (fun a=>?_) (fun a=>?_) a
        · simp only [restoreSlots,state,TemplateRestore.input,TemplateRestore.pack,TemplateRestore.localInput,
            Fin.addCases_left,Fin.addCases_right]
        · fin_cases a; rfl
    · fin_cases j; rfl
  have he : install restoreSlots (state before masters R)
      (NativeFanout.output (fun j=>some j) masters R)=state after masters R := by
    apply HierarchyAllocation.install_eq restoreSlots restoreSlots_injective
    · intro j
      refine Fin.addCases (m:=47+48) (n:=1) (fun j=>?_) (fun j=>?_) j
      · refine Fin.addCases (m:=47) (n:=48) (fun a=>?_) (fun a=>?_) j
        · simp only [restoreSlots,state,NativeFanout.output,Fin.addCases_left,Fin.addCases_right]
        · refine Fin.addCases (m:=47) (n:=1) (fun a=>?_) (fun a=>?_) a
          · simpa only [restoreSlots,state,NativeFanout.output,NativeFanout.word,Option.elim_some,
              Fin.addCases_left,Fin.addCases_right] using ha a
          · fin_cases a; rfl
      · fin_cases j; rfl
    · intro i hi
      have outside : ∀ i,(∀ j,restoreSlots j≠i) → i=34 ∨ i=95 := by decide
      rcases outside i hi with rfl | rfl
      · exact hout
      · rfl
  have call := (TemplateRestore.run masters (fun j=>before (work j)) R hm hd).focus
    restoreSlots restoreSlots_injective (heads out 0) (state before masters R)
  exact (call.congr_in (dockH_existing _ _ _ hh) (install_existing _ _ _ hi)).congr
    (dockH_existing _ _ _ hh) he

variable {q : Nat} (live : Finset (Fin q)) (g : ExactThresholdGate q) (y : BitInput live.card)
  (tail backing : List Bool) (w C D E : Nat)
noncomputable def masters : Fin 47 → List Bool :=
  fun j=>HardwireChild.data live g y tail backing [] w C D E (work j)
noncomputable def padded (out : List Bool) (R : Nat) : Fin 48 → List Bool :=
  fun i=>ZeroPadding.pad (caps R i) (HardwireChild.data live g y tail backing out w C D E i)
noncomputable def input (out : List Bool) (R : Nat) : Fin 98 → List Bool :=
  state (padded live g y tail backing w C D E out R) (masters live g y tail backing w C D E) R
noncomputable def budget (R : Nat) := 2*HardwireChild.budget live g y w C+4*R+16

theorem padded_work (out : List Bool) (R : Nat) (j : Fin 47) :
    padded live g y tail backing w C D E out R (work j)=
      ZeroPadding.pad R (masters live g y tail backing w C D E j) := by
  fin_cases j <;> rfl

theorem padded_out (out : List Bool) (R : Nat) :
    padded live g y tail backing w C D E out R 34=out := ZeroPadding.pad_zero _

theorem run (out : List Bool) (R : Nat)
    (hw : 0<w) (hm : g.target.natAbs+(∑ i,(g.weight i).natAbs)<2^w)
    (hc : 8*w+12≤C)
    (hD : C10NaturalHardwireScore.loopBudget (C10NaturalHardwireScore.items live g y) w C≤D)
    (hE : C10NaturalHardwireWeights.loopBudget (C10NaturalHardwireWeights.gateItems g live)≤E)
    (hmaster : ∀ j,(masters live g y tail backing w C D E j).length≤R)
    (hR : HardwireChild.budget live g y w C+2≤R) :
    Step machine (budget live g y w C R) (heads out 1)
      (input live g y tail backing w C D E out R)
      (heads (out++exactWord (C10SupplierRowInput.hardwire live g y)) 1)
      (input live g y tail backing w C D E
        (out++exactWord (C10SupplierRowInput.hardwire live g y)) R) := by
  obtain ⟨result,hr,_source,hout⟩ := HardwireBounds.child_run live g y tail backing out w C D E hw hm hc hD hE
  let appended := out++exactWord (C10SupplierRowInput.hardwire live g y)
  let resultP : Fin 48 → List Bool := fun i=>ZeroPadding.pad (caps R i) (result i)
  have hp := hr.pad (caps R)
  have fit : ∀ j,(resultP (work j)).length≤R := by
    intro j
    apply LocalSupport.step_fits hp (work j) R
    · change (padded live g y tail backing w C D E out R (work j)).length≤R
      rw [padded_work live g y tail backing w C D E out R j]
      rw [ZeroPadding.pad_length,Nat.max_eq_left (hmaster j)]
    · have hh : HardwireChild.heads out 0 0 (work j)≤1 := by fin_cases j <;> first | exact Nat.zero_le 1 | exact Nat.le_refl 1
      omega
  have reset := hp.mask selected (by
    intro i hi
    fin_cases i <;> first | rfl | contradiction) (by omega : HardwireChild.budget live g y w C≤R)
  have hmask : ∀ j,heads out 1 (maskSlots j)=
      Fin.addCases (HardwireChild.heads out 0 0) (fun _ : Fin 1=>0) j := by
    intro j; fin_cases j <;> rfl
  have tmask : ∀ j,input live g y tail backing w C D E out R (maskSlots j)=
      Fin.addCases (padded live g y tail backing w C D E out R)
        (fun _ : Fin 1=>List.replicate R false) j := by
    intro j
    refine Fin.addCases (m:=48) (n:=1) (fun j=>?_) (fun j=>?_) j
    · simp only [maskSlots,input,state,Fin.addCases_left]
    · fin_cases j; rfl
  have rhead : dockH maskSlots (heads out 1)
      (Fin.addCases (m:=48) (n:=1) (motive:=fun _=>Nat) (fun i=>if selected i then 0 else HardwireChild.heads appended (exactWord g).length q i)
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
  have rtapes : install maskSlots (input live g y tail backing w C D E out R)
      (Fin.addCases (m:=48) (n:=1) (motive:=fun _=>List Bool) resultP (fun _ : Fin 1=>List.replicate R false))=
      state resultP (masters live g y tail backing w C D E) R := by
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
    (input live g y tail backing w C D E out R)).congr_in
      (dockH_existing _ _ _ hmask) (install_existing _ _ _ tmask)).congr rhead rtapes
  have resultOut : resultP 34=appended := by
    change ZeroPadding.pad 0 (result 34)=appended
    rw [ZeroPadding.pad_zero]
    exact hout
  have reload := restore_run resultP (padded live g y tail backing w C D E appended R)
    (masters live g y tail backing w C D E) appended R hmaster fit
    (padded_work live g y tail backing w C D E appended R)
    ((padded_out live g y tail backing w C D E appended R).trans resultOut.symm)
  have joined := ((first.seq (move_run false appended _)).seq reload).seq (move_run true appended _)
  convert joined using 1 <;> first | rfl | (unfold budget; omega)

end NearCubicWires.P1Closure.HardwireReusable
