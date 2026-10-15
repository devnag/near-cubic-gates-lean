import Proof.Assembly.ClosureHardwireReusable

/-! Complete paid restoration of the live-assignment callback. The protected
ports are growing output34, original cache98, framed assignment104, and
increment log105. Every other working tape is restored from its retained
baseline master. Padding handles allocated blank tails without truncation. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.AssignmentRestore
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch ExtIncidence

def work : Fin 108 → Fin 112 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,99,100,101,102,103,106,107,108,109,110,111]
def caps (S : Nat) (i : Fin 112) := if i=34 ∨ i=98 ∨ i=104 ∨ i=105 then 0 else S
def selected (i : Fin 112) : Bool := decide (i≠34)
def localHeads (out : List Bool) (i : Fin 112) : Nat := if i=34 then out.length else 0
def heads (out : List Bool) (i : Fin 223) : Nat := if i=34 then out.length else 0
def masters (A : List Bool → Fin 112 → List Bool) (j : Fin 108) := A [] (work j)
def padded (A : List Bool → Fin 112 → List Bool) (out : List Bool) (S : Nat) :=
  fun i=>ZeroPadding.pad (caps S i) (A out i)
def state (child : Fin 112 → List Bool) (master : Fin 108 → List Bool) (S : Nat) : Fin 223 → List Bool :=
  Fin.addCases (motive:=fun _=>List Bool) child
    (Fin.addCases (motive:=fun _=>List Bool) master
      (![List.replicate S false,List.replicate S true,List.replicate (S+1) false] : Fin 3 → List Bool))
def input (A : List Bool → Fin 112 → List Bool) (out : List Bool) (S : Nat) :=
  state (padded A out S) (masters A) S

def maskSlots : Fin 113 → Fin 223 :=
  Fin.addCases (m:=112) (n:=1) (motive:=fun _=>Fin 223) (fun j : Fin 112=>j.castAdd 111) (fun _ : Fin 1=>220)
def restoreSlots : Fin 218 → Fin 223 :=
  Fin.addCases (m:=217) (n:=1) (motive:=fun _=>Fin 223)
    (Fin.addCases (m:=108) (n:=109) (motive:=fun _=>Fin 223) (fun j : Fin 108=>(j.castAdd 3).natAdd 112)
      (Fin.addCases (m:=108) (n:=1) (motive:=fun _=>Fin 223)
        (fun j : Fin 108=>(work j).castAdd 111) (fun _ : Fin 1=>221)))
    (fun _ : Fin 1=>222)
theorem mask_injective : Function.Injective maskSlots := by decide
theorem restore_injective : Function.Injective restoreSlots := by decide
noncomputable def first {s : Nat} (p : Machine 112 s) := RecoveryFocus.machine maskSlots (MaskedReset.machine p selected)
noncomputable def restore := RecoveryFocus.machine restoreSlots (TemplateRestore.machine 108)
noncomputable def machine {s : Nat} (p : Machine 112 s) := Composition.machine (first p) restore

theorem pad_work (A : List Bool → Fin 112 → List Bool)
    (hA : ∀ a i,i≠34 → A a i=A [] i) (out : List Bool) (S : Nat) (j : Fin 108) :
    padded A out S (work j)=ZeroPadding.pad S (masters A j) := by
  have hc : caps S (work j)=S := by fin_cases j <;>rfl
  have hn : work j≠34 := by fin_cases j <;>decide
  simp only [padded,hc,hA out _ hn,masters]

theorem restore_run (before after : Fin 112 → List Bool) (master : Fin 108 → List Bool)
    (out : List Bool) (S : Nat) (hm : ∀ j,(master j).length≤S)
    (hd : ∀ j,(before (work j)).length≤S)
    (ha : ∀ j,after (work j)=ZeroPadding.pad S (master j))
    (hk : ∀ i,i=34 ∨ i=98 ∨ i=104 ∨ i=105 → after i=before i) :
    Step restore (4*S+9) (heads out) (state before master S)
      (heads out) (state after master S) := by
  have hh : ∀ j,heads out (restoreSlots j)=0 := by intro j;fin_cases j <;>rfl
  have hi : ∀ j,state before master S (restoreSlots j)=TemplateRestore.input master (fun j=>before (work j)) S j := by
    intro j
    refine Fin.addCases (m:=217) (n:=1) (fun j=>?_) (fun j=>?_) j
    · refine Fin.addCases (m:=108) (n:=109) (fun j=>?_) (fun j=>?_) j
      · simp only [restoreSlots,state,TemplateRestore.input,TemplateRestore.pack,TemplateRestore.localInput,
          Fin.addCases_left,Fin.addCases_right]
      · refine Fin.addCases (m:=108) (n:=1) (fun j=>?_) (fun j=>?_) j
        · simp only [restoreSlots,state,TemplateRestore.input,TemplateRestore.pack,TemplateRestore.localInput,
            Fin.addCases_left,Fin.addCases_right]
        · fin_cases j;rfl
    · fin_cases j;rfl
  have he : install restoreSlots (state before master S)
      (NativeFanout.output (fun j=>some j) master S)=state after master S := by
    apply HierarchyAllocation.install_eq restoreSlots restore_injective
    · intro j
      refine Fin.addCases (m:=217) (n:=1) (fun j=>?_) (fun j=>?_) j
      · refine Fin.addCases (m:=108) (n:=109) (fun j=>?_) (fun j=>?_) j
        · simp only [restoreSlots,state,NativeFanout.output,Fin.addCases_left,Fin.addCases_right]
        · refine Fin.addCases (m:=108) (n:=1) (fun j=>?_) (fun j=>?_) j
          · simpa only [restoreSlots,state,NativeFanout.output,NativeFanout.word,Option.elim_some,
              Fin.addCases_left,Fin.addCases_right] using ha j
          · fin_cases j;rfl
      · fin_cases j;rfl
    · intro i hi
      have outside : ∀ i,(∀ j,restoreSlots j≠i) → i=34 ∨ i=98 ∨ i=104 ∨ i=105 ∨ i=220 := by decide
      rcases outside i hi with rfl|rfl|rfl|rfl|rfl
      · exact hk 34 (by simp)
      · exact hk 98 (by simp)
      · exact hk 104 (by simp)
      · exact hk 105 (by simp)
      · rfl
  have call := (TemplateRestore.run master (fun j=>before (work j)) S hm hd).focus
    restoreSlots restore_injective (heads out) (state before master S)
  exact (call.congr_in (dockH_existing _ _ _ hh) (install_existing _ _ _ hi)).congr
    (dockH_existing _ _ _ hh) he

theorem run {s : Nat} (p : Machine 112 s) (A : List Bool → Fin 112 → List Bool)
    (out next : List Bool) (n S : Nat) (J : Fin 112 → Nat) (result : Fin 112 → List Bool)
    (hA : ∀ a i,i≠34 → A a i=A [] i) (houtput : ∀ a,A a 34=a)
    (hr : Step p n (localHeads out) (A out) J result)
    (hj : J 34=next.length) (hout : result 34=next)
    (hkeep : ∀ i,i=98 ∨ i=104 ∨ i=105 → result i=A out i)
    (hm : ∀ j,(masters A j).length≤S) (hS : n+1≤S) :
    Step (machine p) (2*n+4*S+12) (heads out) (input A out S)
      (heads next) (input A next S) := by
  let resultP : Fin 112 → List Bool := fun i=>ZeroPadding.pad (caps S i) (result i)
  have hp := hr.pad (caps S)
  have fit : ∀ j,(resultP (work j)).length≤S := by
    intro j
    apply LocalSupport.step_fits hp (work j) S
    · change (padded A out S (work j)).length≤S
      rw [pad_work A hA out S j,ZeroPadding.pad_length,Nat.max_eq_left (hm j)]
    · have hn : work j≠34 := by fin_cases j <;>decide
      simp only [localHeads,if_neg hn]
      omega
  have reset := hp.mask selected (by
    intro i hi
    have hn : i≠34 := of_decide_eq_true hi
    exact if_neg hn) (by omega : n≤S)
  have mh : (fun i=>if selected i then 0 else J i)=localHeads next := by
    funext i
    by_cases he : i=34
    · subst i;simpa [selected,localHeads] using hj
    · simp [selected,localHeads,he]
  rw [mh] at reset
  have hmask : ∀ j,heads out (maskSlots j)=
      Fin.addCases (m:=112) (n:=1) (motive:=fun _=>Nat) (localHeads out) (fun _=>0) j := by
    intro j;fin_cases j <;>rfl
  have tmask : ∀ j,input A out S (maskSlots j)=
      Fin.addCases (m:=112) (n:=1) (motive:=fun _=>List Bool) (padded A out S)
        (fun _=>List.replicate S false) j := by
    intro j
    refine Fin.addCases (m:=112) (n:=1) (fun j=>?_) (fun j=>?_) j
    · simp only [maskSlots,input,state,Fin.addCases_left]
    · fin_cases j;rfl
  have rhead : dockH maskSlots (heads out)
      (Fin.addCases (m:=112) (n:=1) (motive:=fun _=>Nat) (localHeads next) (fun _=>0))=heads next := by
    funext i
    unfold dockH
    cases hi : RecoveryFocus.pick maskSlots i with
    | none =>
      have hn : i≠34 := by
        intro he;subst i
        have hk : RecoveryFocus.pick maskSlots 34=some 34 := RecoveryFocus.pick_slot maskSlots mask_injective 34
        rw [hi] at hk
        contradiction
      simp only [heads,if_neg hn]
    | some j =>
      have he := RecoveryFocus.slot_of_pick maskSlots hi
      rw [←he]
      fin_cases j <;>rfl
  have rtapes : install maskSlots (input A out S)
      (Fin.addCases (m:=112) (n:=1) (motive:=fun _=>List Bool) resultP (fun _=>List.replicate S false))=
      state resultP (masters A) S := by
    apply HierarchyAllocation.install_eq maskSlots mask_injective
    · intro j
      refine Fin.addCases (m:=112) (n:=1) (fun j=>?_) (fun j=>?_) j
      · simp only [maskSlots,state,Fin.addCases_left]
      · fin_cases j;rfl
    · intro i hi
      exact Fin.addCases (m:=112) (n:=111)
        (fun j hj=>False.elim (hj (j.castAdd 1) (by simp only [maskSlots,Fin.addCases_left])))
        (fun _ _=>by simp only [input,state,Fin.addCases_right]) i hi
  have call := ((reset.focus maskSlots mask_injective (heads out) (input A out S)).congr_in
    (dockH_existing _ _ _ hmask) (install_existing _ _ _ tmask)).congr rhead rtapes
  have retained : ∀ i,i=34 ∨ i=98 ∨ i=104 ∨ i=105 → padded A next S i=resultP i := by
    intro i hi
    rcases hi with rfl|rfl|rfl|rfl
    · change ZeroPadding.pad 0 (A next 34)=ZeroPadding.pad 0 (result 34)
      rw [houtput,hout]
    all_goals
      change ZeroPadding.pad 0 _=ZeroPadding.pad 0 _
      congr 1
      rw [hkeep _ (by simp),hA out _ (by decide),hA next _ (by decide)]
  have last := restore_run resultP (padded A next S) (masters A) next S hm fit
    (pad_work A hA next S) retained
  have all := call.seq last
  convert all using 1 <;>first | rfl | omega

end NearCubicWires.P1Closure.AssignmentRestore
