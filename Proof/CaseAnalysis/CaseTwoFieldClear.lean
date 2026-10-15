import Proof.CaseAnalysis.CaseTwoFieldReady
import Proof.Amplification.RecoveryScratchErase

/-! One complete original field append returns the same reusable work bank.
All scratch is physically cleared; the source, offset, width and native
append cursor are the only live fields. -/
namespace NearCubicWires.RepairOrdinary.CloseoutCaseTwo.FieldClear
open LocalBitMultitape RepairRepresentation OuterPCPRecovery RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old : Fin 23→Fin 25:=fun i=>i.castAdd 2
def work : Fin 19→Fin 25:=![1,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,22]
def eraseSlots : Fin 21→Fin 25:=Fin.addCases (m:=19) (n:=2) work ![23,24]
theorem old_injective : Function.Injective old:=by
  intro i j h
  apply Fin.ext
  exact congrArg (fun x : Fin 25=>x.val) h
theorem erase_injective : Function.Injective eraseSlots:=by decide
def heads (out : List Bool) (i : Fin 25):=if i=21 then out.length else 0
def data (C : ℕ) (source : List Bool) (offset width : ℕ) (out : List Bool) (i : Fin 25):=
  if i=0 then ZeroPadding.pad C (frame source)
  else if i=2 then ZeroPadding.pad C (List.replicate offset true)
  else if i=3 then ZeroPadding.pad C (List.replicate width true)
  else if i=21 then out else if i=23 then List.replicate C true
  else if i=24 then List.replicate (C+1) false else List.replicate C false
noncomputable def first:=RecoveryFocus.machine old FieldReady.machine
noncomputable def last:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 19)
noncomputable def machine:=Composition.machine first last
def budget (offset width value C : ℕ):=FieldReady.budget offset width value+2*C+5

theorem field_run (pre tail : List Bool) (limit value C : ℕ) (out : List Bool)
    (hv : value≤limit) (hsource : 2*(pre++orderedNatBits limit value++tail).length+1≤C)
    (hoffset : pre.length≤C) (hwidth : limit≤C)
    (hbudget : FieldNative.budget pre.length limit value+1≤C) :
    let source:=pre++orderedNatBits limit value++tail
    ∃ r,runFrom machine (budget pre.length limit value C)
      ⟨machine.start,heads out,data C source pre.length limit out⟩=some r ∧
      r.steps≤budget pre.length limit value C ∧
      r.final.heads=heads (out++natWord value) ∧
      r.final.tapes=data C source pre.length limit (out++natWord value) := by
  let source:=pre++orderedNatBits limit value++tail
  obtain ⟨base,hr,hs,h0,h2,h3,_h5,h21,hh21,hlocal⟩:=
    FieldReady.field_run pre tail limit value C out hv hsource hoffset hwidth hbudget
  obtain ⟨a,ar,_af,ast,ah,atp,keep⟩:=RecoveryFocus.dock old old_injective FieldReady.machine _
    (heads out) (data C source pre.length limit out) (FieldReady.entry C source pre.length limit out)
    (by intro i;fin_cases i <;> rfl)
    (by intro i;fin_cases i <;>
      simp [data,old,FieldReady.entry,FieldReady.pads,FieldNative.data,ZeroPadding.config,
        Rewind.Workspace.capacities,Rewind.recording,Rewind.config,Fin.addCases,ZeroPadding.pad]) base hr
  have aHeads : a.final.heads=heads (out++natWord value) := by
    funext i
    refine Fin.addCases (m:=23) (n:=2) (fun j=>?_) (fun j=>?_) i
    · change a.final.heads (old j)=heads (out++natWord value) (old j)
      rw [ah j]
      by_cases hj : j=21
      · subst j;exact hh21
      · have he : old j≠21 := by
          intro h
          apply hj
          exact Fin.ext (congrArg (fun x : Fin 25=>x.val) h)
        simpa only [heads,if_neg he] using (hlocal j hj).1
    · fin_cases j
      · exact (keep 23 (by intro j;have h:=j.isLt;apply Fin.ne_of_val_ne;change j.val≠23;omega)).1
      · exact (keep 24 (by intro j;have h:=j.isLt;apply Fin.ne_of_val_ne;change j.val≠24;omega)).1
  have hwork (i : Fin 19) : (a.final.tapes (work i)).length≤C := by
    let j : Fin 23:=⟨(work i).val,by fin_cases i <;> decide⟩
    have hj : old j=work i:=Fin.ext rfl
    rw [←hj,atp j]
    exact (hlocal j (by fin_cases i <;> decide)).2
  have hdriver : a.final.tapes 23=List.replicate C true :=
    (keep 23 (by intro j;have h:=j.isLt;apply Fin.ne_of_val_ne;change j.val≠23;omega)).2
  have hlog : a.final.tapes 24=List.replicate (C+1) false :=
    (keep 24 (by intro j;have h:=j.isLt;apply Fin.ne_of_val_ne;change j.val≠24;omega)).2
  have he:=RecoveryScratchErase.erase_ready C (C+1) (fun i=>a.final.tapes (work i)) hwork
  obtain ⟨b,br,bh,bt,bst⟩:=he.focus_at eraseSlots erase_injective a.final.heads a.final.tapes
    (by intro i;fin_cases i <;> first | rfl | exact hdriver | exact hlog)
    (by intro i;rw [aHeads];fin_cases i <;> rfl)
  have whole:=Composition.run_join first last _ _ _ a b ar br
  have hb : FieldReady.budget pre.length limit value+1+(2*C+4)=budget pre.length limit value C := by
    unfold budget;omega
  rw [hb] at whole
  refine ⟨Composition.joinedReceipt a b,whole,?_,bh.trans aHeads,?_⟩
  · change a.steps+1+b.steps≤budget pre.length limit value C
    rw [ast]
    unfold budget;omega
  · change b.final.tapes=_
    rw [bt]
    apply HierarchyAllocation.install_eq eraseSlots erase_injective
    · intro i
      fin_cases i <;> simp [data,eraseSlots,work,Fin.addCases]
    · intro i hi
      have hc : ∀ k : Fin 25,(∀ j,eraseSlots j≠k) → k=0 ∨ k=2 ∨ k=3 ∨ k=21 := by decide
      rcases hc i hi with rfl|rfl|rfl|rfl
      · exact ((atp 0).trans h0).symm
      · exact ((atp 2).trans h2).symm
      · exact ((atp 3).trans h3).symm
      · exact ((atp 21).trans h21).symm

end NearCubicWires.RepairOrdinary.CloseoutCaseTwo.FieldClear
