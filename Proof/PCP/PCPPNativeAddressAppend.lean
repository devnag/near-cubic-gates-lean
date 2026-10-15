import Proof.PCP.PCPPNativeAddress
import Proof.PCP.PCPPNativeNaturalAppend

/-! Execute a shared-DAG address and append its exact native natural field
at the current descriptor cursor. Both supplied raw counters are retained. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeAddressAppend
open LocalBitMultitape RepairRepresentation RecoveryExecution ClockJoin
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def addressSlots (i : Fin 4) : Fin 21 := i.castAdd 17
def appendSlots (i : Fin 18) : Fin 21 := if i=0 then 2 else ⟨i.val+3,by omega⟩
theorem append_injective : Function.Injective appendSlots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [appendSlots] at hv
  split_ifs at hv <;> simp_all only [Fin.ext_iff]
  all_goals omega
theorem append_away (i : Fin 18) : 2≤(appendSlots i).val := by
  unfold appendSlots
  split_ifs
  · decide
  · change 2 ≤ i.val+3
    omega
noncomputable def first := RecoveryFocus.machine addressSlots PCPPNativeAddress.machine
noncomputable def last := RecoveryFocus.machine appendSlots PCPPNativeNaturalAppend.machine
noncomputable def machine := Composition.machine first last
def data (base index : ℕ) (out : List Bool) (i : Fin 21) : List Bool :=
  if i=0 then List.replicate base true else if i=1 then List.replicate index true
  else if i=20 then out else []
def heads (out : List Bool) (i : Fin 21) : ℕ := if i=20 then out.length else 0
noncomputable def entry (base index : ℕ) (out : List Bool) :=
  (⟨machine.start,heads out,data base index out⟩ : Configuration 21 _)
def budget (base index : ℕ) := 2*base+4*index+6+1+
  PCPPNativeNaturalAppend.budget (PCPPSubstitution.address base index)

theorem address_append_run (base index : ℕ) (out : List Bool) :
    ∃ r,runFrom machine (budget base index) (entry base index out)=some r ∧
      r.steps≤budget base index ∧
      r.final.tapes 20=out++natWord (PCPPSubstitution.address base index) ∧
      r.final.heads 20=(out++natWord (PCPPSubstitution.address base index)).length ∧
      r.final.tapes 0=List.replicate base true ∧ r.final.heads 0=0 ∧
      r.final.tapes 1=List.replicate index true ∧ r.final.heads 1=0 := by
  obtain ⟨r,hr,rt,rh,rs⟩ := PCPPNativeAddress.address_ready base index
  obtain ⟨a,ha,_,asteps,aheads,atapes,akeep⟩ := RecoveryFocus.dock
    addressSlots (by intro i j h; apply Fin.ext; exact congrArg (fun x : Fin 21 => x.val) h)
    PCPPNativeAddress.machine _ (heads out) (data base index out)
    (initialConfiguration PCPPNativeAddress.machine
      ![List.replicate base true,List.replicate index true,[],[]])
    (by intro i; fin_cases i <;> rfl)
    (by intro i; fin_cases i <;> rfl) r hr
  have fresh (i : Fin 18) (hi : i≠0) :
      a.final.heads (appendSlots i)=PCPPNativeNaturalAppend.heads out i ∧
      a.final.tapes (appendSlots i)=PCPPNativeNaturalAppend.data
        (PCPPSubstitution.address base index) out i := by
    have hv : 4≤(appendSlots i).val := by
      have hiv : i.val≠0 := fun h => hi (Fin.ext h)
      simp only [appendSlots,hi,ite_false,Fin.val_mk]
      omega
    have hk := akeep (appendSlots i) (by
      intro j
      have hj : (addressSlots j).val<4 := j.isLt
      apply Fin.ne_of_val_ne
      omega)
    have h0 : appendSlots i≠0 := fun h => by
      have hx := congrArg Fin.val h
      change (appendSlots i).val=0 at hx
      omega
    have h1 : appendSlots i≠1 := fun h => by
      have hx := congrArg Fin.val h
      change (appendSlots i).val=1 at hx
      omega
    have h20 : appendSlots i=20 ↔ i=17 := by
      simp only [appendSlots,hi,ite_false,Fin.ext_iff]
      omega
    refine ⟨hk.1.trans ?_,hk.2.trans ?_⟩
    · simp only [heads,PCPPNativeNaturalAppend.heads,h20]
    · simp only [data,PCPPNativeNaturalAppend.data,h0,h1,hi,h20,ite_false]
  obtain ⟨s,hs,ss,st,sh,_,_⟩ := PCPPNativeNaturalAppend.append_run
    (PCPPSubstitution.address base index) out
  obtain ⟨b,hb,_,bsteps,bheads,btapes,bkeep⟩ := RecoveryFocus.dock
    appendSlots append_injective PCPPNativeNaturalAppend.machine _ a.final.heads a.final.tapes
    (PCPPNativeNaturalAppend.entry (PCPPSubstitution.address base index) out)
    (by intro i; by_cases hi : i=0
        · subst i; exact (aheads 2).trans (rh 2)
        · exact (fresh i hi).1)
    (by intro i; by_cases hi : i=0
        · subst i; exact (atapes 2).trans (by rw [rt]; rfl)
        · exact (fresh i hi).2) s hs
  let result := Composition.joinedReceipt a b
  have hresult := Composition.run_join first last _ _ _ a b ha hb
  refine ⟨result,hresult,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps≤_
    rw [asteps,bsteps]
    unfold budget
    omega
  · exact (btapes 17).trans st
  · exact (bheads 17).trans sh
  · change b.final.tapes 0=_
    rw [(bkeep 0 (by intro i; have := append_away i; apply Fin.ne_of_val_ne; omega)).2]
    exact (atapes 0).trans (by rw [rt]; rfl)
  · change b.final.heads 0=_
    rw [(bkeep 0 (by intro i; have := append_away i; apply Fin.ne_of_val_ne; omega)).1]
    exact (aheads 0).trans (rh 0)
  · change b.final.tapes 1=_
    rw [(bkeep 1 (by intro i; have := append_away i; apply Fin.ne_of_val_ne; omega)).2]
    exact (atapes 1).trans (by rw [rt]; rfl)
  · change b.final.heads 1=_
    rw [(bkeep 1 (by intro i; have := append_away i; apply Fin.ne_of_val_ne; omega)).1]
    exact (aheads 1).trans (rh 1)

theorem budget_bound (base index : ℕ) : budget base index≤2048*(base+index+1)^2 := by
  have h := PCPPNativeNaturalAppend.budget_bound (PCPPSubstitution.address base index)
  have ha : PCPPSubstitution.address base index+1≤2*(base+index+1) := by
    unfold PCPPSubstitution.address
    omega
  have hs := Nat.pow_le_pow_left ha 2
  unfold budget
  nlinarith [Nat.zero_le (base*base),Nat.zero_le (index*index),Nat.zero_le (base*index)]

end NearCubicWires.RepairOrdinary.PCPPNativeAddressAppend
