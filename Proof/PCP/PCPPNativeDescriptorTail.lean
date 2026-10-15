import Proof.PCP.PCPPNativeColdPadding

/-! Seal a native node stream with exact cold padding and the loop's actual
output-reference counter. The raw padding and output reference survive;
the final descriptor tape stays at its append cursor. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeDescriptorTail
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def paddingSlots : Fin 4 → Fin 21 := ![0,2,3,4]
def footerSlots (i : Fin 18) : Fin 21 :=
  if i=0 then 1 else if h17 : i=17 then 4 else ⟨i.val+4,by
    have h := i.isLt
    have hn : i.val≠17 := fun he => h17 (Fin.ext he)
    omega⟩
theorem footer_injective : Function.Injective footerSlots := by decide
noncomputable def first := RecoveryFocus.machine paddingSlots PCPPNativeColdPadding.machine
noncomputable def last := RecoveryFocus.machine footerSlots PCPPNativeNaturalAppend.machine
noncomputable def machine := Composition.machine first last
def heads (out : List Bool) (i : Fin 21) : ℕ := if i=4 then out.length else 0
def data (count index : ℕ) (out : List Bool) (i : Fin 21) : List Bool :=
  if i=0 then List.replicate count true else if i=1 then List.replicate index true else if i=4 then out else []
noncomputable def entry (count index : ℕ) (out : List Bool) :=
  (⟨machine.start,heads out,data count index out⟩ : Configuration 21 _)
def emitted (count index : ℕ) := PCPPNativePadding.emitted count++natWord index
def budget (count index : ℕ) := PCPPNativeColdPadding.budget count+1+PCPPNativeNaturalAppend.budget index

theorem append_run (count index : ℕ) (out : List Bool) :
    ∃ result,runFrom machine (budget count index) (entry count index out)=some result ∧
      result.steps ≤ budget count index ∧
      result.final.tapes 4=out++emitted count index ∧ result.final.heads 4=(out++emitted count index).length ∧
      result.final.tapes 0=List.replicate count true ∧ result.final.heads 0=0 ∧
      result.final.tapes 5=List.replicate index true ∧ result.final.heads 5=0 := by
  obtain ⟨base,hbase,baseSteps,baseHeads,baseTapes⟩ := PCPPNativeColdPadding.append_run count out
  obtain ⟨a,ha,_,as,ah,atapes,ak⟩ := RecoveryFocus.dock paddingSlots (by decide)
    PCPPNativeColdPadding.machine _ (heads out) (data count index out) _
    (by intro j; fin_cases j <;> rfl) (by intro j; fin_cases j <;> rfl) base hbase
  have footerInput (j : Fin 18) :
      a.final.heads (footerSlots j)=PCPPNativeNaturalAppend.heads (out++PCPPNativePadding.emitted count) j ∧
      a.final.tapes (footerSlots j)=PCPPNativeNaturalAppend.data index (out++PCPPNativePadding.emitted count) j := by
    by_cases hj0 : j=0
    · subst j
      exact ak 1 (by decide)
    by_cases hj17 : j=17
    · subst j
      exact ⟨(ah 3).trans (by rw [baseHeads]; rfl),(atapes 3).trans (by rw [baseTapes]; rfl)⟩
    have away : ∀ i,paddingSlots i≠footerSlots j := by
      intro i hi
      have h := congrArg Fin.val hi
      have hj : j.val≠0 := fun h => hj0 (Fin.ext h)
      simp only [footerSlots,hj0,hj17,if_false] at h
      fin_cases i <;> dsimp [paddingSlots] at h <;> omega
    have hk := ak (footerSlots j) away
    have h0 : footerSlots j≠0 := by simp [footerSlots,hj0,hj17,Fin.ext_iff]
    have h1 : footerSlots j≠1 := by simp [footerSlots,hj0,hj17,Fin.ext_iff]
    have h4 : footerSlots j≠4 := by
      have hj : j.val≠0 := fun h => hj0 (Fin.ext h)
      simp [footerSlots,hj0,hj17,Fin.ext_iff]
    simpa [heads,data,PCPPNativeNaturalAppend.heads,PCPPNativeNaturalAppend.data,hj0,hj17,h0,h1,h4] using hk
  obtain ⟨tail,htail,tailSteps,tailOut,tailHead,tailIndex,tailIndexHead⟩ :=
    PCPPNativeNaturalAppend.append_run index (out++PCPPNativePadding.emitted count)
  obtain ⟨b,hb,_,bs,bh,bt,bk⟩ := RecoveryFocus.dock footerSlots footer_injective
    PCPPNativeNaturalAppend.machine _ a.final.heads a.final.tapes _
    (fun j => (footerInput j).1) (fun j => (footerInput j).2) tail htail
  have joined := Composition.run_join first last _ _ _ a b ha hb
  refine ⟨Composition.joinedReceipt a b,joined,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ _
    unfold budget
    omega
  · exact (bt 17).trans (by simpa only [emitted,List.append_assoc] using tailOut)
  · exact (bh 17).trans (by simpa only [emitted,List.append_assoc] using tailHead)
  · exact ((bk 0 (by decide)).2).trans ((atapes 0).trans (by rw [baseTapes]; rfl))
  · exact ((bk 0 (by decide)).1).trans ((ah 0).trans (by rw [baseHeads]; rfl))
  · exact (bt 1).trans tailIndex
  · exact (bh 1).trans tailIndexHead

theorem budget_bound (count index : ℕ) : budget count index ≤ 1024*(count+index+1)^2 := by
  have hn := PCPPNativeNaturalAppend.budget_bound index
  unfold budget PCPPNativeColdPadding.budget
  nlinarith [Nat.zero_le (count*count),Nat.zero_le (count*index),Nat.zero_le (index*index)]

end NearCubicWires.RepairOrdinary.PCPPNativeDescriptorTail
