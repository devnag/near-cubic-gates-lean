import Proof.PCP.PCPPNativeColdMetadata

/-! Both original native header fields are appended from actual raw domain
and padded-size counters. Their retained raw copies feed the source/cache
caller; the descriptor cursor remains at the end of the printed header. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeColdHeader
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def firstSlots (i : Fin 18) : Fin 35 := if i=0 then 0 else ⟨i.val+1,by omega⟩
def lastSlots (i : Fin 18) : Fin 35 := if i=0 then 1 else if h17 : i=17 then 18 else ⟨i.val+18,by
  have h := i.isLt
  have hn : i.val≠17 := fun he => h17 (Fin.ext he)
  omega⟩
theorem first_injective : Function.Injective firstSlots := by decide
theorem last_injective : Function.Injective lastSlots := by decide
noncomputable def first := RecoveryFocus.machine firstSlots PCPPNativeNaturalAppend.machine
noncomputable def last := RecoveryFocus.machine lastSlots PCPPNativeNaturalAppend.machine
noncomputable def machine := Composition.machine first last
def data (domain size : ℕ) (out : List Bool) (i : Fin 35) : List Bool :=
  if i=0 then List.replicate domain true else if i=1 then List.replicate size true else if i=18 then out else []
def heads (out : List Bool) (i : Fin 35) : ℕ := if i=18 then out.length else 0
noncomputable def entry (domain size : ℕ) (out : List Bool) :=
  (⟨machine.start,heads out,data domain size out⟩ : Configuration 35 _)
def emitted (domain size : ℕ) := natWord domain++natWord size
def budget (domain size : ℕ) := PCPPNativeNaturalAppend.budget domain+1+PCPPNativeNaturalAppend.budget size

theorem first_input (domain size : ℕ) (out : List Bool) (j : Fin 18) :
    heads out (firstSlots j)=PCPPNativeNaturalAppend.heads out j ∧
    data domain size out (firstSlots j)=PCPPNativeNaturalAppend.data domain out j := by
  fin_cases j <;> simp [heads,data,firstSlots,PCPPNativeNaturalAppend.heads,PCPPNativeNaturalAppend.data]

theorem append_run (domain size : ℕ) (out : List Bool) :
    ∃ result,runFrom machine (budget domain size) (entry domain size out)=some result ∧
      result.steps ≤ budget domain size ∧
      result.final.tapes 18=out++emitted domain size ∧
      result.final.heads 18=(out++emitted domain size).length ∧
      result.final.tapes 2=List.replicate domain true ∧ result.final.heads 2=0 ∧
      result.final.tapes 19=List.replicate size true ∧ result.final.heads 19=0 := by
  obtain ⟨base,hbase,baseSteps,baseOut,baseHead,baseDomain,baseDomainHead⟩ :=
    PCPPNativeNaturalAppend.append_run domain out
  obtain ⟨a,ha,_,as,ah,atapes,ak⟩ := RecoveryFocus.dock firstSlots first_injective
    PCPPNativeNaturalAppend.machine _ (heads out) (data domain size out) _
    (fun j => (first_input domain size out j).1) (fun j => (first_input domain size out j).2) base hbase
  have lastInput (j : Fin 18) :
      a.final.heads (lastSlots j)=PCPPNativeNaturalAppend.heads (out++natWord domain) j ∧
      a.final.tapes (lastSlots j)=PCPPNativeNaturalAppend.data size (out++natWord domain) j := by
    by_cases hj0 : j=0
    · subst j
      exact ak 1 (by decide)
    by_cases hj17 : j=17
    · subst j
      exact ⟨(ah 17).trans baseHead,(atapes 17).trans baseOut⟩
    have away : ∀ i,firstSlots i≠lastSlots j := by
      intro i hi
      have h := congrArg Fin.val hi
      have hj : j.val≠0 := fun h => hj0 (Fin.ext h)
      simp only [firstSlots,lastSlots,hj0,hj17,if_false] at h
      split_ifs at h <;> dsimp at h <;> omega
    have hk := ak (lastSlots j) away
    have h0 : lastSlots j≠0 := by simp [lastSlots,hj0,hj17,Fin.ext_iff]
    have h1 : lastSlots j≠1 := by simp [lastSlots,hj0,hj17,Fin.ext_iff]
    have h18 : lastSlots j≠18 := by
      have hj : j.val≠0 := fun h => hj0 (Fin.ext h)
      simp [lastSlots,hj0,hj17,Fin.ext_iff]
    simpa [heads,data,PCPPNativeNaturalAppend.heads,PCPPNativeNaturalAppend.data,hj0,hj17,h0,h1,h18] using hk
  obtain ⟨tail,htail,tailSteps,tailOut,tailHead,tailSize,tailSizeHead⟩ :=
    PCPPNativeNaturalAppend.append_run size (out++natWord domain)
  obtain ⟨b,hb,_,bs,bh,bt,bk⟩ := RecoveryFocus.dock lastSlots last_injective
    PCPPNativeNaturalAppend.machine _ a.final.heads a.final.tapes _
    (fun j => (lastInput j).1) (fun j => (lastInput j).2) tail htail
  have joined := Composition.run_join first last _ _ _ a b ha hb
  refine ⟨Composition.joinedReceipt a b,joined,?_,?_,?_,?_,?_,?_,?_⟩
  · change a.steps+1+b.steps ≤ _
    unfold budget
    omega
  · exact (bt 17).trans (by simpa only [emitted,List.append_assoc] using tailOut)
  · exact (bh 17).trans (by simpa only [emitted,List.append_assoc] using tailHead)
  · exact ((bk 2 (by decide)).2).trans ((atapes 1).trans baseDomain)
  · exact ((bk 2 (by decide)).1).trans ((ah 1).trans baseDomainHead)
  · exact (bt 1).trans tailSize
  · exact (bh 1).trans tailSizeHead

theorem budget_bound (domain size : ℕ) : budget domain size ≤ 1024*(domain+size+1)^2 := by
  have hd := PCPPNativeNaturalAppend.budget_bound domain
  have hs := PCPPNativeNaturalAppend.budget_bound size
  unfold budget
  nlinarith [Nat.zero_le (domain*size),Nat.zero_le (domain*domain),Nat.zero_le (size*size)]

end NearCubicWires.RepairOrdinary.PCPPNativeColdHeader
