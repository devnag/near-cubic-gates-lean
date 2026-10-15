import Proof.PCP.PCPPNativeQueryValue

/-! Append the one shared query-output negation using the original footer's
actual raw index and the existing cleared node workspace. Only output5 changes. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQuery
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem tail_input (bits queries : List Bool) (cursor base position C F index : ℕ) (out : List Bool)
    (ah : Fin 168 → ℕ) (atapes : Fin 168 → List Bool)
    (hlow : lowFrame bits queries cursor base position C F out ah atapes)
    (hindex : ah 164=0 ∧ atapes 164=List.replicate index true) (j : Fin 24) :
    ah (tailSlots j)=PCPPNativeAddressReusable.heads out j ∧
      atapes (tailSlots j)=PCPPNativeQueryTail.paddedData base index C F out j := by
  by_cases hj : j=1
  · subst j; exact hindex
  · have hb : (tailSlots j).val < 122 := by
      fin_cases j <;> first | contradiction | decide
    let k : Fin 122 := ⟨(tailSlots j).val,hb⟩
    have he : k.castAdd 46=tailSlots j := by apply Fin.ext; rfl
    have h := hlow k
    rw [he] at h
    have hd : PCPPNativeNodeReusable.heads cursor out k=PCPPNativeAddressReusable.heads out j ∧
        PCPPNativeNodeReusable.data bits queries base position C F out k=PCPPNativeQueryTail.paddedData base index C F out j := by
      fin_cases j <;> simp_all [k,tailSlots,PCPPNativeNodeReusable.heads,PCPPNativeNodeReusable.data,
        PCPPNativeAddressReusable.heads,PCPPNativeQueryTail.paddedData]
    exact ⟨h.1.trans hd.1,h.2.trans hd.2⟩

theorem tail_run (bits queries : List Bool) (cursor base position C F index : ℕ) (out : List Bool)
    (ah : Fin 168 → ℕ) (atapes : Fin 168 → List Bool)
    (hlow : lowFrame bits queries cursor base position C F out ah atapes)
    (hindex : ah 164=0 ∧ atapes 164=List.replicate index true)
    (hC : PCPPNativeAddressAppend.budget base index+1 ≤ C) (hCF : C+1 ≤ F) :
    ∃ result,runFrom tail (PCPPNativeQueryTail.budget base index C) ⟨tail.start,ah,atapes⟩=some result ∧
      result.steps ≤ PCPPNativeQueryTail.budget base index C ∧
      (∀ i,result.final.heads i=if i=5 then (out++PCPPNativeQueryTail.emitted base index).length else ah i) ∧
      (∀ i,result.final.tapes i=if i=5 then out++PCPPNativeQueryTail.emitted base index else atapes i) := by
  obtain ⟨raw,hr,rs,rh,rt⟩ := PCPPNativeQueryTail.padded_run base index C F out hC hCF
  obtain ⟨result,run,_,steps,hh,ht,keep⟩ := RecoveryFocus.dock tailSlots tail_injective
    PCPPNativeQueryTail.machine _ ah atapes _
    (fun j => (tail_input bits queries cursor base position C F index out ah atapes hlow hindex j).1)
    (fun j => (tail_input bits queries cursor base position C F index out ah atapes hlow hindex j).2) raw hr
  refine ⟨result,run,by omega,?_,?_⟩
  · intro i
    by_cases hi : i=5
    · subst i; rw [if_pos rfl]; exact (hh 20).trans (by rw [rh]; rfl)
    · rw [if_neg hi]
      by_cases hs : ∃ j,tailSlots j=i
      · rcases hs with ⟨j,rfl⟩
        have hj : j≠20 := by intro he; subst j; exact hi rfl
        have hsame : PCPPNativeAddressReusable.heads (out++PCPPNativeQueryTail.emitted base index) j=
            PCPPNativeAddressReusable.heads out j := by simp only [PCPPNativeAddressReusable.heads,hj,ite_false]
        exact (hh j).trans (by
          rw [rh]
          exact hsame.trans (tail_input bits queries cursor base position C F index out ah atapes hlow hindex j).1.symm)
      · exact (keep i (by intro j hj; exact hs ⟨j,hj⟩)).1
  · intro i
    by_cases hi : i=5
    · subst i; rw [if_pos rfl]; exact (ht 20).trans (by rw [rt]; rfl)
    · rw [if_neg hi]
      by_cases hs : ∃ j,tailSlots j=i
      · rcases hs with ⟨j,rfl⟩
        have hj : j≠20 := by intro he; subst j; exact hi rfl
        have hsame : PCPPNativeQueryTail.paddedData base index C F (out++PCPPNativeQueryTail.emitted base index) j=
            PCPPNativeQueryTail.paddedData base index C F out j := by simp only [PCPPNativeQueryTail.paddedData,hj,ite_false]
        exact (ht j).trans (by
          rw [rt]
          exact hsame.trans (tail_input bits queries cursor base position C F index out ah atapes hlow hindex j).2.symm)
      · exact (keep i (by intro j hj; exact hs ⟨j,hj⟩)).2

end NearCubicWires.RepairOrdinary.PCPPNativeQuery
