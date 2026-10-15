import Proof.PCP.PCPPNativeQueryIterationLayout

/-! Dock the paid counted row loader into the same reusable query bank.
The hierarchy source cursor advances once; the resulting padded cache is
exactly the input consumed by the checked whole-query emitter. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeQueryIteration
open LocalBitMultitape SourceInterfaces PCPPNativeNodeMachine
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem load_run {n r : ℕ} (pre suffix bits : List Bool) (base C F G : ℕ)
    (projection : Fin n → ProjectedRandomBit r) (out : List Bool)
    (hG : (rowCache projection).length+3*n+4 ≤ G) :
    ∃ result,runFrom load (PCPPNativeQueryRowLoad.budget (rowFields projection))
      ⟨load.start,heads pre.length out,data bits [] (pre++rowCache projection++suffix) base C F G out n⟩=some result ∧
      result.steps=PCPPNativeQueryRowLoad.budget (rowFields projection) ∧
      (∀ j : Fin 171,result.final.heads (querySlots j)=PCPPNativeQueryReusable.heads out j ∧
        result.final.tapes (querySlots j)=PCPPNativeQueryReusable.data bits (rowCache projection) base C F G out j) ∧
      result.final.heads 171=pre.length+(rowCache projection).length ∧
      result.final.tapes 171=pre++rowCache projection++suffix ∧
      result.final.heads 172=1 ∧ result.final.tapes 172=UnaryTemplate.tape n := by
  have hlen : (rowFields projection).length=n := by simp only [rowFields,List.length_ofFn]
  obtain ⟨raw,hr,rs,rh,rt⟩ := PCPPNativeQueryRowLoad.row_run pre suffix (rowFields projection) G
    (by simpa only [hlen,rowCache] using hG)
  rw [hlen] at hr rt
  obtain ⟨result,run,_,steps,hh,ht,keep⟩ := RecoveryFocus.dock loadSlots load_injective
    PCPPNativeQueryRowLoad.machine _ (heads pre.length out)
    (data bits [] (pre++rowCache projection++suffix) base C F G out n) _
    (fun j => (load_input bits (pre++rowCache projection++suffix) pre.length base C F G out n j).1)
    (fun j => (load_input bits (pre++rowCache projection++suffix) pre.length base C F G out n j).2) raw hr
  refine ⟨result,run,steps.trans rs,?_,(hh 0).trans (by rw [rh]; rfl),
    (ht 0).trans (by rw [rt]; rfl),(hh 2).trans (by rw [rh]; rfl),(ht 2).trans (by rw [rt]; rfl)⟩
  intro i
  by_cases h1 : i=1
  · subst i
    exact ⟨(hh 1).trans (by rw [rh]; rfl),(ht 1).trans (by rw [rt]; rfl)⟩
  · by_cases h6 : i=6
    · subst i
      exact ⟨(hh 3).trans (by rw [rh]; rfl),(ht 3).trans (by rw [rt]; rfl)⟩
    · have hk := keep (querySlots i) (load_low_away i h1 h6)
      constructor
      · simpa only [querySlots,heads,Fin.addCases_left] using hk.1
      · simpa only [querySlots,data,Fin.addCases_left,PCPPNativeQueryReusable.data,h1,ite_false] using hk.2

end NearCubicWires.RepairOrdinary.PCPPNativeQueryIteration
