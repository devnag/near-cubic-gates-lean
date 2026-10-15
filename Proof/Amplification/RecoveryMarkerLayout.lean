import Proof.Amplification.RecoveryMarkerBank

/-! The actual six-copy result supplies the57 marker tapes and retains the
whole cold front. Its sources follow from that front's original cold run. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdMarker
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def markerSlots (j : Fin 57) : Fin 338 := ⟨279+j.val,by omega⟩
theorem markerSlots_injective : Function.Injective markerSlots := by
  intro i j he
  have hv := congrArg Fin.val he
  apply Fin.ext
  change 279+i.val=279+j.val at hv
  omega

theorem bank_tapes (bits : List Bool) (a : Fin 279→List Bool) :
    (fun j=>stage6 bits a (markerSlots j))=tapes bits := by
  funext j
  fin_cases j <;> simp [markerSlots,tapes,stage6,stage5,stage4,stage3,stage2,stage1,put,lift,Fin.addCases]

theorem bank_heads (h : Fin 279→Nat) :
    (fun j=>heads h (markerSlots j))=(fun _ : Fin 57=>0) := by
  funext j
  simp [heads,markerSlots,Fin.addCases]

theorem retained (bits : List Bool) (a : Fin 279→List Bool) (i : Fin 279) :
    stage6 bits a (i.castAdd 59)=a i := by
  have hn : i.castAdd 59≠279 ∧ i.castAdd 59≠304 ∧ i.castAdd 59≠334 ∧
      i.castAdd 59≠308 ∧ i.castAdd 59≠300 ∧ i.castAdd 59≠329 ∧ i.castAdd 59≠336 := by
    simp only [ne_eq,Fin.ext_iff,Fin.val_castAdd]
    change i.val≠279 ∧ i.val≠304 ∧ i.val≠334 ∧ i.val≠308 ∧
      i.val≠300 ∧ i.val≠329 ∧ i.val≠336
    omega
  simp only [stage6,stage5,stage4,stage3,stage2,stage1,put,
    Function.update_of_ne hn.1,Function.update_of_ne hn.2.1,
    Function.update_of_ne hn.2.2.1,Function.update_of_ne hn.2.2.2.1,
    Function.update_of_ne hn.2.2.2.2.1,Function.update_of_ne hn.2.2.2.2.2.1,
    Function.update_of_ne hn.2.2.2.2.2.2,lift,Fin.addCases_left]

theorem sources (bits word : List Bool) (h : Fin 279→Nat) (a : Fin 279→List Bool)
    (ha : RecoveryColdFront.Prepared bits word h a) : Sources bits h a := by
  obtain ⟨k,g,b,_,_,hr,_⟩ := ha
  obtain ⟨pos,c,hc,_,hh,ht⟩ := hr
  have h2 := congrFun ht (2 : Fin 172)
  have h6 := congrFun ht (6 : Fin 172)
  have h10 := congrFun ht (10 : Fin 172)
  have h16 := congrFun ht (16 : Fin 172)
  rw [RecoveryColdSAT.low_retained bits word c 2 (by decide)] at h2
  rw [RecoveryColdSAT.low_retained bits word c 6 (by decide)] at h6
  rw [RecoveryColdSAT.low_retained bits word c 10 (by decide)] at h10
  rw [RecoveryColdSAT.low_retained bits word c 16 (by decide)] at h16
  exact ⟨h2.trans hc.width,h6.trans hc.code,h10.trans hc.zero,h16.trans hc.erase,
    congrFun hh 2,congrFun hh 6,congrFun hh 10,congrFun hh 16⟩

theorem bank_native {s : Nat} (bits : List Bool) (h : Fin 279→Nat)
    (a : Fin 279→List Bool) (q : Fin s) :
    ZeroPadding.config (caps bits)
      ⟨q,(fun j=>heads h (markerSlots j)),(fun j=>stage6 bits a (markerSlots j))⟩=
        (state bits).cfg q := by
  rw [bank_tapes,bank_heads]
  exact native_layout bits q

end NearCubicWires.RepairOrdinary.RecoveryColdMarker
