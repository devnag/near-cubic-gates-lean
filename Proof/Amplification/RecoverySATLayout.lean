import Proof.Amplification.RecoverySATBank

/-! The nine copies give the literal RawSAT input and preserve the entire
already prepared raw-view bank, including its nonzero certificate cursor. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdSAT
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
open RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def satSlots (j : Fin 70) : Fin 172 := ⟨100+j.val,by omega⟩
theorem satSlots_injective : Function.Injective satSlots := by
  intro i j h
  have he := congrArg (fun k : Fin 172=>k.val) h
  apply Fin.ext
  change 100+i.val=100+j.val at he
  omega

theorem low_retained (bits word : List Bool) (a : Fin 172→List Bool) (i : Fin 172)
    (hi : i.val<100) : stage9 bits word a i=a i := by
  have hn : i≠128 ∧ i≠100 ∧ i≠137 ∧ i≠138 ∧ i≠142 ∧ i≠130 ∧ i≠136 ∧ i≠121 ∧ i≠163 ∧ i≠170 := by
    simp only [ne_eq,Fin.ext_iff]
    omega
  simp only [stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,put]
  simp only [Function.update_of_ne hn.1,Function.update_of_ne hn.2.1,
    Function.update_of_ne hn.2.2.1,Function.update_of_ne hn.2.2.2.1,
    Function.update_of_ne hn.2.2.2.2.1,Function.update_of_ne hn.2.2.2.2.2.1,
    Function.update_of_ne hn.2.2.2.2.2.2.1,Function.update_of_ne hn.2.2.2.2.2.2.2.1,
    Function.update_of_ne hn.2.2.2.2.2.2.2.2.1,Function.update_of_ne hn.2.2.2.2.2.2.2.2.2]

theorem low_tapes (bits word : List Bool) (a : Fin 172→List Bool) :
    (fun j : Fin 100=>stage9 bits word a (j.castAdd 72))=(fun j=>a (j.castAdd 72)) := by
  funext j
  exact low_retained bits word a _ j.isLt

theorem sat_tapes (bits word : List Bool) (a : Fin 172→List Bool)
    (ha : Sources bits word a) :
    (fun j=>stage9 bits word a (satSlots j))=tapes bits word := by
  funext j
  fin_cases j <;> simp [satSlots,tapes,stage9,stage8,stage7,stage6,stage5,stage4,stage3,stage2,stage1,put]
  all_goals exact ha.empty _ (by decide)

theorem sat_heads (pos : Nat) : (fun j=>heads pos (satSlots j))=(fun _ : Fin 70=>0) := by
  funext j
  simp [heads,satSlots,Fin.addCases]

theorem bank_native {s : Nat} (bits word : List Bool) (pos : Nat) (a : Fin 172→List Bool)
    (ha : Sources bits word a) (q : Fin s) :
    ZeroPadding.config (caps bits word)
      ⟨q,(fun j=>heads pos (satSlots j)),(fun j=>stage9 bits word a (satSlots j))⟩=(state bits word).cfg q := by
  rw [sat_heads,sat_tapes bits word a ha]
  exact native_layout bits word q

theorem sources_of_return (bits word : List Bool) (h : Fin 100→Nat) (a : Fin 100→List Bool)
    (ha : RecoveryColdView.Ready bits word h a)
    (hs : a 1=frame word) (hl : a 24=CompareMachine.word word.length)
    (hw : a 14=CompareMachine.word (width bits+1)) : Sources bits word (lift a) := by
  obtain ⟨table,tail,count,b,_,_,_,hb,_,_,_,ht⟩ := ha
  constructor
  · exact hs
  · change a 2=_
    rw [ht,boot_low bits b 2 (by decide)]
    exact hb.width
  · change a 6=_
    rw [ht,boot_low bits b 6 (by decide)]
    exact hb.code
  · change a 10=_
    rw [ht,boot_low bits b 10 (by decide)]
    exact hb.zero
  · exact hw
  · change a 16=_
    rw [ht,boot_low bits b 16 (by decide)]
    exact hb.erase
  · change a 21=_
    rw [ht,boot_low bits b 21 (by decide)]
    exact hb.cap
  · exact hl
  · intro i hi
    simp [lift,Fin.addCases,show ¬i.val<100 by omega]

end NearCubicWires.RepairOrdinary.RecoveryColdSAT
