import Proof.CaseAnalysis.RecoveryRowPacketAppend

/-! The exact C-backed fields append directly to the existing prototype
port. Actual raw scalar and width tapes remain available after every call. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
open LocalBitMultitape Composition RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def paddedSlots (source width : Fin 88) : Fin 4→Fin 88:=![source,75,width,73]
noncomputable def paddedField (source width : Fin 88):=
  RecoveryFocus.machine (paddedSlots source width) RecoveryBoundedRowPacketPadded.machine

theorem padded_run (source width : Fin 88) (bits : List Bool) (w B : ℕ) (out : List Bool)
    (H : Fin 88→ℕ) (A : Fin 88→List Bool)
    (hs : source≠75) (hl : source≠73) (hw : width≠75) (hwl : width≠73) (hsw : source≠width)
    (hHs : H source=0) (hHw : H width=0) (hHl : H 73=0)
    (hAs : A source=bits) (hAw : A width=List.replicate w true)
    (hAl : A 73=List.replicate B false) (hb : bits.length≤w) (hB : 2*w+2≤B) :
    Appends (paddedField source width) (4*w+4) H A out
      (out++frame (ZeroPadding.pad w bits)) := by
  have hinj : Function.Injective (paddedSlots source width) := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [paddedSlots]
  obtain ⟨p,pr,ps,ph,pt⟩:=RecoveryBoundedRowPacketPadded.padded_append_run bits out w B hb hB
  obtain ⟨r,rr,_,rs,rh,rt,rkeep⟩:=RecoveryFocus.dock (paddedSlots source width) hinj
    RecoveryBoundedRowPacketPadded.machine _ (outputHeads H out) (outputData A out)
    (RecoveryBoundedRowPacketPadded.input bits out w B)
    (by intro j;fin_cases j
        · change Function.update H 75 out.length source=0
          rw [Function.update_of_ne hs]
          exact hHs
        · change out.length=out.length+2*0
          omega
        · change Function.update H 75 out.length width=0
          rw [Function.update_of_ne hw]
          exact hHw
        · change Function.update H 75 out.length 73=0
          rw [Function.update_of_ne (by decide)]
          exact hHl)
    (by intro j;fin_cases j
        · change Function.update A 75 out source=ZeroPadding.pad 0 bits
          rw [Function.update_of_ne hs,ZeroPadding.pad_zero]
          exact hAs
        · change out=ZeroPadding.pad 0 (out++Streaming.marks (RecoveryColdPaddedCopy.data bits 0))
          rw [ZeroPadding.pad_zero]
          exact (List.append_nil out).symm
        · change Function.update A 75 out width=ZeroPadding.pad 0 (List.replicate w true)
          rw [Function.update_of_ne hw,ZeroPadding.pad_zero]
          exact hAw
        · change Function.update A 75 out 73=ZeroPadding.pad B []
          rw [Function.update_of_ne (by decide),hAl]
          simp only [ZeroPadding.pad,List.length_nil,Nat.sub_zero,List.nil_append]) p pr
  refine ⟨r,rr,rs.le.trans ps,?_,?_⟩
  · funext i
    by_cases hi : ∃ j,paddedSlots source width j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rh j,ph]
      fin_cases j
      · change 0=Function.update H 75 _ source
        rw [Function.update_of_ne hs]
        exact hHs.symm
      · rfl
      · change 0=Function.update H 75 _ width
        rw [Function.update_of_ne hw]
        exact hHw.symm
      · change 0=Function.update H 75 _ 73
        rw [Function.update_of_ne (by decide)]
        exact hHl.symm
    · rw [(rkeep i (by intro j he;exact hi ⟨j,he⟩)).1]
      have h75 : i≠75:=fun he=>hi ⟨1,he.symm⟩
      simp only [outputHeads,Function.update_of_ne h75]
  · funext i
    by_cases hi : ∃ j,paddedSlots source width j=i
    · obtain ⟨j,rfl⟩:=hi
      rw [rt j,pt]
      fin_cases j
      · change bits=Function.update A 75 _ source
        rw [Function.update_of_ne hs]
        exact hAs.symm
      · rfl
      · change List.replicate w true=Function.update A 75 _ width
        rw [Function.update_of_ne hw]
        exact hAw.symm
      · change List.replicate B false=Function.update A 75 _ 73
        rw [Function.update_of_ne (by decide)]
        exact hAl.symm
    · rw [(rkeep i (by intro j he;exact hi ⟨j,he⟩)).2]
      have h75 : i≠75:=fun he=>hi ⟨1,he.symm⟩
      simp only [outputData,Function.update_of_ne h75]

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
