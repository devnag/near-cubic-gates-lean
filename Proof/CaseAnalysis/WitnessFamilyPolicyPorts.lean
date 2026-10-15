import Proof.CaseAnalysis.WitnessLegalTemplateCall

/-! The six legal metadata ports and existing mass bank form the exact
retained input needed by the family call. Their indices stay symbolic. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyPolicyPorts
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def header (e : ℕ) : Fin 6→Fin (LegalTemplate.tapes e):=
  ![LegalTemplate.templateSlots e 0,
    LegalTemplate.slots e (LegalPolicy.modeSlots e (ModeWire.dimensionSlots e 5)),
    LegalTemplate.slots e (LegalPolicy.wireSlot e),
    LegalTemplate.slots e (LegalPolicy.descriptionSlots e 91),
    LegalTemplate.slots e (LegalPolicy.termSlots e 42),
    LegalTemplate.slots e (LegalPolicy.massSlots e 1)]
def mass (e : ℕ) (i : Fin 94):=LegalTemplate.slots e (LegalPolicy.massSlots e (MassCold.nativeSlots i))
def port (e : ℕ) : Fin 100→Fin (LegalTemplate.tapes e):=
  Fin.addCases (m:=6) (n:=94) (motive:=fun _=>Fin (LegalTemplate.tapes e)) (header e) (mass e)

theorem header_val (e : ℕ) (i : Fin 6) : (header e i).val=
    (![0,10,63+2*e,LegalPolicy.M e+140,LegalPolicy.M e+47,LegalPolicy.M e+143] : Fin 6→ℕ) i:=by
  have hm:0<LegalPolicy.M e:=by dsimp [LegalPolicy.M,ModeWire.tapes,ModeDivide.tapes];omega
  fin_cases i
  · rfl
  · rfl
  · change (LegalTemplate.slots e (LegalPolicy.wireSlot e)).val=63+2*e
    simp only [LegalTemplate.slots,LegalPolicy.wire_val,if_neg (show 58+2*e≠0 by omega),Fin.val_natAdd]
    omega
  · change (LegalTemplate.slots e (LegalPolicy.descriptionSlots e 91)).val=LegalPolicy.M e+140
    have hv:(LegalPolicy.descriptionSlots e 91).val=LegalPolicy.M e+135:=by
      rw [LegalPolicy.description_val];simp
    simp only [LegalTemplate.slots,hv,if_neg (show LegalPolicy.M e+135≠0 by omega),Fin.val_natAdd]
    omega
  · change (LegalTemplate.slots e (LegalPolicy.termSlots e 42)).val=LegalPolicy.M e+47
    have hv:(LegalPolicy.termSlots e 42).val=LegalPolicy.M e+42:=rfl
    simp only [LegalTemplate.slots,hv,
      if_neg (show LegalPolicy.M e+42≠0 by omega),Fin.val_natAdd]
    omega
  · change (LegalTemplate.slots e (LegalPolicy.massSlots e 1)).val=LegalPolicy.M e+143
    have hv:(LegalPolicy.massSlots e 1).val=LegalPolicy.M e+138:=by
      rw [LegalPolicy.mass_val];simp
    simp only [LegalTemplate.slots,hv,if_neg (show LegalPolicy.M e+138≠0 by omega),Fin.val_natAdd]
    omega

theorem header_injective (e : ℕ) : Function.Injective (header e):=by
  intro i j he
  have hv:=congrArg Fin.val he
  rw [header_val,header_val] at hv
  have hm:LegalPolicy.M e=60+2*e:=by dsimp [LegalPolicy.M,ModeWire.tapes,ModeDivide.tapes];omega
  fin_cases i <;> fin_cases j <;> first | rfl | (dsimp at hv;omega)

theorem mass_injective (e : ℕ) : Function.Injective (mass e):=
  (LegalTemplate.slots_injective e).comp ((LegalPolicy.mass_injective e).comp MassCold.native_injective)

theorem mass_lower (e : ℕ) (i : Fin 94) : LegalPolicy.M e+150 ≤ (mass e i).val:=by
  have hn:8 ≤ (MassCold.nativeSlots i).val:=by
    dsimp only [MassCold.nativeSlots];split_ifs <;> omega
  have hpos:LegalPolicy.M e+137+(MassCold.nativeSlots i).val≠0:=by omega
  simp only [mass,LegalTemplate.slots,LegalPolicy.mass_val,if_neg (show (MassCold.nativeSlots i).val≠0 by omega),
    if_neg hpos,Fin.val_natAdd]
  omega

theorem port_injective (e : ℕ) : Function.Injective (port e):=by
  apply RecoveryColdAllCode.join_injective (header e) (mass e) (header_injective e) (mass_injective e)
  intro i j he
  have hv:=congrArg Fin.val he
  rw [header_val] at hv
  have hj:=mass_lower e j
  have hm:LegalPolicy.M e=60+2*e:=by dsimp [LegalPolicy.M,ModeWire.tapes,ModeDivide.tapes];omega
  fin_cases i <;> dsimp at hv <;> omega

theorem head_port (e : ℕ) (i : Fin 100) : LegalTemplate.heads e (port e i)=if i.val=0 then 1 else 0:=by
  refine Fin.addCases (m:=6) (n:=94) (fun j=>?_) (fun j=>?_) i
  · simp only [port,Fin.addCases_left,LegalTemplate.heads,header_val,Fin.val_castAdd]
    fin_cases j <;> simp
  · have hj:=mass_lower e j
    have hn:(mass e j).val≠0:=by omega
    simp only [port,Fin.addCases_right,LegalTemplate.heads,if_neg hn,Fin.val_natAdd,
      if_neg (show 6+j.val≠0 by omega)]

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.FamilyPolicyPorts
