import Proof.Amplification.RecoveryPCPFormulaResumeLayout

/-! The actual scalar outputs fill exactly the ten data ports of the
original formula constructor; its remaining tapes are physically blank. -/
namespace NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCold
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces VerifierDecoding ProjectionNormalization CanonicalRecoveryLanguage
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem scalar_input (p : RawProjectionPCP) (R Q : Nat) (i : Fin 66) :
    input p R Q (scalarSlots i)=RecoveryPCPFormulaResumeColdScalars.input R.bits Q.bits i := by
  fin_cases i <;> rfl

theorem installed_other (p : RawProjectionPCP) (R Q : Nat) (out : Fin 66→List Bool)
    (i : Fin 785) (hi : (66 : Nat)≤(i : Fin 785).val) :
    install scalarSlots (input p R Q) out i=input p R Q i := by
  apply install_other
  intro j h
  have hv:=congrArg (fun i : Fin 785=>i.val) h
  have hj:=j.isLt
  change j.val=i.val at hv
  omega

def dockedLookup (p : RawProjectionPCP) (R Q : Nat) (out : Fin 66→List Bool) (i : Fin 716) : List Bool :=
  if i.val=272 then DedupBytes.fields p else
  if i.val=278 then out 37 else
  if i.val=280 then CompareMachine.word (Codec.clauses p).length else
  if i.val=309 then QueryBytes.framedCodes (normalizedRows p R Q).flatten else
  if i.val=310 then out 64 else if i.val=312 then out 17 else
  if i.val=314 then out 3 else if i.val=315 then out 31 else
  if i.val=318 then out 58 else if i.val=560 then out 61 else []

theorem scalar_data (p : RawProjectionPCP) (R Q : Nat) (out : Fin 66→List Bool) (i : Fin 716) :
    install scalarSlots (input p R Q) out (formulaSlots i)=dockedLookup p R Q out i := by
  by_cases h272 : i.val=272
  · have he : i=(272 : Fin 716) := Fin.ext h272
    subst i
    change install scalarSlots (input p R Q) out 67=_
    rw [installed_other p R Q out 67 (by decide)]
    rfl
  by_cases h278 : i.val=278
  · have he : i=(278 : Fin 716) := Fin.ext h278
    subst i
    exact install_slot scalarSlots scalar_injective (input p R Q) out 37
  by_cases h280 : i.val=280
  · have he : i=(280 : Fin 716) := Fin.ext h280
    subst i
    change install scalarSlots (input p R Q) out 68=_
    rw [installed_other p R Q out 68 (by decide)]
    rfl
  by_cases h309 : i.val=309
  · have he : i=(309 : Fin 716) := Fin.ext h309
    subst i
    change install scalarSlots (input p R Q) out 66=_
    rw [installed_other p R Q out 66 (by decide)]
    rfl
  by_cases h310 : i.val=310
  · have he : i=(310 : Fin 716) := Fin.ext h310
    subst i
    exact install_slot scalarSlots scalar_injective (input p R Q) out 64
  by_cases h312 : i.val=312
  · have he : i=(312 : Fin 716) := Fin.ext h312
    subst i
    exact install_slot scalarSlots scalar_injective (input p R Q) out 17
  by_cases h314 : i.val=314
  · have he : i=(314 : Fin 716) := Fin.ext h314
    subst i
    exact install_slot scalarSlots scalar_injective (input p R Q) out 3
  by_cases h315 : i.val=315
  · have he : i=(315 : Fin 716) := Fin.ext h315
    subst i
    exact install_slot scalarSlots scalar_injective (input p R Q) out 31
  by_cases h318 : i.val=318
  · have he : i=(318 : Fin 716) := Fin.ext h318
    subst i
    exact install_slot scalarSlots scalar_injective (input p R Q) out 58
  by_cases h560 : i.val=560
  · have he : i=(560 : Fin 716) := Fin.ext h560
    subst i
    exact install_slot scalarSlots scalar_injective (input p R Q) out 61
  simp only [formulaSlots,dockedLookup,h272,h278,h280,h309,h310,h312,h314,h315,h318,h560,ite_false]
  rw [installed_other p R Q out _ (by change 66≤69+i.val; omega)]
  simp only [input]
  split_ifs <;> first | rfl | omega

end NearCubicWires.RepairSource.RecoveryPCPFormulaResumeCold
