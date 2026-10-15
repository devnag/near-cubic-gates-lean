import Proof.Amplification.RecoveryCaseOnePaddedEvaluationLayout

/-! The original generated table is evaluated at the physically cropped
target address, computing exactly the paper's ignored-variable padding. -/
namespace NearCubicWires.RepairSource.RecoveryCaseOnePaddedEvaluation
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound
open SourceInterfaces ExecutableInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

theorem ready {n target : Nat} (f : BoolFunction n) (hn : n≤target) (address : BitInput target) :
    ∃ out,ClockJoin.ReadyRun machine (budget f hn address)
      (input (RecoveryCaseOneEvaluation.schema f) (List.ofFn address)) out ∧
      out 44=frame (RecoveryPipeline.padCore f hn address).toNat.bits := by
  let schema:=RecoveryCaseOneEvaluation.schema f
  let word:=List.ofFn address
  obtain ⟨prepared,hprepared,preparedSchema,preparedWidth,preparedAddress⟩:=
    RecoveryCaseOneCropPrepare.ready n (boolFunctionTable f) word
  let a:=install prepareSlots (input schema word) prepared
  have ha:=hprepared.focus prepareSlots prepare_injective (input schema word) (by intro i; rfl)
  have a0 : a 0=frame schema := (install_slot prepareSlots prepare_injective _ prepared 0).trans preparedSchema
  have a15 : a 15=UnaryTemplate.tape n := (install_slot prepareSlots prepare_injective _ prepared 15).trans preparedWidth
  have a17 : a 17=frame word := (install_slot prepareSlots prepare_injective _ prepared 17).trans preparedAddress
  have fresh (i : Fin 46) (hi : (18 : Nat)≤(i : Fin 46).val) : a i=[] := by
    dsimp only [a]
    rw [install_other _ _ _ _ (by
      intro j h
      have hv:=congrArg (fun z : Fin 46=>z.val) h
      have hj:=j.isLt
      change j.val=i.val at hv
      omega)]
    simp only [input]
    split_ifs <;> first | rfl | omega
  have hcrop:=RecoveryCaseOneAddressCrop.ready word n (by simpa [word] using hn)
  let b:=install cropSlots a (RecoveryCaseOneAddressCrop.output word n)
  have hb:=hcrop.focus cropSlots crop_injective a (by
    intro i; fin_cases i
    · exact a17
    · exact fresh 18 (by decide)
    · exact a15
    · exact fresh 19 (by decide))
  have b0 : b 0=frame schema := (install_other cropSlots a _ 0 (by decide)).trans a0
  have b18 : b 18=frame (List.ofFn (low hn address)) := by
    rw [low_word]
    exact install_slot cropSlots crop_injective a _ 1
  obtain ⟨evaluated,hevaluated,evaluatedValue⟩:=RecoveryCaseOneEvaluation.ready f (low hn address)
  have hc:=hevaluated.focus evalSlots eval_injective b (by
    intro i
    by_cases h0 : i.val=0
    · simp only [evalSlots,RecoveryCaseOneEvaluation.input,h0,ite_true]
      exact b0
    · by_cases h1 : i.val=1
      · simp only [evalSlots,RecoveryCaseOneEvaluation.input,h1,ite_true]
        exact b18
      · simp only [evalSlots,RecoveryCaseOneEvaluation.input,h0,h1,ite_false]
        dsimp only [b]
        rw [install_other _ _ _ _ (by
          intro j h
          have hv:=congrArg (fun z : Fin 46=>z.val) h
          fin_cases j <;> norm_num [cropSlots] at hv <;> omega)]
        exact fresh _ (by simp))
  have hab:=ClockJoin.join first middle _ _ _ _ _ ha hb
  have whole:=ClockJoin.join (Composition.machine first middle) last _ _ _ _ _ hab hc
  refine ⟨_,whole,?_⟩
  rw [padded_value]
  exact (install_slot evalSlots eval_injective b evaluated 26).trans evaluatedValue

end
end NearCubicWires.RepairSource.RecoveryCaseOnePaddedEvaluation
