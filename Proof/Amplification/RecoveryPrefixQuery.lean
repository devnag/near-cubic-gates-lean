import Proof.Amplification.RecoveryPrefixSentinel

/-! The exact sentinel query is consumed by the actual oracle trace. The
answer is equivalent to satisfiability of precisely the chosen prefix followed
by zero; the high true sentinel is outside every constrained coordinate. -/
namespace NearCubicWires.RepairSource.RecoveryPrefix
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryQuery RecoveryQueryKernel
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem zero_query (cap log : Nat) (flat : Bool) (payload : Nat) (formula : EncodedCNF)
    (xs : List Bool) (ambient : Fin 357→List Bool)
    (paddedPayload paddedCommitted paddedCount : List Bool)
    (hdecode : PayloadDecodes flat payload formula)
    (hcap : capacity payload (commitment xs) (queryCount xs) ≤ cap)
    (hb : Bounded cap ambient) (hd : ambient 3=List.replicate cap true)
    (hl : ambient 4=List.replicate log false) (hz : log ≤ cap+1)
    (hp : ambient 0=frame payload.bits++paddedPayload)
    (ha : ambient 1=frame (xs++[false,true])++paddedCommitted)
    (hn : ambient 2=frame (xs.length+1).bits++paddedCount) :
    ∃ cost ≤ 18*cap,∃ out : Fin 357→List Bool,
      OrdinaryOracleTrace RecoveryOracle.correctedSat (RecoveryQueryStep.program flat) cost
        (RecoveryQueryStep.start flat ambient) (RecoveryQueryStep.stopped flat out) ∧
      (readTapeBit (out RecoveryQueryStep.answerSlot) 0=true ↔
        formula.all (fun clause=>clause.length=3)=true ∧
          ∃ assignment : Nat→Bool,
            (∀ i<xs.length+1,assignment i=(xs++[false]).getD i false) ∧
            TseitinCNF.formulaEval assignment formula=true) ∧
      (∀ i : Fin 357,i.val<3 → out i=ambient i) ∧
      out 3=List.replicate cap true ∧ out 4=List.replicate (cap+1) false ∧ Bounded cap out := by
  obtain ⟨cost,hcost,out,htrace,hanswer,hkeep,hdriver,hlog,hbound⟩ :=
    RecoveryQueryStep.step_trace cap log flat payload (commitment xs) (queryCount xs)
      ambient paddedPayload paddedCommitted paddedCount hcap hb hd hl hz hp
      (by simpa only [commitment_bits] using ha) hn
  refine ⟨cost,hcost,out,htrace,?_,hkeep,hdriver,hlog,hbound⟩
  rw [hanswer]
  exact query_iff flat payload formula xs hdecode

end NearCubicWires.RepairSource.RecoveryPrefix
