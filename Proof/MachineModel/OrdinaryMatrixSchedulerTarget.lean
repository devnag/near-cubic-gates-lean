import Proof.MachineModel.OrdinaryMatrixScoreBatchTarget

/-! The actual row caller supplies a canonical request on tape zero and
blank local work. It pays clear/copy when reusing that finite workspace.
The older arbitrary-dirty ReusableTarget is not needed by this consumer. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreBatch
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- Full ordinary raw-block producer at its actual cold caller boundary.
All sign/bit planes, including p=0, are executed by one finite program.
The raw packet output is rewound once at the end; the original framed
request is retained. Finite local support supports the caller's paid reuse. -/
structure ColdScheduler (source : WilliamsAlgorithm) where
  program : Program
  coefficient : ℕ
  exponent : ℕ
  coefficientPositive : 0<coefficient
  sourceExponentPaid : source.logExponent≤exponent
  runs : ∀ r : Request,∃ actual : ExecutionReceipt program.tapeCount program.stateCount,
    run program.machine (coefficient*(r.U+1)^2*(r.d+r.p+1)^exponent)
      (program.inputTapes (word r))=some actual ∧
    actual.final.tapes program.outputTape=output r ∧
    actual.final.tapes ⟨0,by have h:=program.twoTapes; omega⟩=physicalInput r ∧
    (∀ i,actual.final.heads i=0) ∧
    (∀ i,(actual.final.tapes i).length≤coefficient*(r.U+1)^2*(r.d+r.p+1)^exponent) ∧
    actual.steps≤coefficient*(r.U+1)^2*(r.d+r.p+1)^exponent

end NearCubicWires.RepairOrdinary.MatrixScoreBatch
