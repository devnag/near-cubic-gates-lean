import Proof.MachineModel.OrdinaryMatrixMaskSemantics

/-! Additional physical fields of the existing coefficient header run (`MatrixCoefficientHeaders.full`).
The same receipt as `headers_run`, listing the retained unary `p` (tape 22) with the width, `d` and
`Gates` sentinels; no parsing is repeated. -/
namespace NearCubicWires.RepairOrdinary.MatrixCoefficientRetainedHeaders
open LocalBitMultitape MatrixScoreBatch SignedSortKey RepairRepresentation
open MatrixCoefficientHeaders
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem headers_fields (r : Request) : ∃ actual,
    run full (budget r) (input r)=some actual ∧
    actual.final.tapes 0=physicalInput r ∧ actual.final.heads 0=0 ∧
    actual.final.tapes 1=word r ∧ actual.final.heads 1=(header r).length ∧
    actual.final.tapes 8=UnaryTemplate.tape r.width ∧ actual.final.heads 8=1 ∧
    actual.final.tapes 12=UnaryTemplate.tape r.d ∧ actual.final.heads 12=0 ∧
    actual.final.tapes 32=UnaryTemplate.tape r.Gates ∧ actual.final.heads 32=1 ∧
    actual.final.tapes 22=UnaryTemplate.tape r.p ∧ actual.final.heads 22=1 ∧
    actual.steps≤budget r := by
  obtain ⟨a,ha,t0,h0,t1,h1,t8,h8,t12,h12,t22,h22,t32,h32,s⟩ := headers_run r
  exact ⟨a,ha,t0,h0,t1,h1,t8,h8,t12,h12,t32,h32,t22,h22,s⟩

end NearCubicWires.RepairOrdinary.MatrixCoefficientRetainedHeaders
