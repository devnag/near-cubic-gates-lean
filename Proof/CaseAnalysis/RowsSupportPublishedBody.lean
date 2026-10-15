import Proof.CaseAnalysis.RowsSupportBodyBounds
import Proof.CaseAnalysis.RowsCircuitBodyFields

/-! Either actual top publisher supplies the support-retaining body through
its same physical bank fields. The old reset scope remains bounded. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
open LocalBitMultitape RepairRepresentation ExtDecompositionBatch
open CloseoutRowsCircuitBottomLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem published_run (threshold : Bool) (C core retained : ℕ) (words : List (List Bool))
    (top out supports members bits : List Bool) (initial L W : ℕ) (A : Fin 1703 → List Bool)
    (F : CloseoutRowsCircuitBody.Fields threshold C core retained words top out members bits initial L W A) :
    ∃ B,Step (body threshold)
      (bodyBudget threshold C core retained top (descriptions core words initial words.length) words.length
        (wires threshold core 1 members words 0 words.length) L W)
      (Fin.addCases (m:=1703) (n:=1) (CloseoutRowsCircuitBottomEntry.heads threshold out initial 0) (fun _=>supports.length))
      (Fin.addCases (m:=1703) (n:=1) A (fun _=>supports))
      (Fin.addCases (m:=1703) (n:=1)
        (CloseoutRowsCircuitColdEntry.heads
          ((out++natWord retained++frame top)++(List.range words.length).flatMap (outputs threshold core 1 members words)))
        (fun _=>(supportPrefix threshold core 1 members words supports words.length).length))
      (Fin.addCases (m:=1703) (n:=1) B (fun _=>supportPrefix threshold core 1 members words supports words.length)) ∧
      TailResult threshold C core words (out++natWord retained++frame top) members initial L W A B ∧
      (∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (B i).length ≤ C+1) ∧
      B 1698=List.replicate W true ∧ B 1699=List.replicate L true ∧ B 1=frame bits := by
  obtain ⟨B,run,result⟩:=body_run threshold C core retained words top out supports members initial L W A
    F.input F.capacity F.positive F.resource F.source F.retainedFits F.header F.topFits F.gate
    F.driver F.log F.retained F.topWord F.stream F.scratch F.count F.ports F.rawCount F.capL F.capW F.flag
  exact ⟨B,run,result,result.private_support F.resource F.source F.membersFits F.flag F.privateSupport,
    result.capW.trans F.capW,result.capL.trans F.capL,result.raw.trans F.raw⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
