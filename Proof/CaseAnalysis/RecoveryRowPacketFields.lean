import Proof.CaseAnalysis.RecoveryRowRandomZero

/-! The exact fifteen original row prototype fields, before physical
printing. Both sentinel bytes and the original C-backed fields are retained. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacket
open LocalBitMultitape RepairRepresentation RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (C F R count Q clauses : ℕ) : Fin 15→List Bool:=
  ![ZeroPadding.pad C (List.replicate 6 true),List.replicate C true,CompareMachine.word F,
    ZeroPadding.pad C (List.replicate 6 true),ZeroPadding.pad C (CompareMachine.word 0),
    ZeroPadding.pad C (List.replicate (6+F) true),ZeroPadding.pad C (List.replicate 6 true),
    UnaryTemplate.tape R,CompareMachine.word 6,CompareMachine.word 5,CompareMachine.word count,
    List.replicate 6 true,List.replicate (6+F) true,CompareMachine.word Q,CompareMachine.word clauses]
def port : Fin 15→Fin 78:=![1,22,35,41,42,44,46,50,53,54,55,56,57,60,72]

theorem original (C D F L R count Q clauses : ℕ) (j : Fin 15) :
    fields C F R count Q clauses j=RecoveryBoundedRowPrototype.fields C D F L R count Q clauses (port j) := by
  fin_cases j <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacket
