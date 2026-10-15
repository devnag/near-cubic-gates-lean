import Proof.CaseAnalysis.RowsSupportBody
import Proof.CaseAnalysis.RowsCircuitTailSupport

/-! The original private-bank support bound survives support retention.
The new public support accumulator is outside the original reset scope. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
open LocalBitMultitape RadixSemantics CloseoutRowsCircuitBottomLoop
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem TailResult.private_support {threshold : Bool} {C core : ℕ} {words : List (List Bool)}
    {native members : List Bool} {initial L W : ℕ} {A B : Fin 1703 → List Bool}
    (result : TailResult threshold C core words native members initial L W A B)
    (hc : 32*(descriptions core words initial words.length+words.length+
      wires threshold core 1 members words 0 words.length+3)≤C)
    (hsource : (words.flatMap frame).length≤C ∧ 1+2*words.length≤C)
    (hmember : members.length≤C+1) (hflag : A 1700=[])
    (initialSupport : ∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (A i).length≤C+1) :
    ∀ i,i≠1 → i≠1674 → i≠1694 → i≠1698 → i≠1699 → i≠1688 → (B i).length≤C+1 := by
  obtain ⟨mid,mt,mkeep,retained,small⟩:=result.bounds
  exact CloseoutRowsCircuitTailSupport.final_support C core words.length
    (native++(List.range words.length).flatMap (outputs threshold core 1 members words))
    (words.flatMap frame) members (descriptions core words initial words.length)
    (wires threshold core 1 members words 0 words.length) (validity core true words words.length)
    A mid B (by omega) (by omega) (by omega) hsource.1 hmember (by omega)
    mt mkeep retained small hflag initialSupport

end NearCubicWires.RepairOrdinary.CloseoutRowsSupportStream
