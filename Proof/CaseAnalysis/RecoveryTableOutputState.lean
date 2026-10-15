import Proof.CaseAnalysis.RecoveryTableOutputBank

/-! Opaque table/output boundaries retain all physical fields while the
original output expression prepends precisely the original table suffix. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedTableOutput
open LocalBitMultitape RepairRepresentation RepairSource.VerifierDecoding
open BoundedOracleStructuralCircuit FinitePredicateCircuit
open RecoveryBoundedSelectorLoop (capacity sourceWord)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bankHeads (out : List Bool) : Fin 56→ℕ:=
  Fin.addCases (m:=55) (n:=1) (motive:=fun _=>ℕ) (RecoveryBoundedUniversalNodeBank.heads out) (fun _=>1)
def bankData (index base C D value F prior L : ℕ) (out source : List Bool)
    (second tag : ℕ) (address : List Bool) (count driver : ℕ) : Fin 56→List Bool:=
  Fin.addCases (m:=55) (n:=1) (motive:=fun _=>List Bool)
    (RecoveryBoundedUniversalNodeBank.data index base C D value F prior L out source second tag 0 0 0 address count [])
    (fun _=>CompareMachine.word driver)

theorem bank_head_slot (out : List Bool) (j : Fin 44) :
    bankHeads out (slots j)=RecoveryBoundedSelectorReuse.finalHeads out j := by fin_cases j <;> rfl
theorem bank_tape_slot (index base C D value F prior L : ℕ) (out source : List Bool)
    (second tag : ℕ) (address : List Bool) (count driver : ℕ) (j : Fin 44) :
    bankData index base C D value F prior L out source second tag address count driver (slots j)=
      RecoveryBoundedSelectorReuse.finalData index base C D value F prior L out source j := by
  rw [RecoveryBoundedNodeTagSelect.local_data]
  fin_cases j <;> rfl
theorem bank_output_heads (out result : List Bool) : outputHeads (bankHeads out) result=bankHeads result := by
  funext i
  fin_cases i <;> rfl
theorem bank_output_tapes (index base current C D F prior L : ℕ) (out result source : List Bool)
    (second tag : ℕ) (address : List Bool) (count driver : ℕ) :
    output (bankData index base C D 0 F prior L out source second tag address count driver) current prior C result=
      bankData index current C D prior F prior L result source second tag address count driver := by
  funext i
  fin_cases i <;> rfl

theorem configuration_heads {n bound : ℕ} (phase : Fin 5)
    (b : BooleanDAGBuilder (descriptionWidth n bound)) (address : BitInput n)
    (W D L : ℕ) (out addressTail : List Bool) (k : ℕ) (hk : k ≤ bound) (total : ℕ) :
    (RecoveryBoundedTable.configuration phase b address W D L out addressTail k hk total 1).heads=
      bankHeads (out++RecoveryBoundedTable.native b address k hk) := by rfl
theorem configuration_tapes {n bound : ℕ} (phase : Fin 5)
    (b : BooleanDAGBuilder (descriptionWidth n bound)) (address : BitInput n)
    (W D L : ℕ) (out addressTail : List Bool) (k : ℕ) (hk : k ≤ bound) (total : ℕ) :
    (RecoveryBoundedTable.configuration phase b address W D L out addressTail k hk total 1).tapes=
      bankData (RecoveryBoundedTable.index n bound k 6) (compileUniversalNodes b address k hk).final.nodes.length
        (capacity W) D 0 (OuterPCPRecovery.boundedCircuitFieldLimit n bound) k L
        (out++RecoveryBoundedTable.native b address k hk)
        (ZeroPadding.pad (capacity W) (sourceWord (RecoveryBoundedTable.references b address k hk)))
        (RecoveryBoundedTable.index n bound k (6+OuterPCPRecovery.boundedCircuitFieldLimit n bound))
        (RecoveryBoundedTable.index n bound k 0) (List.ofFn address++addressTail) n total := by rfl

theorem original_native {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total : ℕ) (ht : total ≤ bound) :
    let table:=compileUniversalNodes b address total ht
    let selected:=compileFirstFieldSelect table.final ⟨total,by omega⟩ table.values
    (compileUniversalOutput b address total ht).compiled.extension.suffix.flatMap PCPPRequestNodeSchema.native=
      RecoveryBoundedTable.native b address total ht++selected.extension.suffix.flatMap PCPPRequestNodeSchema.native := by
  dsimp only
  change List.flatMap PCPPRequestNodeSchema.native (_++_)=_
  rw [List.flatMap_append]
  rfl
theorem original_output {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (address : BitInput n) (total : ℕ) (ht : total ≤ bound) :
    let table:=compileUniversalNodes b address total ht
    (compileUniversalOutput b address total ht).compiled.output.val=
      (compileFirstFieldSelect table.final ⟨total,by omega⟩ table.values).output.val := by rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedTableOutput
