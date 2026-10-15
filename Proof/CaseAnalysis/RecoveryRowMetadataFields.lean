import Proof.CaseAnalysis.RecoveryRowReload

/-! Opaque changed-field projections for the original row prototype.
Each equality is checked separately before the fixed-list consumer uses it. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowPrototype
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def fields (C D F L n total queries clauses : ℕ) : Fin 78→List Bool:=
  Fin.addCases (m:=73) (n:=5) (motive:=fun _=>List Bool)
    (RecoveryBoundedRow.data 0 C D F L [] n total [] [] queries [] [] clauses) (fun _=>[])

variable (node C D F L n total queries clauses : ℕ) (out source : List Bool)

theorem field1 : fields C D F L n total queries clauses 1=
    RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses 1 := by rfl

theorem field22 : fields C D F L n total queries clauses 22=
    RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses 22 := by rfl

theorem field35 : fields C D F L n total queries clauses 35=
    RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses 35 := by rfl

theorem field41 : fields C D F L n total queries clauses 41=
    RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses 41 := by rfl

theorem field42 : fields C D F L n total queries clauses 42=
    RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses 42 := by
  change ZeroPadding.pad C (RecoveryBoundedTableOutput.bankData 6 0 C D 0 F 0 L [] (ZeroPadding.pad C []) (6+F) 0 [] n total 42)=ZeroPadding.pad C (RecoveryBoundedTableOutput.bankData 6 node C D 0 F 0 L out (ZeroPadding.pad C []) (6+F) 0 [] n total 42)
  have hl : RecoveryBoundedTableOutput.bankData 6 0 C D 0 F 0 L [] (ZeroPadding.pad C []) (6+F) 0 [] n total 42=RepairSource.VerifierDecoding.CompareMachine.word 0 := by rfl
  have hr : RecoveryBoundedTableOutput.bankData 6 node C D 0 F 0 L out (ZeroPadding.pad C []) (6+F) 0 [] n total 42=RepairSource.VerifierDecoding.CompareMachine.word 0 := by rfl
  exact congrArg (ZeroPadding.pad C) (hl.trans hr.symm)

theorem field44 : fields C D F L n total queries clauses 44=
    RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses 44 := by
  change ZeroPadding.pad C (RecoveryBoundedTableOutput.bankData 6 0 C D 0 F 0 L [] (ZeroPadding.pad C []) (6+F) 0 [] n total 44)=ZeroPadding.pad C (RecoveryBoundedTableOutput.bankData 6 node C D 0 F 0 L out (ZeroPadding.pad C []) (6+F) 0 [] n total 44)
  have hl : RecoveryBoundedTableOutput.bankData 6 0 C D 0 F 0 L [] (ZeroPadding.pad C []) (6+F) 0 [] n total 44=List.replicate (6+F) true := by rfl
  have hr : RecoveryBoundedTableOutput.bankData 6 node C D 0 F 0 L out (ZeroPadding.pad C []) (6+F) 0 [] n total 44=List.replicate (6+F) true := by rfl
  exact congrArg (ZeroPadding.pad C) (hl.trans hr.symm)

theorem field46 : fields C D F L n total queries clauses 46=
    RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses 46 := by
  change ZeroPadding.pad C (RecoveryBoundedTableOutput.bankData 6 0 C D 0 F 0 L [] (ZeroPadding.pad C []) (6+F) 0 [] n total 46)=ZeroPadding.pad C (RecoveryBoundedTableOutput.bankData 6 node C D 0 F 0 L out (ZeroPadding.pad C []) (6+F) 0 [] n total 46)
  have hl : RecoveryBoundedTableOutput.bankData 6 0 C D 0 F 0 L [] (ZeroPadding.pad C []) (6+F) 0 [] n total 46=List.replicate 6 true := by rfl
  have hr : RecoveryBoundedTableOutput.bankData 6 node C D 0 F 0 L out (ZeroPadding.pad C []) (6+F) 0 [] n total 46=List.replicate 6 true := by rfl
  exact congrArg (ZeroPadding.pad C) (hl.trans hr.symm)

theorem field50 : fields C D F L n total queries clauses 50=
    RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses 50 := by rfl

theorem field53 : fields C D F L n total queries clauses 53=
    RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses 53 := by rfl

theorem field54 : fields C D F L n total queries clauses 54=
    RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses 54 := by rfl

theorem field55 : fields C D F L n total queries clauses 55=
    RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses 55 := by rfl

theorem field56 : fields C D F L n total queries clauses 56=
    RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses 56 := by rfl

theorem field57 : fields C D F L n total queries clauses 57=
    RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses 57 := by rfl

theorem field60 : fields C D F L n total queries clauses 60=
    RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses 60 := by rfl

theorem field72 : fields C D F L n total queries clauses 72=
    RecoveryBoundedRow.data node C D F L out n total [] [] queries source [] clauses 72 := by rfl

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowPrototype

