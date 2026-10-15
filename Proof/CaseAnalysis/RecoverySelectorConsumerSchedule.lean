import Proof.CaseAnalysis.RecoverySelectorForwardMeaning

/-! The bounded forward loop is the exact first/second field selector prefix.
These coarse graph bounds are sufficient for recovery allocation. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
open LocalBitMultitape SourceInterfaces RepairRepresentation
open BoundedOracleStructuralCircuit FinitePredicateCircuit RecoveryBoundedNative RecoveryBoundedUniversal
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fieldItems_zipIdx {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit value : ℕ) (hblock : start+limit ≤ rowWidth n bound)
    (wires : List (LiveWire b)) :
    fieldItems row start limit hblock value (wires.map (fun w=>w.output.val))=
      choices ((wires.zipIdx value).map fun e=>
        (⟨unaryEqualsExpr row start limit e.2 hblock,e.1⟩ : GuardedChoice b)) := by
  induction wires generalizing value with
  | nil=>rfl
  | cons wire wires ih=>
    simp only [List.map_cons,fieldItems,List.zipIdx_cons,choices,List.map_cons]
    exact congrArg (List.cons _) (ih (value+1))

theorem fieldItems_choices {n bound : ℕ} (b : BooleanDAGBuilder (descriptionWidth n bound))
    (row : Fin (bound+1)) (start limit : ℕ) (hblock : start+limit ≤ rowWidth n bound)
    (wires : List (LiveWire b)) :
    fieldItems row start limit hblock 0 (wires.map (fun w=>w.output.val))=
      choices (fieldChoices (fun row value=>unaryEqualsExpr row start limit value hblock) row wires) :=
  fieldItems_zipIdx b row start limit 0 hblock wires

theorem prefix_bound {n bound : ℕ} (row : Fin (bound+1)) (start limit value : ℕ)
    (hblock : start+limit ≤ rowWidth n bound) (refs : List ℕ) :
    prefixSize (fieldItems row start limit hblock value refs) ≤ refs.length*(3*limit+2) := by
  induction refs generalizing value with
  | nil=>simp [fieldItems,prefixSize]
  | cons ref refs ih=>
    have h:=prefixCount_bound (unaryItems row start limit value hblock)
    have hl : (unaryItems row start limit value hblock).length=limit := by simp [unaryItems]
    rw [hl] at h
    have ht:=ih (value+1)
    simp only [fieldItems,prefixSize,unary_count,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem saved_bound {n : ℕ} (base : ℕ) (xs : List (BoolExpr n×ℕ)) (ref : ℕ)
    (hr : ref∈RecoveryBoundedUniversal.references base xs) : ref ≤ base+prefixSize xs := by
  induction xs generalizing base with
  | nil=>simp [RecoveryBoundedUniversal.references] at hr
  | cons x xs ih=>
    rcases x with ⟨e,v⟩
    simp only [RecoveryBoundedUniversal.references,List.mem_cons] at hr
    rcases hr with rfl|hr
    · simp only [prefixSize]
      omega
    · have h:=ih (base+e.nodeCount+1) hr
      simp only [prefixSize]
      omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedSelectorLoop
