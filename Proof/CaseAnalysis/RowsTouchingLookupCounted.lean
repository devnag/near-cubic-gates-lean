import Proof.CaseAnalysis.RowsTouchingLookupReady

/-! Query the actual table using the retained padded Compare words emitted
by the support pass and the coordinate loop. Both count words survive. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.LookupCounted
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def caps (P : ℕ):Fin 8→ℕ:=![0,0,P,P,0,0,0,0]
def input (q m k P C : ℕ) (backing : List Bool):Fin 8→List Bool:=
  ![PascalTable.table q,UnaryTemplate.tape (PascalReady.width q),
    ZeroPadding.pad P (CompareMachine.word m),ZeroPadding.pad P (CompareMachine.word k),
    backing,[],List.replicate (PascalReady.width q) false,List.replicate C false]

theorem padded_input (q m k P C : ℕ) (backing : List Bool):
    (fun i=>ZeroPadding.pad (caps P i) (LookupReady.input q m k C backing i))=input q m k P C backing:=by
  funext i
  fin_cases i
  · exact ZeroPadding.pad_zero _
  · exact ZeroPadding.pad_zero _
  · rfl
  · rfl
  · exact ZeroPadding.pad_zero _
  · exact ZeroPadding.pad_zero _
  · exact ZeroPadding.pad_zero _
  · exact ZeroPadding.pad_zero _

theorem lookup_run (q m k P C : ℕ) (backing : List Bool) (hm:m≤q) (hk:k≤q)
    (hb:backing.length≤2*(q+1)+1) (hC:Lookup.budget (PascalReady.width q) (q+1) m k+2≤C):
    Step LookupReady.machine (LookupReady.budget q m k) (fun _=>0) (input q m k P C backing)
      (fun _=>0) (input q m k P C (frame (binary (q+1) (Nat.choose m k)))):=by
  have padded:=(LookupReady.ready_run q m k C backing hm hk hb hC).pad (caps P)
  exact padded.congr_in rfl (padded_input q m k P C backing) |>.congr rfl
    (padded_input q m k P C (frame (binary (q+1) (Nat.choose m k))))

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.LookupCounted
