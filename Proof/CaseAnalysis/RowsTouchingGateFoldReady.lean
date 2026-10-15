import Proof.CaseAnalysis.RowsTouchingGateFoldRun

/-! Return the original support cursor once after a complete score fold.
All masks, both accumulated scores, the table and original G driver survive. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.GateFoldReady
open LocalBitMultitape SupportScan ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 25):Bool:=decide (i=0)
noncomputable def machine:=MaskedReset.machine GateFold.machine selected
def budget (q w P G : ℕ):=2*GateFold.budget q w P G+2
def heads (i : Fin 26):ℕ:=
  Fin.addCases (m:=25) (n:=1) (motive:=fun _=>ℕ)
    (fun j=>Fin.addCases (m:=24) (n:=1) (motive:=fun _=>ℕ) (Gate.heads 0) (fun _=>1) j) (fun _=>0) i
def data (q k w P C D G : ℕ) (source : List Bool) (mask : List Cell) (st : Gate.Store) (i : Fin 26):List Bool:=
  Fin.addCases (m:=25) (n:=1) (motive:=fun _=>List Bool)
    (fun j=>Fin.addCases (m:=24) (n:=1) (motive:=fun _=>List Bool) (Gate.data q k w P C source mask st)
      (fun _=>CompareMachine.word G) j) (fun _=>List.replicate D false) i

theorem final_heads (pos : ℕ):
    (fun i=>Fin.addCases (m:=25) (n:=1) (motive:=fun _=>ℕ) (fun j=>if selected j then 0 else
      Fin.addCases (m:=24) (n:=1) (motive:=fun _=>ℕ) (Gate.heads pos) (fun _=>1) j) (fun _=>0) i)=heads:=by
  funext i;fin_cases i <;> rfl

theorem ready_run (q k w P C D : ℕ) (records : List (List Cell)) (mask : List Cell)
    (initial : Gate.Store) (tail : List Bool)
    (hq:∀ xs∈records,xs.length=q) (hmask:∀ xs∈records,masks xs=masks mask)
    (hk:k≤q) (hw:q+1≤w) (hwidth:q+records.length+1≤w) (hP:q+1≤P)
    (valid:Gate.Valid q w P initial) (hzero:initial.excluded=0 ∧ initial.included=0)
    (hC:P+1≤C) (hScan:2*q+3≤C) (hW:2*w+3≤C)
    (hLookup:Lookup.budget (PascalReady.width q) (q+1) q q+2≤C)
    (hD:GateFold.budget q w P records.length≤D):
    Step machine (budget q w P records.length) heads
      (data q k w P C D records.length (records.flatMap GateFold.word++tail) mask initial) heads
      (data q k w P C D records.length (records.flatMap GateFold.word++tail) mask
        (Gate.states q k w P records initial records.length)):=by
  obtain ⟨r,run,rf,_⟩:=GateFold.fold_run q k w P C records mask initial [] tail hq hmask hk hw hwidth hP
    valid hzero hC hScan hW hLookup
  have actual:=Step.of_run run (congrArg Configuration.heads rf) (congrArg Configuration.tapes rf)
  have reset:=actual.mask selected (by intro i hi;have he:i=0:=of_decide_eq_true hi;subst i;rfl) hD
  refine reset.congr_in ?_ ?_ |>.congr ?_ ?_
  · rfl
  · rfl
  · exact final_heads _
  · rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.GateFoldReady
