import Proof.CaseAnalysis.RowsTouchingGateFoldReady
import Proof.CaseAnalysis.RowsTouchingGateMeaning

/-! The actual returned fold exposes the two scalar words consumed by the
unchanged touching comparison, on the original declared support stream. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.GateFoldReady
open LocalBitMultitape SupportScan ExtDecompositionBatch SignedSortKey CloseoutRowsGateSupport
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def supportWord {q G : ℕ} (support : Fin G→Finset (Fin q)):List Bool:=
  (List.ofFn (fun g=>frame (gateMembers (support g)))).flatten

theorem records_word {q G : ℕ} (support : Fin G→Finset (Fin q))
    (selected undecided : Finset (Fin q)) (coordinate : Fin q):
    (Gate.records support selected undecided coordinate).flatMap GateFold.word=supportWord support:=by
  rw [List.flatMap_def]
  simp only [Gate.records,List.map_ofFn,Function.comp_def,GateFold.word,cells_support,supportWord]

theorem typed_run {q G : ℕ} (support : Fin G→Finset (Fin q))
    (selected undecided : Finset (Fin q)) (coordinate : Fin q) (k w P C D : ℕ)
    (initial : Gate.Store) (tail : List Bool)
    (hk:k≤q) (hw:q+1≤w) (hwidth:q+G+1≤w) (hP:q+1≤P)
    (valid:Gate.Valid q w P initial) (hzero:initial.excluded=0 ∧ initial.included=0)
    (hC:P+1≤C) (hScan:2*q+3≤C) (hW:2*w+3≤C)
    (hLookup:Lookup.budget (PascalReady.width q) (q+1) q q+2≤C) (hD:GateFold.budget q w P G≤D):
    let mask:=cells ∅ selected undecided coordinate
    ∃ out,Step machine (budget q w P G) heads
      (data q k w P C D G (supportWord support++tail) mask initial) heads out ∧
      out 18=frame (binary w (Complement.score support selected undecided k)) ∧
      out 19=frame (binary w (Complement.score support (insert coordinate selected) undecided (k-1))) ∧
      out=data q k w P C D G (supportWord support++tail) mask
        (Gate.states q k w P (Gate.records support selected undecided coordinate) initial G):=by
  dsimp only
  let records:=Gate.records support selected undecided coordinate
  let mask:=cells ∅ selected undecided coordinate
  have length:records.length=G:=List.length_ofFn
  have lengths:∀ xs∈records,xs.length=q:=by
    intro xs hxs
    rcases List.mem_ofFn.mp hxs with ⟨g,rfl⟩
    exact cells_length _ _ _ _
  have masks:∀ xs∈records,SupportScan.masks xs=SupportScan.masks mask:=by
    intro xs hxs
    rcases List.mem_ofFn.mp hxs with ⟨g,rfl⟩
    simp only [mask,cells_masks]
  have actual:=ready_run q k w P C D records mask initial tail lengths masks hk hw
    (by rw [length];exact hwidth) hP valid hzero hC hScan hW hLookup (by rw [length];exact hD)
  have words:records.flatMap GateFold.word=supportWord support:=records_word support selected undecided coordinate
  rw [length,words] at actual
  have exactScores:=Gate.records_scores support selected undecided coordinate k w P initial
  simp only [hzero.1,hzero.2,Nat.zero_add] at exactScores
  refine ⟨_,actual,?_,?_,rfl⟩
  · change frame (binary w (Gate.states q k w P records initial G).excluded)=_
    rw [exactScores.1]
  · change frame (binary w (Gate.states q k w P records initial G).included)=_
    rw [exactScores.2]

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.GateFoldReady
