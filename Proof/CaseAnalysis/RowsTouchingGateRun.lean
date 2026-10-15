import Proof.CaseAnalysis.RowsTouchingGateCalls
import Proof.CaseAnalysis.RowsTouchingGateLengths

/-! The actual original support record supplies both conditional scores.
Its one count and two flags are produced once, then reused by both score
blocks. The old source and mask order are retained literally. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Gate
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SupportScan
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem gate_run (q k w P C : ℕ) (pre tail : List Bool) (xs : List Cell) (st : Store)
    (hxs:xs.length=q) (hk:k≤q) (hw:q+1≤w) (hP:q+1≤P) (valid:Valid q w P st)
    (hC:P+1≤C) (hScan:2*q+3≤C) (hW:2*w+3≤C)
    (hLookup:∀ j,j≤q→Lookup.budget (PascalReady.width q) (q+1) (count xs) j+2≤C)
    (hExcluded:ScoreAdd.skip false (xs.any touched) (xs.any current)=false→
      Nat.choose (count xs) k+st.excluded<2^w)
    (hIncluded:ScoreAdd.skip true (xs.any touched) (xs.any current)=false→
      Nat.choose (count xs) (k-1)+st.included<2^w):
    Step machine (budget q (count xs) k w P) (heads pre.length)
      (data q k w P C (pre++frame (xs.map Prod.fst)++tail) xs st)
      (heads (pre.length+2*q+1))
      (data q k w P C (pre++frame (xs.map Prod.fst)++tail) xs (after st q k w P xs)):=by
  let source:=pre++frame (xs.map Prod.fst)++tail
  let pos:=pre.length+2*q+1
  let ready:=summarized st P xs
  let excluded:=scored ready q (count xs) k w false (xs.any touched) (xs.any current)
  have hp:xs.length+1≤P:=by omega
  have hm:count xs≤q:=(GateSummary.count_le xs).trans (by omega)
  have hkm:k-1≤q:=by omega
  have readyValid:=summarized_valid q w P xs st valid hp
  have excludedValid:=scored_valid q (count xs) k w P false (xs.any touched) (xs.any current) ready readyValid
  have first:Step summary (2*P+4*q+13) (heads pre.length) (data q k w P C source xs st)
      (heads pos) (data q k w P C source xs ready):=by
    have actual:=summary_run q k w P C pre tail xs st (by omega) valid.1 hC (by omega)
    exact (actual.enlarge (by omega)).congr (by rw [hxs]) rfl
  have second:=block_run q k w P C pos source xs ready false rfl hm hk hw
    readyValid.2.1 readyValid.2.2.1 readyValid.2.2.2 (hLookup k hk) hW hExcluded
  have third:=block_run q k w P C pos source xs excluded true rfl hm hkm hw
    excludedValid.2.1 excludedValid.2.2.1 excludedValid.2.2.2 (hLookup (k-1) hkm) hW hIncluded
  exact ((first.seq second).seq third).enlarge (by simp [budget,key])

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Gate
