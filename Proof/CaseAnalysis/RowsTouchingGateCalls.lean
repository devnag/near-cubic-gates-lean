import Proof.CaseAnalysis.RowsTouchingGatePorts

namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Gate
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SupportScan
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem summary_run (q k w P C : ℕ) (pre tail : List Bool) (xs : List Cell) (st : Store)
    (hP:1≤P) (hb:∀ j,(st.summary j).length≤P) (hC:P+1≤C) (hScan:2*xs.length+3≤C):
    Step summary (2*P+4*xs.length+13) (heads pre.length)
      (data q k w P C (pre++frame (xs.map Prod.fst)++tail) xs st)
      (heads (pre.length+2*xs.length+1))
      (data q k w P C (pre++frame (xs.map Prod.fst)++tail) xs (summarized st P xs)):=by
  have actual:=(GateSummary.summary_run P C pre tail xs st.summary hP hb hC hScan).embed
    (fun _ : Fin 15=>0) (extra q k w P st)
  exact actual.congr_in (summary_heads pre.length) rfl |>.congr
    (summary_heads (pre.length+2*xs.length+1)) rfl

theorem block_run (q k w P C pos : ℕ) (source : List Bool) (xs : List Cell) (st : Store)
    (withCandidate : Bool) (hSummary:st.summary=GateSummary.result P xs)
    (hm:count xs≤q) (hk:key withCandidate k≤q) (hw:q+1≤w)
    (hn:st.narrow.length≤2*(q+1)+1) (hb:st.wide.length≤2*w+1) (hs:st.scratch.length≤2*w+1)
    (hC:Lookup.budget (PascalReady.width q) (q+1) (count xs) (key withCandidate k)+2≤C) (hW:2*w+3≤C)
    (hfit:ScoreAdd.skip withCandidate (xs.any touched) (xs.any current)=false→
      Nat.choose (count xs) (key withCandidate k)+(scoreStore st withCandidate).accumulator<2^w):
    Step (block withCandidate) (ScoreBlock.budget q (count xs) (key withCandidate k) w)
      (heads pos) (data q k w P C source xs st) (heads pos)
      (data q k w P C source xs (scored st q (count xs) k w withCandidate (xs.any touched) (xs.any current))):=by
  have actual:=ScoreBlock.block_run q (count xs) (key withCandidate k) w P C withCandidate
    (xs.any touched) (xs.any current) (scoreStore st withCandidate) hm hk hw hn hb hs hC hW hfit
  have focused:=actual.dock (blockSlots withCandidate) (block_injective withCandidate)
    (heads pos) (data q k w P C source xs st) (block_heads withCandidate pos)
    (congrFun (block_data q k w P C source xs st withCandidate hSummary))
  exact focused.congr (dockH_existing _ _ _ (block_heads withCandidate pos))
    (replace_data q k w P C source xs st withCandidate _ hSummary)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.Gate
