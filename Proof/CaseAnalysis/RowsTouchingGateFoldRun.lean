import Proof.CaseAnalysis.RowsTouchingGateRun
import Proof.CaseAnalysis.RowsTouchingGateFoldLayout

/-! One counted traversal reads every original support record in order.
Both exact scores use the same selected/current/remaining masks. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.GateFold
open LocalBitMultitape SupportScan ExtDecompositionBatch CloseoutRowsFamilyLoop
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem fold_run (q k w P C : ℕ) (records : List (List Cell)) (mask : List Cell)
    (initial : Gate.Store) (pre tail : List Bool)
    (hq:∀ xs∈records,xs.length=q) (hmask:∀ xs∈records,masks xs=masks mask)
    (hk:k≤q) (hw:q+1≤w) (hwidth:q+records.length+1≤w) (hP:q+1≤P)
    (valid:Gate.Valid q w P initial) (hzero:initial.excluded=0 ∧ initial.included=0)
    (hC:P+1≤C) (hScan:2*q+3≤C) (hW:2*w+3≤C)
    (hLookup:Lookup.budget (PascalReady.width q) (q+1) q q+2≤C):
    ∃ r,runFrom machine (budget q w P records.length)
      (RepeatMachine.cfg 0 (entry q k w P C records mask initial pre tail 0 []) records.length 1)=some r ∧
      r.final=RepeatMachine.cfg 3
        (entry q k w P C records mask initial pre tail records.length []) records.length 1 ∧
      r.steps≤budget q w P records.length:=by
  let source:=entry q k w P C records mask initial pre tail
  have supplier:∀ j<records.length,∀ out,∃ r,runFrom Gate.machine (cost q w P) (source j out)=some r ∧
      r.final.heads=(source (j+1) (out++[])).heads ∧
      r.final.tapes=(source (j+1) (out++[])).tapes ∧ r.steps≤cost q w P:=by
    intro j hj out
    let xs:=records.getD j []
    let st:=Gate.states q k w P records initial j
    let lp:=pre++(records.take j).flatMap word
    let rt:=(records.drop (j+1)).flatMap word++tail
    have mem:xs∈records:=by
      dsimp only [xs];rw [List.getD_eq_getElem records [] hj];exact List.getElem_mem hj
    have hm:count xs≤q:=(GateSummary.count_le xs).trans (by rw [hq _ mem])
    have bound:=Gate.states_scores q k w P records initial hq j (by omega)
    simp only [hzero.1,hzero.2,Nat.zero_add] at bound
    have fits (a : ℕ) (ha:a≤j*2^q) (key : ℕ):Nat.choose (count xs) key+a<2^w:=by
      have hc:Nat.choose (count xs) key≤2^q:=
        (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide : 0<2) hm)
      exact (Nat.add_le_add_right hc a).trans_lt
        ((Gate.fold_fits q records.length j a hj ha).trans_le
          (Nat.pow_le_pow_right (by decide : 0<2) hwidth))
    have split:lp++frame (xs.map Prod.fst)++rt=pre++records.flatMap word++tail:=by
      rw [split_word records [] word j hj]
      simp only [lp,rt,xs,word,List.append_assoc]
    have actual:=Gate.gate_run q k w P C lp rt xs st (hq _ mem) hk hw hP
      (Gate.states_valid q k w P records initial hq hP valid j (by omega)) hC hScan hW
      (by intro key hkey;exact (Nat.add_le_add_right (lookup_le q (count xs) key hm hkey) 2).trans hLookup)
      (by intro _;exact fits st.excluded bound.1 k)
      (by intro _;exact fits st.included bound.2 (k-1))
    have paid:=actual.enlarge (gate_le q (count xs) k w P hm hk)
    have headsIn:Gate.heads lp.length=(source j out).heads:=by
      simp only [source,entry,lp,List.length_append]
    have headsOut:Gate.heads (lp.length+2*q+1)=(source (j+1) (out++[])).heads:=by
      simp only [source,entry,next_word records [] word j hj]
      have hlen:(word xs).length=2*q+1:=by simp [word,hq _ mem]
      rw [show (word (records.getD j [])).length=2*q+1 from hlen]
      simp only [lp,List.length_append,Nat.add_assoc]
    have tapesIn:Gate.data q k w P C (lp++frame (xs.map Prod.fst)++rt) xs st=(source j out).tapes:=by
      rw [split]
      exact data_masks q k w P C _ xs mask st (hmask _ mem)
    have tapesOut:Gate.data q k w P C (lp++frame (xs.map Prod.fst)++rt) xs
        (Gate.after st q k w P xs)=(source (j+1) (out++[])).tapes:=by
      rw [split]
      exact data_masks q k w P C _ xs mask (Gate.after st q k w P xs) (hmask _ mem)
    exact paid.congr_in headsIn tapesIn |>.congr headsOut tapesOut
  obtain ⟨r,run,rf,rs⟩:=CloseoutRowsDegreeLoop.loop_run Gate.machine source (fun _=>[]) (cost q w P)
    records.length (by intro j hj out;rfl) supplier []
  have emitted:(List.range records.length).flatMap (fun _ : ℕ=>([] : List Bool))=[]:=by simp
  rw [emitted,List.nil_append] at rf
  exact ⟨r,run,rf,rs⟩

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.GateFold
