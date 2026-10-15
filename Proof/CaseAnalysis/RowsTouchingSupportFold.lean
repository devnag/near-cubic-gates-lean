import Proof.CaseAnalysis.RowsTouchingSupportScan

/-! The same retained support frame supplies both candidate flags and the
actual unary row-index input for binomial lookup in one pass. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan
open LocalBitMultitape RecoveryExecution Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def count : List Cell→ℕ
  | []=>0
  | e::xs=>(kept e).toNat+count xs

theorem prefixed_scan_timed (lead : List Bool) (pre : List Bool) (before xs : List Cell) (tail : List Bool) (n : ℕ) (hit cur : Bool):
    Timed machine (2*xs.length+1)
      (prefixedCfg lead 0 (pre++frame (xs.map Prod.fst)++tail) pre.length (masks (before++xs)) before.length n hit cur)
      (prefixedCfg lead 2 (pre++frame (xs.map Prod.fst)++tail) (pre.length+2*xs.length+1)
        (masks (before++xs)) (before.length+xs.length) (n+count xs)
        (hit||xs.any touched) (cur||xs.any current)):=by
  induction xs generalizing pre before n hit cur with
  | nil=>simpa [count,frame] using Timed.single (by rfl) (prefixed_stop_step lead pre tail (masks before) before.length n hit cur)
  | cons e xs ih=>
    let mask:=masks (before++e::xs)
    have hs:readTapeBit (mask 0) before.length=e.2.1:=by
      simpa [mask,masks,List.map_append] using read_append (before.map (fun e:Cell=>e.2.1)) (xs.map (fun e:Cell=>e.2.1)) e.2.1
    have hc:readTapeBit (mask 1) before.length=e.2.2.1:=by
      simpa [mask,masks,List.map_append] using read_append (before.map (fun e:Cell=>e.2.2.1)) (xs.map (fun e:Cell=>e.2.2.1)) e.2.2.1
    have hr:readTapeBit (mask 2) before.length=e.2.2.2:=by
      simpa [mask,masks,List.map_append] using read_append (before.map (fun e:Cell=>e.2.2.2)) (xs.map (fun e:Cell=>e.2.2.2)) e.2.2.2
    have first:=prefixed_bit_steps lead pre (frame (xs.map Prod.fst)++tail) e mask before.length n hit cur hs hc hr
    have rest:=ih (pre++[true,e.1]) (before++[e]) (n+(kept e).toNat) (hit||touched e) (cur||current e)
    have actual:=first.trans (by
      simpa only [mask,List.append_assoc,List.cons_append,List.nil_append,List.length_append,
        List.length_cons,List.length_nil,Nat.add_zero] using rest)
    have time:2+(2*xs.length+1)=2*(e::xs).length+1:=by simp;omega
    rw [time] at actual
    simpa [count,frame,List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_add,Bool.or_assoc] using actual

theorem scan_timed (pre : List Bool) (before xs : List Cell) (tail : List Bool) (n : ℕ) (hit cur : Bool):
    Timed machine (2*xs.length+1)
      (cfg 0 (pre++frame (xs.map Prod.fst)++tail) pre.length (masks (before++xs)) before.length n hit cur)
      (cfg 2 (pre++frame (xs.map Prod.fst)++tail) (pre.length+2*xs.length+1)
        (masks (before++xs)) (before.length+xs.length) (n+count xs)
        (hit||xs.any touched) (cur||xs.any current)):=by
  simpa only [prefixedCfg,cfg,List.length_nil,List.nil_append,Nat.zero_add] using
    prefixed_scan_timed [] pre before xs tail n hit cur

theorem scan_run (pre : List Bool) (xs : List Cell) (tail : List Bool):
    ∃ r,runFrom machine (2*xs.length+1)
      (cfg 0 (pre++frame (xs.map Prod.fst)++tail) pre.length (masks xs) 0 0 false false)=some r ∧
      r.final=cfg 2 (pre++frame (xs.map Prod.fst)++tail) (pre.length+2*xs.length+1)
        (masks xs) xs.length (count xs) (xs.any touched) (xs.any current) ∧ r.steps=2*xs.length+1:=by
  simpa only [List.nil_append,List.length_nil,Nat.zero_add,Bool.false_or] using
    (scan_timed pre [] xs tail 0 false false).run (by rfl)

theorem counter_run (pre : List Bool) (xs : List Cell) (tail : List Bool):
    ∃ r,runFrom machine (2*xs.length+1)
      (prefixedCfg [false] 0 (pre++frame (xs.map Prod.fst)++tail) pre.length (masks xs) 0 0 false false)=some r ∧
      r.final=prefixedCfg [false] 2 (pre++frame (xs.map Prod.fst)++tail) (pre.length+2*xs.length+1)
        (masks xs) xs.length (count xs) (xs.any touched) (xs.any current) ∧ r.steps=2*xs.length+1:=by
  simpa only [List.nil_append,List.length_nil,Nat.zero_add,Bool.false_or] using
    (prefixed_scan_timed [false] pre [] xs tail 0 false false).run (by rfl)

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.SupportScan
