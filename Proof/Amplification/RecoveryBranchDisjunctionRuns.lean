import Proof.Amplification.RecoveryBranchDisjunction

/-! The complete two-branch physical composition, charged from the two
literal source run budgets. Its only extra work is two call returns and
the final Boolean write/stop. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBranchDisjunction
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem joined_run {t u s v : Nat} (p : Machine t s) (q : Machine u v) (a : Fin t) (b : Fin u)
    (lh : Fin t→Nat) (lt : Fin t→List Bool) (rh : Fin u→Nat) (rt : Fin u→List Bool)
    (b1 b2 : Nat) (r1 : ExecutionReceipt t s) (r2 : ExecutionReceipt u v)
    (h1 : runFrom p b1 ⟨p.start,lh,lt⟩=some r1)
    (h2 : runFrom q b2 ⟨q.start,rh,rt⟩=some r2)
    (left right : Bool) (hlh : r1.final.heads a=0) (hlt : r1.final.tapes a=[left])
    (hrh : r2.final.heads b=0) (hrt : r2.final.tapes b=[right]) :
    ∃ r,runFrom (machine p q a b) (b1+b2+4)
      (RecoveryBankPair.cfg lh lt rh rt (machine p q a b).start)=some r ∧
      r.steps ≤ b1+b2+4 ∧ r.final.heads (a.castAdd u)=0 ∧ r.final.tapes (a.castAdd u)=[left || right] := by
  obtain ⟨first,hfirst,_,hf⟩ := RecoveryBankPair.left_run p b1 ⟨p.start,lh,lt⟩ r1 h1 rh rt
  obtain ⟨n0,hn0,h0⟩ := call_receipt (sizes s v) (programs p q a b) 0 route 0 1 b1
    (RecoveryBankPair.cfg lh lt rh rt p.start) first hfirst (by rfl)
  have he0 : controlConfig (RecoveryCalls.code (sizes s v) 1)
      (RecoveryCalls.restarted (programs p q a b 1) first.final.heads first.final.tapes)=
      RecoveryBankPair.cfg r1.final.heads r1.final.tapes rh rt (RecoveryCalls.code (sizes s v) 1 q.start) := by
    rw [hf]
    rfl
  rw [he0] at h0
  obtain ⟨second,hsecond,_,hs⟩ := RecoveryBankPair.right_run q b2 ⟨q.start,rh,rt⟩ r2 h2 r1.final.heads r1.final.tapes
  obtain ⟨n1,hn1,h1'⟩ := call_receipt (sizes s v) (programs p q a b) 0 route 1 2 b2
    (RecoveryBankPair.cfg r1.final.heads r1.final.tapes rh rt q.start) second hsecond (by rfl)
  have he1 : controlConfig (RecoveryCalls.code (sizes s v) 2)
      (RecoveryCalls.restarted (programs p q a b 2) second.final.heads second.final.tapes)=
      RecoveryBankPair.cfg r1.final.heads r1.final.tapes r2.final.heads r2.final.tapes
        (RecoveryCalls.code (sizes s v) 2 (0 : Fin 2)) := by
    rw [hs]
    rfl
  rw [he1] at h1'
  obtain ⟨last,hlast,_,hlheads,hltapes⟩ := flag_run a b r1.final.heads r1.final.tapes r2.final.heads r2.final.tapes
    left right hlh hlt hrh hrt
  obtain ⟨n2,hn2,h2'⟩ := stop_receipt (sizes s v) (programs p q a b) 0 route 2 1
    (RecoveryBankPair.cfg r1.final.heads r1.final.tapes r2.final.heads r2.final.tapes (0 : Fin 2)) last hlast (by rfl)
  have h := (h0.trans h1').trans h2'
  have hn : n0+n1+n2 ≤ b1+b2+4 := by omega
  obtain ⟨r,hr,hout,hsteps⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := runFrom_moreFuel (machine p q a b) (n0+n1+n2) (b1+b2+4-(n0+n1+n2))
    (RecoveryBankPair.cfg lh lt rh rt (machine p q a b).start) r hr
  rw [Nat.add_sub_of_le hn] at hm
  refine ⟨r,hm,hsteps.le.trans hn,?_,?_⟩
  · rw [hout]
    change last.final.heads (a.castAdd u)=0
    rw [hlheads]
    simpa using hlh
  · rw [hout]
    change last.final.tapes (a.castAdd u)=[left || right]
    rw [hltapes,Function.update_self]

end NearCubicWires.RepairOrdinary.RecoveryBranchDisjunction
