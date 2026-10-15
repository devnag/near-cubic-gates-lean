import Proof.Amplification.RecoveryBankFlag

/-! The inner table gates the outer table on disjoint fixed tape banks.
The right answer is physically copied back into the final result cell. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBankPair
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def gateMachine {t u s v : Nat} (p : Machine t s) (q : Machine u v)
    (leftSlot : Fin t) (rightSlot : Fin u) :=
  RecoveryGatedSequence.machine (leftMachine (u:=u) p) (rightReturn q leftSlot rightSlot) (leftSlot.castAdd u)

theorem gate_run {t u s v : Nat} (p : Machine t s) (q : Machine u v)
    (leftSlot : Fin t) (rightSlot : Fin u) (b1 b2 : Nat)
    (lh : Fin t → Nat) (lt : Fin t → List Bool) (rh : Fin u → Nat) (rt : Fin u → List Bool)
    (gate answer : Bool) (base : ExecutionReceipt t s)
    (hp : runFrom p b1 ⟨p.start,lh,lt⟩=some base)
    (hph : base.final.heads leftSlot=0) (hpt : base.final.tapes leftSlot=[gate])
    (hq : gate=true → ∃ last,runFrom q b2 ⟨q.start,rh,rt⟩=some last ∧
      last.final.heads rightSlot=0 ∧ last.final.tapes rightSlot=[answer]) :
    ∃ r,runFrom (gateMachine p q leftSlot rightSlot) (b1+(b2+1+1)+2)
        (cfg lh lt rh rt (gateMachine p q leftSlot rightSlot).start)=some r ∧
      r.steps ≤ b1+(b2+1+1)+2 ∧ r.final.heads (leftSlot.castAdd u)=0 ∧
      r.final.tapes (leftSlot.castAdd u)=[gate && answer] := by
  obtain ⟨first,hr,_,hf⟩ := left_run p b1 ⟨p.start,lh,lt⟩ base hp rh rt
  have hh : first.final.heads (leftSlot.castAdd u)=0 := by
    rw [hf]; simpa only [cfg,Fin.addCases_left] using hph
  have ht : first.final.tapes (leftSlot.castAdd u)=[gate] := by
    rw [hf]; simpa only [cfg,Fin.addCases_left] using hpt
  have hn : gate=true → ∃ last,runFrom (rightReturn q leftSlot rightSlot) (b2+1+1)
      (RecoveryCalls.restarted (rightReturn q leftSlot rightSlot) first.final.heads first.final.tapes)=some last ∧
      last.final.heads (leftSlot.castAdd u)=0 ∧ last.final.tapes (leftSlot.castAdd u)=[gate && answer] := by
    intro ha
    obtain ⟨qb,hqb,hqh,hqt⟩ := hq ha
    obtain ⟨last,hl,_,hlh,hlt⟩ := right_return_run q leftSlot rightSlot b2
      base.final.heads base.final.tapes rh rt gate answer hph hpt qb hqb hqh hqt
    have he : RecoveryCalls.restarted (rightReturn q leftSlot rightSlot) first.final.heads first.final.tapes=
        cfg base.final.heads base.final.tapes rh rt (rightReturn q leftSlot rightSlot).start := by rw [hf]; rfl
    rw [he]
    refine ⟨last,hl,hlh,?_⟩
    rw [ha,Bool.true_and]; exact hlt
  have hrun := RecoveryGatedSequence.boolean_start_run (leftMachine (u:=u) p) (rightReturn q leftSlot rightSlot)
    (leftSlot.castAdd u) b1 (b2+1+1)
    (Fin.addCases (m:=t) (n:=u) (motive:=fun _=>Nat) lh rh)
    (Fin.addCases (m:=t) (n:=u) (motive:=fun _=>List Bool) lt rt) first gate (gate && answer)
    hr hh ht (by intro ha; rw [ha,Bool.false_and]) hn
  exact hrun

end NearCubicWires.RepairOrdinary.RecoveryBankPair
