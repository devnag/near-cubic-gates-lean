import Proof.Amplification.RecoveryMarkerAtomTail

/-! Whole actual marker-atom execution. Missing literals, invalid Boolean
tags, wrong committed/count signs and extra clause tails return false.
Successful decoded natural fields are retained by paid framed copies. -/
namespace NearCubicWires.RepairOrdinary.RecoveryMarkerAtom
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryMarkerClause
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem atom_trace (which : Fin 3) (x : State) (hx : x.Valid) :
    ∃ n,n ≤ budget x.width ∧ Timed (machine which) n
      (initialConfiguration (machine which) x.tapes)
      (RecoveryCalls.stopped (sizes which) (fun _=>0) (output which x).tapes) := by
  have hrun := RecoveryMarkerClause.literal_run x hx.1
  obtain ⟨r,hr,hf,hrb⟩ := hrun
  have hready : ReadyRun literalMachine r.steps x.tapes (literalStep x).tapes := by
    have hh : ∀ i,r.final.heads i=0 := by intro i; rw [hf]; rfl
    have h := ready_of_run literalMachine (RecoveryRawLiteral.cost x.inner) x.tapes r hr hh
    rw [hf] at h
    exact h
  have hc := RecoveryRawLiteral.cost_bound x.inner
  change RecoveryRawLiteral.cost x.inner ≤ 524288*(x.width+1)^2 at hc
  by_cases hg : good which (literalStep x)=true
  · have h0 := hready.call (sizes which) (programs which) 0 (next which) 0
      (if which.val=0 then 1 else 2) (by
        intro q
        change some (if gate which (fun i=>readTapeBit ((literalStep x).tapes i) 0) then
          if which.val=0 then (1 : Fin 6) else 2 else 5)=_
        rw [gate_tapes,hg]
        rfl)
    have hy := literal_valid x hx
    obtain ⟨n,hn,h⟩ := sign_trace which (literalStep x) (variableWord x) hy
      (variable_length x) (variable_field which x hg)
    have hw : (literalStep x).width=x.width := RecoveryRawLiteral.output_width x.inner
    rw [hw] at hn
    refine ⟨r.steps+1+n,?_,?_⟩
    · unfold budget saveBudget at *
      nlinarith only [hrb,hc,hn,show 0<(x.width+1)^2 by positivity]
    · have ho : output which x=final which (withSign which (literalStep x)) := by
        dsimp only [output]
        exact if_pos hg
      rw [ho]
      exact h0.trans h
  · have h0 := hready.call (sizes which) (programs which) 0 (next which) 0 5 (by
      intro q
      change some (if gate which (fun i=>readTapeBit ((literalStep x).tapes i) 0) then
        if which.val=0 then (1 : Fin 6) else 2 else 5)=some 5
      rw [gate_tapes,if_neg hg])
    have h1 := (RecoveryMarkerFlags.answer_ready (literalStep x) false).stop
      (sizes which) (programs which) 0 (next which) 5 (by intro q; rfl)
    refine ⟨r.steps+1+2,?_,?_⟩
    · unfold budget
      nlinarith only [hrb,hc,show 0<(x.width+1)^2 by positivity]
    · have ho : output which x=RecoveryMarkerFlags.answered (literalStep x) false := by
        dsimp only [output]
        exact if_neg hg
      rw [ho]
      exact h0.trans h1

theorem atom_run (which : Fin 3) (x : State) (hx : x.Valid) :
    ∃ r,run (machine which) (budget x.width) x.tapes=some r ∧
      r.steps ≤ budget x.width ∧ (∀ i,r.final.heads i=0) ∧ r.final.tapes=(output which x).tapes := by
  obtain ⟨n,hn,h⟩ := atom_trace which x hx
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := run_moreFuel (machine which) n (budget x.width-n) x.tapes r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,hs.le.trans hn,by intro i; rw [hf]; rfl,by rw [hf]; rfl⟩

theorem output_answer (which : Fin 3) (x : State) : (output which x).inner.present=answer which x := by
  cases hg : good which (literalStep x)
  · simp only [output,hg,Bool.false_eq_true,ite_false,answer,Bool.false_and]
    rfl
  · simp only [output,hg,ite_true,answer,Bool.true_and]
    rfl

theorem output_valid (which : Fin 3) (x : State) (hx : x.Valid) : (output which x).Valid := by
  have hy := literal_valid x hx
  have hz : (withSign which (literalStep x)).Valid := by
    unfold withSign
    split
    · exact hy
    · exact hy
  dsimp only [output]
  split
  · exact tested_valid which _ hz
  · exact hy

theorem output_width (which : Fin 3) (x : State) : (output which x).width=x.width := by
  have hy : (literalStep x).width=x.width := RecoveryRawLiteral.output_width x.inner
  have hz : (withSign which (literalStep x)).width=x.width := by
    unfold withSign
    split <;> exact hy
  dsimp only [output]
  split
  · exact (tested_width which _).trans hz
  · exact hy

end NearCubicWires.RepairOrdinary.RecoveryMarkerAtom
