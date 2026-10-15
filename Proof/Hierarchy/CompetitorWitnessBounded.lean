import Proof.Hierarchy.CompetitorWitnessBoundedLayout

/-! The actual all-input branch precedes the canonical header. Oversized
witnesses halt immediately after the linear cap guard; the nested parser is
entered only with the physical cap bit true. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessBounded
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev headerStates := Fintype.card (RecoveryCalls.Control CompetitorWitnessTriple.sizes)+
  Fintype.card (RecoveryCalls.Control CompetitorWitnessHeader.sizes)
def sizes : Fin 2→ℕ := ![36,headerStates]
noncomputable def programs : (j : Fin 2)→Machine 150 (sizes j)
  | ⟨0,_⟩=>cap
  | ⟨1,_⟩=>header
  | ⟨n+2,h⟩=>False.elim (by omega)
def next (j : Fin 2) (_ : Fin (sizes j)) (cells : Fin 150→Bool) : Option (Fin 2) :=
  if j.val=0 ∧ cells 148=true then some 1 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next
noncomputable def output (x w : List Bool) (scratch : ℕ) :=
  if 16*w.length≤x.length then bank (CompetitorWitnessHeader.output x w) true scratch
  else capped x w scratch
def budget (x : List Bool) := 26010*(x.length+1)^2

theorem bounded_ready (x w : List Bool) :
    ∃ scratch,scratch≤3*x.length+2 ∧ ∃ t,t≤budget x ∧
      ReadyRun machine t (input x w) (output x w scratch) := by
  obtain ⟨scratch,hsc,hcap⟩ := cap_ready x w
  by_cases hx : 16*w.length≤x.length
  · have h0 := hcap.call sizes programs 0 next 0 1 (by
      intro q
      change (if (0 : ℕ)=0 ∧ readTapeBit [decide (16*w.length≤x.length)] 0=true then some 1 else none)=some 1
      simp [hx,readTapeBit])
    have h1 := (header_ready x w scratch).stop sizes programs 0 next 1 (by intro q; rfl)
    have h := h0.trans h1
    obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have ht : (2*scratch+2+1)+(CompetitorWitnessHeader.time w+1)≤budget x := by
      have hb := CompetitorWitnessHeader.time_bound w
      have hw : w.length≤x.length := by omega
      have hp : (w.length+1)^2≤(x.length+1)^2 := Nat.pow_le_pow_left (by omega) 2
      unfold CompetitorWitnessHeader.budget at hb
      unfold budget
      nlinarith
    refine ⟨scratch,hsc,_,ht,r,hr,?_,?_,hs⟩
    · simp [hf,RecoveryCalls.stopped,output,hx]
    · intro i;simp [hf,RecoveryCalls.stopped]
  · have h := hcap.stop sizes programs 0 next 0 (by
      intro q
      change (if (0 : ℕ)=0 ∧ readTapeBit [decide (16*w.length≤x.length)] 0=true then some 1 else none)=none
      simp [hx,readTapeBit])
    obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
    have ht : 2*scratch+2+1≤budget x := by unfold budget; nlinarith
    refine ⟨scratch,hsc,_,ht,r,hr,?_,?_,hs⟩
    · simp only [hf,RecoveryCalls.stopped,output,if_neg hx]
    · intro i;simp [hf,RecoveryCalls.stopped]

theorem bounded_run (x w : List Bool) :
    ∃ scratch,scratch≤3*x.length+2 ∧ ∃ r,
      run machine (budget x) (input x w)=some r ∧
      r.final.tapes=output x w scratch ∧ (∀ i,r.final.heads i=0) ∧ r.steps≤budget x := by
  obtain ⟨scratch,hsc,t,ht,r,hr,rt,rh,rs⟩ := bounded_ready x w
  have hm := run_moreFuel machine t (budget x-t) _ r hr
  rw [Nat.add_sub_of_le ht] at hm
  exact ⟨scratch,hsc,r,hm,rt,rh,rs.le.trans ht⟩

theorem output_valid (x w : List Bool) (scratch : ℕ) :
    readTapeBit (output x w scratch 147) 0=true ↔
      16*w.length≤x.length ∧ CompetitorWitnessTriple.headerValid w := by
  by_cases hx : 16*w.length≤x.length
  · simp only [output,hx,if_true,true_and]
    change readTapeBit (CompetitorWitnessHeader.output x w 147) 0=true ↔_
    exact CompetitorWitnessHeader.output_passes x w
  · simp only [output,hx,if_false,false_and]
    change readTapeBit (CompetitorWitnessHeader.input x w 147) 0=true ↔ False
    rw [CompetitorWitnessHeader.input_eq]
    simp [readTapeBit]

end NearCubicWires.RepairOrdinary.CompetitorWitnessBounded
