import Proof.Hierarchy.CompetitorWitnessTripleLayout

/-! A fixed ordinary machine physically extracts the canonical tagged triple
on every witness bit string. The cost depends only on its binary length. -/
namespace NearCubicWires.RepairOrdinary.CompetitorWitnessTriple
open LocalBitMultitape RecoveryRootRound RecoveryExecution RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev count := Fintype.card (RecoveryCalls.Control RecoveryFixedUnpair.sizes)
def sizes (_ : Fin 6) := count
noncomputable def programs (j : Fin 6) : Machine 122 (sizes j) := program j
def next (j : Fin 6) (_ : Fin (sizes j)) (_ : Fin 122 → Bool) : Option (Fin 6) :=
  if h : j.val+1<6 then some ⟨j.val+1,h⟩ else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

def time (bits : List Bool) :=
  ((((RecoveryFixedUnpair.time (word bits 0)+1+(RecoveryFixedUnpair.time (word bits 1)+1))+
      (RecoveryFixedUnpair.time (word bits 2)+1))+(RecoveryFixedUnpair.time (word bits 3)+1))+
      (RecoveryFixedUnpair.time (word bits 4)+1))+(RecoveryFixedUnpair.time (word bits 5)+1)
def budget (bits : List Bool) := 25000*(bits.length+1)^2

theorem triple_ready (x bits : List Bool) : ReadyRun machine (time bits) (input x bits) (stage x bits 6) := by
  have h0 := (step_ready x bits 0).call sizes programs 0 next 0 1 (by intro q;rfl)
  have h1 := (step_ready x bits 1).call sizes programs 0 next 1 2 (by intro q;rfl)
  have h2 := (step_ready x bits 2).call sizes programs 0 next 2 3 (by intro q;rfl)
  have h3 := (step_ready x bits 3).call sizes programs 0 next 3 4 (by intro q;rfl)
  have h4 := (step_ready x bits 4).call sizes programs 0 next 4 5 (by intro q;rfl)
  have h5 := (step_ready x bits 5).stop sizes programs 0 next 5 (by intro q;rfl)
  have h := ((((h0.trans h1).trans h2).trans h3).trans h4).trans h5
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [RecoveryCalls.machine,RecoveryCalls.stopped])
  exact ⟨r,hr,by simp [hf,RecoveryCalls.stopped],by intro i;simp [hf,RecoveryCalls.stopped],hs⟩

theorem time_bound (bits : List Bool) : time bits ≤ budget bits := by
  have h (k : ℕ) : RecoveryFixedUnpair.time (word bits k) ≤ 4096*(bits.length+1)^2 := by
    simpa only [RecoveryFixedUnpair.budget,word_length] using RecoveryFixedUnpair.time_bound (word bits k)
  have h0:=h 0
  have h1:=h 1
  have h2:=h 2
  have h3:=h 3
  have h4:=h 4
  have h5:=h 5
  have hp : 0 < (bits.length+1)^2 := by positivity
  unfold time budget
  omega

theorem triple_run (x bits : List Bool) :
    ∃ r : ExecutionReceipt 122 _,run machine (budget bits) (input x bits)=some r ∧
      r.final.tapes=stage x bits 6 ∧ (∀ i,r.final.heads i=0) ∧ r.steps ≤ budget bits := by
  obtain ⟨r,hr,ht,hh,hs⟩ := triple_ready x bits
  have hm := run_moreFuel machine (time bits) (budget bits-time bits) _ r hr
  rw [Nat.add_sub_of_le (time_bound bits)] at hm
  exact ⟨r,hm,ht,hh,hs.le.trans (time_bound bits)⟩

theorem stage_stable (x bits : List Bool) (k n : ℕ) (i : Fin 122)
    (hi : i.val < 20*k-1) : stage x bits (k+n) i=stage x bits k i := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.add_succ,stage]
    split_ifs with hk
    · rw [install_other]
      · exact ih
      · intro j h
        have hv := congrArg Fin.val h
        simp only [slots] at hv
        split_ifs at hv <;> simp_all <;> omega
    · exact ih

theorem field_output (x bits : List Bool) (j : Fin 6) :
    stage x bits 6 (slots j 17)=frame (RecoveryFixedUnpair.leftWord (word bits j.val)) := by
  have he : j.val+1+(5-j.val)=6 := by omega
  have h := stage_stable x bits (j.val+1) (5-j.val) (slots j 17) (by simp [slots];omega)
  rw [he] at h
  rw [h,stage,dif_pos j.isLt,install_slot _ (slots_injective _)]
  rfl

theorem tail_output (x bits : List Bool) : stage x bits 6 119=frame (word bits 6) := by
  change stage x bits (5+1) (slots 5 18)=_
  rw [stage,dif_pos (by omega : 5<6)]
  exact install_slot (slots 5) (slots_injective 5) _ _ 18

end NearCubicWires.RepairOrdinary.CompetitorWitnessTriple
