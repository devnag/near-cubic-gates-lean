import Proof.Amplification.RecoveryRowComparison

/-! One actual prior-row lookup cell: compare the retained code, copy its
count only on the first match, and retain all later matches without copying.
The finite branch reads real flags; input codes and counts remain intact. -/
namespace NearCubicWires.RepairOrdinary.RecoveryRowLookupCell
open LocalBitMultitape RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Data where
  key : List Bool
  code : List Bool
  count : List Bool
  saved : List Bool
  found : Bool
  same : Bool
  aux : Bool
  copyCapacity : Nat
  resetCapacity : Nat

def Data.extra (d : Data) : Fin 4→List Bool :=
  ![frame d.count,frame d.saved,[d.found],List.replicate d.copyCapacity false]
def Data.tapes (d : Data) : Fin 9→List Bool :=
  Fin.addCases (m:=5) (n:=4) (motive:=fun _=>List Bool)
    (RecoveryRowComparison.tapes d.key d.code ![d.same,d.aux] d.resetCapacity) d.extra
def Data.Valid (d : Data) : Prop :=
  d.code.length=d.key.length ∧ d.count.length=d.key.length ∧ d.saved.length≤d.key.length ∧
    2*d.key.length+1≤d.copyCapacity ∧ 4*d.key.length+3≤d.resetCapacity
def Data.compared (d : Data) : Data :=
  {d with same:=decide (value d.key=value d.code),aux:=decide (value d.code≤value d.key)}
def Data.copied (d : Data) : Data := {d with saved:=d.count}
def Data.finished (d : Data) : Data := {d with found:=d.found || d.same}
def Data.done (d : Data) : Data :=
  if d.found then d.compared.finished else
    if value d.key=value d.code then d.compared.copied.finished else d.compared.finished

def copySlots : Fin 4→Fin 9 := ![5,6,8,4]
theorem copySlots_injective : Function.Injective copySlots := by decide
noncomputable def compareMachine := TapeEmbedding.machine 4 RecoveryRowComparison.machine
noncomputable def copyMachine := RecoveryFocus.machine copySlots RecoveryRootRound.copyMachine

private theorem install_eq {t u : Nat} (slot : Fin t→Fin u) (hi : Function.Injective slot)
    (ambient target : Fin u→List Bool) (replacement : Fin t→List Bool)
    (hselected : ∀ j,replacement j=target (slot j))
    (hother : ∀ i,(∀ j,slot j≠i) → ambient i=target i) : install slot ambient replacement=target := by
  funext i
  cases hp : RecoveryFocus.pick slot i with
  | none =>
    simp only [install,hp]
    apply hother i
    intro j hj
    subst i
    rw [RecoveryFocus.pick_slot slot hi] at hp
    contradiction
  | some j =>
    simp only [install,hp]
    exact (hselected j).trans (congrArg target (RecoveryFocus.slot_of_pick slot hp))

theorem compare_small (d : Data) (hd : d.Valid) :
    ReadyRun RecoveryRowComparison.machine (8*d.key.length+20)
      (RecoveryRowComparison.tapes d.key d.code ![d.same,d.aux] d.resetCapacity)
      (RecoveryRowComparison.tapes d.key d.code
        ![decide (value d.key=value d.code),decide (value d.code≤value d.key)] d.resetCapacity) := by
  have hc : max d.resetCapacity (2*d.key.length+3)=d.resetCapacity := by
    apply Nat.max_eq_left
    have hr := hd.2.2.2.2
    omega
  have h := RecoveryRowComparison.equal_ready d.key d.code ![d.same,d.aux]
    d.resetCapacity hd.1.symm
  rw [hc] at h
  exact h

theorem compare_ready (d : Data) (hd : d.Valid) :
    ReadyRun compareMachine (8*d.key.length+20) d.tapes d.compared.tapes := by
  exact (compare_small d hd).embed d.extra

theorem copy_ready (d : Data) (hd : d.Valid) :
    ReadyRun copyMachine (8*d.key.length+8) d.tapes d.copied.tapes := by
  have hb : (frame d.saved).length≤2*d.count.length+1 := by
    rw [frame_length,hd.2.1]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 hd.2.2.1) 1
  have h := (RecoveryRootRound.copy_ready d.count (frame d.saved) d.copyCapacity d.resetCapacity hb).focus
    copySlots copySlots_injective d.tapes (by intro j; fin_cases j <;> rfl)
  simp only [hd.2.1,Nat.max_eq_left hd.2.2.2.1,Nat.max_eq_left hd.2.2.2.2] at h
  have he : install copySlots d.tapes ![frame d.count,frame d.count,
      List.replicate d.copyCapacity false,List.replicate d.resetCapacity false]=d.copied.tapes := by
    funext i
    fin_cases i
    case «5» => exact install_slot copySlots copySlots_injective _ _ 0
    case «6» => exact install_slot copySlots copySlots_injective _ _ 1
    case «8» => exact install_slot copySlots copySlots_injective _ _ 2
    case «4» => exact install_slot copySlots copySlots_injective _ _ 3
    all_goals exact install_other copySlots _ _ _ (by intro j; fin_cases j <;> decide)
  rw [he] at h
  exact h

def finish : Machine 9 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then some ⟨1,
    fun i=>if i=7 then some (scanned 7 || scanned 2) else none,fun _=>.stay⟩ else none

theorem finish_ready (d : Data) : ReadyRun finish 1 d.tapes d.finished.tapes := by
  let final : Configuration 9 2 := ⟨1,fun _=>0,d.finished.tapes⟩
  have h : step finish (initialConfiguration finish d.tapes)=some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · rfl
    · funext i; fin_cases i <;> rfl
  obtain ⟨r,hr,hf,ht⟩ := (Timed.single (by rfl) h).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],ht⟩

noncomputable def sizes : Fin 3→Nat :=
  ![Fintype.card (RecoveryCalls.Control RecoveryRowComparison.sizes),6,2]
noncomputable def programs : (j : Fin 3)→Machine 9 (sizes j)
  | ⟨0,_⟩=>compareMachine
  | ⟨1,_⟩=>copyMachine
  | ⟨2,_⟩=>finish
  | ⟨n+3,h⟩=>False.elim (by omega)
def next (j : Fin 3) (_ : Fin (sizes j)) (scanned : Fin 9→Bool) : Option (Fin 3) :=
  if j.val=0 then if !(scanned 7) && scanned 2 then some 1 else some 2 else
    if j.val=1 then some 2 else none
noncomputable def machine := RecoveryCalls.machine sizes programs 0 next

theorem cell_trace (d : Data) (hd : d.Valid) :
    ∃ n≤16*d.key.length+32,Timed machine n (initialConfiguration machine d.tapes)
      (RecoveryCalls.stopped sizes (fun _=>0) d.done.tapes) := by
  have hc : d.compared.Valid := hd
  by_cases htake : d.found=false ∧ value d.key=value d.code
  · have h0 := (compare_ready d hd).call sizes programs 0 next 0 1 (by
      intro q
      change (if (!d.found && decide (value d.key=value d.code)) then some (1 : Fin 3) else some 2)=some 1
      simp [htake.1,htake.2])
    have h1 := (copy_ready d.compared hc).call sizes programs 0 next 1 2 (by intro q; rfl)
    have h2 := (finish_ready d.compared.copied).stop sizes programs 0 next 2 (by intro q; rfl)
    have h := (h0.trans h1).trans h2
    have hi : controlConfig (RecoveryCalls.code sizes 0) (initialConfiguration (programs 0) d.tapes)=
        initialConfiguration machine d.tapes := rfl
    rw [hi] at h
    change Timed machine ((8*d.key.length+20+1)+(8*d.key.length+8+1)+(1+1)) _ _ at h
    refine ⟨(8*d.key.length+20+1)+(8*d.key.length+8+1)+(1+1),by omega,?_⟩
    simpa only [Data.done,htake.1,Bool.false_eq_true,if_false,if_pos htake.2] using h
  · have h0 := (compare_ready d hd).call sizes programs 0 next 0 2 (by
      intro q
      change (if (!d.found && decide (value d.key=value d.code)) then some (1 : Fin 3) else some 2)=some 2
      cases hf : d.found <;> simp_all)
    have h1 := (finish_ready d.compared).stop sizes programs 0 next 2 (by intro q; rfl)
    have h := h0.trans h1
    have hi : controlConfig (RecoveryCalls.code sizes 0) (initialConfiguration (programs 0) d.tapes)=
        initialConfiguration machine d.tapes := rfl
    rw [hi] at h
    refine ⟨(8*d.key.length+20+1)+(1+1),by omega,?_⟩
    have he : d.done=d.compared.finished := by
      unfold Data.done
      cases hf : d.found <;> simp_all
    rw [he]
    exact h

theorem cell_run (d : Data) (hd : d.Valid) :
    ∃ r,run machine (16*d.key.length+32) d.tapes=some r ∧
      r.final.tapes=d.done.tapes ∧ (∀ i,r.final.heads i=0) ∧ r.steps≤16*d.key.length+32 := by
  obtain ⟨n,hn,h⟩ := cell_trace d hd
  obtain ⟨r,hr,hf,hs⟩ := h.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  have hm := run_moreFuel machine n (16*d.key.length+32-n) _ r hr
  rw [Nat.add_sub_of_le hn] at hm
  exact ⟨r,hm,by simp [hf,RecoveryCalls.stopped],by intro i; simp [hf,RecoveryCalls.stopped],hs.le.trans hn⟩

theorem done_valid (d : Data) (hd : d.Valid) : d.done.Valid := by
  unfold Data.done
  split
  · exact hd
  · split
    · exact ⟨hd.1,hd.2.1,hd.2.1.le,hd.2.2.2⟩
    · exact hd

theorem done_found (d : Data) : d.done.found=(d.found || decide (value d.key=value d.code)) := by
  unfold Data.done
  split <;> try rfl
  split <;> rfl

theorem done_saved (d : Data) : d.done.saved=
    (if d.found then d.saved else if value d.key=value d.code then d.count else d.saved) := by
  unfold Data.done
  split <;> try rfl
  split <;> rfl

end NearCubicWires.RepairOrdinary.RecoveryRowLookupCell
