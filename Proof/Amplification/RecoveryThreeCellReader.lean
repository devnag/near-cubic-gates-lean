import Proof.Amplification.RecoveryClauseState

/-! The actual fixed-three-cell clause reader. Each nonempty cell preserves
its literal code in a different external field. A fourth call tests that
the tail is empty; all early failures stop with the physically cleared bit. -/
namespace NearCubicWires.RepairOrdinary.RecoveryThreeCellReader
open LocalBitMultitape RecoveryExecution RecoveryRootRound RecoveryClauseState
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

@[simp] theorem state_flag (s : State) : s.tapes 23=[s.flag] := rfl
@[simp] theorem after_flag (s : State) (which : Fin 3) :
    (s.after which).flag=decide (RadixSemantics.value s.bits≠0) := by
  by_cases hz : RadixSemantics.value s.bits=0 <;> simp [State.after,hz]
@[simp] theorem after_result (s : State) (which : Fin 3) : (s.after which).result=s.result := by
  by_cases hz : RadixSemantics.value s.bits=0 <;> simp [State.after,hz]

def flagMachine (bit : Bool) : Machine 28 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun q _ => if q.val=0 then
    some ⟨1,fun i => if i=27 then some bit else none,fun _ => .stay⟩ else none

theorem flag_ready (s : State) (bit : Bool) :
    ReadyRun (flagMachine bit) 1 s.tapes ({s with result:=bit} : State).tapes := by
  let final : Configuration 28 2 := ⟨1,fun _ => 0,({s with result:=bit} : State).tapes⟩
  have hs : step (flagMachine bit) (initialConfiguration (flagMachine bit) s.tapes)=some final := by
    apply congrArg some
    apply configuration_ext
    · rfl
    · funext i; rfl
    · funext i
      fin_cases i <;> simp [applyAction,flagMachine,State.tapes,State.core,final,initialConfiguration,
        writeTapeBit,Fin.addCases]
  obtain ⟨r,hr,hf,ht⟩ := (Timed.single (by rfl) hs).run (by rfl)
  exact ⟨r,hr,by rw [hf],by intro i; rw [hf],ht⟩

def s0 (s : State) : State := {s with result:=false}
def s1 (s : State) := (s0 s).after 0
def s2 (s : State) := (s1 s).after 1
def s3 (s : State) := (s2 s).after 2
def s4 (s : State) := (s3 s).after 0
def endState (s : State) : State :=
  if (s1 s).flag then
    if (s2 s).flag then
      if (s3 s).flag then
        if (s4 s).flag then s4 s else {s4 s with result:=true}
      else s3 s
    else s2 s
  else s1 s

def time (s : State) := 2+(RecoveryStoredListCell.time (s0 s).bits+1+
  if (s1 s).flag then RecoveryStoredListCell.time (s1 s).bits+1+
    if (s2 s).flag then RecoveryStoredListCell.time (s2 s).bits+1+
      if (s3 s).flag then RecoveryStoredListCell.time (s3 s).bits+1+
        if (s4 s).flag then 0 else 2
      else 0
    else 0
  else 0)

abbrev cellStates := Fintype.card (RecoveryCalls.Control RecoveryStoredListCell.sizes)
def sizes : Fin 6 → Nat := ![2,cellStates,cellStates,cellStates,cellStates,2]
noncomputable def programs : (j : Fin 6) → Machine 28 (sizes j)
  | ⟨0,_⟩ => flagMachine false
  | ⟨1,_⟩ => RecoveryClauseState.machine 0
  | ⟨2,_⟩ => RecoveryClauseState.machine 1
  | ⟨3,_⟩ => RecoveryClauseState.machine 2
  | ⟨4,_⟩ => RecoveryClauseState.machine 0
  | ⟨5,_⟩ => flagMachine true
  | ⟨n+6,h⟩ => False.elim (by omega)
def next (j : Fin 6) (_ : Fin (sizes j)) (scanned : Fin 28 → Bool) : Option (Fin 6) :=
  ![some 1,if scanned 23 then some 2 else none,if scanned 23 then some 3 else none,
    if scanned 23 then some 4 else none,if scanned 23 then none else some 5,none] j
noncomputable abbrev machine := RecoveryCalls.machine sizes programs 0 next

private theorem one_one (n : Nat) : 1+(1+n)=2+n := by omega

theorem reader_ready (s : State) (hv : s.Valid) :
    ReadyRun machine (time s) s.tapes (endState s).tapes := by
  have h0v : (s0 s).Valid := hv
  have h1v := after_valid (s0 s) 0 h0v
  have h2v := after_valid (s1 s) 1 h1v
  have h3v := after_valid (s2 s) 2 h2v
  have cell1 : ReadyRun (programs 1) (RecoveryStoredListCell.time (s0 s).bits) (s0 s).tapes (s1 s).tapes := cell_ready (s0 s) 0 h0v
  have cell2 : ReadyRun (programs 2) (RecoveryStoredListCell.time (s1 s).bits) (s1 s).tapes (s2 s).tapes := cell_ready (s1 s) 1 h1v
  have cell3 : ReadyRun (programs 3) (RecoveryStoredListCell.time (s2 s).bits) (s2 s).tapes (s3 s).tapes := cell_ready (s2 s) 2 h2v
  have cell4 : ReadyRun (programs 4) (RecoveryStoredListCell.time (s3 s).bits) (s3 s).tapes (s4 s).tapes := cell_ready (s3 s) 0 h3v
  have hc0 := (flag_ready s false).call sizes programs 0 next 0 1 (by intro q; rfl)
  have hin : controlConfig (RecoveryCalls.code sizes 0)
      (initialConfiguration (programs 0) s.tapes)=initialConfiguration machine s.tapes := rfl
  rw [hin] at hc0
  have hpath : Timed machine (time s) (initialConfiguration machine s.tapes)
      (RecoveryCalls.stopped sizes (fun _ => 0) (endState s).tapes) := by
    cases h1 : (s1 s).flag
    · have ht := cell1.stop sizes programs 0 next 1
        (by intro q; change (if readTapeBit ((s1 s).tapes 23) 0 then some 2 else none)=none
            rw [state_flag]; change (if (s1 s).flag then _ else _)=_; rw [h1]; rfl)
      simpa only [time,endState,h1,Bool.false_eq_true,↓reduceIte,Nat.add_assoc,Nat.add_zero,one_one] using hc0.trans ht
    · have hc1 := cell1.call sizes programs 0 next 1 2
        (by intro q; change (if readTapeBit ((s1 s).tapes 23) 0 then some 2 else none)=some 2
            rw [state_flag]; change (if (s1 s).flag then _ else _)=_; rw [h1]; rfl)
      cases h2 : (s2 s).flag
      · have ht := cell2.stop sizes programs 0 next 2
          (by intro q; change (if readTapeBit ((s2 s).tapes 23) 0 then some 3 else none)=none
              rw [state_flag]; change (if (s2 s).flag then _ else _)=_; rw [h2]; rfl)
        simpa only [time,endState,h1,h2,Bool.false_eq_true,↓reduceIte,Nat.add_assoc,Nat.add_zero,one_one] using (hc0.trans hc1).trans ht
      · have hc2 := cell2.call sizes programs 0 next 2 3
          (by intro q; change (if readTapeBit ((s2 s).tapes 23) 0 then some 3 else none)=some 3
              rw [state_flag]; change (if (s2 s).flag then _ else _)=_; rw [h2]; rfl)
        cases h3 : (s3 s).flag
        · have ht := cell3.stop sizes programs 0 next 3
            (by intro q; change (if readTapeBit ((s3 s).tapes 23) 0 then some 4 else none)=none
                rw [state_flag]; change (if (s3 s).flag then _ else _)=_; rw [h3]; rfl)
          simpa only [time,endState,h1,h2,h3,Bool.false_eq_true,↓reduceIte,Nat.add_assoc,Nat.add_zero,one_one] using ((hc0.trans hc1).trans hc2).trans ht
        · have hc3 := cell3.call sizes programs 0 next 3 4
            (by intro q; change (if readTapeBit ((s3 s).tapes 23) 0 then some 4 else none)=some 4
                rw [state_flag]; change (if (s3 s).flag then _ else _)=_; rw [h3]; rfl)
          cases h4 : (s4 s).flag
          · have hc4 := cell4.call sizes programs 0 next 4 5
              (by intro q; change (if readTapeBit ((s4 s).tapes 23) 0 then none else some 5)=some 5
                  rw [state_flag]; change (if (s4 s).flag then _ else _)=_; rw [h4]; rfl)
            have ht := (flag_ready (s4 s) true).stop sizes programs 0 next 5 (by intro q; rfl)
            simpa only [time,endState,h1,h2,h3,h4,Bool.false_eq_true,↓reduceIte,Nat.add_assoc,Nat.add_zero,one_one] using
              ((((hc0.trans hc1).trans hc2).trans hc3).trans hc4).trans ht
          · have ht := cell4.stop sizes programs 0 next 4
              (by intro q; change (if readTapeBit ((s4 s).tapes 23) 0 then none else some 5)=none
                  rw [state_flag]; change (if (s4 s).flag then _ else _)=_; rw [h4]; rfl)
            simpa only [time,endState,h1,h2,h3,h4,Bool.false_eq_true,↓reduceIte,Nat.add_assoc,Nat.add_zero,one_one] using
              (((hc0.trans hc1).trans hc2).trans hc3).trans ht
  obtain ⟨r,hr,hf,ht⟩ := hpath.run (by simp [machine,RecoveryCalls.machine,RecoveryCalls.stopped])
  exact ⟨r,hr,by simp [hf,RecoveryCalls.stopped],by intro i; simp [hf,RecoveryCalls.stopped],ht⟩

def budget (s : State) := 2097152*(s.bits.length+1)^2
private theorem four_costs (t0 t1 t2 t3 B : Nat) (b1 b2 b3 b4 : Bool)
    (h0 : t0≤262144*(B+1)^2) (h1 : t1≤262144*(B+1)^2)
    (h2 : t2≤262144*(B+1)^2) (h3 : t3≤262144*(B+1)^2) :
    2+(t0+1+if b1 then t1+1+if b2 then t2+1+if b3 then t3+1+
      if b4 then 0 else 2 else 0 else 0 else 0)≤2097152*(B+1)^2 := by
  have hp : 0<(B+1)^2 := by positivity
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

theorem time_bound (s : State) : time s≤budget s := by
  have h0 := RecoveryStoredListCell.time_bound (s0 s).bits
  have h1 := RecoveryStoredListCell.time_bound (s1 s).bits
  have h2 := RecoveryStoredListCell.time_bound (s2 s).bits
  have h3 := RecoveryStoredListCell.time_bound (s3 s).bits
  have hl1 : (s1 s).bits.length=s.bits.length := after_length (s0 s) 0
  have hl2 : (s2 s).bits.length=s.bits.length := (after_length (s1 s) 1).trans hl1
  have hl3 : (s3 s).bits.length=s.bits.length := (after_length (s2 s) 2).trans hl2
  change RecoveryStoredListCell.time (s0 s).bits ≤ 262144*(s.bits.length+1)^2 at h0
  unfold RecoveryStoredListCell.budget at h1 h2 h3
  rw [hl1] at h1
  rw [hl2] at h2
  rw [hl3] at h3
  exact four_costs _ _ _ _ _ _ _ _ _ h0 h1 h2 h3

end NearCubicWires.RepairOrdinary.RecoveryThreeCellReader
