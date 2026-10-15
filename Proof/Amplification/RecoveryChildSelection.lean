import Proof.Amplification.RecoveryReusableUnpair

/-! Executed return of one decoded child to the fixed-width parser input.
The output of a repeated unpair call is consumed literally, including its
zero padding, retained driver and reset tape. -/
namespace NearCubicWires.RepairOrdinary.RecoveryChildSelection
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem ReadyRun.pad {t s time : Nat} {p : Machine t s}
    {input output : Fin t → List Bool} (h : ReadyRun p time input output)
    (capacities : Fin t → Nat) :
    ReadyRun p time (fun i => ZeroPadding.pad (capacities i) (input i))
      (fun i => ZeroPadding.pad (capacities i) (output i)) := by
  obtain ⟨base,hr,ht,hh,hs⟩ := h
  obtain ⟨r,hrun,hf,hsteps,_⟩ := ZeroPadding.run_config p capacities _ _ base hr
  refine ⟨r,hrun,?_,?_,hsteps.trans hs⟩
  · rw [hf]
    exact congrArg (fun tapes i => ZeroPadding.pad (capacities i) (tapes i)) ht
  · intro i
    rw [hf]
    exact hh i

def word (left : Bool) (bits : List Bool) :=
  if left then RecoveryFixedUnpair.leftWord bits else RecoveryFixedUnpair.rightWord bits

theorem word_length (left : Bool) (bits : List Bool) : (word left bits).length=bits.length := by
  cases left <;> simp [word,RecoveryFixedUnpair.word_lengths]

def slots (left : Bool) : Fin 4 → Fin 23 := ![if left then 17 else 18,0,16,22]
theorem slots_injective (left : Bool) : Function.Injective (slots left) := by
  cases left <;> decide

def output (left : Bool) (bits : List Bool) (resetCapacity : Nat) (i : Fin 23) : List Bool :=
  if i.val=0 then frame (word left bits) else RecoveryReusableUnpair.output bits resetCapacity i

noncomputable def machine (left : Bool) := RecoveryFocus.machine (slots left) RecoveryFieldCopy.machine

theorem copy_ready (left : Bool) (bits : List Bool) (resetCapacity : Nat) :
    ReadyRun (machine left) (8*bits.length+10)
      (RecoveryReusableUnpair.output bits resetCapacity) (output left bits resetCapacity) := by
  let S := RecoveryReusableUnpair.capacity bits
  let R := max resetCapacity (S+1)
  have hlen := word_length left bits
  have hcap : 4*bits.length+4≤R := by
    have hp : 0<(bits.length+1)^2 := by positivity
    have hb : 4*bits.length+4≤S+1 := by
      dsimp [S,RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity]
      nlinarith
    exact hb.trans (Nat.le_max_right _ _)
  have hcopy := ReadyRun.pad (RecoveryFieldCopy.copy_ready (word left bits) [false] (frame bits) R
    (by simp [hlen])) ![S,0,S,0]
  have hsource : Streaming.marks (word left bits) ++ [false] = frame (word left bits) := by
    simpa [frame] using (Streaming.frame_append (word left bits) []).symm
  simp only [hsource,hlen,Nat.max_eq_left hcap] at hcopy
  have hin : (fun i : Fin 4 => ZeroPadding.pad (![S,0,S,0] i)
      (![frame (word left bits),frame bits,CompareMachine.word bits.length,List.replicate R false] i)) =
      ![ZeroPadding.pad S (frame (word left bits)),frame bits,
        ZeroPadding.pad S (CompareMachine.word bits.length),List.replicate R false] := by
    funext i; fin_cases i <;> simp
  have hout : (fun i : Fin 4 => ZeroPadding.pad (![S,0,S,0] i)
      (![frame (word left bits),frame (word left bits),CompareMachine.word bits.length,List.replicate R false] i)) =
      ![ZeroPadding.pad S (frame (word left bits)),frame (word left bits),
        ZeroPadding.pad S (CompareMachine.word bits.length),List.replicate R false] := by
    funext i; fin_cases i <;> simp
  rw [hin,hout] at hcopy
  have h := hcopy.focus (slots left) (slots_injective left)
    (RecoveryReusableUnpair.output bits resetCapacity) (by
      intro j; cases left <;> fin_cases j
      all_goals first | rfl | exact ZeroPadding.pad_zero (frame bits))
  have he : install (slots left) (RecoveryReusableUnpair.output bits resetCapacity)
      ![ZeroPadding.pad S (frame (word left bits)),frame (word left bits),
        ZeroPadding.pad S (CompareMachine.word bits.length),List.replicate R false] =
      output left bits resetCapacity := by
    funext i
    cases left <;> fin_cases i
    all_goals first
      | exact install_slot (slots _) (slots_injective _) _ _ 0
      | exact install_slot (slots _) (slots_injective _) _ _ 1
      | exact install_slot (slots _) (slots_injective _) _ _ 2
      | exact install_slot (slots _) (slots_injective _) _ _ 3
      | exact install_other (slots _) _ _ _ (by intro j; fin_cases j <;> decide)
  rw [he] at h
  exact h

def backing (bits : List Bool) (resetCapacity : Nat) (i : Fin 20) :=
  RecoveryReusableUnpair.output bits resetCapacity ⟨i.val+1,by omega⟩

theorem backing_bound (bits : List Bool) (resetCapacity : Nat) (i : Fin 20) :
    (backing bits resetCapacity i).length≤RecoveryReusableUnpair.capacity bits := by
  exact (RecoveryReusableUnpair.output_support bits resetCapacity ⟨i.val+1,by omega⟩
    (by change i.val+1≠0; omega)).le

theorem next_input (left : Bool) (bits : List Bool) (resetCapacity : Nat) :
    output left bits resetCapacity = RecoveryReusableUnpair.input (word left bits)
      (max resetCapacity (RecoveryReusableUnpair.capacity bits+1)) (backing bits resetCapacity) := by
  have hcap : RecoveryReusableUnpair.capacity (word left bits)=RecoveryReusableUnpair.capacity bits := by
    simp [RecoveryReusableUnpair.capacity,RecoveryTapeSupport.capacity,word_length]
  funext i
  refine Fin.addCases (m := 1) (n := 22) (motive := fun j : Fin 23 =>
    output left bits resetCapacity j = RecoveryReusableUnpair.input (word left bits)
      (max resetCapacity (RecoveryReusableUnpair.capacity bits+1)) (backing bits resetCapacity) j) ?_ ?_ i
  · intro j; fin_cases j; rfl
  · intro j
    rw [RecoveryReusableUnpair.input,Fin.addCases_right]
    refine Fin.addCases (m := 21) (n := 1) (motive := fun k : Fin 22 =>
      output left bits resetCapacity (k.natAdd 1) =
        Fin.addCases (m := 21) (n := 1) (motive := fun _ => List Bool)
          (Fin.addCases (m := 20) (n := 1) (motive := fun _ => List Bool)
            (backing bits resetCapacity) (fun _ => List.replicate (RecoveryReusableUnpair.capacity (word left bits)) true))
          (fun _ => List.replicate (max resetCapacity (RecoveryReusableUnpair.capacity bits+1)) false) k) ?_ ?_ j
    · intro k
      rw [Fin.addCases_left]
      refine Fin.addCases (m := 20) (n := 1) (motive := fun l : Fin 21 =>
        output left bits resetCapacity ((l.castAdd 1).natAdd 1) =
          Fin.addCases (m := 20) (n := 1) (motive := fun _ => List Bool)
            (backing bits resetCapacity) (fun _ => List.replicate (RecoveryReusableUnpair.capacity (word left bits)) true) l) ?_ ?_ k
      · intro l
        rw [Fin.addCases_left]
        rw [output,if_neg (by simp)]
        apply congrArg (RecoveryReusableUnpair.output bits resetCapacity)
        apply Fin.ext
        simp [Nat.add_comm]
      · intro l
        fin_cases l
        change List.replicate (RecoveryReusableUnpair.capacity bits) true =
          List.replicate (RecoveryReusableUnpair.capacity (word left bits)) true
        rw [hcap]
    · intro k
      fin_cases k
      rfl

end NearCubicWires.RepairOrdinary.RecoveryChildSelection
