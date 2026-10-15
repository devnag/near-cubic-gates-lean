import Proof.Wire_3_5.CompilerMachinePoolRun

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.Block
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay overlay_write overlay_length)

/-- Copy ones: while the source reads `1`, write `1` on the output and move both right; halt on `0`. -/
def ucopyM : Machine 2 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q sc =>
    if q.val = 0 then
      some (if sc 0 then ⟨0, ![none, some true], ![.right, .right]⟩ else ⟨1, fun _ => none, fun _ => .stay⟩)
    else none

theorem ucopy_one (S O : List Bool) (s o : ℕ) (hs : readTapeBit S s = true) :
    step ucopyM ⟨0, ![s, o], ![S, O]⟩ = some ⟨0, ![s + 1, o + 1], ![S, writeTapeBit O o true]⟩ := by
  simp [step, ucopyM, Configuration.scanned, hs]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem ucopy_end (S O : List Bool) (s o : ℕ) (hs : readTapeBit S s = false) :
    step ucopyM ⟨0, ![s, o], ![S, O]⟩ = some ⟨1, ![s, o], ![S, O]⟩ := by
  simp [step, ucopyM, Configuration.scanned, hs]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction]

theorem ucopy_timed (S : List Bool) (s0 : ℕ) (out BW : List Bool) :
    ∀ x j, j ≤ x → (∀ i < x, readTapeBit S (s0 + i) = true) →
      RecoveryExecution.Timed ucopyM (x - j)
        ⟨0, ![s0 + j, (out ++ List.replicate j true).length], ![S, overlay (out ++ List.replicate j true) BW]⟩
        ⟨0, ![s0 + x, (out ++ List.replicate x true).length], ![S, overlay (out ++ List.replicate x true) BW]⟩
  | x, j, hj, hS => by
    induction h : x - j generalizing j with
    | zero =>
      have : j = x := by omega
      subst this
      exact RecoveryExecution.Timed.refl (p := ucopyM) _
    | succ m ih =>
      have hjx : j < x := by omega
      have s1 := ucopy_one S (overlay (out ++ List.replicate j true) BW) (s0 + j) (out ++ List.replicate j true).length
        (hS j hjx)
      rw [overlay_write] at s1
      have e : out ++ List.replicate j true ++ [true] = out ++ List.replicate (j + 1) true := by
        simp [List.replicate_succ', List.append_assoc]
      rw [e] at s1
      have t1 := RecoveryExecution.Timed.single (p := ucopyM) rfl s1
      have t2 := ih (j + 1) (by omega) (by omega)
      have hl : (out ++ List.replicate j true).length + 1 = (out ++ List.replicate (j + 1) true).length := by simp; omega
      rw [hl] at t1
      have := t1.trans t2
      rwa [show 1 + m = m + 1 by omega] at this

/-- **Copy a unary block**: the source's `x` ones (then a `0`) are appended to the output. -/
theorem ucopy_run (pre rest out BW : List Bool) (x : ℕ) :
    Step ucopyM (x + 1) ![pre.length, out.length] ![pre ++ List.replicate x true ++ false :: rest, overlay out BW]
      ![pre.length + x, (out ++ List.replicate x true).length]
      ![pre ++ List.replicate x true ++ false :: rest, overlay (out ++ List.replicate x true) BW] := by
  set S := pre ++ List.replicate x true ++ false :: rest
  have hS : ∀ i < x, readTapeBit S (pre.length + i) = true := by
    intro i hi
    simp only [S]
    rw [List.append_assoc, read_suffix, read_prefix _ _ _ (by simpa using hi)]
    simp [readTapeBit, List.getD_eq_getElem?_getD, hi]
  have hE : readTapeBit S (pre.length + x) = false := by
    simp only [S]
    rw [List.append_assoc, read_suffix]
    have := read_suffix (List.replicate x true) (false :: rest) 0
    rw [List.length_replicate, Nat.add_zero] at this
    rw [this]; rfl
  have t := ucopy_timed S pre.length out BW x 0 (by omega) hS
  simp only [List.replicate_zero, List.append_nil, Nat.add_zero, Nat.sub_zero] at t
  have te := RecoveryExecution.Timed.single (p := ucopyM) rfl
    (ucopy_end S (overlay (out ++ List.replicate x true) BW) (pre.length + x) (out ++ List.replicate x true).length hE)
  have := t.trans te
  obtain ⟨r, hr, hf, hs⟩ := this.run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

/-- A unary copy with the source head returned to `0` (log on tape 2). -/
noncomputable def ucopyR := MaskedReset.machine ucopyM ![true, false]

theorem ucopyStep (rest out BW : List Bool) (x cap : ℕ) (hcap : x + 1 ≤ cap) :
    Step ucopyR (2 * (x + 1) + 2) ![0, out.length, 0]
      ![List.replicate x true ++ false :: rest, overlay out BW, List.replicate cap false]
      ![0, (out ++ List.replicate x true).length, 0]
      ![List.replicate x true ++ false :: rest, overlay (out ++ List.replicate x true) BW, List.replicate cap false] := by
  have h0 := ucopy_run [] rest out BW x
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at h0
  have hm := h0.mask ![true, false] (by intro i hi; fin_cases i <;> simp_all) hcap
  refine (hm.congr_in ?_ ?_).congr ?_ ?_ <;> funext i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;>
    (try fin_cases j) <;> rfl

end NearCubicWires.WireExponent3_5.CompilerMachine.Pool
