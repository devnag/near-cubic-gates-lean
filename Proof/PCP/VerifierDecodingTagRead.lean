import Proof.PCP.VerifierDecodingTagKernel

/-! Complete constant-width literal reads for presence bits, two-bit state
flags, and four-bit write/move tags. All three share the same finite reader;
truncated fields return its rejecting control without a padded-value guess. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.TagMachine
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def prefixWord (bits : Word) (n : ℕ) := (List.ofFn bits).take n
@[simp] theorem prefixWord_length (bits : Word) (n : ℕ) (hn : n ≤ 4) : (prefixWord bits n).length = n := by
  simp [prefixWord,Nat.min_eq_left hn]
theorem prefixWord_succ (bits : Word) (n : ℕ) (hn : n < 4) :
    prefixWord bits (n+1) = prefixWord bits n ++ [bits ⟨n,hn⟩] := by
  have hl : n < (List.ofFn bits).length := by simpa only [List.length_ofFn] using hn
  have hg : (List.ofFn bits)[n] = bits ⟨n,hn⟩ := List.getElem_ofFn hl
  exact (List.take_succ_eq_append_getElem hl).trans
    (congrArg (fun bit => (List.ofFn bits).take n ++ [bit]) hg)

theorem read_prefix (pre tail : List Bool) (bits : Word) (limit : Fin 5) (n : ℕ) (hn : n ≤ limit.val) :
    let source := pre++Streaming.marks (prefixWord bits n)++tail
    Prefix (machine limit) source.length (2*n)
      (cfg 0 (fun _ => false) source pre.length)
      (cfg ⟨2*n,by omega⟩ (received bits n) source (pre.length+2*n)) := by
  induction n generalizing tail with
  | zero =>
    simp only [prefixWord,List.take_zero,Streaming.marks,List.flatMap_nil,List.append_nil,
      Nat.mul_zero,Nat.add_zero,received_zero]
    exact Prefix.refl _ (by simp)
  | succ n ih =>
    have h4 : n < 4 := by omega
    let before := pre++Streaming.marks (prefixWord bits n)
    let source := pre++Streaming.marks (prefixWord bits (n+1))++tail
    have hb : before.length = pre.length+2*n := by simp [before,Streaming.marks_length,prefixWord_length bits n (by omega)]
    have he : before++true::bits ⟨n,h4⟩::tail = source := by
      simp [before,source,prefixWord_succ bits n h4,Streaming.marks,List.append_assoc]
    have hp := ih (true::bits ⟨n,h4⟩::tail) (by omega)
    dsimp only at hp
    change Prefix (machine limit) (before++true::bits ⟨n,h4⟩::tail).length (2*n)
      (cfg 0 (fun _ => false) (before++true::bits ⟨n,h4⟩::tail) pre.length)
      (cfg ⟨2*n,by omega⟩ (received bits n) (before++true::bits ⟨n,h4⟩::tail) (pre.length+2*n)) at hp
    rw [he] at hp
    have ht := bit_prefix before tail bits n limit (by omega)
    dsimp only at ht
    rw [he,hb] at ht
    have hj := hp.trans ht
    have htime : 2*n+2=2*(n+1) := by omega
    simpa only [htime,Nat.add_assoc] using hj

theorem read_run (pre tail : List Bool) (bits : Word) (limit : Fin 5) :
    let source := pre++Streaming.marks (prefixWord bits limit.val)++tail
    ∃ receipt,
      runFrom (machine limit) (2*limit.val) (cfg 0 (fun _ => false) source pre.length) = some receipt ∧
      receipt.final = cfg ⟨2*limit.val,by omega⟩ (received bits limit.val) source (pre.length+2*limit.val) ∧
      receipt.steps = 2*limit.val ∧ receipt.peakTapeCells ≤ source.length := by
  exact (read_prefix pre tail bits limit limit.val (Nat.le_refl _)).run
    (by simp [machine,cfg]) (by simp)

theorem reject_run (pre : List Bool) (bits : Word) (limit : Fin 5) (n : ℕ) (hn : n < limit.val) :
    let source := pre++frame (prefixWord bits n)
    ∃ receipt,
      runFrom (machine limit) (2*n+1) (cfg 0 (fun _ => false) source pre.length) = some receipt ∧
      receipt.final = rejected source (pre.length+2*n+1) ∧
      receipt.steps = 2*n+1 ∧ receipt.peakTapeCells ≤ source.length := by
  let before := pre++Streaming.marks (prefixWord bits n)
  let source := pre++frame (prefixWord bits n)
  have hb : before.length = pre.length+2*n := by simp [before,Streaming.marks_length,prefixWord_length bits n (by omega)]
  have he : before++[false] = source := by
    have h := Streaming.frame_append (prefixWord bits n) []
    simpa [before,source,RepairOrdinary.frame,List.append_assoc] using congrArg (fun x => pre++x) h.symm
  have hp := read_prefix pre [false] bits limit n (by omega)
  dsimp only at hp
  change Prefix (machine limit) (before++[false]).length (2*n)
    (cfg 0 (fun _ => false) (before++[false]) pre.length)
    (cfg ⟨2*n,by omega⟩ (received bits n) (before++[false]) (pre.length+2*n)) at hp
  rw [he] at hp
  have hs := missing_step before (received bits n) n limit hn
  rw [he,hb] at hs
  have ht : Prefix (machine limit) source.length 1
      (cfg ⟨2*n,by omega⟩ (received bits n) source (pre.length+2*n))
      (rejected source (pre.length+2*n+1)) := Prefix.step (by simp) (by simp [machine,cfg]; omega) hs (Prefix.refl _ (by simp))
  exact (hp.trans ht).run (by simp [machine,rejected]) (by simp)

end NearCubicWires.RepairSource.VerifierDecoding.TagMachine
