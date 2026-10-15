import Proof.PCP.VerifierDecodingRun
import Proof.MachineModel.OrdinaryControlPrefix
import Proof.MachineModel.OrdinaryStreamConcat

/-! Actual local lookup of a bounded literal field. The source is framed;
offset and width are supplied as explicitly charged unary tapes. Producing
and validating those counters belongs to the enclosing decoder. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.SliceMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (next : Fin 6) (inputMove outputMove skipMove countMove : HeadMove)
    (output : Option Bool := none) : Action 4 6 :=
  ⟨next, ![none, output, none, none], ![inputMove, outputMove, skipMove, countMove]⟩

def machine : Machine 4 6 where
  descriptionBits := 0
  start := 0
  halted := fun state => 4 ≤ state.val
  rule := fun state scanned =>
    if state.val = 0 then
      if scanned 2 then
        some (action (if scanned 0 then 1 else 5) .right .stay .stay .stay)
      else some (action 2 .stay .stay .stay .stay)
    else if state.val = 1 then some (action 0 .right .stay .right .stay)
    else if state.val = 2 then
      if scanned 3 then
        some (action (if scanned 0 then 3 else 5) .right .stay .stay .stay)
      else some (action 4 .stay .stay .stay .stay)
    else if state.val = 3 then some (action 2 .right .right .stay .right (some (scanned 0)))
    else none

def cfg (state : Fin 6) (source : List Bool) (pos : ℕ) (output : List Bool)
    (skip skipPos count countPos : ℕ) : Configuration 4 6 :=
  ⟨state, ![pos, output.length, skipPos, countPos],
    ![source, output, List.replicate skip true, List.replicate count true]⟩

@[simp] theorem cfg_cells (state : Fin 6) (source output : List Bool)
    (pos skip skipPos count countPos : ℕ) :
    (cfg state source pos output skip skipPos count countPos).tapeCells =
      source.length+output.length+skip+count := by
  simp [cfg, Configuration.tapeCells, Fin.sum_univ_succ, Nat.add_assoc]

theorem read_unary (n pos : ℕ) : readTapeBit (List.replicate n true) pos = decide (pos < n) := by
  induction n generalizing pos with
  | zero => simp [readTapeBit, List.getD]
  | succ n ih =>
    cases pos with
    | zero => simp [List.replicate_succ, readTapeBit, List.getD]
    | succ pos => simpa [List.replicate_succ, readTapeBit, List.getD] using ih pos

theorem skip_marker (pre tail out : List Bool) (skip k count j : ℕ) (hk : k < skip) :
    step machine (cfg 0 (pre ++ true :: tail) pre.length out skip k count j) =
      some (cfg 1 (pre ++ true :: tail) (pre.length+1) out skip k count j) := by
  simp [step, machine, cfg, Configuration.scanned, read_unary, hk, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem skip_bit (source out : List Bool) (pos skip k count j : ℕ) :
    step machine (cfg 1 source pos out skip k count j) =
      some (cfg 0 source (pos+1) out skip (k+1) count j) := by
  simp [step, machine, cfg]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem skip_done (source out : List Bool) (pos skip count j : ℕ) :
    step machine (cfg 0 source pos out skip skip count j) =
      some (cfg 2 source pos out skip skip count j) := by
  simp [step, machine, cfg, Configuration.scanned, read_unary]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem copy_marker (pre tail out : List Bool) (skip k count j : ℕ) (hj : j < count) :
    step machine (cfg 2 (pre ++ true :: tail) pre.length out skip k count j) =
      some (cfg 3 (pre ++ true :: tail) (pre.length+1) out skip k count j) := by
  simp [step, machine, cfg, Configuration.scanned, read_unary, hj, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem copy_bit (pre tail out : List Bool) (bit : Bool) (skip k count j : ℕ) :
    step machine (cfg 3 (pre ++ bit :: tail) pre.length out skip k count j) =
      some (cfg 2 (pre ++ bit :: tail) (pre.length+1) (out ++ [bit]) skip k count (j+1)) := by
  simp [step, machine, cfg, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action, Streaming.write_append]

theorem copy_done (source out : List Bool) (pos skip k count : ℕ) :
    step machine (cfg 2 source pos out skip k count count) =
      some (cfg 4 source pos out skip k count count) := by
  simp [step, machine, cfg, Configuration.scanned, read_unary]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem skip_prefix (bits pre tail out : List Bool) (done count j : ℕ) :
    let source := pre ++ Streaming.marks bits ++ tail
    let total := done+bits.length
    Prefix machine (source.length+out.length+total+count) (2*bits.length+1)
      (cfg 0 source pre.length out total done count j)
      (cfg 2 source (pre.length+2*bits.length) out total total count j) := by
  induction bits generalizing pre done with
  | nil =>
    simpa [Streaming.marks] using Prefix.step (by simp)
      (by rfl : machine.halted (0 : Fin 6) = false)
      (skip_done (pre ++ tail) out pre.length done count j) (Prefix.refl _ (by simp))
  | cons bit bits ih =>
    let source := pre ++ Streaming.marks (bit::bits) ++ tail
    let total := done+(bit::bits).length
    let space := source.length+out.length+total+count
    have he : (pre ++ [true,bit]) ++ Streaming.marks bits ++ tail = source := by
      simp [source, Streaming.marks, List.append_assoc]
    have ht := ih (pre ++ [true,bit]) (done+1)
    have htotal : done+1+bits.length = total := by simp [total]; omega
    dsimp only at ht
    rw [he, htotal] at ht
    have hpre : (pre ++ [true,bit]).length = pre.length+2 := by simp
    have hpos : pre.length+2+2*bits.length = pre.length+2*(bit::bits).length := by simp; omega
    rw [hpre, hpos] at ht
    have h1 := Prefix.step (by simp [space] : (cfg 1 source (pre.length+1) out total done count j).tapeCells ≤ space)
      (by rfl : machine.halted (1 : Fin 6) = false)
      (skip_bit source out (pre.length+1) total done count j)
      (by simpa [space, Nat.add_assoc] using ht)
    have h0 := Prefix.step (by simp [space] : (cfg 0 source pre.length out total done count j).tapeCells ≤ space)
      (by rfl : machine.halted (0 : Fin 6) = false)
      (by simpa [source, Streaming.marks, List.append_assoc] using
        skip_marker pre (bit :: Streaming.marks bits ++ tail) out total done count j (by simp [total])) h1
    simpa [space, source, total, Streaming.marks, Nat.mul_add, Nat.add_assoc] using h0

theorem copy_prefix (bits pre tail out : List Bool) (skip k done : ℕ) :
    let source := pre ++ Streaming.marks bits ++ tail
    let total := done+bits.length
    Prefix machine (source.length+out.length+bits.length+skip+total) (2*bits.length+1)
      (cfg 2 source pre.length out skip k total done)
      (cfg 4 source (pre.length+2*bits.length) (out++bits) skip k total total) := by
  induction bits generalizing pre out done with
  | nil =>
    simpa [Streaming.marks] using Prefix.step (by simp)
      (by rfl : machine.halted (2 : Fin 6) = false)
      (copy_done (pre ++ tail) out pre.length skip k done) (Prefix.refl _ (by simp))
  | cons bit bits ih =>
    let source := pre ++ Streaming.marks (bit::bits) ++ tail
    let total := done+(bit::bits).length
    let space := source.length+out.length+(bit::bits).length+skip+total
    have he : (pre ++ [true,bit]) ++ Streaming.marks bits ++ tail = source := by
      simp [source, Streaming.marks, List.append_assoc]
    have ht := ih (pre ++ [true,bit]) (out++[bit]) (done+1)
    have htotal : done+1+bits.length = total := by simp [total]; omega
    dsimp only at ht
    rw [he, htotal] at ht
    have hpre : (pre ++ [true,bit]).length = pre.length+2 := by simp
    have hpos : pre.length+2+2*bits.length = pre.length+2*(bit::bits).length := by simp; omega
    rw [hpre, hpos] at ht
    have htail : Prefix machine space (2*bits.length+1)
        (cfg 2 source (pre.length+2) (out++[bit]) skip k total (done+1))
        (cfg 4 source (pre.length+2*(bit::bits).length) (out++bit::bits) skip k total total) := by
      simpa [space, List.append_assoc, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ht
    have h1 := Prefix.step (by simp [space] :
        (cfg 3 source (pre.length+1) out skip k total done).tapeCells ≤ space)
      (by rfl : machine.halted (3 : Fin 6) = false)
      (by simpa [source, Streaming.marks, List.append_assoc] using
        copy_bit (pre++[true]) (Streaming.marks bits++tail) out bit skip k total done)
      (by simpa [source, Streaming.marks, List.append_assoc, Nat.add_assoc] using htail)
    have h0 := Prefix.step (by simp [space] :
        (cfg 2 source pre.length out skip k total done).tapeCells ≤ space)
      (by rfl : machine.halted (2 : Fin 6) = false)
      (by simpa [source, Streaming.marks, List.append_assoc] using
        copy_marker pre (bit :: Streaming.marks bits ++ tail) out skip k total done (by simp [total])) h1
    simpa [space, source, total, Streaming.marks, Nat.mul_add, Nat.add_assoc] using h0

def input (preBits payload suffix : List Bool) : Fin 4 → List Bool :=
  ![frame (preBits++payload++suffix), [], List.replicate preBits.length true,
    List.replicate payload.length true]

/-- Both small counter tapes are explicit premises of this actual run.
The ordinary decoder must produce them after its scalar guards. -/
theorem field_run (preBits payload suffix : List Bool) :
    ∃ receipt : ExecutionReceipt 4 6,
      run machine (2*preBits.length+2*payload.length+2) (input preBits payload suffix) = some receipt ∧
      receipt.final = cfg 4 (frame (preBits++payload++suffix))
        (2*preBits.length+2*payload.length) payload preBits.length preBits.length payload.length payload.length ∧
      receipt.steps = 2*preBits.length+2*payload.length+2 ∧
      receipt.peakTapeCells ≤ 4*(preBits++payload++suffix).length+1 := by
  let source := frame (preBits++payload++suffix)
  let space := source.length+preBits.length+2*payload.length
  have hsource : Streaming.marks preBits ++ Streaming.marks payload ++ frame suffix = source := by
    simp [source, Streaming.frame_append, List.append_assoc]
  have hs := skip_prefix preBits [] (Streaming.marks payload ++ frame suffix) [] 0 payload.length 0
  dsimp only at hs
  simp only [List.nil_append, List.length_nil, Nat.zero_add] at hs
  rw [← List.append_assoc, hsource] at hs
  have hc := copy_prefix payload (Streaming.marks preBits) (frame suffix) [] preBits.length preBits.length 0
  dsimp only at hc
  simp only [List.length_nil, List.nil_append, Nat.zero_add, Streaming.marks_length] at hc
  rw [hsource] at hc
  have hskip : Prefix machine space (2*preBits.length+1)
      (cfg 0 source 0 [] preBits.length 0 payload.length 0)
      (cfg 2 source (2*preBits.length) [] preBits.length preBits.length payload.length 0) :=
    hs.enlarge (by dsimp [space]; omega)
  have hcopy : Prefix machine space (2*payload.length+1)
      (cfg 2 source (2*preBits.length) [] preBits.length preBits.length payload.length 0)
      (cfg 4 source (2*preBits.length+2*payload.length) payload preBits.length preBits.length payload.length payload.length) := by
    simpa [space, two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
  have hwhole := hskip.trans hcopy
  obtain ⟨receipt, hr, hf, ht, hp⟩ := hwhole.run (by rfl) (by simp [space]; omega)
  have hi : cfg 0 source 0 [] preBits.length 0 payload.length 0 =
      initialConfiguration machine (input preBits payload suffix) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> rfl
    · rfl
  rw [hi] at hr
  have htime : (2*preBits.length+1)+(2*payload.length+1) = 2*preBits.length+2*payload.length+2 := by omega
  rw [htime] at hr ht
  refine ⟨receipt, hr, hf, ht, hp.trans ?_⟩
  simp only [space, source, frame_length, List.length_append]
  omega

end NearCubicWires.RepairSource.VerifierDecoding.SliceMachine
