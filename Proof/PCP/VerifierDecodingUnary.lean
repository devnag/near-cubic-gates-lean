import Proof.PCP.VerifierDecodingRun
import Proof.MachineModel.OrdinaryControlPrefix
import Proof.MachineModel.OrdinaryStreamConcat

/-! Actual bounded unary-header parsing on the shared framed tape. Each true
payload bit emits one unary count cell; the first false payload terminates
successfully, while the frame delimiter rejects a missing unary delimiter. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.UnaryMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def action (next : Fin 4) (move : HeadMove) (write : Option Bool := none) : Action 2 4 :=
  ⟨next, ![none, write], ![.right, move]⟩

def machine : Machine 2 4 where
  descriptionBits := 0
  start := 0
  halted := fun state => 2 ≤ state.val
  rule := fun state scanned =>
    if state.val = 0 then some (action (if scanned 0 then 1 else 3) .stay)
    else if state.val = 1 then
      if scanned 0 then some (action 0 .right (some true)) else some (action 2 .stay)
    else none

def cfg (state : Fin 4) (source : List Bool) (pos count : ℕ) : Configuration 2 4 :=
  ⟨state, ![pos, count], ![source, List.replicate count true]⟩

@[simp] theorem cfg_cells (state : Fin 4) (source : List Bool) (pos count : ℕ) :
    (cfg state source pos count).tapeCells = source.length+count := by
  simp [cfg, Configuration.tapeCells, Fin.sum_univ_succ]

theorem marker_step (pre tail : List Bool) (count : ℕ) (marker : Bool) :
    step machine (cfg 0 (pre ++ marker :: tail) pre.length count) =
      some (cfg (if marker then 1 else 3) (pre ++ marker :: tail) (pre.length+1) count) := by
  simp [step, machine, cfg, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem true_step (pre tail : List Bool) (count : ℕ) :
    step machine (cfg 1 (pre ++ true :: tail) pre.length count) =
      some (cfg 0 (pre ++ true :: tail) (pre.length+1) (count+1)) := by
  simp [step, machine, cfg, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]
    have h := Streaming.write_append (List.replicate count true) true
    simpa only [List.replicate_add, List.replicate_one, List.length_replicate] using h

theorem false_step (pre tail : List Bool) (count : ℕ) :
    step machine (cfg 1 (pre ++ false :: tail) pre.length count) =
      some (cfg 2 (pre ++ false :: tail) (pre.length+1) count) := by
  simp [step, machine, cfg, Configuration.scanned, Streaming.read_append]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, action, HeadMove.apply]
  · funext i; fin_cases i <;> simp [applyAction, action]

theorem true_prefix (n : ℕ) (pre tail : List Bool) (count : ℕ) :
    let source := pre ++ Streaming.marks (List.replicate n true) ++ tail
    Prefix machine (source.length+count+n) (2*n)
      (cfg 0 source pre.length count)
      (cfg 0 source (pre.length+2*n) (count+n)) := by
  induction n generalizing pre count with
  | zero => simp [Streaming.marks]; exact Prefix.refl _ (by simp)
  | succ n ih =>
    let source := pre ++ Streaming.marks (List.replicate (n+1) true) ++ tail
    let space := source.length+count+(n+1)
    have he : (pre++[true,true]) ++ Streaming.marks (List.replicate n true) ++ tail = source := by
      simp [source, List.replicate_succ, Streaming.marks, List.append_assoc]
    have ht := ih (pre++[true,true]) (count+1)
    dsimp only at ht
    rw [he] at ht
    have hp : (pre++[true,true]).length = pre.length+2 := by simp
    rw [hp] at ht
    have htail : Prefix machine space (2*n)
        (cfg 0 source (pre.length+2) (count+1))
        (cfg 0 source (pre.length+2*(n+1)) (count+(n+1))) := by
      simpa [space, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht
    have h1 := Prefix.step (by simp [space] : (cfg 1 source (pre.length+1) count).tapeCells ≤ space)
      (by rfl : machine.halted (1 : Fin 4) = false)
      (by simpa [source, List.replicate_succ, Streaming.marks, List.append_assoc] using
        true_step (pre++[true]) (Streaming.marks (List.replicate n true) ++ tail) count)
      (by simpa [source, List.replicate_succ, Streaming.marks, List.append_assoc, Nat.add_assoc] using htail)
    have h0 := Prefix.step (by simp [space] : (cfg 0 source pre.length count).tapeCells ≤ space)
      (by rfl : machine.halted (0 : Fin 4) = false)
      (by simpa [source, List.replicate_succ, Streaming.marks, List.append_assoc] using
        marker_step pre (true :: Streaming.marks (List.replicate n true) ++ tail) count true) h1
    simpa [space, source, List.replicate_succ, Streaming.marks, List.append_assoc, Nat.mul_add, Nat.add_assoc] using h0

theorem parse_run (n : ℕ) (pre fields : List Bool) :
    ∃ receipt : ExecutionReceipt 2 4,
      runFrom machine (2*n+2)
        (cfg 0 (pre ++ frame (List.replicate n true ++ false::fields)) pre.length 0) = some receipt ∧
      receipt.final = cfg 2 (pre ++ frame (List.replicate n true ++ false::fields)) (pre.length+2*n+2) n ∧
      receipt.steps = 2*n+2 ∧
      receipt.peakTapeCells ≤ (pre ++ frame (List.replicate n true ++ false::fields)).length+n := by
  let source := pre ++ frame (List.replicate n true ++ false::fields)
  let before := pre ++ Streaming.marks (List.replicate n true)
  let space := source.length+n
  have hsource : before ++ true :: false :: frame fields = source := by
    simp [before, source, Streaming.frame_append, RepairSource.frame, RepairOrdinary.frame, List.append_assoc]
  have hbefore : before.length = pre.length+2*n := by simp [before, Streaming.marks_length]
  have htail : Prefix machine space 2 (cfg 0 source before.length n)
      (cfg 2 source (before.length+2) n) := by
    have h1 := Prefix.step (by simp [space] : (cfg 1 source (before.length+1) n).tapeCells ≤ space)
      (by rfl : machine.halted (1 : Fin 4) = false)
      (by simpa [hsource, List.append_assoc] using false_step (before++[true]) (frame fields) n)
      (Prefix.refl _ (by simp [space] : (cfg 2 source (before.length+2) n).tapeCells ≤ space))
    have h0 := Prefix.step (by simp [space] : (cfg 0 source before.length n).tapeCells ≤ space)
      (by rfl : machine.halted (0 : Fin 4) = false)
      (by simpa [hsource] using marker_step before (false::frame fields) n true) h1
    simpa [Nat.add_assoc] using h0
  rw [hbefore] at htail
  have hp := true_prefix n pre (true :: false :: frame fields) 0
  dsimp only at hp
  have hs : pre ++ Streaming.marks (List.replicate n true) ++ true :: false :: frame fields = source := hsource
  rw [hs] at hp
  simp only [Nat.zero_add, Nat.add_zero] at hp
  have hwhole := hp.trans htail
  obtain ⟨receipt, hr, hf, ht, hspace⟩ := hwhole.run (by rfl) (by simp)
  exact ⟨receipt, hr, by simpa [Nat.add_assoc] using hf, ht, hspace⟩

theorem reject_run (n : ℕ) (pre : List Bool) :
    ∃ receipt : ExecutionReceipt 2 4,
      runFrom machine (2*n+1)
        (cfg 0 (pre ++ frame (List.replicate n true)) pre.length 0) = some receipt ∧
      receipt.final = cfg 3 (pre ++ frame (List.replicate n true)) (pre.length+2*n+1) n ∧
      receipt.steps = 2*n+1 ∧
      receipt.peakTapeCells ≤ (pre ++ frame (List.replicate n true)).length+n := by
  let source := pre ++ frame (List.replicate n true)
  let before := pre ++ Streaming.marks (List.replicate n true)
  let space := source.length+n
  have hs : before ++ [false] = source := by
    have h := Streaming.frame_append (List.replicate n true) []
    simp only [List.append_nil, RepairOrdinary.frame] at h
    change (pre ++ Streaming.marks (List.replicate n true)) ++ [false] =
      pre ++ RepairOrdinary.frame (List.replicate n true)
    rw [List.append_assoc]
    exact congrArg (fun bits : List Bool => pre ++ bits) h.symm
  have hb : before.length = pre.length+2*n := by simp [before, Streaming.marks_length]
  have ht : Prefix machine space 1 (cfg 0 source before.length n) (cfg 3 source (before.length+1) n) :=
    Prefix.step (by simp [space]) (by rfl)
      (by simpa [hs] using marker_step before [] n false) (Prefix.refl _ (by simp [space]))
  rw [hb] at ht
  have hp := true_prefix n pre [false] 0
  dsimp only at hp
  have hs' : pre ++ Streaming.marks (List.replicate n true) ++ [false] = source := hs
  rw [hs'] at hp
  simp only [Nat.zero_add, Nat.add_zero] at hp
  obtain ⟨receipt, hr, hf, hsteps, hspace⟩ := (hp.trans ht).run (by rfl) (by simp)
  exact ⟨receipt, hr, hf, hsteps, hspace⟩

theorem unary_decomposition {word fields : List Bool} {n : ℕ}
    (h : unary word = some (n, fields)) : word = List.replicate n true ++ false::fields := by
  induction word generalizing n with
  | nil => simp [unary] at h
  | cons bit word ih =>
    cases bit with
    | false =>
      simp only [unary, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl,rfl⟩ := h
      rfl
    | true =>
      cases hu : unary word with
      | none => simp [unary, hu] at h
      | some pair =>
        rcases pair with ⟨count,rest⟩
        simp only [unary, hu, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        simp only [List.replicate_succ, List.cons_append, ih hu]

theorem unary_none {word : List Bool} (h : unary word = none) : word = List.replicate word.length true := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
    cases bit with
    | false => simp [unary] at h
    | true =>
      have hn : unary word = none := by
        cases hu : unary word with
        | none => rfl
        | some result => simp only [unary, hu, Option.map_some, reduceCtorEq] at h
      simp only [List.length_cons, List.replicate_succ]
      exact congrArg (List.cons true) (ih hn)

/-- Total ordinary header parsing, including malformed inputs, within a
linear bit-time bound. The successful parser allocates its count itself. -/
theorem bounded_parse (word : List Bool) :
    ∃ receipt : ExecutionReceipt 2 4,
      run machine (2*word.length+2) ![frame word, []] = some receipt ∧
      receipt.peakTapeCells ≤ 3*word.length+1 ∧
      (receipt.final.control = 2 ↔ (unary word).isSome = true) := by
  cases hu : unary word with
  | none =>
    have hw := unary_none hu
    obtain ⟨r, hr, hf, ht, hp⟩ := reject_run word.length []
    have hi : cfg 0 ([] ++ frame (List.replicate word.length true)) 0 0 =
        initialConfiguration machine ![frame word, []] := by
      rw [← hw]
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · rfl
    simp only [List.length_nil] at hr
    rw [hi] at hr
    have hm := RepairOrdinary.runFrom_moreFuel machine (2*word.length+1) 1 _ r hr
    have htime : (2*word.length+1)+1 = 2*word.length+2 := by omega
    rw [htime] at hm
    refine ⟨r, hm, ?_, ?_⟩
    · simp only [List.nil_append, RepairSource.frame, RepairOrdinary.frame_length, List.length_replicate] at hp
      omega
    · rw [hf]
      simp [cfg]
  | some pair =>
    rcases pair with ⟨n,fields⟩
    have hw := unary_decomposition hu
    have hn : n+1 ≤ word.length := by have h := unary_bounded hu; omega
    obtain ⟨r, hr, hf, ht, hp⟩ := parse_run n [] fields
    have hi : cfg 0 ([] ++ frame (List.replicate n true ++ false::fields)) 0 0 =
        initialConfiguration machine ![frame word, []] := by
      rw [← hw]
      apply configuration_ext
      · rfl
      · funext i; fin_cases i <;> rfl
      · rfl
    simp only [List.length_nil] at hr
    rw [hi] at hr
    have hm := RepairOrdinary.runFrom_moreFuel machine (2*n+2) (2*word.length+2-(2*n+2)) _ r hr
    have htime : (2*n+2)+(2*word.length+2-(2*n+2)) = 2*word.length+2 := by omega
    refine ⟨r, by rw [htime] at hm; exact hm, ?_, ?_⟩
    · simp only [List.nil_append] at hp
      rw [← hw] at hp
      simp only [RepairSource.frame, RepairOrdinary.frame_length] at hp
      omega
    · rw [hf]
      simp [cfg]

end NearCubicWires.RepairSource.VerifierDecoding.UnaryMachine
