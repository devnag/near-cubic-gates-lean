import Proof.MachineModel.OrdinaryMemoryCycle

/-! Repeatable actual memory-check body, with a one-bit cumulative result.
Only the record stream and flag cursor advance. Local scratch and previous-key
heads return to zero; the sticky bit records the conjunction of all checks.
No final scan of the flag history or global record rewind is needed. -/
namespace NearCubicWires.RepairOrdinary.MemoryBody
open LocalBitMultitape MemoryLog MemorySort MemoryCompare StablePartition SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workspace (K : ℕ) (record clone rank : List Bool) : Fin 7 → List Bool :=
  ![record, clone, List.replicate (4*K+1) false, List.replicate (8*K+3) false,
    rank, List.replicate (2*K+1) false, List.replicate (24*K+14) false]

theorem workspace_input (I W timestamp : ℕ) (current : Event)
    (record clone rank : List Bool) :
    RecordLoad.workspace (front I timestamp current) (key I W current) record clone rank =
      workspace (I+2) record clone rank := by
  funext i
  fin_cases i <;> simp [RecordLoad.workspace, RecordExtractReset.input, RecordExtract.input,
    RecordClone.input, RecordClone.raw, workspace, Fin.addCases,
    Nat.mul_add, Nat.add_assoc] <;> omega

theorem workspace_output (I W timestamp : ℕ) (current : Event) :
    RecordExtractReset.output (front I timestamp current) (key I W current) =
      workspace (I+2) (frame (front I timestamp current ++ key I W current))
        (frame (front I timestamp current ++ key I W current)) (frame (key I W current)) := by
  funext i
  fin_cases i <;> simp [RecordExtractReset.output, RecordExtract.finished, workspace,
    Fin.addCases, Nat.mul_add, Nat.add_assoc] <;> omega

def core : Machine 14 39 := TapeEmbedding.machine 1 MemoryCycle.machine
def advanceAction (scanned : Fin 14 → Bool) : Action 14 2 where
  nextControl := 1
  write := fun i => if i = 13 then some (scanned 13 && scanned 10) else none
  move := fun i => if i = 10 then .right else .stay
def advance : Machine 14 2 where
  descriptionBits := 0
  start := 0
  halted := fun i => i.val == 1
  rule := fun i scanned => if i = 0 then some (advanceAction scanned) else none
def machine : Machine 14 41 := Composition.machine core advance
def bodyCost (I : ℕ) : ℕ := 2*MemoryCycle.copyCap I+4

def config {s : ℕ} (state : Fin s) (I : ℕ) (record clone rank : List Bool)
    (source : List Bool) (position : ℕ) (previousKey : List Bool) (previousAfter : Bool)
    (flags : List Bool) (accepted : Bool) : Configuration 14 s :=
  TapeEmbedding.config (fun _ : Fin 1 => 0) (fun _ => [accepted])
    (MemoryCycle.ready state I (workspace (I+2) record clone rank)
      source position previousKey previousAfter flags flags.length)

def advanced (c : Configuration 14 2) : Configuration 14 2 := applyAction c (advanceAction c.scanned)

theorem advance_run (c : Configuration 14 2) (hc : c.control = 0) :
    runFrom advance 1 c = some
      { final := advanced c, steps := 1, peakTapeCells := max c.tapeCells (advanced c).tapeCells } := by
  have hn : advance.halted c.control = false := by simp [advance, hc]
  have hs : step advance c = some (advanced c) := by simp [step, advance, hc, advanced]
  have hh : advance.halted (advanced c).control = true := by
    simp [advance, advanced, applyAction, advanceAction]
  exact runFrom_step advance c (advanced c) _ hn hs (runFrom_zero_of_halted advance _ hh)

theorem body_run (I W timestamp : ℕ) (previous current : Event)
    (pre suffix recordBacking cloneBacking rankBacking flags : List Bool) (accepted : Bool)
    (hrecord : recordBacking.length ≤ 4*(I+2)+1)
    (hclone : cloneBacking.length ≤ 4*(I+2)+1)
    (hrank : rankBacking.length ≤ 2*(I+2)+1)
    (hp : cellCode W previous.cell < 2^(I+2))
    (hc : cellCode W current.cell < 2^(I+2))
    (hap : previous.cell.2 < 2^W) (hac : current.cell.2 < 2^W)
    (order : cellCode W previous.cell ≤ cellCode W current.cell) :
    let stored := frame (front I timestamp current ++ key I W current)
    ∃ r : ExecutionReceipt 14 41,
      runFrom machine (bodyCost I)
        (config machine.start I recordBacking cloneBacking rankBacking
          (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix) pre.length
          (key I W previous) previous.after flags accepted) = some r ∧
      r.final = config 40 I stored stored (frame (key I W current))
        (pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix)
        (pre.length+4*(I+2)+1) (key I W current) current.after
        (flags ++ [MemoryCheck.passed previous current]) (accepted && MemoryCheck.passed previous current) ∧
      r.steps = bodyCost I := by
  dsimp only
  obtain ⟨base, hb, hbf, hbs⟩ := MemoryCycle.cycle_run I W timestamp previous current
    pre suffix recordBacking cloneBacking rankBacking flags hrecord hclone hrank hp hc hap hac order
  rw [workspace_input] at hb
  rw [workspace_output] at hbf
  let source := pre ++ recordBits (encoded I (I+2) W timestamp current) ++ suffix
  let next := pre.length+4*(I+2)+1
  let stored := frame (front I timestamp current ++ key I W current)
  let pass := MemoryCheck.passed previous current
  let first := TapeEmbedding.receipt (fun _ : Fin 1 => 0) (fun _ => [accepted]) base
  have hfirst := TapeEmbedding.run_embed MemoryCycle.machine (fun _ : Fin 1 => 0)
    (fun _ => [accepted]) _ _ base hb
  let c := Composition.restart first.final advance.start
  have hc0 : c.control = 0 := rfl
  let second : ExecutionReceipt 14 2 :=
    ⟨advanced c, 1, max c.tapeCells (advanced c).tapeCells⟩
  have hsecond : runFrom advance 1 c = some second := advance_run c hc0
  have hflag : c.scanned 10 = pass := by
    change readTapeBit (base.final.tapes 10) (base.final.heads 10) = pass
    rw [hbf]
    change readTapeBit (flags ++ [pass]) flags.length = pass
    exact Streaming.read_append flags [] pass
  have haccepted : c.scanned 13 = accepted := by
    change readTapeBit [accepted] 0 = accepted
    rfl
  have hfinal : advanced c =
      config (1 : Fin 2) I stored stored (frame (key I W current)) source next
        (key I W current) current.after (flags ++ [pass]) (accepted && pass) := by
    apply configuration_ext
    · rfl
    · funext i
      fin_cases i <;> simp [advanced, applyAction, advanceAction, c, Composition.restart,
        first, TapeEmbedding.receipt, TapeEmbedding.config, hbf, config, MemoryCycle.ready,
        MemoryCycle.config, HeadMove.apply, Fin.addCases, next]
    · funext i
      change (match (advanceAction c.scanned).write i with
        | none => c.tapes i
        | some b => writeTapeBit (c.tapes i) (c.heads i) b) = _
      simp only [advanceAction, haccepted, hflag]
      fin_cases i <;> simp [c, Composition.restart,
        first, TapeEmbedding.receipt, TapeEmbedding.config, hbf, config, MemoryCycle.ready,
        MemoryCycle.config, Fin.addCases, source, stored, pass, writeTapeBit]
  have hj := Composition.run_join core advance (2*MemoryCycle.copyCap I+2) 1
    (config core.start I recordBacking cloneBacking rankBacking source pre.length
      (key I W previous) previous.after flags accepted) first second hfirst hsecond
  have htime : (2*MemoryCycle.copyCap I+2)+1+1 = bodyCost I := by simp [bodyCost, Nat.add_assoc]
  refine ⟨Composition.joinedReceipt first second, ?_, ?_, ?_⟩
  · rw [htime] at hj
    exact hj
  · change Composition.rightConfig 39 (advanced c) = _
    rw [hfinal]
    rfl
  · change base.steps+1+1 = _
    rw [hbs]
    exact htime

end NearCubicWires.RepairOrdinary.MemoryBody
