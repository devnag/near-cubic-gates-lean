import Proof.Packets.PacketFamilyKeys
import Proof.MachineModel.BlockLoop
import Proof.MachineModel.BlockWordFunction
import Proof.MachineModel.OrdinaryZeroUnpadding

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketFamilyParent
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.BlockPlatform
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource.VerifierDecoding
open FixedLivePackets PacketProduction
noncomputable section

/-- The framed-input bank `Program.inputTapes` builds. -/
def inBank (n : ℕ) (w : List Bool) : Fin n → List Bool :=
  fun i => if i.val = 0 then frame w else []

/-! ## The cleanup form consumed here (to be discharged by `Block.scrub`) -/

structure ScrubForm (t : ℕ) (S : Fin t → Bool) where
  extra : ℕ
  states : ℕ → ℕ
  wrap : {s : ℕ} → Machine t s → Machine (t + extra) (states s)
  residentH : ℕ → Fin extra → ℕ
  residentA : ℕ → Fin extra → List Bool
  cost : ℕ → ℕ → ℕ
  factor : ℕ
  cost_le : ∀ n R, cost n R ≤ factor * (n + R + 1)
  run : ∀ {s : ℕ} (M : Machine t s) (n R : ℕ) (H H' : Fin t → ℕ) (A A' : Fin t → List Bool),
    Step M n H A H' A' → n + 1 ≤ R →
    (∀ i, S i = true → H i = 0 ∧ (A i).length ≤ R) →
    Step (wrap M) (cost n R) (Fin.addCases H (residentH R)) (Fin.addCases A (residentA R))
      (Fin.addCases (fun i => if S i then 0 else H' i) (residentH R))
      (Fin.addCases (fun i => if S i then List.replicate R false else A' i) (residentA R))

variable {selector : CyclicChoice.Laws} {a : DecompositionAlgorithm}

/-! ## The per-row bank -/

/-- The row bank. Output port holds the accumulated stream with its head at the
append end; scratch ports hold `replicate (width r) false`; cursor ports hold
the current key's code; every other port is a request resident, and tape `0`
keeps the framed request input. -/
structure Layout (a : DecompositionAlgorithm) (K : RowKeys a) where
  tapes : ℕ
  output : Fin tapes
  outputFresh : output.val ≠ 0
  scratch : Fin tapes → Bool
  scratchOutput : scratch output = false
  cursorPort : Fin tapes → Bool
  resident : Request → Fin tapes → List Bool
  cursor : ∀ r : Request, Option (K.Key r) → Fin tapes → List Bool
  inputResident : ∀ r (i : Fin tapes), i.val = 0 →
    scratch i = false ∧ cursorPort i = false ∧ resident r i = frame (Request.input a r)
  width : Request → ℕ
  widthCoefficient : ℕ
  widthDegree : ℕ
  width_le : ∀ r, width r ≤ widthCoefficient * (r.smallSize a)^widthDegree

namespace Layout
variable {K : RowKeys a} (L : Layout a K)

def heads (out : List Bool) : Fin L.tapes → ℕ :=
  fun i => if i = L.output then out.length else 0

def bank (r : Request) (c : Option (K.Key r)) (out : List Bool) : Fin L.tapes → List Bool :=
  fun i => if i = L.output then out
    else if L.scratch i then List.replicate (L.width r) false
    else if L.cursorPort i then L.cursor r c i else L.resident r i
end Layout

/-- The exact packet word of one row, as the consumer defines it. -/
def rowWord (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) (K : RowKeys a)
    (r : Request) (k : K.Key r) : List Bool :=
  ExternalRowFamily.rawWord a (r.family a) (Packets.geometry selector (r.family a)) (K.decode r k)

/-! ## The remaining duties, one structure each -/

/-- **P1, the per-row writer, in reusable form.** One machine fixed before any
request. For every actual key and every accumulated prefix `out`, it appends
exactly `rowWord k`; off the scratch set every head and tape is exactly the
next row's (kept ports unchanged, output head at the new end); the scratch
exit is unconstrained. Cost is a fixed power of `smallSize`. -/
structure RowWriter (selector : CyclicChoice.Laws) {K : RowKeys a} (L : Layout a K) where
  states : ℕ
  machine : Machine L.tapes states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * (r.smallSize a)^degree
  write : ∀ r (k : K.Key r), k ∈ K.keys r → ∀ out : List Bool,
    ∃ (H' : Fin L.tapes → ℕ) (A' : Fin L.tapes → List Bool),
      Step machine (cost r) (L.heads out) (L.bank r (some k) out) H' A' ∧
      ∀ i, L.scratch i = false →
        H' i = L.heads (out ++ rowWord selector a K r k) i ∧
        A' i = L.bank r (some k) (out ++ rowWord selector a K r k) i

/-- **The row-key cursor.** From the code of `keys[j]` to the code of
`keys[j+1]?` (`none` after the last row), in exactly the key order; output,
scratch and residents unchanged, all heads back. -/
structure CursorAdvance {K : RowKeys a} (L : Layout a K) where
  states : ℕ
  machine : Machine L.tapes states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * (r.smallSize a)^degree
  advance : ∀ r (j : ℕ), j < (K.keys r).length → ∀ out : List Bool,
    Step machine (cost r) (L.heads out) (L.bank r (K.keys r)[j]? out)
      (L.heads out) (L.bank r (K.keys r)[j+1]? out)

/-- **Setup: drivers, cursor start, residents.** From the framed request input
(false blanks are free, `blank`), produce the loop's first cell: the unary
row-count driver `CompareMachine.word rows` at head `1` on the added tape, the
row bank at `keys[0]?` with empty output, and the scrub residents at width
`R` (including the physical `replicate R true` driver). Cost carries the one
family-row factor. -/
structure Setup {K : RowKeys a} (L : Layout a K) (C : ScrubForm L.tapes L.scratch) where
  states : ℕ
  machine : Machine (L.tapes + C.extra + 1) states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * ((r.family a).rows.length + 1) * (r.smallSize a)^degree
  blank : Request → Fin (L.tapes + C.extra + 1) → ℕ
  blankOutput : ∀ r, blank r ((L.output.castAdd C.extra).castAdd 1) = 0
  run : ∀ r, Step machine (cost r) (fun _ => 0)
    (fun i => ZeroPadding.pad (blank r i) (inBank (L.tapes + C.extra + 1) (Request.input a r) i))
    (Fin.addCases (Fin.addCases (L.heads []) (C.residentH (L.width r))) (fun _ : Fin 1 => 1))
    (Fin.addCases (Fin.addCases (L.bank r (K.keys r)[0]? []) (C.residentA (L.width r)))
      (fun _ : Fin 1 => CompareMachine.word (K.keys r).length))

structure RowWriterContract (selector : CyclicChoice.Laws) (a : DecompositionAlgorithm) where
  keys : RowKeys a
  layout : Layout a keys
  writer : RowWriter selector layout
  cursor : CursorAdvance layout
  scrub : ScrubForm layout.tapes layout.scratch
  setup : Setup layout scrub
  widthFits : ∀ r, writer.cost r + 1 ≤ layout.width r

def FamilyContract (selector : CyclicChoice.Laws) : Prop :=
  ∀ a : DecompositionAlgorithm, Nonempty (RowWriterContract selector a)

/-! ## Generic plumbing lemmas -/

/-- A run on false-padded tapes is a run on the actual tapes (`run_unpad`). -/
theorem step_unpad {t s : ℕ} {p : Machine t s} {n : ℕ} {H H' : Fin t → ℕ}
    {A A' : Fin t → List Bool} (cap : Fin t → ℕ)
    (h : Step p n H (fun i => ZeroPadding.pad (cap i) (A i)) H' A') :
    ∃ B : Fin t → List Bool, Step p n H A H' B ∧ ∀ i, ZeroPadding.pad (cap i) (B i) = A' i := by
  obtain ⟨r, hr, hh, ht, hs⟩ := h
  have hc : (⟨p.start, H, fun i => ZeroPadding.pad (cap i) (A i)⟩ : Configuration t s) =
      ZeroPadding.config cap ⟨p.start, H, A⟩ := rfl
  rw [hc] at hr
  obtain ⟨u, hu, hf, hsteps, _⟩ := ZeroPadding.run_unpad p cap n _ r hr
  refine ⟨u.final.tapes, ⟨u, hu, ?_, rfl, by omega⟩, ?_⟩
  · exact (congrArg Configuration.heads hf).trans hh
  · intro i
    exact (congrFun (congrArg Configuration.tapes hf) i).trans (congrFun ht i)

theorem addCases_zero (m : ℕ) :
    (Fin.addCases (fun _ : Fin m => (0 : ℕ)) (fun _ : Fin 1 => 0) : Fin (m + 1) → ℕ) = fun _ => 0 := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp

theorem inBank_padded (m : ℕ) (w : List Bool) (blank : Fin (m + 1) → ℕ) (cap : ℕ) :
    (Fin.addCases (fun i => ZeroPadding.pad (blank i) (inBank (m + 1) w i))
      (fun _ : Fin 1 => List.replicate cap false) : Fin (m + 1 + 1) → List Bool) =
    fun i => ZeroPadding.pad (Fin.addCases (motive := fun _ => ℕ) blank (fun _ : Fin 1 => cap) i)
      (inBank (m + 1 + 1) w i) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.addCases_left, inBank, Fin.val_castAdd]
    rfl
  · have hj : j = 0 := Fin.eq_zero j
    subst hj
    have hv : (Fin.natAdd (m + 1) (0 : Fin 1)).val ≠ 0 := by simp
    simp only [Fin.addCases_right, inBank, hv, if_false, ZeroPadding.pad, List.nil_append,
      List.length_nil, Nat.sub_zero]

/-! ## The parent -/

namespace RowWriterContract
variable (c : RowWriterContract selector a)

/-- The exact emitted words, one per key, in key order. -/
def emitList (r : Request) : List (List Bool) :=
  (c.keys.keys r).map (rowWord selector a c.keys r)

def emit (r : Request) (j : ℕ) : List Bool := (c.emitList r).getD j []

/-- One fixed row body: scrub-wrapped writer, then the embedded cursor. -/
def bodyMachine :=
  Composition.machine (c.scrub.wrap c.writer.machine)
    (TapeEmbedding.machine c.scrub.extra c.cursor.machine)

def rowCost (r : Request) : ℕ :=
  c.scrub.cost (c.writer.cost r) (c.layout.width r) + 1 + c.cursor.cost r

/-- The `j`-th cell: row bank at `keys[j]?`, prefix `out`, scrub residents. -/
def source (r : Request) (j : ℕ) (out : List Bool) :
    Configuration (c.layout.tapes + c.scrub.extra)
      (c.scrub.states c.writer.states + c.cursor.states) :=
  ⟨c.bodyMachine.start, Fin.addCases (c.layout.heads out) (c.scrub.residentH (c.layout.width r)),
    Fin.addCases (c.layout.bank r (c.keys.keys r)[j]? out) (c.scrub.residentA (c.layout.width r))⟩

theorem emit_at (r : Request) (j : ℕ) (hj : j < (c.keys.keys r).length) :
    c.emit r j = rowWord selector a c.keys r (c.keys.keys r)[j] := by
  simp [emit, emitList, List.getD_eq_getElem?_getD, hj]

/-- The row body meets `Cells.step`'s exact next-cell bank. -/
theorem body_step (r : Request) (j : ℕ) (hj : j < (c.keys.keys r).length) (out : List Bool) :
    Step c.bodyMachine (c.rowCost r) (c.source r j out).heads (c.source r j out).tapes
      (c.source r (j+1) (out ++ c.emit r j)).heads (c.source r (j+1) (out ++ c.emit r j)).tapes := by
  have hk : (c.keys.keys r)[j] ∈ c.keys.keys r := List.getElem_mem hj
  have hget : (c.keys.keys r)[j]? = some (c.keys.keys r)[j] := List.getElem?_eq_getElem hj
  obtain ⟨H', A', hw, hkeep⟩ := c.writer.write r (c.keys.keys r)[j] hk out
  have hpre : ∀ i, c.layout.scratch i = true →
      c.layout.heads out i = 0 ∧
        (c.layout.bank r (some (c.keys.keys r)[j]) out i).length ≤ c.layout.width r := by
    intro i hi
    have hne : i ≠ c.layout.output := by
      intro h
      rw [h, c.layout.scratchOutput] at hi
      exact Bool.false_ne_true hi
    simp [Layout.heads, Layout.bank, hne, hi]
  have hs := c.scrub.run c.writer.machine (c.writer.cost r) (c.layout.width r) _ H' _ A' hw
    (c.widthFits r) hpre
  set out' := out ++ rowWord selector a c.keys r (c.keys.keys r)[j] with hout'
  have hH : (fun i => if c.layout.scratch i then 0 else H' i) = c.layout.heads out' := by
    funext i
    by_cases hi : c.layout.scratch i = true
    · have hne : i ≠ c.layout.output := by
        intro h
        rw [h, c.layout.scratchOutput] at hi
        exact Bool.false_ne_true hi
      simp [Layout.heads, hne, hi]
    · have hf : c.layout.scratch i = false := by simpa using hi
      rw [if_neg hi]
      exact (hkeep i hf).1
  have hA : (fun i => if c.layout.scratch i then List.replicate (c.layout.width r) false else A' i) =
      c.layout.bank r (some (c.keys.keys r)[j]) out' := by
    funext i
    by_cases hi : c.layout.scratch i = true
    · have hne : i ≠ c.layout.output := by
        intro h
        rw [h, c.layout.scratchOutput] at hi
        exact Bool.false_ne_true hi
      simp [Layout.bank, hne, hi]
    · have hf : c.layout.scratch i = false := by simpa using hi
      rw [if_neg hi]
      exact (hkeep i hf).2
  rw [hH, hA] at hs
  have ha := (c.cursor.advance r j hj out').embed (c.scrub.residentH (c.layout.width r))
    (c.scrub.residentA (c.layout.width r))
  rw [hget] at ha
  have hall := hs.seq ha
  have he : out ++ c.emit r j = out' := by rw [c.emit_at r j hj]
  rw [he]
  simp only [source, hget]
  exact hall

/-- The family loop as `Cells`: one body, one cost, bound = number of rows. -/
def cells (r : Request) : Cells (c.layout.tapes + c.scrub.extra)
    (c.scrub.states c.writer.states + c.cursor.states) where
  body := c.bodyMachine
  cost := c.rowCost r
  bound := (c.keys.keys r).length
  source := c.source r
  emit := c.emit r
  entry := fun _ _ _ => rfl
  step := fun j hj out => c.body_step r j hj out

/-- The emitted stream of the whole loop is exactly the consumer's `Request.raw`. -/
theorem loop_raw (r : Request) :
    [] ++ (List.range (c.cells r).bound).flatMap (c.cells r).emit = Request.raw selector a r := by
  have hl : (c.emitList r).length = (c.keys.keys r).length := List.length_map _
  change (List.range (c.keys.keys r).length).flatMap (fun j => (c.emitList r).getD j []) = _
  rw [← hl, RepairSource.CloseoutFinal.C10ExternalRowLoop.flatten_getD, emitList,
    ← List.flatMap_def]
  exact RowKeys.raw_eq selector c.keys r

def loopCost (r : Request) : ℕ := (c.keys.keys r).length * (c.rowCost r + 3) + 3

/-- The whole row loop, from `Cells.run`, as a `Step` on the driver-extended bank. -/
theorem loop_step (r : Request) :
    Step (CloseoutRowsDegreeLoop.machine c.bodyMachine) (c.loopCost r)
      (Fin.addCases (c.source r 0 []).heads (fun _ : Fin 1 => 1))
      (Fin.addCases (c.source r 0 []).tapes (fun _ : Fin 1 => CompareMachine.word (c.keys.keys r).length))
      (Fin.addCases (c.source r (c.keys.keys r).length (Request.raw selector a r)).heads
        (fun _ : Fin 1 => 1))
      (Fin.addCases (c.source r (c.keys.keys r).length (Request.raw selector a r)).tapes
        (fun _ : Fin 1 => CompareMachine.word (c.keys.keys r).length)) := by
  obtain ⟨res, hrun, hfinal, _⟩ := (c.cells r).run []
  rw [c.loop_raw r] at hfinal
  exact Step.of_run hrun (congrArg Configuration.heads hfinal) (congrArg Configuration.tapes hfinal)

def innerCost (r : Request) : ℕ := c.setup.cost r + 1 + c.loopCost r

/-- Setup, then the loop. -/
theorem inner_step (r : Request) :
    Step (Composition.machine c.setup.machine (CloseoutRowsDegreeLoop.machine c.bodyMachine))
      (c.innerCost r) (fun _ => 0)
      (fun i => ZeroPadding.pad (c.setup.blank r i)
        (inBank (c.layout.tapes + c.scrub.extra + 1) (Request.input a r) i))
      (Fin.addCases (c.source r (c.keys.keys r).length (Request.raw selector a r)).heads
        (fun _ : Fin 1 => 1))
      (Fin.addCases (c.source r (c.keys.keys r).length (Request.raw selector a r)).tapes
        (fun _ : Fin 1 => CompareMachine.word (c.keys.keys r).length)) :=
  (c.setup.run r).seq (c.loop_step r)

/-- The one fixed program: `masked` (every head selected) around setup and loop. -/
def machine :=
  MaskedReset.machine
    (Composition.machine c.setup.machine (CloseoutRowsDegreeLoop.machine c.bodyMachine))
    (fun _ => true)

def outputTape : Fin (c.layout.tapes + c.scrub.extra + 1 + 1) :=
  ((c.layout.output.castAdd c.scrub.extra).castAdd 1).castAdd 1

def cost (r : Request) : ℕ := 2 * c.innerCost r + 2

/-- The complete execution from the program's own input bank: every head at `0`,
the output tape exactly `Request.raw`. Final rewind by `masked`; all false
blanks (mask log, scratch, logs) removed by `run_unpad`. -/
theorem whole_run (r : Request) :
    ∃ B : Fin (c.layout.tapes + c.scrub.extra + 1 + 1) → List Bool,
      Step c.machine (c.cost r) (fun _ => 0)
        (fun i => if i.val = 0 then frame (Request.input a r) else []) (fun _ => 0) B ∧
      B c.outputTape = Request.raw selector a r := by
  let b := BlockPlatform.masked (BlockPlatform.ofStep (c.inner_step r)) (fun _ => true)
    (c.innerCost r) (fun _ _ => rfl) le_rfl
  have hb : Step c.machine (c.cost r) b.entryH b.entryA b.exitH b.exitA := b.run
  have hH : b.entryH = fun _ => 0 := addCases_zero _
  have hA := inBank_padded (c.layout.tapes + c.scrub.extra) (Request.input a r)
    (c.setup.blank r) (c.innerCost r)
  have hX : b.exitH = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [b, BlockPlatform.masked]
  have hb' := (hb.congr_in hH hA).congr hX rfl
  obtain ⟨B, hB, hpad⟩ := step_unpad _ hb'
  refine ⟨B, hB, ?_⟩
  have ho := hpad c.outputTape
  have hcap : (Fin.addCases (motive := fun _ => ℕ) (c.setup.blank r)
      (fun _ : Fin 1 => c.innerCost r)) c.outputTape = 0 := by
    simp only [outputTape, Fin.addCases_left]
    exact c.setup.blankOutput r
  rw [hcap, ZeroPadding.pad_zero] at ho
  rw [ho]
  simp [b, BlockPlatform.masked, BlockPlatform.ofStep, outputTape, source, Layout.bank]

/-! ### Budget: one family-row factor, one fixed power of `smallSize` -/

def degree : ℕ :=
  c.writer.degree + c.layout.widthDegree + c.cursor.degree + c.setup.degree

def rowFactor : ℕ :=
  c.scrub.factor * (c.writer.coefficient + c.layout.widthCoefficient + 1) + 1 + c.cursor.coefficient

def coefficient : ℕ := 2 * (c.setup.coefficient + c.rowFactor + 4) + 2

theorem budget_arith (N P cW cR cA cS k w R sc adv st : ℕ) (hP : 1 ≤ P)
    (hw : w ≤ cW * P) (hR : R ≤ cR * P) (hsc : sc ≤ k * (w + R + 1)) (hadv : adv ≤ cA * P)
    (hst : st ≤ cS * (N + 1) * P) :
    2 * (st + 1 + (N * (sc + 1 + adv + 3) + 3)) + 2 ≤
      (2 * (cS + (k * (cW + cR + 1) + 1 + cA) + 4) + 2) * (N + 1) * P := by
  have h1 : w + R + 1 ≤ (cW + cR + 1) * P := by nlinarith
  have h2 : sc ≤ k * (cW + cR + 1) * P := by
    calc sc ≤ k * (w + R + 1) := hsc
      _ ≤ k * ((cW + cR + 1) * P) := Nat.mul_le_mul_left k h1
      _ = k * (cW + cR + 1) * P := by ring
  have h3 : sc + 1 + adv + 3 ≤ (k * (cW + cR + 1) + 1 + cA + 3) * P := by nlinarith
  have h4 : N * (sc + 1 + adv + 3) ≤ N * ((k * (cW + cR + 1) + 1 + cA + 3) * P) :=
    Nat.mul_le_mul_left N h3
  nlinarith

theorem fits (r : Request) : c.cost r ≤ packetBudget a c.coefficient c.degree r := by
  have hS : 0 < r.smallSize a := by
    unfold Request.smallSize
    exact Nat.zero_lt_succ _
  have hP : 1 ≤ (r.smallSize a)^c.degree := Nat.one_le_pow _ _ hS
  have hmono : ∀ d, d ≤ c.degree → (r.smallSize a)^d ≤ (r.smallSize a)^c.degree :=
    fun d hd => Nat.pow_le_pow_right hS hd
  have hw : c.writer.cost r ≤ c.writer.coefficient * (r.smallSize a)^c.degree :=
    (c.writer.cost_le r).trans (Nat.mul_le_mul_left _ (hmono _ (by unfold degree; omega)))
  have hR : c.layout.width r ≤ c.layout.widthCoefficient * (r.smallSize a)^c.degree :=
    (c.layout.width_le r).trans (Nat.mul_le_mul_left _ (hmono _ (by unfold degree; omega)))
  have hadv : c.cursor.cost r ≤ c.cursor.coefficient * (r.smallSize a)^c.degree :=
    (c.cursor.cost_le r).trans (Nat.mul_le_mul_left _ (hmono _ (by unfold degree; omega)))
  have hlen := c.keys.length_eq r
  have hst : c.setup.cost r ≤
      c.setup.coefficient * ((c.keys.keys r).length + 1) * (r.smallSize a)^c.degree := by
    rw [hlen]
    exact (c.setup.cost_le r).trans (Nat.mul_le_mul_left _ (hmono _ (by unfold degree; omega)))
  have hmain := budget_arith ((c.keys.keys r).length) ((r.smallSize a)^c.degree)
    c.writer.coefficient c.layout.widthCoefficient c.cursor.coefficient c.setup.coefficient
    c.scrub.factor (c.writer.cost r) (c.layout.width r)
    (c.scrub.cost (c.writer.cost r) (c.layout.width r)) (c.cursor.cost r) (c.setup.cost r)
    hP hw hR (c.scrub.cost_le _ _) hadv hst
  unfold packetBudget
  rw [← hlen]
  exact hmain

/-- The contract's program as the consumer's `WordBlocks`. -/
def wordBlocks : WordBlocks Request (Request.input a) (Request.raw selector a)
    (packetBudget a c.coefficient c.degree) where
  tapeCount := c.layout.tapes + c.scrub.extra + 1 + 1
  stateCount := _
  twoTapes := by omega
  machine := c.machine
  outputTape := c.outputTape
  outputFresh := by simpa [outputTape] using c.layout.outputFresh
  cost := c.cost
  exitH := fun _ _ => 0
  exitA := fun r => Classical.choose (c.whole_run r)
  step := fun r => (Classical.choose_spec (c.whole_run r)).1
  exitOut := fun r => (Classical.choose_spec (c.whole_run r)).2
  fits := c.fits

/-- **The packet writer**, through `WordBlocks.toRewound` at the consumer's own budget. -/
def packetWriter : PacketWriter selector a where
  coefficient := c.coefficient
  degree := c.degree
  positive := by unfold coefficient; omega
  ordinary := c.wordBlocks.toRewound (fun _ => rfl)

end RowWriterContract

theorem packetConstruction_of_contract (selector : CyclicChoice.Laws)
    (h : FamilyContract selector) : PacketConstruction selector :=
  fun a => (h a).elim fun c => ⟨c.packetWriter⟩

end
end NearCubicWires.PacketFamilyParent
