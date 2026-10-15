import Proof.Packets.PacketsCursorOrder

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator NearCubicWires.SupplierPrime
open NearCubicWires.SupplierWalkBridge NearCubicWires.SourceInterfaces
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open FixedLivePackets PacketProduction
open NearCubicWires.PacketFamilyParent
noncomputable section

/-! ## The values (each pinned by an accepted definition) -/

/-- The family's occurrence list. -/
abbrev occ (a : DecompositionAlgorithm) (r : Request) := (r.family a).occurrences
/-- The live set (the cyclic-choice mask; it is IN the input, part 3). -/
abbrev live (a : DecompositionAlgorithm) (r : Request) := Packets.live (r.family a)

/-- `pop`: the number of occurrences. -/
def pop (a : DecompositionAlgorithm) (r : Request) : ℕ := (occ a r).length
/-- `K`: the live count (the number of `true`s of the mask frame, input part 3). -/
def liveCount (a : DecompositionAlgorithm) (r : Request) : ℕ := (live a r).card
/-- `2^K`. -/
def twoK (a : DecompositionAlgorithm) (r : Request) : ℕ := 2 ^ liveCount a r
/-- `B = touchingCost`: occurrences whose support meets the live set. -/
def touch (a : DecompositionAlgorithm) (r : Request) : ℕ := LiveRows.bound (occ a r) (live a r)
/-- `depth = canonicalGradedDepth B = clog₂ (256·B)`. -/
def depth (a : DecompositionAlgorithm) (r : Request) : ℕ := canonicalGradedDepth (touch a r)
/-- `rank = max depth (clog₂ pop)`. -/
def rank (a : DecompositionAlgorithm) (r : Request) : ℕ := canonicalGradedRank (pop a r) (touch a r)
/-- The walk length `canonicalWalkLength (Request.denominator a r)`. -/
def walkLength (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  canonicalWalkLength (Request.denominator a r)
/-- The per-pool-entry child counts: exactly the list encoded in input part 4. -/
def childCounts (a : DecompositionAlgorithm) (r : Request) : List ℕ :=
  ExtDecompositionBatch.counts a (CloseoutRowsUniversal.pool (live a r) (occ a r))
/-- `N`: the total child count (every lowered code is `< N`). -/
def childTotal (a : DecompositionAlgorithm) (r : Request) : ℕ := (childCounts a r).sum
/-- The row alphabet size `Packets.alphabet`. -/
def alphabet (a : DecompositionAlgorithm) (r : Request) : ℕ := Packets.alphabet a (r.family a)
/-- The request degree (max row degree). -/
def degree (a : DecompositionAlgorithm) (r : Request) : ℕ := Request.degree a r
/-- The tuple dimension. -/
def tupleWork (a : DecompositionAlgorithm) (r : Request) : ℕ := Request.tupleWork a r
/-- `smallSize` itself. -/
def small (a : DecompositionAlgorithm) (r : Request) : ℕ := Request.smallSize a r
/-- `⌊log₂ smallSize⌋ + 1`: P's register width is `12·sizeLog` (`sizeLog_pow` below). -/
def sizeLog (a : DecompositionAlgorithm) (r : Request) : ℕ := Nat.log 2 (small a r) + 1
/-- A strict bound on every code a row polynomial mentions (level codes `< (depth+2·pop+2)^2`,
literal codes `< pop`, lowered codes `< N`). -/
def codeBound (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  (depth a r + 2 * pop a r + 2) ^ 2 + pop a r + childTotal a r + 1
/-- The level-`l` window `executableGradedWindow B l` (`Proof/MachineModel/CanonicalFourfoldRowProgram.lean`). -/
def window (a : DecompositionAlgorithm) (r : Request) (l : ℕ) : ℕ :=
  executableGradedWindow (touch a r) (depth := l + 1) ⟨l, Nat.lt_succ_self l⟩
/-- The seed count (the cursor's field-5 bound). -/
def seedCount (a : DecompositionAlgorithm) (r : Request) : ℕ :=
  (Packets.seedList (occ a r) (live a r) (Request.denominator a r)).length
/-- The cursor field width `fieldWidth a r` (`Proof/Packets/PacketsLayout.lean`). -/
def fieldWidth (a : DecompositionAlgorithm) (r : Request) : ℕ := PacketsConstruction.fieldWidth a r

/-! ## The stage shapes -/

/-- **One scalar, one fixed machine.** Entry: the framed input on tape 0, every other tape empty,
all heads 0. Exit: tape 0 and its head unchanged; tape 1 = `replicate (v r) true`, head 0; the private
tapes `2..` are existential. Cost a fixed power of `smallSize`. -/
structure UnaryStage (a : DecompositionAlgorithm) (v : Request → ℕ) where
  extra : ℕ
  states : ℕ
  machine : Machine (2 + extra) states
  cost : Request → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r, cost r ≤ coefficient * (r.smallSize a) ^ degree
  run : ∀ r, ∃ (H' : Fin (2 + extra) → ℕ) (A' : Fin (2 + extra) → List Bool),
    Step machine (cost r) (fun _ => 0) (inBank (2 + extra) (Request.input a r)) H' A' ∧
    A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
    A' ⟨1, by omega⟩ = List.replicate (v r) true ∧ H' ⟨1, by omega⟩ = 0

/-- The argument bank of a level-indexed stage: framed input on tape 0, unary argument on tape 1. -/
def argBank (n : ℕ) (w : List Bool) (l : ℕ) : Fin n → List Bool :=
  fun i => if i.val = 0 then RepairOrdinary.frame w else if i.val = 1 then List.replicate l true else []

/-- **One level-indexed scalar, one fixed machine.** Entry: framed input on tape 0, unary `l` on
tape 1, every other tape empty, heads 0. Exit: tapes 0 and 1 and their heads unchanged; tape 2 =
`replicate (v r l) true`, head 0; tapes `3..` existential. Cost a fixed power of `smallSize + l`. -/
structure UnaryFunStage (a : DecompositionAlgorithm) (v : Request → ℕ → ℕ) where
  extra : ℕ
  states : ℕ
  machine : Machine (3 + extra) states
  cost : Request → ℕ → ℕ
  coefficient : ℕ
  degree : ℕ
  cost_le : ∀ r l, cost r l ≤ coefficient * (r.smallSize a + l) ^ degree
  run : ∀ r l, ∃ (H' : Fin (3 + extra) → ℕ) (A' : Fin (3 + extra) → List Bool),
    Step machine (cost r l) (fun _ => 0) (argBank (3 + extra) (Request.input a r) l) H' A' ∧
    A' ⟨0, by omega⟩ = RepairOrdinary.frame (Request.input a r) ∧ H' ⟨0, by omega⟩ = 0 ∧
    A' ⟨1, by omega⟩ = List.replicate l true ∧ H' ⟨1, by omega⟩ = 0 ∧
    A' ⟨2, by omega⟩ = List.replicate (v r l) true ∧ H' ⟨2, by omega⟩ = 0

/-- **The `RequestMeta` output contract**: one stage per metadata value. -/
structure Contract (a : DecompositionAlgorithm) where
  pop : UnaryStage a (pop a)
  liveCount : UnaryStage a (liveCount a)
  twoK : UnaryStage a (twoK a)
  touch : UnaryStage a (touch a)
  depth : UnaryStage a (depth a)
  rank : UnaryStage a (rank a)
  walkLength : UnaryStage a (walkLength a)
  childTotal : UnaryStage a (childTotal a)
  alphabet : UnaryStage a (alphabet a)
  degree : UnaryStage a (degree a)
  tupleWork : UnaryStage a (tupleWork a)
  small : UnaryStage a (small a)
  sizeLog : UnaryStage a (sizeLog a)
  codeBound : UnaryStage a (codeBound a)
  seedCount : UnaryStage a (seedCount a)
  fieldWidth : UnaryStage a (fieldWidth a)
  window : UnaryFunStage a (window a)

/-! ## Facts the consumers use -/

/-- P's register width: `2^(12·sizeLog)` covers `smallSize^12` and is itself a fixed power of
`smallSize`. -/
theorem sizeLog_pow (a : DecompositionAlgorithm) (r : Request) :
    (r.smallSize a) ^ 12 < 2 ^ (12 * sizeLog a r) ∧
      2 ^ (12 * sizeLog a r) ≤ 2 ^ 12 * (r.smallSize a) ^ 12 := by
  have hpos : 0 < r.smallSize a := by
    unfold Request.smallSize
    exact Nat.succ_pos _
  have hlt : r.smallSize a < 2 ^ sizeLog a r := Nat.lt_pow_succ_log_self (by norm_num) _
  have hle : 2 ^ Nat.log 2 (r.smallSize a) ≤ r.smallSize a := Nat.pow_log_le_self 2 hpos.ne'
  have e : 2 ^ (12 * sizeLog a r) = (2 ^ sizeLog a r) ^ 12 := by rw [Nat.mul_comm, Nat.pow_mul]
  refine ⟨?_, ?_⟩
  · rw [e]
    exact Nat.pow_lt_pow_left hlt (by norm_num)
  · rw [e, ← Nat.mul_pow]
    apply Nat.pow_le_pow_left
    change 2 ^ (Nat.log 2 (small a r) + 1) ≤ 2 * r.smallSize a
    rw [Nat.pow_succ]
    change 2 ^ Nat.log 2 (r.smallSize a) * 2 ≤ 2 * r.smallSize a
    omega

/-- A stage whose machine is halted at its start writes nothing: it only serves the value `0`
(the contract forces real work for every positive value). -/
theorem UnaryStage.halted_zero {a : DecompositionAlgorithm} {v : Request → ℕ} (s : UnaryStage a v)
    (hM : s.machine.halted s.machine.start = true) (r : Request) : v r = 0 := by
  obtain ⟨H', A', ⟨res, hres, _, ht, _⟩, _, _, h1, _⟩ := s.run r
  have hz := runFrom_zero_of_halted s.machine
    (⟨s.machine.start, fun _ => 0, inBank (2 + s.extra) (Request.input a r)⟩ :
      Configuration (2 + s.extra) s.states) hM
  have hmore := runFrom_moreFuel s.machine 0 (s.cost r) _ _ hz
  rw [Nat.zero_add, hres] at hmore
  have hf := congrArg (fun x => Option.map (fun y => y.final.tapes) x) hmore
  simp only [Option.map_some] at hf
  have hb := (Option.some.inj hf).symm.trans ht
  have h1' := congrFun hb ⟨1, by omega⟩
  rw [h1] at h1'
  simp only [inBank] at h1'
  have hl := congrArg List.length h1'
  simp only [List.length_replicate] at hl
  simp at hl
  exact hl.symm

end
end NearCubicWires.PacketsGlue.RequestMeta

