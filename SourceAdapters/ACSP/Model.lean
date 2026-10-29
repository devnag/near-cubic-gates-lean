import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Data.ZMod.Basic
import NineInputs

/-!
# The RAM model, arithmetic circuits and binary fields

The RAM simulation of `lem:tm-ram` uses the machine conventions of `def:ram`.
The general carrier here permits any finite arithmetic unit; the simulation uses
addition, subtraction, bitwise conjunction and comparison. Its auxiliary `pload`
instruction leaves the configuration's data and memory unchanged and advances the
program counter. The affine instances of `def:acsp` are in `ACSP/Affine.lean`.

- **Registers.** A register holds a `w`-bit word or `#` (`Option (BitVec w)`,
  `none = #`). In operands and addresses `#` reads as zero; `iseof` tests the flag.
  A configuration has `w + k(w+1)` bits, including one flag per register.
- **Control.** The base jump instructions are `je`, `jne` and `jmp`; their tests
  are equality to zero, inequality to zero and unconditional branching.
- **Tape words.** Bit `j` is the `j`-th bit of the next `w` tape bits, least significant first.
- **Steps and memory.** Executing `I_pc` takes `(S, mem)` to `(S', mem')`;
  only `store` changes memory. An out-of-code counter or an `out` instruction has no successor.
- **Transition circuits.** `Ram.ComputesTransition` is an auxiliary circuit predicate
  for `Ram.transition` on `Ram.configBits`. Its degree is a formal circuit degree.
- **Fields and circuits.** Field elements are polynomials over `F2` modulo an
  irreducible polynomial. Circuits are lists of input, constant, addition and
  multiplication gates, with the last gate as output, as used in `def:acsp`.
- **Subspaces.** Basis coefficients are the index's binary digits, least significant
  first (`def:acsp` and the preceding subspace convention).
- **Bounded acceptance.** `BHRAM` records the padded run length `2^t`, a witness
  of length at most `2^t`, and an address-count bound `2^s`. The simulation uses `s = t`.
- **Encodings.** `numCode`, `ramCode` and `circuitCode` are the natural encodings
  read and written by the ordinary machines implementing these objects.
-/

set_option autoImplicit false

noncomputable section

namespace NearCubicGates.Adapters.ACSP

open Polynomial

/-! ## Arithmetic circuits -/

/-- One gate of an arithmetic circuit: an input variable, a constant, or the sum or product of two earlier gates
(gates are numbered from `0` in order). -/
inductive ArithGate (R : Type) where
  | input (index : ℕ)
  | const (value : R)
  | add (left right : ℕ)
  | mul (left right : ℕ)

/-- An arithmetic circuit for `def:acsp`: a straight-line program whose last gate is the output. -/
structure ArithCircuit (R : Type) where
  gates : List (ArithGate R)

/-- The size of a circuit: its number of gates. -/
def ArithCircuit.size {R : Type} (c : ArithCircuit R) : ℕ := c.gates.length

/-- The polynomial of one gate, given the polynomials `prior` of the earlier gates. -/
def ArithGate.poly {R : Type} [CommSemiring R] (m : ℕ) (prior : List (MvPolynomial (Fin m) R)) :
    ArithGate R → MvPolynomial (Fin m) R
  | .input index => if h : index < m then MvPolynomial.X ⟨index, h⟩ else 0
  | .const value => MvPolynomial.C value
  | .add left right => prior.getD left 0 + prior.getD right 0
  | .mul left right => prior.getD left 0 * prior.getD right 0

/-- The polynomial computed by a circuit in `m` variables (its last gate; `0` for the empty circuit). -/
def ArithCircuit.poly {R : Type} [CommSemiring R] (c : ArithCircuit R) (m : ℕ) : MvPolynomial (Fin m) R :=
  (c.gates.foldl (fun prior g => prior ++ [g.poly m prior]) []).getLastD 0

/-! ## Finite fields of characteristic two (`def:acsp`) -/

/-- `F2(x)` with `x` a root of `irr`. -/
abbrev Field2 (irr : (ZMod 2)[X]) : Type := AdjoinRoot irr

/-- A field element given as a polynomial over `F2`, read modulo `irr`. -/
def elt (irr : (ZMod 2)[X]) (a : (ZMod 2)[X]) : Field2 irr := AdjoinRoot.mk irr a

/-- A circuit with constants in `F2[x]`, read over `F2(x)`. -/
def fieldPoly (irr : (ZMod 2)[X]) (c : ArithCircuit (ZMod 2)[X]) (m : ℕ) :
    MvPolynomial (Fin m) (Field2 irr) :=
  MvPolynomial.map (AdjoinRoot.mk irr) (c.poly m)

/-- The element of an affine subspace with basis `basis 0, …, basis (κ-1)` and offset `offset` selected by the
coefficient vector `coeff` (`Σ_j coeff_j·a_j + O`). -/
def affineElt (irr : (ZMod 2)[X]) (κ : ℕ) (basis : ℕ → (ZMod 2)[X]) (offset : (ZMod 2)[X])
    (coeff : Fin κ → Bool) : Field2 irr :=
  elt irr offset + ∑ j : Fin κ, if coeff j then elt irr (basis j) else 0

/-- "the `i`-th element" (`i` counted from `0`): basis element `j` has coefficient bit `j` of `i`, least
significant first (BCGT13 Algorithms 20, 22–23). -/
def indexedElt (irr : (ZMod 2)[X]) (κ : ℕ) (basis : ℕ → (ZMod 2)[X]) (offset : (ZMod 2)[X]) (i : ℕ) :
    Field2 irr :=
  affineElt irr κ basis offset fun j => i.testBit j.val

/-- The affine subspace has dimension `κ`: its `2^κ` coefficient vectors give distinct elements. -/
def AffineIndependent (irr : (ZMod 2)[X]) (κ : ℕ) (basis : ℕ → (ZMod 2)[X]) (offset : (ZMod 2)[X]) : Prop :=
  Function.Injective (affineElt irr κ basis offset)

/-! ## Random-access machines (`def:ram`) -/

/-- An operand is a register, the program counter, or a constant word (`def:ram`). -/
inductive Operand (w k : ℕ) where
  | reg (i : Fin k)
  | pc
  | const (c : BitVec w)

/-- Instructions for the RAM model of `def:ram`, with an auxiliary `pload`:
`nop`, tape reads, `load`, `store`, `iseof`, `out`, arithmetic operations and
`je`, `jne`, `jmp`. `pload` advances the program counter without changing data. -/
inductive Instr (w k ops : ℕ) where
  | nop
  | readA (i : Fin k)
  | readB (i : Fin k)
  | load (i j : Fin k)
  | pload (i j : Fin k)
  | store (j : Fin k) (x : Operand w k)
  | iseof (i j : Fin k)
  | out (accept : Bool)
  | arith (op : Fin ops) (i : Fin k) (x y : Operand w k)
  | je (i : Fin k) (c : ℕ)
  | jne (i : Fin k) (c : ℕ)
  | jmp (c : ℕ)

/-- A RAM carrier: word width `w`, register count `k`, a finite arithmetic unit and
nonempty code of length at most `2^w`. The machines of `lem:tm-ram` instantiate
this carrier with the four arithmetic operations specified in `def:ram`. -/
structure Ram where
  w : ℕ
  k : ℕ
  ops : ℕ
  alu : Fin ops → BitVec w → BitVec w → BitVec w
  code : List (Instr w k ops)
  codeNonempty : 1 ≤ code.length
  codeFits : code.length ≤ 2 ^ w

namespace Ram

variable (M : Ram)

/-- A configuration consists of a word-sized program counter and registers holding words or `#` (`def:ram`). -/
structure Config (M : Ram) where
  pc : BitVec M.w
  regs : Fin M.k → Option (BitVec M.w)

/-- The memory: `2^w` cells of `w` bits. -/
abbrev Memory : Type := BitVec M.w → BitVec M.w

/-- The instruction `I_pc`, if `pc` is inside the code. -/
def instrAt (pc : BitVec M.w) : Option (Instr M.w M.k M.ops) := M.code[pc.toNat]?

variable {M}

/-- The value of an operand (`#` reads as zero). -/
def Config.val (S : Config M) : Operand M.w M.k → BitVec M.w
  | .reg i => (S.regs i).getD 0
  | .pc => S.pc
  | .const c => c

/-- Write a register and advance `pc` by one. -/
def Config.setNext (S : Config M) (i : Fin M.k) (v : Option (BitVec M.w)) : Config M :=
  { pc := S.pc + 1, regs := Function.update S.regs i v }

/-- Advance `pc` by one. -/
def Config.next (S : Config M) : Config M := { S with pc := S.pc + 1 }

/-- Jump to instruction `c`. -/
def Config.jump (S : Config M) (c : ℕ) : Config M := { S with pc := BitVec.ofNat M.w c }

variable (M)

/-- One instruction step with its memory update (`def:ram`). A tape read may
return any word or `#`; the run's prefix conditions constrain the returned words. -/
def Step (S : Config M) (mem : M.Memory) (S' : Config M) (mem' : M.Memory) : Prop :=
  match M.instrAt S.pc with
  | none => False
  | some .nop => S' = S.next ∧ mem' = mem
  | some (.pload _ _) => S' = S.next ∧ mem' = mem
  | some (.readA i) => (∃ v, S' = S.setNext i v) ∧ mem' = mem
  | some (.readB i) => (∃ v, S' = S.setNext i v) ∧ mem' = mem
  | some (.load i j) => S' = S.setNext j (some (mem (S.val (.reg i)))) ∧ mem' = mem
  | some (.store j x) => S' = S.next ∧ mem' = Function.update mem (S.val (.reg j)) (S.val x)
  | some (.iseof i j) => S' = S.setNext i (some (if S.regs j = none then 1 else 0)) ∧ mem' = mem
  | some (.out _) => False
  | some (.arith op i x y) => S' = S.setNext i (some (M.alu op (S.val x) (S.val y))) ∧ mem' = mem
  | some (.je i c) => S' = (if S.val (.reg i) = 0 then S.jump c else S.next) ∧ mem' = mem
  | some (.jne i c) => S' = (if S.val (.reg i) ≠ 0 then S.jump c else S.next) ∧ mem' = mem
  | some (.jmp c) => S' = S.jump c ∧ mem' = mem

/-- The initial configuration has program counter and every register equal to zero (`def:ram`). -/
def Initial (S : Config M) : Prop := S.pc = 0 ∧ ∀ i, S.regs i = some 0

/-- A final configuration points to an `out` instruction (`def:ram`). -/
def Final (S : Config M) : Prop := ∃ b, M.instrAt S.pc = some (.out b)

/-- An accepting configuration points to `out accept` (`def:ram`). -/
def AcceptingConfig (S : Config M) : Prop := M.instrAt S.pc = some (.out true)

/-- Auxiliary cyclic transition indicator: zero for an instruction step with
some memories, or for a final-to-initial pair, and one otherwise. -/
def transition (S S' : Config M) : ZMod 2 :=
  open Classical in
  if (∃ mem mem', M.Step S mem S' mem') ∨ (M.Final S ∧ M.Initial S') then 0 else 1

/-- An accepting sequence starts in the initial configuration and ends in an accepting one (`def:ram`). -/
def AcceptingSeq (T : ℕ) (S : ℕ → Config M) : Prop := M.Initial (S 0) ∧ M.AcceptingConfig (S (T - 1))

/-- A valid sequence has zero cyclic transition indicators and a memory sequence
starting at zero whose consecutive configurations are actual instruction steps.
Together with `AcceptingSeq`, the cyclic wrap is the final-to-initial pair. -/
def ValidSeq (T : ℕ) (S : ℕ → Config M) : Prop :=
  (∀ i < T, M.transition (S i) (S ((i + 1) % T)) = 0) ∧
  ∃ mem : ℕ → M.Memory, mem 0 = 0 ∧ ∀ i, i + 1 < T → M.Step (S i) (mem i) (S (i + 1)) (mem (i + 1))

/-- The bits of a word, least significant first. -/
def wordBits {w : ℕ} (v : BitVec w) : List Bool := List.ofFn fun j : Fin w => v.getLsbD j.val

/-- The word read at step `i` from tape A (`tapeA = true`) or B: the value that `readA r` / `readB r` puts into
`r`, as seen in `S^{i+1}`. -/
def readAt (tapeA : Bool) (S : ℕ → Config M) (i : ℕ) : Option (Option (BitVec M.w)) :=
  match M.instrAt (S i).pc with
  | some (.readA r) => if tapeA then some ((S (i + 1)).regs r) else none
  | some (.readB r) => if tapeA then none else some ((S (i + 1)).regs r)
  | _ => none

/-- The time-ordered concatenation of the words, other than `#`, read from one tape during `T` steps. -/
def readString (tapeA : Bool) (T : ℕ) (S : ℕ → Config M) : List Bool :=
  ((List.range (T - 1)).filterMap fun i =>
    (M.readAt tapeA S i).bind fun v => v.map wordBits).flatten

/-- The time-ordered words other than `#` read from each tape concatenate to a
prefix of that tape's supplied string (`def:ram`). -/
def ConsistentSeq (T : ℕ) (S : ℕ → Config M) (x wit : List Bool) : Prop :=
  M.readString true T S <+: x ∧ M.readString false T S <+: wit

/-- The memory address accessed at step `i` (by `load`, `pload` or `store`), if any. -/
def addressAt (S : ℕ → Config M) (i : ℕ) : Option (BitVec M.w) :=
  match M.instrAt (S i).pc with
  | some (.load a _) => some ((S i).val (.reg a))
  | some (.pload a _) => some ((S i).val (.reg a))
  | some (.store j _) => some ((S i).val (.reg j))
  | _ => none

/-- The number of distinct addresses accessed during `T` steps. -/
def addressCount (T : ℕ) (S : ℕ → Config M) : ℕ :=
  ((List.range T).filterMap (M.addressAt S)).toFinset.card

/-- Bounded acceptance with unary exponents: positive `t,s`, input length at most
`2^t`, a witness of length at most `2^t`, and an accepting, valid, tape-consistent
sequence of `2^t` configurations accessing at most `2^s` addresses. At `s = t`
this is the bounded run predicate used for the simulation in `lem:tm-ram`. -/
def BHRAM (x : List Bool) (t s : ℕ) : Prop :=
  1 ≤ t ∧ 1 ≤ s ∧ x.length ≤ 2 ^ t ∧
  ∃ wit : List Bool, wit.length ≤ 2 ^ t ∧ ∃ S : ℕ → Config M,
    M.AcceptingSeq (2 ^ t) S ∧ M.ValidSeq (2 ^ t) S ∧ M.ConsistentSeq (2 ^ t) S x wit ∧
      M.addressCount (2 ^ t) S ≤ 2 ^ s

/-- Auxiliary syntactic memory discipline: the first instruction stores to cell
zero (all registers initially vanish), and every `load i j` has distinct operands
and is immediately followed by `pload i j`. -/
def MemoryWellBehaved : Prop :=
  (∃ j x, M.code[0]? = some (.store j x)) ∧
  ∀ p i j, M.code[p]? = some (.load i j) → i ≠ j ∧ M.code[p + 1]? = some (.pload i j)

/-- The bit encoding of a configuration: `pc`, then for each register a `#` flag and its `w` bits. -/
def configBits (S : Config M) : List Bool :=
  wordBits S.pc ++ (List.ofFn fun i : Fin M.k =>
    ((S.regs i).isNone) :: wordBits ((S.regs i).getD 0)).flatten

/-- The length of `configBits`: `w + k·(w + 1)`. -/
def configWidth : ℕ := M.w + M.k * (M.w + 1)

/-- `D` computes the auxiliary transition indicator on the concatenated bit
encodings of two configurations, using `2·configWidth` inputs. -/
def ComputesTransition (D : ArithCircuit (ZMod 2)) : Prop :=
  ∀ S S' : Config M,
    MvPolynomial.eval (fun v : Fin (2 * M.configWidth) =>
        if (M.configBits S ++ M.configBits S').getD v.val false then (1 : ZMod 2) else 0)
      (D.poly (2 * M.configWidth)) = M.transition S S'

end Ram

/-! ## Natural encodings -/

/-- A self-delimiting number: its bit length in unary, a `0`, then its bits, least significant first. -/
def numCode (n : ℕ) : List Bool :=
  List.replicate (Nat.size n) true ++ false :: List.ofFn fun i : Fin (Nat.size n) => n.testBit i.val

/-- A polynomial over `F2`: its degree, then its `deg + 1` coefficients, constant term first. -/
def polyCode (a : (ZMod 2)[X]) : List Bool :=
  numCode a.natDegree ++ List.ofFn fun i : Fin (a.natDegree + 1) => decide (a.coeff i.val = 1)

/-- An element of `F2`. -/
def bitCode (z : ZMod 2) : List Bool := [decide (z = 1)]

/-- An operand. -/
def operandCode {w k : ℕ} : Operand w k → List Bool
  | .reg i => numCode 0 ++ numCode i.val
  | .pc => numCode 1 ++ numCode 0
  | .const c => numCode 2 ++ numCode c.toNat

/-- An instruction: a tag, then its fields. -/
def instrCode {w k ops : ℕ} : Instr w k ops → List Bool
  | .nop => numCode 0
  | .readA i => numCode 1 ++ numCode i.val
  | .readB i => numCode 2 ++ numCode i.val
  | .load i j => numCode 3 ++ numCode i.val ++ numCode j.val
  | .pload i j => numCode 4 ++ numCode i.val ++ numCode j.val
  | .store j x => numCode 5 ++ numCode j.val ++ operandCode x
  | .iseof i j => numCode 6 ++ numCode i.val ++ numCode j.val
  | .out b => numCode 7 ++ numCode b.toNat
  | .arith op i x y => numCode 8 ++ numCode op.val ++ numCode i.val ++ operandCode x ++ operandCode y
  | .je i c => numCode 9 ++ numCode i.val ++ numCode c
  | .jne i c => numCode 10 ++ numCode i.val ++ numCode c
  | .jmp c => numCode 11 ++ numCode c

/-- The code of a machine: `w`, `k`, the number of arithmetic-unit operations, the code length, the instructions. -/
def ramCode (M : Ram) : List Bool :=
  numCode M.w ++ numCode M.k ++ numCode M.ops ++ numCode M.code.length ++ (M.code.map instrCode).flatten

/-- A gate, with constants encoded by `enc`. -/
def gateCode {R : Type} (enc : R → List Bool) : ArithGate R → List Bool
  | .input i => numCode 0 ++ numCode i
  | .const v => numCode 1 ++ enc v
  | .add a b => numCode 2 ++ numCode a ++ numCode b
  | .mul a b => numCode 3 ++ numCode a ++ numCode b

/-- A circuit: its number of gates, then the gates in order. -/
def circuitCode {R : Type} (enc : R → List Bool) (c : ArithCircuit R) : List Bool :=
  numCode c.gates.length ++ (c.gates.map (gateCode enc)).flatten

end NearCubicGates.Adapters.ACSP

end
