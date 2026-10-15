import Proof.Wire_3_5.Runtime
import Proof.Foundations.OrdinaryMachine

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Machine
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.RepairOrdinary

/-- The five-field contract. -/
structure MachineContract (E : Envelope) where
  /- (1) inputs: a paper object and its framed tape-0 encoding. -/
  Req : Type
  input : Req → List Bool
  /-- (2) precondition. -/
  pre : Req → Prop
  /-- (4) output: the reference value and its encoding on the output tape. -/
  Out : Type
  ref : Req → Out
  encode : Out → List Bool
  /-- (3) budget: class, class arguments, constant coefficient. -/
  cls : BudgetClass
  q : Req → ℕ
  k : Req → ℕ
  psi : Req → ℕ
  coef : ℕ
  /-- (5) error: what the mathematics proves about `ref`, against the paper quantity. -/
  errSpec : Req → Out → Prop

def MachineContract.budget {E : Envelope} (C : MachineContract E) (r : {r // C.pre r}) : ℕ :=
  C.coef * classBound E C.cls (C.q r.1) (C.k r.1) (C.psi r.1)

/-- The machine obligation: REL's rewound word function at the class budget, on admissible
requests. -/
abbrev Implements {E : Envelope} (C : MachineContract E) : Type :=
  RewoundWordFunction {r // C.pre r} (fun r => C.input r.1) (fun r => C.encode (C.ref r.1)) C.budget

/-- Machine and mathematics fused: the implementation plus the paper's error bound on `ref`. -/
structure Certified {E : Envelope} (C : MachineContract E) where
  machine : Implements C
  err : ∀ r, C.pre r → C.errSpec r (C.ref r)

/-- The A7 hypothesis is the A9 budget field, verbatim. -/
theorem Implements.cost_le {E : Envelope} {C : MachineContract E} (_M : Implements C)
    (r : {r // C.pre r}) :
    C.budget r ≤ C.coef * classBound E C.cls (C.q r.1) (C.k r.1) (C.psi r.1) := le_refl _

/-! ## S0 stand-ins -/
namespace S0Defs

structure IntGate (n : ℕ) where
  weights : Fin n → ℤ
  threshold : ℤ

def IntGate.eval {n : ℕ} (g : IntGate n) (x : Fin n → Bool) : Bool :=
  decide (g.threshold ≤ ∑ i, (if x i then g.weights i else 0))

structure HalfScore where
  const : ℤ
  terms : List (ℤ × List ℕ × Bool)

def parityOf (z : ℕ) (mask : List ℕ) : Bool := mask.foldl (fun b i => xor b (z.testBit i)) false

def HalfScore.eval (h : HalfScore) (z : ℕ) : ℤ :=
  h.const + (h.terms.map (fun t => if xor (parityOf z t.2.1) t.2.2 then t.1 else 0)).sum

structure Occurrence where
  v : ℤ
  left : HalfScore
  right : HalfScore

abbrev PrintedPoly := List (ℤ × List ℕ)

abbrev Coset := List ℕ

end S0Defs
open S0Defs

structure SelectionReq where
  n : ℕ
  r : ℕ
  gates : List (IntGate n)

  pops : List (List ℕ × ℚ)

def SelectionReq.s (R : SelectionReq) : ℕ := Nat.log 2 (R.n / R.r + 1)
def SelectionReq.k (R : SelectionReq) : ℕ := R.r * R.s

def c1 (E : Envelope) (objective : SelectionReq → Coset → ℚ) (argmin : SelectionReq → Coset)
    (encodeCoset : Coset → List Bool) (inputWord : SelectionReq → List Bool) (psi : SelectionReq → ℕ)
    (coef : ℕ) : MachineContract E where
  Req := SelectionReq
  input := inputWord
  pre := fun R => R.r % 2 = 0 ∧ 2 ≤ R.r ∧ 4 * R.r ≤ R.n ∧
    (R.pops.map Prod.snd).sum = 1 ∧ ∀ X ∈ R.pops, 0 ≤ X.2
  Out := Coset
  ref := argmin
  encode := encodeCoset
  cls := .selection
  q := fun R => R.n
  k := SelectionReq.k
  psi := psi
  coef := coef

  errSpec := fun R c => c.length = R.r ∧ ∀ c' : Coset, c'.length = R.r →
    (∀ σ ∈ c', σ < 2 ^ R.s) → objective R c ≤ objective R c'

/-- The list/filter/row construction's request; its content is B2/B4/B5's frozen record. -/
structure ListReq where
  n : ℕ
  k : ℕ
  psi : ℕ
  description : List Bool

def c2 (E : Envelope) (ref : ListReq → PrintedPoly) (encodePoly : PrintedPoly → List Bool)
    (semantics : ListReq → PrintedPoly → Prop) (coef : ℕ) : MachineContract E where
  Req := ListReq
  input := fun R => frame R.description
  pre := fun R => R.k ≤ R.n
  Out := PrintedPoly
  ref := ref
  encode := encodePoly
  cls := .preprocessing
  q := fun R => R.n
  k := fun R => R.k
  psi := fun R => R.psi
  coef := coef

  errSpec := semantics

/-! ## C3: compiler to printer, and the printer (`alg:compiler`, `alg:separable-printer`) -/

structure PrinterReq where
  n : ℕ
  k : ℕ
  psi : ℕ

  nL : ℕ
  nR : ℕ

  prec : ℕ
  occ : List Occurrence

def PrinterReq.table (R : PrinterReq) (zL zR : ℕ) : ℤ :=
  (R.occ.map (fun o => if o.left.eval zL + o.right.eval zR = 0 then o.v else 0)).sum

def PrinterReq.recoveredSum (R : PrinterReq) : ℤ :=
  ((List.range (2 ^ R.nL)).map (fun zL => ((List.range (2 ^ R.nR)).map
    (fun zR => (R.table zL zR) % (2 ^ R.prec : ℤ))).sum)).sum

def c3 (E : Envelope) (inputWord : PrinterReq → List Bool) (coef : ℕ) : MachineContract E where
  Req := PrinterReq
  input := inputWord
  pre := fun R => R.nL ≤ R.nR ∧ R.nR ≤ R.nL + 1 ∧ R.nL + R.nR = R.n - R.k ∧
    100 * Nat.log 2 (R.occ.length + 1) ≤ R.nL + R.nR
  Out := ℤ
  ref := PrinterReq.recoveredSum
  encode := fun z => frame (Nat.bits z.natAbs) ++ [decide (z < 0)]
  cls := .table
  q := fun R => R.n
  k := fun R => R.k
  psi := fun R => R.psi
  coef := coef

  errSpec := fun R z => z = R.recoveredSum

structure SeedReq where
  n : ℕ
  k : ℕ
  psi : ℕ
  seedLen : ℕ

  childPotential : List Bool → PrinterReq

def SeedReq.greedy (R : SeedReq) : List Bool :=
  (List.range R.seedLen).foldl (fun p _ =>
    if (R.childPotential (p ++ [true])).recoveredSum < (R.childPotential (p ++ [false])).recoveredSum
    then p ++ [true] else p ++ [false]) []

def c4 (E : Envelope) (inputWord : SeedReq → List Bool) (average : SeedReq → ℚ)
    (potential : SeedReq → List Bool → ℚ) (coef : ℕ) : MachineContract E where
  Req := SeedReq
  input := inputWord
  pre := fun R => R.k ≤ R.n
  Out := List Bool
  ref := SeedReq.greedy
  encode := frame
  cls := .table
  q := fun R => R.n
  k := fun R => R.k
  psi := fun R => R.psi
  coef := coef

  errSpec := fun R seed => seed.length = R.seedLen ∧ potential R seed ≤ average R

structure FinalReq where
  n : ℕ
  k : ℕ
  psi : ℕ

  samples : List (ℕ × ℕ)

  lookup : ℕ → ℕ → ℕ → ℤ

/-- `Σ_z Σ_j lookup(U_j, V_j; z)` over the `2^{n-k}` columns. -/
def FinalReq.sum (R : FinalReq) : ℤ :=
  ((List.range (2 ^ (R.n - R.k))).map (fun z =>
    (R.samples.map (fun uv => R.lookup uv.1 uv.2 z)).sum)).sum

def c5 (E : Envelope) (inputWord : FinalReq → List Bool) (truth : FinalReq → ℚ) (D : ℕ)
    (coef : ℕ) : MachineContract E where
  Req := FinalReq
  input := inputWord
  pre := fun R => R.k ≤ R.n ∧ R.k % 2 = 0 ∧ R.samples.length ≤ 2 ^ ((3 * R.k + 3) / 4) * R.n ^ E.Amain
  Out := ℤ
  ref := FinalReq.sum
  encode := fun z => frame (Nat.bits z.natAbs) ++ [decide (z < 0)]
  cls := .mainPass
  q := fun R => R.n
  k := fun R => R.k
  psi := fun R => R.psi
  coef := coef

  errSpec := fun R z => |(z : ℚ) / ((2 ^ (R.n - R.k) : ℚ) * R.samples.length) - truth R| ≤
    1 / (R.n : ℚ) ^ D

structure WeakReq where
  N : ℕ
  q : ℕ
  k : ℕ
  psi : ℕ
  input : List Bool
  guess : List Bool

  estimates : ℚ × ℚ × ℚ

def WeakReq.decide (v0 cp sp : ℚ) (R : WeakReq) : Bool :=
  Decidable.decide (16 * R.guess.length ≤ R.N) &&
    Decidable.decide (R.estimates.1 ≤ 2 * v0) &&
    Decidable.decide (R.estimates.2.1 ≤ 1 + v0) &&
    Decidable.decide ((cp + sp) / 2 ≤ R.estimates.2.2)

def c6 (E : Envelope) (inputWord : WeakReq → List Bool) (v0 cp sp : ℚ)
    (sound : WeakReq → Bool → Prop) (coef : ℕ) : MachineContract E where
  Req := WeakReq
  input := inputWord
  pre := fun R => R.k ≤ R.q
  Out := Bool
  ref := WeakReq.decide v0 cp sp
  encode := fun b => [b]
  cls := .mainPass
  q := fun R => R.q
  k := fun R => R.k
  psi := fun R => R.psi
  coef := coef
  /- one-sidedness and completeness are B8/D1's (`tr:soundness`, `tr:completeness`). -/
  errSpec := sound

/-! ## C7 is A7: `Runtime3.littleO` instantiated with C1-C6's budgets. -/

/-- The four A7 cost functions from the contracts' budgets at fixed class arguments. -/
def costsOf (E : Envelope) (coef : ℕ) : ComponentCosts E where
  coef := coef
  sel := fun q k psi => coef * classBound E .selection q k psi
  pre := fun q k psi => coef * classBound E .preprocessing q k psi
  table := fun q k psi => coef * classBound E .table q k psi
  main := fun q k psi => coef * classBound E .mainPass q k psi
  hsel := fun _ _ _ => le_refl _
  hpre := fun _ _ _ => le_refl _
  htable := fun _ _ _ => le_refl _
  hmain := fun _ _ _ => le_refl _

/-! ## Executable twins at tiny parameters (P19, P25) -/

/-- C3: two occurrences over `n_out = 2 + 2` column bits. -/
def tinyPrinter : PrinterReq where
  n := 8
  k := 4
  psi := 0
  nL := 2
  nR := 2
  prec := 4
  occ := [⟨3, ⟨-1, [(1, [0], false)]⟩, ⟨0, [(1, [1], true)]⟩⟩,
          ⟨-2, ⟨0, [(1, [0, 1], false)]⟩, ⟨0, []⟩⟩]

/-- Hand count (and a Python check): occurrence 1 is `3·[z_L.0 + ¬z_R.1 = 1]` (8 columns),
occurrence 2 is `-2·[z_L.0 ⊕ z_L.1 = 0]` (8 columns), both on 4. Per-column residues mod 16:
3 (4 columns), 14 (4), 1 (4), 0 (4); recovered sum 72. -/
theorem tinyPrinter_sum : tinyPrinter.recoveredSum = 72 := by decide

/-- C5: `2^{n-k} = 4` columns, three samples, lookup `u + v + z`. -/
def tinyFinal : FinalReq where
  n := 6
  k := 4
  psi := 0
  samples := [(0, 1), (1, 1), (2, 3)]
  lookup := fun u v z => (u + v + z : ℤ)

theorem tinyFinal_sum : tinyFinal.sum = 50 := by decide

end NearCubicWires.WireExponent3_5.Machine
