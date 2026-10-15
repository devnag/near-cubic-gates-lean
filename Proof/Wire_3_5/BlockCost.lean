import Proof.Wire_3_5.Contracts
import Proof.MachineModel.BlockWordFunction
import Proof.MachineModel.BlockScrubEntry

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Block
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Machine
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.BlockPlatform

/-! ## The class bound as `2^{exp} · q^{deg}` -/

/-- The exponent of `2` in each class bound. -/
def classExp (E : Envelope) : BudgetClass → ℕ → ℕ → ℕ → ℕ
  | .sourcePoly, _, _, _ => 0
  | .selection, q, k, _ => q / 2 + E.csel * k
  | .preprocessing, _, _, psi => E.cpsi * psi
  | .table, q, k, _ => q - k
  | .mainPass, q, k, _ => q - k / 4

/-- The polynomial degree of each class bound, fixed by the envelope before `r`. -/
def classDeg (E : Envelope) : BudgetClass → ℕ
  | .sourcePoly => E.Amain
  | .selection => E.Asel
  | .preprocessing => E.Apre
  | .table => E.Atable
  | .mainPass => E.Amain

theorem classBound_eq (E : Envelope) (cls : BudgetClass) (q k psi : ℕ) :
    classBound E cls q k psi = 2 ^ classExp E cls q k psi * q ^ classDeg E cls := by
  cases cls <;> simp [classBound, classExp, classDeg]

theorem classBound_pos (E : Envelope) (cls : BudgetClass) {q : ℕ} (k psi : ℕ) (hq : 1 ≤ q) :
    1 ≤ classBound E cls q k psi := by
  rw [classBound_eq]
  exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by positivity) (by positivity))

/-! ## `Within`: a cost in a named class -/

/-- The cost `n` is within class `cls` at `(q, k, Ψ)` with coefficient `c`: the shape of A9's budget
field `coef · classBound E cls (q, k, Ψ)`. -/
def Within (E : Envelope) (cls : BudgetClass) (c q k psi n : ℕ) : Prop :=
  n ≤ c * classBound E cls q k psi

namespace Within
variable {E : Envelope} {cls : BudgetClass} {q k psi : ℕ}

theorem mono {c n m : ℕ} (h : Within E cls c q k psi n) (hm : m ≤ n) : Within E cls c q k psi m :=
  hm.trans h

theorem coef_mono {c c' n : ℕ} (h : Within E cls c q k psi n) (hc : c ≤ c') : Within E cls c' q k psi n :=
  h.trans (Nat.mul_le_mul_right _ hc)

theorem zero (c : ℕ) : Within E cls c q k psi 0 := Nat.zero_le _

theorem add {c₁ c₂ n₁ n₂ : ℕ} (h₁ : Within E cls c₁ q k psi n₁) (h₂ : Within E cls c₂ q k psi n₂) :
    Within E cls (c₁ + c₂) q k psi (n₁ + n₂) := by
  unfold Within at *
  rw [Nat.add_mul]
  exact Nat.add_le_add h₁ h₂

theorem const (hq : 1 ≤ q) (c : ℕ) : Within E cls c q k psi c := by
  have := classBound_pos E cls k psi hq (q := q)
  unfold Within
  nlinarith

/-- Sequencing: `b.cost + 1 + c.cost` (the paid bridge step of `BlockPlatform.seq`). -/
theorem seq (hq : 1 ≤ q) {c₁ c₂ n₁ n₂ : ℕ} (h₁ : Within E cls c₁ q k psi n₁)
    (h₂ : Within E cls c₂ q k psi n₂) : Within E cls (c₁ + c₂ + 1) q k psi (n₁ + 1 + n₂) := by
  have h := (h₁.add h₂).add (const (E := E) (cls := cls) (k := k) (psi := psi) hq 1)
  exact h.mono (by omega)

/-- A cost `c · 2^e · q^a` is within any class whose exponent and degree dominate `e` and `a`. -/
theorem of_scaled (hq : 1 ≤ q) {c n e a : ℕ} (h : n ≤ c * (2 ^ e * q ^ a))
    (he : e ≤ classExp E cls q k psi) (ha : a ≤ classDeg E cls) : Within E cls c q k psi n := by
  unfold Within
  rw [classBound_eq]
  have h2 : 2 ^ e ≤ 2 ^ classExp E cls q k psi := Nat.pow_le_pow_right (by norm_num) he
  have h3 : q ^ a ≤ q ^ classDeg E cls := Nat.pow_le_pow_right hq ha
  exact h.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul h2 h3))

/-- A polynomial cost `c · q^a` is within every class of degree at least `a`. -/
theorem of_poly (hq : 1 ≤ q) {c n a : ℕ} (h : n ≤ c * q ^ a) (ha : a ≤ classDeg E cls) :
    Within E cls c q k psi n :=
  of_scaled hq (e := 0) (by simpa using h) (Nat.zero_le _) ha

/-- Class inclusion: a cost within `cls₁` is within `cls₂` when `cls₂`'s exponent and degree dominate. -/
theorem promote (hq : 1 ≤ q) {cls₂ : BudgetClass} {c n : ℕ} (h : Within E cls c q k psi n)
    (he : classExp E cls q k psi ≤ classExp E cls₂ q k psi) (hd : classDeg E cls ≤ classDeg E cls₂) :
    Within E cls₂ c q k psi n := by
  unfold Within at h
  rw [classBound_eq] at h
  exact of_scaled hq h he hd

/-- The shared sub-bound of a loop body and its count, before the class is chosen. -/
theorem loop_scaled (hq : 1 ≤ q) {bound cost c e a b : ℕ} (hbound : bound ≤ 2 ^ e * q ^ b)
    (hcost : cost ≤ c * q ^ a) :
    bound * (cost + 3) + 3 ≤ (c + 6) * (2 ^ e * q ^ (b + a)) := by
  have hqa : 1 ≤ q ^ a := Nat.one_le_pow _ _ hq
  have hqb : 1 ≤ q ^ b := Nat.one_le_pow _ _ hq
  have he1 : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  have hc3 : cost + 3 ≤ (c + 3) * q ^ a := by nlinarith
  have hP : 1 ≤ 2 ^ e * q ^ (b + a) := by
    rw [pow_add]; exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  calc bound * (cost + 3) + 3 ≤ (2 ^ e * q ^ b) * ((c + 3) * q ^ a) + 3 :=
        Nat.add_le_add_right (Nat.mul_le_mul hbound hc3) 3
    _ = (c + 3) * (2 ^ e * q ^ (b + a)) + 3 := by rw [pow_add]; ring
    _ ≤ (c + 3) * (2 ^ e * q ^ (b + a)) + 3 * (2 ^ e * q ^ (b + a)) := by omega
    _ ≤ (c + 6) * (2 ^ e * q ^ (b + a)) := by nlinarith

/-- A bounded loop (`Cells.budget = bound · (cost + 3) + 3`): at most `2^e · q^b` iterations of a body
of cost `≤ c · q^a`, within a class whose exponent is at least `e` and degree at least `b + a`. -/
theorem loop (hq : 1 ≤ q) {bound cost c e a b : ℕ} (hbound : bound ≤ 2 ^ e * q ^ b)
    (hcost : cost ≤ c * q ^ a) (he : e ≤ classExp E cls q k psi) (hd : b + a ≤ classDeg E cls) :
    Within E cls (c + 6) q k psi (bound * (cost + 3) + 3) :=
  of_scaled hq (loop_scaled hq hbound hcost) he hd

/-- Enumerating all `w`-bit strings: `2^w` iterations of a body of cost `≤ c · q^a`, within a class
whose exponent is at least `w`. -/
theorem enumerate (hq : 1 ≤ q) {w cost c a : ℕ} (hcost : cost ≤ c * q ^ a)
    (hw : w ≤ classExp E cls q k psi) (hd : a ≤ classDeg E cls) :
    Within E cls (c + 6) q k psi (2 ^ w * (cost + 3) + 3) :=
  loop hq (b := 0) (by simp) hcost hw (by simpa using hd)

/-- Counting: `m ≤ q^b` repetitions of a cost `≤ c · 2^e · q^a`. -/
theorem times (hq : 1 ≤ q) {m n c e a b : ℕ} (hm : m ≤ q ^ b) (hn : n ≤ c * (2 ^ e * q ^ a))
    (he : e ≤ classExp E cls q k psi) (hd : a + b ≤ classDeg E cls) :
    Within E cls c q k psi (m * n) := by
  refine of_scaled hq (e := e) (a := a + b) ?_ he hd
  calc m * n ≤ q ^ b * (c * (2 ^ e * q ^ a)) := Nat.mul_le_mul hm hn
    _ = c * (2 ^ e * q ^ (a + b)) := by rw [pow_add]; ring

end Within

/-! ## Costed blocks -/

/-- A block with its cost certified in a named class at `(q, k, Ψ)`. -/
structure Costed (E : Envelope) (cls : BudgetClass) (q k psi t : ℕ) where
  block : Block t
  coef : ℕ
  within : Within E cls coef q k psi block.cost

namespace Costed
variable {E : Envelope} {cls : BudgetClass} {q k psi t u : ℕ}

/-- Sequencing, with the seam stated once. -/
noncomputable def seq (hq : 1 ≤ q) (b c : Costed E cls q k psi t) (hH : b.block.exitH = c.block.entryH)
    (hA : b.block.exitA = c.block.entryA) : Costed E cls q k psi t :=
  ⟨BlockPlatform.seq b.block c.block hH hA, b.coef + c.coef + 1, Within.seq hq b.within c.within⟩

@[simp] theorem seq_coef (hq : 1 ≤ q) (b c : Costed E cls q k psi t) (hH : b.block.exitH = c.block.entryH)
    (hA : b.block.exitA = c.block.entryA) : (seq hq b c hH hA).coef = b.coef + c.coef + 1 := rfl

/-- Docking into an ambient layout keeps the cost and the class. -/
noncomputable def focusedInto (b : Costed E cls q k psi t) (slots : Fin t → Fin u)
    (hi : Function.Injective slots) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hH : ∀ j, H (slots j) = b.block.entryH j) (hA : ∀ j, A (slots j) = b.block.entryA j) :
    Costed E cls q k psi u :=
  ⟨BlockPlatform.focusedInto b.block slots hi H A hH hA, b.coef, b.within⟩

/-- A bounded loop of `Cells` as a costed block (the loop's counter is the added tape). -/
noncomputable def loop {s : ℕ} (hq : 1 ≤ q) (c : Cells t s) (out : List Bool) {coef e a b : ℕ}
    (hbound : c.bound ≤ 2 ^ e * q ^ b) (hcost : c.cost ≤ coef * q ^ a)
    (he : e ≤ classExp E cls q k psi) (hd : b + a ≤ classDeg E cls) : Costed E cls q k psi (t + 1) :=
  ⟨ofStep (c.loopStep out), coef + 6, Within.loop hq hbound hcost he hd⟩

/-- The class budget as the block's cost (`BlockPlatform.upto`). -/
noncomputable def toBudget (b : Costed E cls q k psi t) : Block t :=
  upto b.block (b.coef * classBound E cls q k psi) b.within

@[simp] theorem toBudget_cost (b : Costed E cls q k psi t) :
    (toBudget b).cost = b.coef * classBound E cls q k psi := rfl

end Costed

/-! ## The consumer: A9's machine contract -/

/-- A block family over ONE machine for the admissible requests of the contract `C`. Each run goes from
the framed input with every head at cell 0 to an exit whose output tape carries the encoding of the
reference value `C.ref`. Every head is back at cell 0, and the cost is within `C`'s budget class at `C`'s
coefficient. -/
structure ClassBlocks {E : Envelope} (C : MachineContract E) where
  tapeCount : ℕ
  stateCount : ℕ
  twoTapes : 2 ≤ tapeCount
  machine : Machine tapeCount stateCount
  outputTape : Fin tapeCount
  outputFresh : outputTape.val ≠ 0
  cost : {r // C.pre r} → ℕ
  exitA : {r // C.pre r} → Fin tapeCount → List Bool
  step : ∀ r, Step machine (cost r) (fun _ => 0)
    (fun i => if i.val = 0 then frame (C.input r.1) else []) (fun _ => 0) (exitA r)
  exitOut : ∀ r, exitA r outputTape = C.encode (C.ref r.1)
  within : ∀ r, Within E C.cls C.coef (C.q r.1) (C.k r.1) (C.psi r.1) (cost r)

/-- The Block v3 word function of a class-costed family, at the contract's budget. -/
noncomputable def ClassBlocks.wordBlocks {E : Envelope} {C : MachineContract E} (B : ClassBlocks C) :
    WordBlocks {r // C.pre r} (fun r => C.input r.1) (fun r => C.encode (C.ref r.1)) C.budget where
  tapeCount := B.tapeCount
  stateCount := B.stateCount
  twoTapes := B.twoTapes
  machine := B.machine
  outputTape := B.outputTape
  outputFresh := B.outputFresh
  cost := B.cost
  exitH := fun _ => fun _ => 0
  exitA := B.exitA
  step := B.step
  exitOut := B.exitOut
  fits := B.within

/-- **`ClassBlocks C` is `Implements C`**: the contract's rewound word function at exactly the
contract's class budget `C.coef · classBound E C.cls (q, k, Ψ)`. -/
noncomputable def ClassBlocks.implements {E : Envelope} {C : MachineContract E} (B : ClassBlocks C) :
    Implements C :=
  B.wordBlocks.toRewound (fun _ => rfl)

/-- With the paper's error bound on the reference, the family certifies the contract. -/
noncomputable def ClassBlocks.certified {E : Envelope} {C : MachineContract E} (B : ClassBlocks C)
    (err : ∀ r, C.pre r → C.errSpec r (C.ref r)) : Certified C :=
  ⟨B.implements, err⟩

/-! ## The tight class forbids a per-column `2^k` -/

theorem sq_le_two_pow {j : ℕ} (hj : 4 ≤ j) : j * j ≤ 2 ^ j := by
  induction j, hj using Nat.le_induction with
  | base => norm_num
  | succ j hj ih =>
    rw [pow_succ]
    nlinarith

/-- Exponential beats every polynomial: `c · (4m)^A < 2^m` for some `m ≥ 1`. -/
theorem exists_poly_lt_two_pow (c A : ℕ) : ∃ m, 1 ≤ m ∧ c * (4 * m) ^ A < 2 ^ m := by
  set j := c + 2 * A + 4 with hj
  refine ⟨2 ^ j, Nat.one_le_two_pow, ?_⟩
  have h4 : 4 * 2 ^ j = 2 ^ (j + 2) := by rw [pow_add]; ring
  rw [h4, ← pow_mul]
  have hc : c < 2 ^ c := Nat.lt_two_pow_self
  have hsq : j * j ≤ 2 ^ j := sq_le_two_pow (by omega)
  have hlin : c + (j + 2) * A < j * j := by nlinarith
  calc c * 2 ^ ((j + 2) * A) < 2 ^ c * 2 ^ ((j + 2) * A) :=
        Nat.mul_lt_mul_of_pos_right hc (by positivity)
    _ = 2 ^ (c + (j + 2) * A) := by rw [pow_add]
    _ < 2 ^ (j * j) := Nat.pow_lt_pow_right (by norm_num) hlin
    _ ≤ 2 ^ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hsq

theorem per_column_2k_not_mainPass (E : Envelope) (c : ℕ) :
    ¬ ∀ q k psi, k ≤ q → Within E .mainPass c q k psi (2 ^ (q - k) * 2 ^ k) := by
  intro h
  obtain ⟨m, hm, hlt⟩ := exists_poly_lt_two_pow c E.Amain
  have h1 := h (4 * m) (4 * m) 0 (le_refl _)
  have hb : classBound E .mainPass (4 * m) (4 * m) 0 = 2 ^ (3 * m) * (4 * m) ^ E.Amain := by
    have e2 : 4 * m - 4 * m / 4 = 3 * m := by omega
    simp only [classBound, e2]
  unfold Within at h1
  rw [hb, Nat.sub_self, pow_zero, one_mul] at h1
  have e3 : 2 ^ (4 * m) = 2 ^ (3 * m) * 2 ^ m := by rw [← pow_add]; ring_nf
  rw [e3] at h1
  have h2 : 2 ^ (3 * m) * 2 ^ m ≤ 2 ^ (3 * m) * (c * (4 * m) ^ E.Amain) := by
    calc 2 ^ (3 * m) * 2 ^ m ≤ c * (2 ^ (3 * m) * (4 * m) ^ E.Amain) := h1
      _ = 2 ^ (3 * m) * (c * (4 * m) ^ E.Amain) := by ring
  have h3 := Nat.le_of_mul_le_mul_left h2 (by positivity)
  omega

end NearCubicWires.WireExponent3_5.Block
