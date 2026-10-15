import Mathlib.Tactic

set_option autoImplicit false

namespace NearCubicGates.Close.Dispatch

/-- Primitive operations on `V` variables. -/
inductive Op (V : ℕ) where
  | zero (x : Fin V)
  | inc (x : Fin V)
  | add (x y : Fin V)
  | sub (x y : Fin V)
  | copy (x y : Fin V)
  | half (x : Fin V)
  | shl (x : Fin V)
  | mul (x y z : Fin V)
  | dm (x y q r : Fin V)
  | rdC (x : Fin V)
  | rstC
  | rdW (x : Fin V)
  | emit (b : Bool)

/-- Tests. -/
inductive Cnd (V : ℕ) where
  | lt (x y : Fin V)
  | eq (x y : Fin V)

/-- Programs. -/
inductive St (V : ℕ) where
  | op (o : Op V)
  | seq (s t : St V)
  | ite (c : Cnd V) (s t : St V)
  | loop (c : Cnd V) (s : St V)

/-- The abstract state: variables, the call-word cursor, the witness cursor, the output so far. -/
structure DS (V : ℕ) where
  env : Fin V → ℕ
  cp : ℕ
  wq : ℕ
  out : List Bool

/-- The fixed data of a run: the width, the call word, the witness word. -/
structure Ctx where
  Wd : ℕ
  cw : List Bool
  wit : List Bool

variable {V : ℕ}

namespace DS

/-- Set one variable. -/
def set (a : DS V) (x : Fin V) (v : ℕ) : DS V := { a with env := Function.update a.env x v }

@[simp] theorem set_env_self (a : DS V) (x : Fin V) (v : ℕ) : (a.set x v).env x = v := by simp [set]
theorem set_env_ne (a : DS V) {x y : Fin V} (v : ℕ) (h : y ≠ x) : (a.set x v).env y = a.env y := by
  simp [set, Function.update_of_ne h]
@[simp] theorem set_cp (a : DS V) (x : Fin V) (v : ℕ) : (a.set x v).cp = a.cp := rfl
@[simp] theorem set_wq (a : DS V) (x : Fin V) (v : ℕ) : (a.set x v).wq = a.wq := rfl
@[simp] theorem set_out (a : DS V) (x : Fin V) (v : ℕ) : (a.set x v).out = a.out := rfl

end DS

/-- The bit read by `rdC`, `rdW`. -/
def bitOf (l : List Bool) (i : ℕ) : ℕ := (l.getD i false).toNat

theorem bitOf_le (l : List Bool) (i : ℕ) : bitOf l i ≤ 1 := by
  unfold bitOf; cases l.getD i false <;> simp

/-- Operation semantics. Side conditions: distinct operands where the compiled program needs them, and no overflow
of width `Wd`. -/
inductive OpEx (C : Ctx) : Op V → DS V → DS V → Prop where
  | zero (x : Fin V) (a : DS V) : OpEx C (.zero x) a (a.set x 0)
  | inc (x : Fin V) (a : DS V) : a.env x + 1 < 2 ^ C.Wd → OpEx C (.inc x) a (a.set x (a.env x + 1))
  | add (x y : Fin V) (a : DS V) : x ≠ y → a.env x + a.env y < 2 ^ C.Wd →
      OpEx C (.add x y) a (a.set x (a.env x + a.env y))
  | sub (x y : Fin V) (a : DS V) : x ≠ y → a.env y ≤ a.env x → OpEx C (.sub x y) a (a.set x (a.env x - a.env y))
  | copy (x y : Fin V) (a : DS V) : x ≠ y → OpEx C (.copy x y) a (a.set x (a.env y))
  | half (x : Fin V) (a : DS V) : OpEx C (.half x) a (a.set x (a.env x / 2))
  | shl (x : Fin V) (a : DS V) : 2 * a.env x < 2 ^ C.Wd → OpEx C (.shl x) a (a.set x (2 * a.env x))
  | mul (x y z : Fin V) (a : DS V) : x ≠ y → x ≠ z → y ≠ z → a.env x * a.env y < 2 ^ C.Wd →
      OpEx C (.mul x y z) a (a.set z (a.env x * a.env y))
  | dm (x y q r : Fin V) (a : DS V) : x ≠ y → x ≠ q → x ≠ r → y ≠ q → y ≠ r → q ≠ r → 0 < a.env y →
      2 * a.env y ≤ 2 ^ C.Wd → OpEx C (.dm x y q r) a ((a.set q (a.env x / a.env y)).set r (a.env x % a.env y))
  | rdC (x : Fin V) (a : DS V) : a.cp < C.cw.length →
      OpEx C (.rdC x) a { a.set x (bitOf C.cw a.cp) with cp := a.cp + 1 }
  | rstC (a : DS V) : OpEx C .rstC a { a with cp := 0 }
  | rdW (x : Fin V) (a : DS V) :
      OpEx C (.rdW x) a { a.set x (bitOf C.wit a.wq) with wq := if a.wq < C.wit.length then a.wq + 1 else a.wq }
  | emit (b : Bool) (a : DS V) : OpEx C (.emit b) a { a with out := a.out ++ [b] }

namespace Cnd

/-- Well-formed: distinct operands. -/
def wf : Cnd V → Prop
  | .lt x y => x ≠ y
  | .eq x y => x ≠ y

/-- Value of a test. -/
def eval (a : DS V) : Cnd V → Bool
  | .lt x y => decide (a.env x < a.env y)
  | .eq x y => decide (a.env x = a.env y)

end Cnd

/-- **Big-step semantics with a step count.** -/
inductive Ex (C : Ctx) : St V → DS V → DS V → ℕ → Prop where
  | op {o : Op V} {a b : DS V} : OpEx C o a b → Ex C (.op o) a b 1
  | seq {s t : St V} {a b d : DS V} {n k : ℕ} : Ex C s a b n → Ex C t b d k → Ex C (.seq s t) a d (n + k + 1)
  | iteT {c : Cnd V} {s t : St V} {a b : DS V} {n : ℕ} : c.wf → c.eval a = true → Ex C s a b n →
      Ex C (.ite c s t) a b (n + 1)
  | iteF {c : Cnd V} {s t : St V} {a b : DS V} {n : ℕ} : c.wf → c.eval a = false → Ex C t a b n →
      Ex C (.ite c s t) a b (n + 1)
  | loopF {c : Cnd V} {s : St V} {a : DS V} : c.wf → c.eval a = false → Ex C (.loop c s) a a 2
  | loopT {c : Cnd V} {s : St V} {a b d : DS V} {n k : ℕ} : c.wf → c.eval a = true → Ex C s a b n →
      Ex C (.loop c s) b d k → Ex C (.loop c s) a d (n + k + 2)
  | mono {s : St V} {a b : DS V} {n m : ℕ} : Ex C s a b n → n ≤ m → Ex C s a b m

/-- States the compiled program can represent: every value below `2^Wd`, cursors within their words. -/
structure Valid (C : Ctx) (a : DS V) : Prop where
  env_lt : ∀ x, a.env x < 2 ^ C.Wd
  cp_le : a.cp ≤ C.cw.length
  wq_le : a.wq ≤ C.wit.length

theorem OpEx.valid {C : Ctx} {o : Op V} {a b : DS V} (h : OpEx C o a b) (hW : 1 ≤ C.Wd) (ha : Valid C a) :
    Valid C b := by
  have h2 : (1 : ℕ) < 2 ^ C.Wd := Nat.one_lt_two_pow (by omega)
  have hset : ∀ (a : DS V) (x : Fin V) (v : ℕ), Valid C a → v < 2 ^ C.Wd → Valid C (a.set x v) := by
    intro a x v ha hv
    refine ⟨fun y => ?_, ha.cp_le, ha.wq_le⟩
    by_cases hy : y = x
    · subst hy; simpa using hv
    · rw [DS.set_env_ne _ _ hy]; exact ha.env_lt y
  cases h with
  | zero x a => exact hset a x 0 ha (by positivity)
  | inc x a hv => exact hset a x _ ha hv
  | add x y a _ hv => exact hset a x _ ha hv
  | sub x y a _ _ => exact hset a x _ ha (lt_of_le_of_lt (Nat.sub_le _ _) (ha.env_lt x))
  | copy x y a _ => exact hset a x _ ha (ha.env_lt y)
  | half x a => exact hset a x _ ha (lt_of_le_of_lt (Nat.div_le_self _ _) (ha.env_lt x))
  | shl x a hv => exact hset a x _ ha hv
  | mul x y z a _ _ _ hv => exact hset a z _ ha hv
  | dm x y q r a _ _ _ _ _ _ hy _ =>
    refine hset _ r _ (hset a q _ ha (lt_of_le_of_lt (Nat.div_le_self _ _) (ha.env_lt x))) ?_
    exact lt_of_lt_of_le (Nat.mod_lt _ hy) (le_of_lt (ha.env_lt y))
  | rdC x a hc =>
    have hv := hset a x (bitOf C.cw a.cp) ha (lt_of_le_of_lt (bitOf_le _ _) h2)
    exact ⟨hv.env_lt, by simp; omega, ha.wq_le⟩
  | rstC a => exact ⟨ha.env_lt, by simp, ha.wq_le⟩
  | rdW x a =>
    have hv := hset a x (bitOf C.wit a.wq) ha (lt_of_le_of_lt (bitOf_le _ _) h2)
    refine ⟨hv.env_lt, ha.cp_le, ?_⟩
    have := ha.wq_le
    simp only
    split_ifs <;> omega
  | emit b a => exact ⟨ha.env_lt, ha.cp_le, ha.wq_le⟩

theorem Ex.valid {C : Ctx} {s : St V} {a b : DS V} {n : ℕ} (h : Ex C s a b n) (hW : 1 ≤ C.Wd) (ha : Valid C a) :
    Valid C b := by
  induction h with
  | op h => exact h.valid hW ha
  | seq _ _ ih1 ih2 => exact ih2 (ih1 ha)
  | iteT _ _ _ ih => exact ih ha
  | iteF _ _ _ ih => exact ih ha
  | loopF _ _ => exact ha
  | loopT _ _ _ _ ih1 ih2 => exact ih2 (ih1 ha)
  | mono _ _ ih => exact ih ha

theorem OpEx.out_len {C : Ctx} {o : Op V} {a b : DS V} (h : OpEx C o a b) : b.out.length ≤ a.out.length + 1 := by
  cases h <;> simp [DS.set]

theorem Ex.out_len {C : Ctx} {s : St V} {a b : DS V} {n : ℕ} (h : Ex C s a b n) :
    b.out.length ≤ a.out.length + n := by
  induction h with
  | op h => exact h.out_len
  | seq _ _ ih1 ih2 => omega
  | iteT _ _ _ ih => omega
  | iteF _ _ _ ih => omega
  | loopF _ _ => omega
  | loopT _ _ _ _ ih1 ih2 => omega
  | mono _ hnm ih => omega

theorem Ex.pos {C : Ctx} {s : St V} {a b : DS V} {n : ℕ} (h : Ex C s a b n) : 1 ≤ n := by
  induction h with
  | op _ => exact le_refl _
  | seq _ _ _ _ => omega
  | iteT _ _ _ _ => omega
  | iteF _ _ _ _ => omega
  | loopF _ _ => omega
  | loopT _ _ _ _ _ _ => omega
  | mono _ hnm ih => omega

end NearCubicGates.Close.Dispatch
