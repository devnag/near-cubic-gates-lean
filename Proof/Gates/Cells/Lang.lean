import Mathlib.Tactic
import Proof.Gates.Interfaces.CounterFormats

set_option autoImplicit false

namespace NearCubicGates.Close.Cells

open NearCubicGates.Close.Interfaces.Formats

/-- Primitive operations on `V` variables and `M` record stores. -/
inductive Op (V M : ℕ) where
  | zero (x : Fin V)
  | inc (x : Fin V)
  | add (x y : Fin V)
  | sub (x y : Fin V)
  | copy (x y : Fin V)
  | half (x : Fin V)
  | shl (x : Fin V)
  | mul (x y z : Fin V)
  | dm (x y q r : Fin V)
  | rdI (x : Fin V)
  | bkI
  | emit (b : Bool)
  | rdM (m : Fin M) (x : Fin V)
  | wrM (m : Fin M) (x : Fin V)
  | rwM (m : Fin M)
  | srtM (m : Fin M)
  | kem (b : Bool)
  | kcall
  | rdK (x : Fin V)

/-- Tests. -/
inductive Cnd (V : ℕ) where
  | lt (x y : Fin V)
  | eq (x y : Fin V)

/-- Programs. -/
inductive St (V M : ℕ) where
  | op (o : Op V M)
  | seq (s t : St V M)
  | ite (c : Cnd V) (s t : St V M)
  | loop (c : Cnd V) (s : St V M)

/-- The abstract state. -/
structure DS (V M : ℕ) where
  env : Fin V → ℕ
  ip : ℕ
  out : List Bool
  ram : Fin M → List ℕ
  rc : Fin M → ℕ
  kin : List Bool
  kout : List Bool
  kc : ℕ

structure Callee where
  Req : Type
  inw : Req → List Bool
  outw : Req → List Bool
  bud : Req → ℕ
  wf : NearCubicWires.RepairOrdinary.WordFunction Req inw outw bud

def Callee.ofSolve (S : SolveMachine) : Callee := ⟨SysReq, sysWord, fun s => solveWord (S.solve s), S.budget, S.wf⟩

/-- The fixed data of a run: the width, the input word, the callee, and the bounds the compiled program
reserves for calls (input words of length at most `Lk`, budgets at most `Bk`). -/
structure Ctx where
  Wd : ℕ
  inp : List Bool
  K : Callee
  Lk : ℕ
  Bk : ℕ

variable {V M : ℕ}

namespace DS

/-- Set one variable. -/
def set (a : DS V M) (x : Fin V) (v : ℕ) : DS V M := { a with env := Function.update a.env x v }

@[simp] theorem set_env_self (a : DS V M) (x : Fin V) (v : ℕ) : (a.set x v).env x = v := by simp [set]
theorem set_env_ne (a : DS V M) {x y : Fin V} (v : ℕ) (h : y ≠ x) : (a.set x v).env y = a.env y := by
  simp [set, Function.update_of_ne h]
@[simp] theorem set_ip (a : DS V M) (x : Fin V) (v : ℕ) : (a.set x v).ip = a.ip := rfl
@[simp] theorem set_out (a : DS V M) (x : Fin V) (v : ℕ) : (a.set x v).out = a.out := rfl
@[simp] theorem set_ram (a : DS V M) (x : Fin V) (v : ℕ) : (a.set x v).ram = a.ram := rfl
@[simp] theorem set_rc (a : DS V M) (x : Fin V) (v : ℕ) : (a.set x v).rc = a.rc := rfl
@[simp] theorem set_kin (a : DS V M) (x : Fin V) (v : ℕ) : (a.set x v).kin = a.kin := rfl
@[simp] theorem set_kout (a : DS V M) (x : Fin V) (v : ℕ) : (a.set x v).kout = a.kout := rfl
@[simp] theorem set_kc (a : DS V M) (x : Fin V) (v : ℕ) : (a.set x v).kc = a.kc := rfl

end DS

/-- Writing record `v` at position `i` of a store (appending when `i` is its length). -/
def putAt (l : List ℕ) (i v : ℕ) : List ℕ := if i < l.length then l.set i v else l ++ [v]

namespace DS

/-- Advance the cursor of store `m`. -/
def adv (a : DS V M) (m : Fin M) : DS V M := { a with rc := Function.update a.rc m (a.rc m + 1) }

/-- Write `v` at the cursor of store `m` and advance. -/
def put (a : DS V M) (m : Fin M) (v : ℕ) : DS V M :=
  { a with ram := Function.update a.ram m (putAt (a.ram m) (a.rc m) v), rc := Function.update a.rc m (a.rc m + 1) }

/-- Rewind the cursor of store `m`. -/
def rew (a : DS V M) (m : Fin M) : DS V M := { a with rc := Function.update a.rc m 0 }

/-- Sort store `m` (numeric order of the records). -/
def srt (a : DS V M) (m : Fin M) : DS V M :=
  { a with ram := Function.update a.ram m ((a.ram m).insertionSort (· ≤ ·)) }

def called (a : DS V M) (o : List Bool) : DS V M := { a with kin := [], kout := o, kc := 0 }

end DS

/-- The bit read by `rdI`, `rdK`. -/
def bitOf (l : List Bool) (i : ℕ) : ℕ := (l.getD i false).toNat

theorem bitOf_le (l : List Bool) (i : ℕ) : bitOf l i ≤ 1 := by
  unfold bitOf; cases l.getD i false <;> simp

inductive OpEx (C : Ctx) : Op V M → DS V M → DS V M → ℕ → Prop where
  | zero (x : Fin V) (a : DS V M) : OpEx C (.zero x) a (a.set x 0) 1
  | inc (x : Fin V) (a : DS V M) : a.env x + 1 < 2 ^ C.Wd → OpEx C (.inc x) a (a.set x (a.env x + 1)) 1
  | add (x y : Fin V) (a : DS V M) : x ≠ y → a.env x + a.env y < 2 ^ C.Wd →
      OpEx C (.add x y) a (a.set x (a.env x + a.env y)) 1
  | sub (x y : Fin V) (a : DS V M) : x ≠ y → a.env y ≤ a.env x →
      OpEx C (.sub x y) a (a.set x (a.env x - a.env y)) 1
  | copy (x y : Fin V) (a : DS V M) : x ≠ y → OpEx C (.copy x y) a (a.set x (a.env y)) 1
  | half (x : Fin V) (a : DS V M) : OpEx C (.half x) a (a.set x (a.env x / 2)) 1
  | shl (x : Fin V) (a : DS V M) : 2 * a.env x < 2 ^ C.Wd → OpEx C (.shl x) a (a.set x (2 * a.env x)) 1
  | mul (x y z : Fin V) (a : DS V M) : x ≠ y → x ≠ z → y ≠ z → a.env x * a.env y < 2 ^ C.Wd →
      OpEx C (.mul x y z) a (a.set z (a.env x * a.env y)) 1
  | dm (x y q r : Fin V) (a : DS V M) : x ≠ y → x ≠ q → x ≠ r → y ≠ q → y ≠ r → q ≠ r → 0 < a.env y →
      2 * a.env y ≤ 2 ^ C.Wd →
      OpEx C (.dm x y q r) a ((a.set q (a.env x / a.env y)).set r (a.env x % a.env y)) 1
  | rdI (x : Fin V) (a : DS V M) : a.ip < C.inp.length →
      OpEx C (.rdI x) a { a.set x (bitOf C.inp a.ip) with ip := a.ip + 1 } 1
  | bkI (a : DS V M) : 0 < a.ip → OpEx C .bkI a { a with ip := a.ip - 1 } 1
  | emit (b : Bool) (a : DS V M) : OpEx C (.emit b) a { a with out := a.out ++ [b] } 1
  | rdM (m : Fin M) (x : Fin V) (a : DS V M) : a.rc m < (a.ram m).length →
      OpEx C (.rdM m x) a ((a.set x ((a.ram m).getD (a.rc m) 0)).adv m) 1
  | wrM (m : Fin M) (x : Fin V) (a : DS V M) : a.rc m ≤ (a.ram m).length →
      OpEx C (.wrM m x) a (a.put m (a.env x)) 1
  | rwM (m : Fin M) (a : DS V M) : OpEx C (.rwM m) a (a.rew m) (a.rc m + 1)
  | srtM (m : Fin M) (a : DS V M) : a.rc m = 0 → OpEx C (.srtM m) a (a.srt m) ((a.ram m).length + 1)
  | kem (b : Bool) (a : DS V M) : a.kin.length < C.Lk → OpEx C (.kem b) a { a with kin := a.kin ++ [b] } 1
  | kcall (s : C.K.Req) (a : DS V M) : a.kin = C.K.inw s → C.K.bud s ≤ C.Bk →
      OpEx C .kcall a (a.called (C.K.outw s)) (1 + C.Lk + C.Bk)
  | rdK (x : Fin V) (a : DS V M) : a.kc < a.kout.length →
      OpEx C (.rdK x) a { a.set x (bitOf a.kout a.kc) with kc := a.kc + 1 } 1

namespace Cnd

/-- Well-formed: distinct operands. -/
def wf : Cnd V → Prop
  | .lt x y => x ≠ y
  | .eq x y => x ≠ y

/-- Value of a test. -/
def eval (a : DS V M) : Cnd V → Bool
  | .lt x y => decide (a.env x < a.env y)
  | .eq x y => decide (a.env x = a.env y)

end Cnd

/-- **Big-step semantics with a cost.** -/
inductive Ex (C : Ctx) : St V M → DS V M → DS V M → ℕ → Prop where
  | op {o : Op V M} {a b : DS V M} {k : ℕ} : OpEx C o a b k → Ex C (.op o) a b k
  | seq {s t : St V M} {a b d : DS V M} {n k : ℕ} : Ex C s a b n → Ex C t b d k → Ex C (.seq s t) a d (n + k + 1)
  | iteT {c : Cnd V} {s t : St V M} {a b : DS V M} {n : ℕ} : c.wf → c.eval a = true → Ex C s a b n →
      Ex C (.ite c s t) a b (n + 1)
  | iteF {c : Cnd V} {s t : St V M} {a b : DS V M} {n : ℕ} : c.wf → c.eval a = false → Ex C t a b n →
      Ex C (.ite c s t) a b (n + 1)
  | loopF {c : Cnd V} {s : St V M} {a : DS V M} : c.wf → c.eval a = false → Ex C (.loop c s) a a 2
  | loopT {c : Cnd V} {s : St V M} {a b d : DS V M} {n k : ℕ} : c.wf → c.eval a = true → Ex C s a b n →
      Ex C (.loop c s) b d k → Ex C (.loop c s) a d (n + k + 2)
  | mono {s : St V M} {a b : DS V M} {n m : ℕ} : Ex C s a b n → n ≤ m → Ex C s a b m

/-- The record `v` fits the width. -/
def Fits (C : Ctx) (v : ℕ) : Prop := v < 2 ^ C.Wd

structure Valid (C : Ctx) (a : DS V M) : Prop where
  env_lt : ∀ x, a.env x < 2 ^ C.Wd
  ip_le : a.ip ≤ C.inp.length
  ram_lt : ∀ m, ∀ v ∈ a.ram m, v < 2 ^ C.Wd
  rc_le : ∀ m, a.rc m ≤ (a.ram m).length
  kin_le : a.kin.length ≤ C.Lk
  kout_le : a.kout.length ≤ C.Bk + 3
  kc_le : a.kc ≤ a.kout.length

theorem putAt_length (l : List ℕ) (i v : ℕ) (hi : i ≤ l.length) :
    (putAt l i v).length = max l.length (i + 1) := by
  unfold putAt; split_ifs with h
  · simp; omega
  · simp; omega

theorem mem_putAt (l : List ℕ) (i v w : ℕ) (hw : w ∈ putAt l i v) : w ∈ l ∨ w = v := by
  unfold putAt at hw; split_ifs at hw with h
  · rcases List.mem_or_eq_of_mem_set hw with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  · simp at hw; tauto

theorem getD_putAt_self (l : List ℕ) (i v : ℕ) (hi : i ≤ l.length) : (putAt l i v).getD i 0 = v := by
  unfold putAt; split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · have : i = l.length := by omega
    subst this; simp [List.getD_eq_getElem?_getD]

theorem getD_putAt_ne (l : List ℕ) (i v j : ℕ) (hi : i ≤ l.length) (hj : j ≠ i) :
    (putAt l i v).getD j 0 = l.getD j 0 := by
  unfold putAt; split_ifs with h
  · simp [List.getD_eq_getElem?_getD, Ne.symm hj]
  · have hil : i = l.length := by omega
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    by_cases hjl : j < l.length
    · rw [List.getElem?_append_left hjl]
    · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

theorem OpEx.valid {C : Ctx} {o : Op V M} {a b : DS V M} {k : ℕ} (h : OpEx C o a b k) (hW : 1 ≤ C.Wd)
    (hB : ∀ s, C.K.bud s ≤ C.Bk → (C.K.outw s).length ≤ C.Bk + 3) (ha : Valid C a) : Valid C b := by
  have h2 : (1 : ℕ) < 2 ^ C.Wd := Nat.one_lt_two_pow (by omega)
  have hset : ∀ (a : DS V M) (x : Fin V) (v : ℕ), Valid C a → v < 2 ^ C.Wd → Valid C (a.set x v) := by
    intro a x v ha hv
    refine ⟨fun y => ?_, ha.ip_le, ha.ram_lt, ha.rc_le, ha.kin_le, ha.kout_le, ha.kc_le⟩
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
  | rdI x a hc =>
    have hv := hset a x (bitOf C.inp a.ip) ha (lt_of_le_of_lt (bitOf_le _ _) h2)
    exact ⟨hv.env_lt, by simp; omega, ha.ram_lt, ha.rc_le, ha.kin_le, ha.kout_le, ha.kc_le⟩
  | bkI a hp => exact ⟨ha.env_lt, by have := ha.ip_le; simp; omega, ha.ram_lt, ha.rc_le, ha.kin_le, ha.kout_le,
      ha.kc_le⟩
  | emit b a => exact ⟨ha.env_lt, ha.ip_le, ha.ram_lt, ha.rc_le, ha.kin_le, ha.kout_le, ha.kc_le⟩
  | rdM m x a hr =>
    have hv : (a.ram m).getD (a.rc m) 0 < 2 ^ C.Wd := by
      rw [List.getD_eq_getElem _ _ hr]; exact ha.ram_lt m _ (List.getElem_mem _)
    have hs := hset a x _ ha hv
    refine ⟨hs.env_lt, ha.ip_le, ha.ram_lt, fun m' => ?_, ha.kin_le, ha.kout_le, ha.kc_le⟩
    by_cases hm : m' = m
    · subst hm; simp [DS.adv]; omega
    · simp [DS.adv, Function.update_of_ne hm]; exact ha.rc_le m'
  | wrM m x a hr =>
    refine ⟨ha.env_lt, ha.ip_le, fun m' v hv => ?_, fun m' => ?_, ha.kin_le, ha.kout_le, ha.kc_le⟩
    · by_cases hm : m' = m
      · subst hm
        simp only [DS.put, Function.update_self] at hv
        rcases mem_putAt _ _ _ _ hv with h1 | h1
        · exact ha.ram_lt m' v h1
        · rw [h1]; exact ha.env_lt x
      · simp only [DS.put, Function.update_of_ne hm] at hv; exact ha.ram_lt m' v hv
    · by_cases hm : m' = m
      · subst hm; simp only [DS.put, Function.update_self]; rw [putAt_length _ _ _ hr]; omega
      · simp only [DS.put, Function.update_of_ne hm]; exact ha.rc_le m'
  | rwM m a =>
    refine ⟨ha.env_lt, ha.ip_le, ha.ram_lt, fun m' => ?_, ha.kin_le, ha.kout_le, ha.kc_le⟩
    by_cases hm : m' = m
    · subst hm; simp [DS.rew]
    · simp [DS.rew, Function.update_of_ne hm]; exact ha.rc_le m'
  | srtM m a h0 =>
    refine ⟨ha.env_lt, ha.ip_le, fun m' v hv => ?_, fun m' => ?_, ha.kin_le, ha.kout_le, ha.kc_le⟩
    · by_cases hm : m' = m
      · subst hm
        simp only [DS.srt, Function.update_self] at hv
        exact ha.ram_lt m' v ((List.perm_insertionSort _ _).mem_iff.mp hv)
      · simp only [DS.srt, Function.update_of_ne hm] at hv; exact ha.ram_lt m' v hv
    · by_cases hm : m' = m
      · subst hm; simp [DS.srt, h0]
      · simp only [DS.srt, Function.update_of_ne hm]; exact ha.rc_le m'
  | kem b a hk => exact ⟨ha.env_lt, ha.ip_le, ha.ram_lt, ha.rc_le, by simp; omega, ha.kout_le, ha.kc_le⟩
  | kcall s a _ hb =>
    exact ⟨ha.env_lt, ha.ip_le, ha.ram_lt, ha.rc_le, by simp [DS.called], hB s hb, by simp [DS.called]⟩
  | rdK x a hk =>
    have hv := hset a x (bitOf a.kout a.kc) ha (lt_of_le_of_lt (bitOf_le _ _) h2)
    exact ⟨hv.env_lt, ha.ip_le, ha.ram_lt, ha.rc_le, ha.kin_le, ha.kout_le, by simp; omega⟩

theorem Ex.valid {C : Ctx} {s : St V M} {a b : DS V M} {n : ℕ} (h : Ex C s a b n) (hW : 1 ≤ C.Wd)
    (hB : ∀ s, C.K.bud s ≤ C.Bk → (C.K.outw s).length ≤ C.Bk + 3) (ha : Valid C a) : Valid C b := by
  induction h with
  | op h => exact h.valid hW hB ha
  | seq _ _ ih1 ih2 => exact ih2 (ih1 ha)
  | iteT _ _ _ ih => exact ih ha
  | iteF _ _ _ ih => exact ih ha
  | loopF _ _ => exact ha
  | loopT _ _ _ _ ih1 ih2 => exact ih2 (ih1 ha)
  | mono _ _ ih => exact ih ha

theorem OpEx.out_len {C : Ctx} {o : Op V M} {a b : DS V M} {k : ℕ} (h : OpEx C o a b k) :
    b.out.length ≤ a.out.length + k := by
  cases h <;> simp [DS.set, DS.adv, DS.put, DS.rew, DS.called, DS.srt]

theorem Ex.out_len {C : Ctx} {s : St V M} {a b : DS V M} {n : ℕ} (h : Ex C s a b n) :
    b.out.length ≤ a.out.length + n := by
  induction h with
  | op h => exact h.out_len
  | seq _ _ ih1 ih2 => omega
  | iteT _ _ _ ih => omega
  | iteF _ _ _ ih => omega
  | loopF _ _ => omega
  | loopT _ _ _ _ ih1 ih2 => omega
  | mono _ hnm ih => omega

theorem OpEx.pos {C : Ctx} {o : Op V M} {a b : DS V M} {k : ℕ} (h : OpEx C o a b k) : 1 ≤ k := by
  cases h <;> omega

theorem Ex.pos {C : Ctx} {s : St V M} {a b : DS V M} {n : ℕ} (h : Ex C s a b n) : 1 ≤ n := by
  induction h with
  | op h => exact h.pos
  | seq _ _ _ _ => omega
  | iteT _ _ _ _ => omega
  | iteF _ _ _ _ => omega
  | loopF _ _ => omega
  | loopT _ _ _ _ _ _ => omega
  | mono _ hnm ih => omega

end NearCubicGates.Close.Cells
