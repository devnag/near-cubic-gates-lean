import Proof.Gates.Cells.Hs

set_option autoImplicit false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces

/-- Variables. -/
abbrev VV : ℕ := 128
/-- Record stores (`Cells.Vars` names them). -/
abbrev MM : ℕ := 10

def vZ : Fin VV := ⟨0, by decide⟩
def v1 : Fin VV := ⟨1, by decide⟩
def v2 : Fin VV := ⟨2, by decide⟩
def vJ : Fin VV := ⟨3, by decide⟩
def t0 : Fin VV := ⟨4, by decide⟩
def t1 : Fin VV := ⟨5, by decide⟩
def t2 : Fin VV := ⟨6, by decide⟩
def t3 : Fin VV := ⟨7, by decide⟩
def t4 : Fin VV := ⟨8, by decide⟩
def t5 : Fin VV := ⟨9, by decide⟩
def t6 : Fin VV := ⟨10, by decide⟩
def t7 : Fin VV := ⟨11, by decide⟩
def t8 : Fin VV := ⟨12, by decide⟩
def t9 : Fin VV := ⟨13, by decide⟩

@[simp] theorem DS.env_set (a : DS VV MM) (x : Fin VV) (v : ℕ) : (a.set x v).env = Function.update a.env x v := rfl

/-- The program-wide constants. -/
structure Cst (a : DS VV MM) : Prop where
  z : a.env vZ = 0
  one : a.env v1 = 1
  two : a.env v2 = 2

theorem Cst.of_fr {a b : DS VV MM} {T : List (Fin VV)} (hc : Cst a) (hf : Fr a b T)
    (hT : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T) : Cst b :=
  ⟨by rw [hf vZ hT.1]; exact hc.z, by rw [hf v1 hT.2.1]; exact hc.one, by rw [hf v2 hT.2.2]; exact hc.two⟩

variable {C : Ctx}

/-! ## Single operations -/

section Ops
variable (C)

theorem hs_zero (x : Fin VV) (a : DS VV MM) : Hs C (.op (.zero x)) a 1 (· = a.set x 0) :=
  Hs.op (OpEx.zero x a) rfl

theorem hs_inc (x : Fin VV) (a : DS VV MM) (h : a.env x + 1 < 2 ^ C.Wd) :
    Hs C (.op (.inc x)) a 1 (· = a.set x (a.env x + 1)) := Hs.op (OpEx.inc x a h) rfl

theorem hs_add (x y : Fin VV) (a : DS VV MM) (hxy : x ≠ y) (h : a.env x + a.env y < 2 ^ C.Wd) :
    Hs C (.op (.add x y)) a 1 (· = a.set x (a.env x + a.env y)) := Hs.op (OpEx.add x y a hxy h) rfl

theorem hs_sub (x y : Fin VV) (a : DS VV MM) (hxy : x ≠ y) (h : a.env y ≤ a.env x) :
    Hs C (.op (.sub x y)) a 1 (· = a.set x (a.env x - a.env y)) := Hs.op (OpEx.sub x y a hxy h) rfl

theorem hs_copy (x y : Fin VV) (a : DS VV MM) (hxy : x ≠ y) :
    Hs C (.op (.copy x y)) a 1 (· = a.set x (a.env y)) := Hs.op (OpEx.copy x y a hxy) rfl

theorem hs_half (x : Fin VV) (a : DS VV MM) : Hs C (.op (.half x)) a 1 (· = a.set x (a.env x / 2)) :=
  Hs.op (OpEx.half x a) rfl

theorem hs_shl (x : Fin VV) (a : DS VV MM) (h : 2 * a.env x < 2 ^ C.Wd) :
    Hs C (.op (.shl x)) a 1 (· = a.set x (2 * a.env x)) := Hs.op (OpEx.shl x a h) rfl

theorem hs_mul (x y z : Fin VV) (a : DS VV MM) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : a.env x * a.env y < 2 ^ C.Wd) :
    Hs C (.op (.mul x y z)) a 1 (· = a.set z (a.env x * a.env y)) := Hs.op (OpEx.mul x y z a hxy hxz hyz h) rfl

theorem hs_dm (x y q r : Fin VV) (a : DS VV MM) (hxy : x ≠ y) (hxq : x ≠ q) (hxr : x ≠ r) (hyq : y ≠ q)
    (hyr : y ≠ r) (hqr : q ≠ r) (hy : 0 < a.env y) (h2 : 2 * a.env y ≤ 2 ^ C.Wd) :
    Hs C (.op (.dm x y q r)) a 1 (· = (a.set q (a.env x / a.env y)).set r (a.env x % a.env y)) :=
  Hs.op (OpEx.dm x y q r a hxy hxq hxr hyq hyr hqr hy h2) rfl

theorem hs_rdI (x : Fin VV) (a : DS VV MM) (h : a.ip < C.inp.length) :
    Hs C (.op (.rdI x)) a 1 (· = { a.set x (bitOf C.inp a.ip) with ip := a.ip + 1 }) := Hs.op (OpEx.rdI x a h) rfl

theorem hs_emit (b : Bool) (a : DS VV MM) : Hs C (.op (.emit b)) a 1 (· = { a with out := a.out ++ [b] }) :=
  Hs.op (OpEx.emit b a) rfl

theorem hs_kem (b : Bool) (a : DS VV MM) (h : a.kin.length < C.Lk) :
    Hs C (.op (.kem b)) a 1 (· = { a with kin := a.kin ++ [b] }) := Hs.op (OpEx.kem b a h) rfl

theorem hs_rdK (x : Fin VV) (a : DS VV MM) (h : a.kc < a.kout.length) :
    Hs C (.op (.rdK x)) a 1 (· = { a.set x (bitOf a.kout a.kc) with kc := a.kc + 1 }) := Hs.op (OpEx.rdK x a h) rfl

theorem hs_rdM (m : Fin MM) (x : Fin VV) (a : DS VV MM) (h : a.rc m < (a.ram m).length) :
    Hs C (.op (.rdM m x)) a 1 (· = (a.set x ((a.ram m).getD (a.rc m) 0)).adv m) := Hs.op (OpEx.rdM m x a h) rfl

theorem hs_wrM (m : Fin MM) (x : Fin VV) (a : DS VV MM) (h : a.rc m ≤ (a.ram m).length) :
    Hs C (.op (.wrM m x)) a 1 (· = a.put m (a.env x)) := Hs.op (OpEx.wrM m x a h) rfl

theorem hs_rwM (m : Fin MM) (a : DS VV MM) : Hs C (.op (.rwM m)) a (a.rc m + 1) (· = a.rew m) :=
  Hs.op (OpEx.rwM m a) rfl

theorem hs_srtM (m : Fin MM) (a : DS VV MM) (h : a.rc m = 0) :
    Hs C (.op (.srtM m)) a ((a.ram m).length + 1) (· = a.srt m) := Hs.op (OpEx.srtM m a h) rfl

end Ops

/-! ## Basics -/

/-- No effect (clears the junk variable). -/
def skipS : St VV MM := .op (.zero vJ)

theorem skip_spec (a : DS VV MM) : Hs C skipS a 1 (· = a.set vJ 0) := hs_zero C vJ a

/-! ## natWord facts -/

theorem natWord_eq (v : ℕ) : natWord v =
    List.replicate (natBitLength v) true ++ false :: List.ofFn (fun i : Fin (natBitLength v) => v.testBit i.val) := rfl

theorem natWord_length (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 := by
  rw [natWord_eq]; simp; ring

theorem natWord_one (v j : ℕ) (hj : j < natBitLength v) : (natWord v).getD j false = true := by
  rw [natWord_eq, List.getD_append _ _ _ _ (by simpa using hj)]
  simp [List.getD_eq_getElem?_getD, hj]

theorem natWord_zero (v : ℕ) : (natWord v).getD (natBitLength v) false = false := by
  rw [natWord_eq, List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem natWord_bit (v k : ℕ) (hk : k < natBitLength v) :
    (natWord v).getD (natBitLength v + 1 + k) false = v.testBit k := by
  rw [natWord_eq, List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_replicate, show natBitLength v + 1 + k - natBitLength v = k + 1 by omega,
    List.getD_cons_succ]
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

theorem lt_natBitLength (v : ℕ) : v < 2 ^ natBitLength v := by
  unfold natBitLength; exact Nat.lt_pow_succ_log_self (by norm_num) v

theorem bitOf_drop {cw u rest : List Bool} {cp : ℕ} (h : cw.drop cp = u ++ rest) (j : ℕ) (hj : j < u.length) :
    bitOf cw (cp + j) = (u.getD j false).toNat := by
  unfold bitOf
  have : cw.getD (cp + j) false = (cw.drop cp).getD j false := by
    simp [List.getD_eq_getElem?_getD]
  rw [this, h, List.getD_append _ _ _ _ hj]

theorem lt_of_drop {cw u rest : List Bool} {cp : ℕ} (h : cw.drop cp = u ++ rest) (j : ℕ) (hj : j < u.length) :
    cp + j < cw.length := by
  have := congrArg List.length h
  simp at this; omega

theorem drop_adv {cw u rest : List Bool} {cp : ℕ} (h : cw.drop cp = u ++ rest) :
    cw.drop (cp + u.length) = rest := by
  rw [← List.drop_drop, h, List.drop_left]

theorem natBitLength_pos (v : ℕ) : 1 ≤ natBitLength v := by unfold natBitLength; omega

end NearCubicGates.Close.Cells
