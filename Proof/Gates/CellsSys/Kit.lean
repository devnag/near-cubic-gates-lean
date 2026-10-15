import Proof.Gates.CellsSys.Math

set_option autoImplicit false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

/-- Everything but the variables and the store cursors. -/
structure Kp (a b : DS VV MM) : Prop where
  ip : b.ip = a.ip
  out : b.out = a.out
  ram : b.ram = a.ram
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  rcA : b.rc sA = a.rc sA

theorem Kp.refl (a : DS VV MM) : Kp a a := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem Kp.trans {a b d : DS VV MM} (h1 : Kp a b) (h2 : Kp b d) : Kp a d :=
  ⟨h2.ip.trans h1.ip, h2.out.trans h1.out, h2.ram.trans h1.ram, h2.kin.trans h1.kin, h2.kout.trans h1.kout,
    h2.kc.trans h1.kc, h2.rcA.trans h1.rcA⟩
theorem Kp.of_same {a b : DS VV MM} (h : Same a b) : Kp a b :=
  ⟨h.ip, h.out, h.ram, h.kin, h.kout, h.kc, by rw [h.rc]⟩

theorem Fr.ev {a b : DS VV MM} {T : List (Fin VV)} (h : Fr a b T) {y : Fin VV} (hy : y ∉ T) : b.env y = a.env y :=
  h y hy

theorem cst_of {a b : DS VV MM} {T : List (Fin VV)} (hc : Cst a) (hf : Fr a b T)
    (hT : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T) : Cst b := Cst.of_fr hc hf hT

/-! ## Operations -/

theorem o_zero (x : Fin VV) (a : DS VV MM) :
    Hs C (.op (.zero x)) a 1 (fun b => b.env x = 0 ∧ Fr a b [x] ∧ Same a b) :=
  Hs.mono (hs_zero C x a) le_rfl (fun b hb => by subst hb; exact ⟨by simp, Fr.set a 0 (by simp), Same.set a x 0⟩)

theorem o_inc (x : Fin VV) (a : DS VV MM) (h : a.env x + 1 < 2 ^ C.Wd) :
    Hs C (.op (.inc x)) a 1 (fun b => b.env x = a.env x + 1 ∧ Fr a b [x] ∧ Same a b) :=
  Hs.mono (hs_inc C x a h) le_rfl (fun b hb => by subst hb; exact ⟨by simp, Fr.set a _ (by simp), Same.set a x _⟩)

theorem o_add (x y : Fin VV) (a : DS VV MM) (hxy : x ≠ y) (h : a.env x + a.env y < 2 ^ C.Wd) :
    Hs C (.op (.add x y)) a 1 (fun b => b.env x = a.env x + a.env y ∧ Fr a b [x] ∧ Same a b) :=
  Hs.mono (hs_add C x y a hxy h) le_rfl
    (fun b hb => by subst hb; exact ⟨by simp, Fr.set a _ (by simp), Same.set a x _⟩)

theorem o_sub (x y : Fin VV) (a : DS VV MM) (hxy : x ≠ y) (h : a.env y ≤ a.env x) :
    Hs C (.op (.sub x y)) a 1 (fun b => b.env x = a.env x - a.env y ∧ Fr a b [x] ∧ Same a b) :=
  Hs.mono (hs_sub C x y a hxy h) le_rfl
    (fun b hb => by subst hb; exact ⟨by simp, Fr.set a _ (by simp), Same.set a x _⟩)

theorem o_copy (x y : Fin VV) (a : DS VV MM) (hxy : x ≠ y) :
    Hs C (.op (.copy x y)) a 1 (fun b => b.env x = a.env y ∧ Fr a b [x] ∧ Same a b) :=
  Hs.mono (hs_copy C x y a hxy) le_rfl
    (fun b hb => by subst hb; exact ⟨by simp, Fr.set a _ (by simp), Same.set a x _⟩)

theorem o_shl (x : Fin VV) (a : DS VV MM) (h : 2 * a.env x < 2 ^ C.Wd) :
    Hs C (.op (.shl x)) a 1 (fun b => b.env x = 2 * a.env x ∧ Fr a b [x] ∧ Same a b) :=
  Hs.mono (hs_shl C x a h) le_rfl (fun b hb => by subst hb; exact ⟨by simp, Fr.set a _ (by simp), Same.set a x _⟩)

/-- All store cursors in range. -/
def RcOK (a : DS VV MM) : Prop := ∀ m, a.rc m ≤ (a.ram m).length

theorem RcOK.fetch {a b : DS VV MM} {m : Fin MM} {x : ℕ} (h : RcOK a) (hk : Kp a b)
    (hrc : b.rc = Function.update a.rc m (x + 1)) (hx : x < (a.ram m).length) : RcOK b := by
  intro m'
  rw [hrc, hk.ram]
  by_cases hm : m' = m
  · subst hm; simp; omega
  · rw [Function.update_of_ne hm]; exact h m'

theorem RcOK.same {a b : DS VV MM} (h : RcOK a) (hs : Same a b) : RcOK b := fun m => by
  rw [hs.rc, hs.ram]; exact h m

/-- `z := x * y`. -/
theorem o_mul (x y z : Fin VV) (a : DS VV MM) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (h : a.env x * a.env y < 2 ^ C.Wd) :
    Hs C (.op (.mul x y z)) a 1 (fun b => b.env z = a.env x * a.env y ∧ Fr a b [z] ∧ Same a b) :=
  Hs.mono (hs_mul C x y z a hxy hxz hyz h) le_rfl
    (fun b hb => by subst hb; exact ⟨by simp, Fr.set a _ (by simp), Same.set a z _⟩)

/-- `q := x / y`, `r := x % y`. -/
theorem o_dm (x y q r : Fin VV) (a : DS VV MM) (hxy : x ≠ y) (hxq : x ≠ q) (hxr : x ≠ r) (hyq : y ≠ q)
    (hyr : y ≠ r) (hqr : q ≠ r) (hy : 0 < a.env y) (h2 : 2 * a.env y ≤ 2 ^ C.Wd) :
    Hs C (.op (.dm x y q r)) a 1 (fun b => b.env q = a.env x / a.env y ∧ b.env r = a.env x % a.env y ∧
      Fr a b [q, r] ∧ Same a b) :=
  Hs.mono (hs_dm C x y q r a hxy hxq hxr hyq hyr hqr hy h2) le_rfl (fun b hb => by
    subst hb
    refine ⟨by rw [DS.set_env_ne _ _ hqr]; simp, by simp,
      Fr.trans (Fr.set a _ (by simp)) (Fr.set _ _ (by simp)), Same.trans (Same.set a q _) (Same.set _ r _)⟩)

/-- Fetch the record at index `x` of store `m` into `d`. -/
theorem o_fetch (m : Fin MM) (x d : Fin VV) (hx0 : x ≠ c0) (hxJ : x ≠ vJ) (hm : m ≠ sA) (a : DS VV MM)
    (hlt : a.env x < (a.ram m).length) (hW : a.env x < 2 ^ C.Wd) :
    Hs C (fetch m x d) a (a.rc m + 5 * a.env x + 9) (fun b => b.env d = (a.ram m).getD (a.env x) 0 ∧
      Fr a b [c0, vJ, d] ∧ Kp a b ∧ b.rc = Function.update a.rc m (a.env x + 1)) :=
  Hs.mono (fetch_spec m x d hx0 hxJ a hlt hW) le_rfl
    (fun _ ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ => ⟨h1, h9, ⟨h2, h3, h4, h6, h7, h8,
      by rw [h5, Function.update_of_ne (Ne.symm hm)]⟩, h5⟩)

/-- One `natWord` read from the call output. -/
theorem o_rdNatK (a : DS VV MM) (hc : Cst a) (v : ℕ) (rest : List Bool) (hcw : a.kout.drop a.kc = natWord v ++ rest)
    (hW : natBitLength v + 2 ≤ C.Wd) :
    Hs C rdNatK a (30 * natBitLength v + 30) (fun b => b.env t3 = v ∧ b.kout.drop b.kc = rest ∧
      b.kout = a.kout ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.kin = a.kin ∧ Cst b ∧ Fr a b rdNatT) :=
  Hs.mono (rdNatK_spec a hc v rest hcw hW) le_rfl (fun b ⟨h1, _, h3, h4, h5⟩ => by
    simp only [Prod.mk.injEq] at h4
    obtain ⟨e1, e2, e3, -, e5, e6⟩ := h4
    refine ⟨h1, ?_, e6, e1, e2, e3, e5, cst_fr hc h5, h5⟩
    rw [h3, e6, ← List.drop_drop, hcw, List.drop_left])

/-- One `natWord` (of `t3`) printed to the call input. -/
theorem o_emitNatK (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd) (hv : natBitLength (a.env t3) + 2 < 2 ^ C.Wd)
    (hk : a.kin.length + (natWord (a.env t3)).length ≤ C.Lk) :
    Hs C emitNatK a (40 * natBitLength (a.env t3) + 40) (fun b => b.kin = a.kin ++ natWord (a.env t3) ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Cst b ∧ Fr a b emitNatT) :=
  Hs.mono (emitNatK_spec a hc hW hv hk) le_rfl (fun b ⟨h1, h2, h3, h4⟩ => by
    simp only [Prod.mk.injEq] at h2
    obtain ⟨e1, e2, e3, -, e5, e6⟩ := h2
    exact ⟨h1, e1, e2, e3, e5, e6, h3, h4⟩)

end NearCubicGates.Close.Cells
