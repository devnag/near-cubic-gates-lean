import Proof.Gates.CellsGatherK.KeySpec
import Proof.Gates.CellsSys.Kit
import Proof.Gates.CellsSys.Sem
import Proof.Gates.Cells.Loop

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.QueryKey

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

def kTmp : Fin VV := ⟨91, by decide⟩
def kW : Fin VV := ⟨92, by decide⟩
def kN : Fin VV := ⟨93, by decide⟩
def kP : Fin VV := ⟨94, by decide⟩
def kI : Fin VV := ⟨95, by decide⟩
def kD : Fin VV := ⟨96, by decide⟩
def kX : Fin VV := ⟨97, by decide⟩
def kA : Fin VV := ⟨98, by decide⟩
def kB : Fin VV := ⟨99, by decide⟩

/-! ## The frame -/

/-- What the key program keeps. -/
structure KF (a b : DS VV MM) : Prop where
  ram : b.ram = a.ram
  rc : ∀ m, m ≠ sE → b.rc m = a.rc m
  rcE : b.rc sE ≤ (b.ram sE).length
  ip : b.ip = a.ip
  out : b.out = a.out
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc
  env : ∀ x : Fin VV, ¬ keyScratch x → b.env x = a.env x

theorem KF.trans {a b d : DS VV MM} (h1 : KF a b) (h2 : KF b d) : KF a d :=
  ⟨h2.ram.trans h1.ram, fun m hm => (h2.rc m hm).trans (h1.rc m hm), h2.rcE, h2.ip.trans h1.ip,
    h2.out.trans h1.out, h2.kin.trans h1.kin, h2.kout.trans h1.kout, h2.kc.trans h1.kc,
    fun x hx => (h2.env x hx).trans (h1.env x hx)⟩

theorem KF.of_same {a b : DS VV MM} {T : List (Fin VV)} (hf : Fr a b T) (hs : Same a b)
    (hT : ∀ x ∈ T, keyScratch x) (hE : a.rc sE ≤ (a.ram sE).length) : KF a b :=
  ⟨hs.ram, fun m _ => by rw [hs.rc], by rw [hs.rc, hs.ram]; exact hE, hs.ip, hs.out, hs.kin, hs.kout, hs.kc,
    fun x hx => hf x (fun h => hx (hT x h))⟩

theorem KF.refl (a : DS VV MM) (hE : a.rc sE ≤ (a.ram sE).length) : KF a a :=
  KF.of_same (T := []) (Fr.refl a []) (Same.refl a) (by simp) hE

theorem KF.cst {a b : DS VV MM} (h : KF a b) (hc : Cst a) : Cst b := by
  have h0 : b.env vZ = a.env vZ := h.env vZ (by unfold keyScratch; decide)
  have h1 : b.env v1 = a.env v1 := h.env v1 (by unfold keyScratch; decide)
  have h2 : b.env v2 = a.env v2 := h.env v2 (by unfold keyScratch; decide)
  exact ⟨h0.trans hc.z, h1.trans hc.one, h2.trans hc.two⟩

variable {C : Ctx}

/-! ## Radix accumulation -/

/-- `kKey := kKey·2^{keyBits} + x`. -/
def accP (x : Fin VV) : St VV MM :=
  .seq (.op (.mul kKey vKB kTmp)) (.seq (.op (.copy kKey kTmp)) (.op (.add kKey x)))

theorem accP_spec (x : Fin VV) (hx1 : x ≠ kKey) (hx2 : x ≠ kTmp) (a : DS VV MM) (KB : ℕ) (hKB : a.env vKB = KB)
    (hW : a.env kKey * KB + a.env x < 2 ^ C.Wd) :
    Hs C (accP x) a 5 (fun b => b.env kKey = a.env kKey * KB + a.env x ∧ Fr a b [kKey, kTmp] ∧ Same a b) := by
  obtain ⟨s1, n1, e1, hn1, h1, f1, m1⟩ := o_mul (C := C) kKey vKB kTmp a (by decide) (by decide) (by decide)
    (by rw [hKB]; omega)
  obtain ⟨s2, n2, e2, hn2, h2, f2, m2⟩ := o_copy (C := C) kKey kTmp s1 (by decide)
  have hx : s2.env x = a.env x := by
    rw [f2.ev (by simp; exact hx1), f1.ev (by simp; exact hx2)]
  obtain ⟨s3, n3, e3, hn3, h3, f3, m3⟩ := o_add (C := C) kKey x s2 (Ne.symm hx1)
    (by rw [h2, h1, hx, hKB]; exact hW)
  refine ⟨s3, n1 + (n2 + n3 + 1) + 1, Ex.seq e1 (Ex.seq e2 e3), by omega, ?_, ?_, (m1.trans m2).trans m3⟩
  · rw [h3, h2, h1, hx, hKB]
  · exact ((f1.weaken (by decide)).trans (f2.weaken (by decide))).trans (f3.weaken (by decide))

/-- One field fits: `rk kb L · 2^{kb} + x < 2^{Wd}`. -/
theorem acc_fit (kb W : ℕ) (L : List ℕ) (x : ℕ) (hL : ∀ z ∈ L ++ [x], z < 2 ^ kb)
    (hW : 2 ^ (kb * (L ++ [x]).length) ≤ 2 ^ W) : rk kb L * 2 ^ kb + x < 2 ^ W := by
  have := rk_lt kb (L ++ [x]) hL
  rw [rk_snoc] at this; omega

/-! ## The key as a radix number -/

section V
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I)

/-- The digit fields `κl` and the residue fields `σl` of query `(t, q, s)`. -/
noncomputable def kapL (t q : ℕ) : List ℕ := GatherPhase.kmod c p wt y (digitsM (List.replicate (nDig c p) (wWin p)) t) q
def sigL (q s : ℕ) : List ℕ := digitsM (List.replicate (roleCount c.kind) q) s

theorem kapL_length (t q : ℕ) : (kapL c p wt y t q).length = nDig c p := by simp [kapL, GatherPhase.kmod]
theorem sigL_length (q s : ℕ) : (sigL c q s).length = roleCount c.kind := by
  simp [sigL, digitsM_length]

theorem qKey_eq (part : Option Bool) (t q s : ℕ) :
    qKey c p wt y part t q s = rk (keyBits p) ([0, partCode part, q] ++ kapL c p wt y t q ++ sigL c q s) := by
  unfold qKey reqKey
  rw [radixKey_eq]
  have hl : (keyFields (ReqId.residue part q (kapL c p wt y t q) (sigL c q s))).length = keyLen c p := by
    simp only [keyFields, List.length_append, List.length_cons, List.length_nil, kapL_length, sigL_length]
    unfold keyLen nDig; ring
  unfold kapL sigL at hl
  rw [hl, Nat.sub_self, List.replicate_zero, List.append_nil]
  rfl

theorem modlem (P N h d q : ℕ) (hq : 0 < q) :
    (((P : ℤ) - N - h + 1 + d) % (q : ℤ)).toNat = (P % q + d + 1 + 2 * q - (N % q + h % q)) % q := by
  have hN := Nat.mod_lt N hq
  have hh := Nat.mod_lt h hq
  have e1 : (P : ℤ) = ((P % q : ℕ) : ℤ) + (q : ℤ) * ((P / q : ℕ) : ℤ) := by exact_mod_cast (Nat.mod_add_div P q).symm
  have e2 : (N : ℤ) = ((N % q : ℕ) : ℤ) + (q : ℤ) * ((N / q : ℕ) : ℤ) := by exact_mod_cast (Nat.mod_add_div N q).symm
  have e3 : (h : ℤ) = ((h % q : ℕ) : ℤ) + (q : ℤ) * ((h / q : ℕ) : ℤ) := by exact_mod_cast (Nat.mod_add_div h q).symm
  set A := P % q + d + 1 + 2 * q - (N % q + h % q) with hA
  have eA : (A : ℤ) = ((P % q : ℕ) : ℤ) + d + 1 + 2 * q - ((N % q : ℕ) : ℤ) - ((h % q : ℕ) : ℤ) := by
    rw [hA]; push_cast [Nat.cast_sub (show N % q + h % q ≤ P % q + d + 1 + 2 * q by omega)]; ring
  have key : (P : ℤ) - N - h + 1 + d = (A : ℤ) + (q : ℤ) * (((P / q : ℕ) : ℤ) - ((N / q : ℕ) : ℤ) -
      ((h / q : ℕ) : ℤ) - 2) := by
    rw [eA]; nth_rewrite 1 [e1]; nth_rewrite 1 [e2]; nth_rewrite 1 [e3]; ring
  rw [key, Int.add_mul_emod_self_left]
  have : ((A : ℤ) % (q : ℤ)) = ((A % q : ℕ) : ℤ) := by push_cast; rfl
  rw [this, Int.toNat_natCast]

/-- **Field `idx` of `κl` from the stored centres.** -/
theorem kfield_eq (t q : ℕ) (hq : 0 < q) (idx : ℕ) (hidx : idx < nDig c p) :
    (kapL c p wt y t q).getD idx 0 =
      ((ctrL c p wt y).getD (2 * idx) 0 % q + t / wWin p ^ (nDig c p - 1 - idx) % wWin p + 1 + 2 * q -
        ((ctrL c p wt y).getD (2 * idx + 1) 0 % q + p.hE % q)) % q := by
  have hJ : 0 < p.J := by
    rcases Nat.eq_zero_or_pos p.J with h | h
    · unfold nDig at hidx; rw [h] at hidx; simp at hidx
    · exact h
  set rj := rjOf c p idx hidx with hrj
  have hix : rj.1.val * p.J + rj.2.val = idx := idx_rjOf c p idx hidx
  have hpos : (ctrL c p wt y).getD (2 * idx) 0 = (ctr c p wt y rj).toNat := by
    have := SystemsPhase.ctrL_pos c p wt y rj.1.val rj.2.val rj.1.isLt rj.2.isLt
    rw [hix] at this; rw [this]
  have hneg : (ctrL c p wt y).getD (2 * idx + 1) 0 = (-ctr c p wt y rj).toNat := by
    have := SystemsPhase.ctrL_neg c p wt y rj.1.val rj.2.val rj.1.isLt rj.2.isLt
    rw [hix] at this; rw [this]
  have hd : (digitsM (List.replicate (nDig c p) (wWin p)) t).getD idx 0 =
      t / wWin p ^ (nDig c p - 1 - idx) % wWin p := digitsM_rep_getD (wWin p) (nDig c p) t idx hidx
  unfold kapL GatherPhase.kmod
  rw [List.getD_eq_getElem _ _ (by simp; exact hidx), List.getElem_ofFn]
  show (kappaOf c p wt y (digitsM (List.replicate (nDig c p) (wWin p)) t) rj % (q : ℤ)).toNat = _
  rw [hpos, hneg, ← modlem _ _ _ _ _ hq]
  unfold kappaOf
  rw [hix, hd]
  congr 2
  have := SystemsPhase.toNat_sub_toNat_neg' (ctr c p wt y rj)
  push_cast
  linarith

end V

end NearCubicGates.Close.Cells.QueryKey
