import Proof.Gates.CellsGather.Plan
import Proof.Gates.CellsSys.Kit
import Proof.Gates.Cells.Loop

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.GatherPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

def gx : Fin VV := ⟨90, by decide⟩
def gPZ : Fin VV := ⟨91, by decide⟩
def gPad : Fin VV := ⟨92, by decide⟩
def gLast : Fin VV := ⟨93, by decide⟩
def gNQ : Fin VV := ⟨94, by decide⟩
def gQ : Fin VV := ⟨95, by decide⟩
def gR : Fin VV := ⟨96, by decide⟩
def gK : Fin VV := ⟨97, by decide⟩
def gF : Fin VV := ⟨98, by decide⟩
def gA : Fin VV := ⟨99, by decide⟩

def swAns : St VV MM :=
  .seq (.op (.mul gR p2VW gA)) (.seq (.op (.add gA gLast)) (.seq (.op (.wrM sA gA)) (.op (.inc gNQ))))

/-- One record of the sweep. -/
def swBody : St VV MM :=
  .seq (.op (.dm gx gPZ gQ gR)) (.seq (.op (.dm gQ v2 gK gF)) (.ite (.eq gF vZ) (.op (.copy gLast gR)) swAns))

/-- The variables the sweep step writes. -/
def swT : List (Fin VV) := [gQ, gR, gK, gF, gA, gLast, gNQ]

theorem putAt_pre (W S : List ℕ) (v : ℕ) :
    putAt (W ++ S.drop W.length) W.length v = (W ++ [v]) ++ S.drop (W.length + 1) := by
  unfold putAt
  rcases h : S.drop W.length with _ | ⟨s, rest⟩
  · have : S.drop (W.length + 1) = [] := by
      rw [← List.drop_drop, h]; rfl
    simp [this]
  · have : S.drop (W.length + 1) = rest := by
      rw [← List.drop_drop, h]; rfl
    rw [if_pos (by simp), this, List.set_append_right _ _ (by omega)]
    simp

theorem sweep_one_t (Z Z' x l : ℕ) (h : gFlag Z x = 0) : sweep Z Z' [x] l = [] := by simp [sweep, h]
theorem sweep_one_q (Z Z' x l : ℕ) (h : gFlag Z x ≠ 0) : sweep Z Z' [x] l = [gPay Z x * 2 ^ Z' + l] := by
  simp [sweep, h]
theorem lastV_one_t (Z x l : ℕ) (h : gFlag Z x = 0) : lastV Z [x] l = gPay Z x := by simp [lastV, h]
theorem lastV_one_q (Z x l : ℕ) (h : gFlag Z x ≠ 0) : lastV Z [x] l = l := by simp [lastV, h]

variable {C : Ctx}

/-- **One record of the sweep.** -/
theorem swBody_spec (a : DS VV MM) (hc : Cst a) (Z VW : ℕ) (hPZ : a.env gPZ = 2 ^ Z)
    (hVW : a.env p2VW = 2 ^ VW) (hW1 : 2 * 2 ^ Z ≤ 2 ^ C.Wd) (hW2 : 4 ≤ 2 ^ C.Wd)
    (hW3 : 2 ^ Z * 2 ^ VW + 2 ^ Z ≤ 2 ^ C.Wd) (hl : a.env gLast < 2 ^ Z) (hq : a.env gNQ + 1 < 2 ^ C.Wd)
    (W S : List ℕ) (hA : a.ram sA = W ++ S.drop W.length) (hrA : a.rc sA = W.length) :
    Hs C swBody a 12 (fun b =>
      b.ram sA = (W ++ sweep Z VW [a.env gx] (a.env gLast)) ++
        S.drop (W ++ sweep Z VW [a.env gx] (a.env gLast)).length ∧
      b.rc sA = (W ++ sweep Z VW [a.env gx] (a.env gLast)).length ∧
      (∀ m, m ≠ sA → b.ram m = a.ram m ∧ b.rc m = a.rc m) ∧
      b.env gLast = lastV Z [a.env gx] (a.env gLast) ∧
      b.env gNQ = a.env gNQ + (sweep Z VW [a.env gx] (a.env gLast)).length ∧
      Fr a b swT ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc) := by
  obtain ⟨s1, n1, e1, hn1, h1q, h1r, f1, m1⟩ := o_dm (C := C) gx gPZ gQ gR a (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [hPZ]; positivity) (by rw [hPZ]; exact hW1)
  have hv2 : s1.env v2 = 2 := by rw [f1.ev (by decide)]; exact hc.two
  obtain ⟨s2, n2, e2, hn2, h2k, h2f, f2, m2⟩ := o_dm (C := C) gQ v2 gK gF s1 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by rw [hv2]; norm_num) (by rw [hv2]; omega)
  have hF : s2.env gF = gFlag Z (a.env gx) := by rw [h2f, h1q, hv2, hPZ]; rfl
  have hR : s2.env gR = gPay Z (a.env gx) := by rw [f2.ev (by decide), h1r, hPZ]; rfl
  have hZ : s2.env vZ = 0 := by rw [f2.ev (by decide), f1.ev (by decide)]; exact hc.z
  have hL : s2.env gLast = a.env gLast := by rw [f2.ev (by decide), f1.ev (by decide)]
  have hN : s2.env gNQ = a.env gNQ := by rw [f2.ev (by decide), f1.ev (by decide)]
  have hV : s2.env p2VW = 2 ^ VW := by rw [f2.ev (by decide), f1.ev (by decide)]; exact hVW
  have hm2 : Same a s2 := m1.trans m2
  have f12 : Fr a s2 swT := (f1.weaken (by decide)).trans (f2.weaken (by decide))
  by_cases hfl : gFlag Z (a.env gx) = 0
  · obtain ⟨s3, n3, e3, hn3, h3l, f3, m3⟩ := o_copy (C := C) gLast gR s2 (by decide)
    have hsw := sweep_one_t Z VW (a.env gx) (a.env gLast) hfl
    have hm : Same a s3 := hm2.trans m3
    refine ⟨s3, n1 + (n2 + (n3 + 1) + 1) + 1, Ex.seq e1 (Ex.seq e2 (Ex.iteT (show (Cnd.eq gF vZ).wf from (by decide : gF ≠ vZ))
      (by simp [Cnd.eval, hF, hZ, hfl]) e3)), by omega, ?_⟩
    refine ⟨by rw [hsw, List.append_nil, hm.ram]; exact hA, by rw [hsw, List.append_nil, hm.rc]; exact hrA,
      fun m _ => ⟨by rw [hm.ram], by rw [hm.rc]⟩, by rw [h3l, hR, lastV_one_t Z _ _ hfl],
      by rw [hsw, f3.ev (by decide), hN]; rfl, f12.trans (f3.weaken (by decide)), hm.ip, hm.out, hm.kin, hm.kout,
      hm.kc⟩
  · have hsw := sweep_one_q Z VW (a.env gx) (a.env gLast) hfl
    have hpay : gPay Z (a.env gx) < 2 ^ Z := Nat.mod_lt _ (by positivity)
    have hprod : gPay Z (a.env gx) * 2 ^ VW + 2 ^ VW ≤ 2 ^ Z * 2 ^ VW := by
      have := Nat.mul_le_mul_right (2 ^ VW) (show gPay Z (a.env gx) + 1 ≤ 2 ^ Z by omega)
      rw [Nat.add_mul, one_mul] at this; exact this
    have hVp : 0 < 2 ^ VW := by positivity
    obtain ⟨s3, n3, e3, hn3, h3a, f3, m3⟩ := o_mul (C := C) gR p2VW gA s2 (by decide) (by decide) (by decide)
      (by rw [hR, hV]; omega)
    have h3l : s3.env gLast = a.env gLast := by rw [f3.ev (by decide), hL]
    obtain ⟨s4, n4, e4, hn4, h4a, f4, m4⟩ := o_add (C := C) gA gLast s3 (by decide)
      (by rw [h3a, h3l, hR, hV]; omega)
    have hm4 : Same a s4 := (hm2.trans m3).trans m4
    have hrc4 : s4.rc sA ≤ (s4.ram sA).length := by rw [hm4.rc, hm4.ram, hA, hrA]; simp
    obtain ⟨s5, n5, e5, hn5, rfl⟩ := hs_wrM (C := C) sA gA s4 hrc4
    have h5n : (s4.put sA (s4.env gA)).env gNQ = a.env gNQ := by
      show s4.env gNQ = _; rw [f4.ev (by decide), f3.ev (by decide), hN]
    obtain ⟨s6, n6, e6, hn6, h6n, f6, m6⟩ := o_inc (C := C) gNQ (s4.put sA (s4.env gA)) (by rw [h5n]; exact hq)
    refine ⟨s6, n1 + (n2 + ((n3 + (n4 + (n5 + n6 + 1) + 1) + 1) + 1) + 1) + 1, Ex.seq e1 (Ex.seq e2
      (Ex.iteF (show (Cnd.eq gF vZ).wf from (by decide : gF ≠ vZ)) (by simp [Cnd.eval, hF, hZ, hfl]) (Ex.seq e3 (Ex.seq e4 (Ex.seq e5 e6))))),
      by omega, ?_⟩
    have hval : s4.env gA = gPay Z (a.env gx) * 2 ^ VW + a.env gLast := by rw [h4a, h3a, h3l, hR, hV]
    refine ⟨?_, ?_, fun m hm => ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [m6.ram]; simp only [DS.put, Function.update_self]
      rw [hm4.rc, hm4.ram, hA, hrA, hval, putAt_pre, hsw, List.length_append, List.length_singleton]
    · rw [m6.rc]; simp only [DS.put, Function.update_self]
      rw [hm4.rc, hrA, hsw, List.length_append, List.length_singleton]
    · rw [m6.ram]; simp only [DS.put, Function.update_of_ne hm]; rw [hm4.ram]
    · rw [m6.rc]; simp only [DS.put, Function.update_of_ne hm]; rw [hm4.rc]
    · rw [f6.ev (by decide)]; show s4.env gLast = _
      rw [f4.ev (by decide), h3l, lastV_one_q Z _ _ hfl]
    · rw [h6n, h5n, hsw]; rfl
    · exact ((f12.trans (f3.weaken (by decide))).trans (f4.weaken (by decide))).trans
        ((show Fr s4 (s4.put sA (s4.env gA)) swT from fun _ _ => rfl).trans (f6.weaken (by decide)))
    · rw [m6.ip]; exact hm4.ip
    · rw [m6.out]; exact hm4.out
    · rw [m6.kin]; exact hm4.kin
    · rw [m6.kout]; exact hm4.kout
    · rw [m6.kc]; exact hm4.kc

end NearCubicGates.Close.Cells.GatherPhase
