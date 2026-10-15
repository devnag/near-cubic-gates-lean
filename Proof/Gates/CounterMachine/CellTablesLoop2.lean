import Proof.Gates.CounterMachine.CellTablesLoop1

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader (sN)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW sREC sTMP convP Frame)

def lIQ : Fin VV := ⟨98, by decide⟩
def lI2 : Fin VV := ⟨99, by decide⟩
def lTmp2 : Fin VV := ⟨90, by decide⟩

def primeB : St VV MM :=
  .seq (.op (.rdM sQ lQ)) (.seq (.op (.copy lQE v1)) (.seq (powP lQE lQ lI2 wE lTmp2) (.seq (.op (.copy lQD v1))
  (.seq (powP lQD lQ lI2 kD lTmp2) (forS lT lQD resB)))))

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

/-- The records of all residue requests of one part and one prime. -/
def resRecs (c : Call) (p : Params) (wt : Wit c.n) (part : Option Bool) (q : ℕ) : List ℕ :=
  ((List.range (q ^ dOf c p)).map (resId c p part q)).flatMap (recsOf c p wt)

/-- The frame of the prime loop: like `Keep`, but `sQ`'s cursor moves too. -/
structure KeepQ (a e : DS VV MM) (T : List (Fin VV)) : Prop where
  ram : ∀ m, m ≠ sREC → m ≠ sTMP → e.ram m = a.ram m
  rc : ∀ m, m ≠ sREC → m ≠ sTMP → m ≠ sN → m ≠ sQ → e.rc m = a.rc m
  out : e.out = a.out
  ip : e.ip = a.ip
  env : ∀ y, ¬ BodyVar y → y ∉ T → e.env y = a.env y

theorem KeepQ.trans {a b d : DS VV MM} {T : List (Fin VV)} (h1 : KeepQ a b T) (h2 : KeepQ b d T) : KeepQ a d T :=
  ⟨fun m h h' => (h2.ram m h h').trans (h1.ram m h h'),
    fun m h h' h'' h''' => (h2.rc m h h' h'' h''').trans (h1.rc m h h' h'' h'''),
    h2.out.trans h1.out, h2.ip.trans h1.ip, fun y h h' => (h2.env y h h').trans (h1.env y h h')⟩

theorem KeepQ.of_keep {a e : DS VV MM} {T T' : List (Fin VV)} (h : Keep a e T) (hT : ∀ y ∈ T, y ∈ T') :
    KeepQ a e T' :=
  ⟨h.ram, fun m h1 h2 h3 _ => h.rc m h1 h2 h3, h.out, h.ip, fun y h1 h2 => h.env y h1 (fun hm => h2 (hT y hm))⟩

theorem KeepQ.refl (a : DS VV MM) (T : List (Fin VV)) : KeepQ a a T :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, rfl, rfl, fun _ _ _ => rfl⟩

def primeBT : List (Fin VV) := [lQ, lQE, lQD, lT, lI2, lTmp2]
def primeT : List (Fin VV) := lIQ :: primeBT

/-- The protected variables a `Pre` mentions. -/
theorem Pre.of_fr {C : Ctx} {r : CellReq B1 B2 cT} {a e : DS VV MM} {T : List (Fin VV)} (hP : Pre C r a)
    (hv : Valid C e) (hs : e.sh = a.sh) (hf : Fr a e T)
    (hT : T.all (fun y => decide (3 ≤ y.val) && !(y = CellTablesProg.wN || y = vS || y = vH1 || y = vH0 || y = vSH || y = kB2 ||
      y = kD || y = kVW2 || y = kPAD)) = true) : Pre C r e := by
  have hm : ∀ z : Fin VV, (z = vZ ∨ z = v1 ∨ z = v2 ∨ z = CellTablesProg.wN ∨ z = vS ∨ z = vH1 ∨ z = vH0 ∨ z = vSH ∨ z = kB2 ∨
      z = kD ∨ z = kVW2 ∨ z = kPAD) → z ∉ T := by
    intro z hz hzT
    have := List.all_eq_true.mp hT z hzT
    rcases hz with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> exact absurd this (by decide)
  simp only [DS.sh, Prod.mk.injEq] at hs
  obtain ⟨_, _, h3, h4, h5, _, _⟩ := hs
  exact ⟨hv, ⟨by rw [hf vZ (hm vZ (by simp))]; exact hP.cst.z, by rw [hf v1 (hm v1 (by simp))]; exact hP.cst.one,
    by rw [hf v2 (hm v2 (by simp))]; exact hP.cst.two⟩, by rw [h3]; exact hP.ramN,
    by rw [hf _ (hm CellTablesProg.wN (by simp))]; exact hP.wN, by rw [hf _ (hm vS (by simp))]; exact hP.s,
    by rw [hf _ (hm vH1 (by simp))]; exact hP.h1, by rw [hf _ (hm vH0 (by simp))]; exact hP.h0,
    by rw [hf _ (hm vSH (by simp))]; exact hP.sh, by rw [hf _ (hm kB2 (by simp))]; exact hP.b2,
    by rw [hf _ (hm kD (by simp))]; exact hP.d, by rw [hf _ (hm kVW2 (by simp))]; exact hP.vw2,
    by rw [hf _ (hm kPAD (by simp))]; exact hP.pad, by rw [h5]; exact hP.kin, by rw [h4, h3]; exact hP.rcR⟩

theorem Pre.adv {C : Ctx} {r : CellReq B1 B2 cT} {a : DS VV MM} (hP : Pre C r a) (hv : Valid C (a.adv sQ)) :
    Pre C r (a.adv sQ) :=
  ⟨hv, ⟨hP.cst.z, hP.cst.one, hP.cst.two⟩, hP.ramN, hP.wN, hP.s, hP.h1, hP.h0, hP.sh, hP.b2, hP.d, hP.vw2, hP.pad,
    hP.kin,
    by simp only [DS.adv]; rw [Function.update_of_ne (by decide)]; exact hP.rcR⟩

theorem primeB_spec (RK : TabCallMachine B1 B2 cT PolyTab) (r : CellReq B1 B2 cT) (Wd Lk Bk wb : ℕ) (inp : List Bool)
    (a : DS VV MM) (part : Option Bool) (L : List ℕ) (k : ℕ) (hk : k < L.length) (hF : Fit RK r Wd Lk Bk wb)
    (hP : Pre (ctxK RK Wd inp Lk Bk) r a) (hpart : part ∈ parts r.c) (hL : ∀ q ∈ L, q ∈ r.p.primes)
    (hQ : a.ram sQ = L) (hQc : a.rc sQ = k) (hPC : a.env lPC = partCode part) (hE : a.env wE = r.p.e) :
    Hs (ctxK RK Wd inp Lk Bk) primeB a (L[k] ^ dOf r.c r.p * (bodyCost Lk Bk wb r + 4) + 7 * r.p.e +
        7 * dOf r.c r.p + 30) (fun e => Pre (ctxK RK Wd inp Lk Bk) r e ∧
      e.ram sREC = a.ram sREC ++ resRecs r.c r.p r.wt part L[k] ∧ e.rc sQ = k + 1 ∧ KeepQ a e primeBT) := by
  set C := ctxK RK Wd inp Lk Bk with hC
  set q := L[k] with hqd
  have hq : q ∈ r.p.primes := hL q (List.getElem_mem hk)
  have hWd : 4 ≤ C.Wd := by have := hF.wd; show 4 ≤ Wd; omega
  have hqe : 4 * q ^ r.p.e ≤ 2 ^ C.Wd := hF.qe q hq
  have hqD : 2 * q ^ dOf r.c r.p ≤ 2 ^ C.Wd := hF.qd q hq
  have hpos : 0 < 2 ^ C.Wd := Nat.two_pow_pos _
  have nb : ∀ y : Fin VV, bodyVarB y = false → ¬ BodyVar y := fun y h => not_bodyVar h
  unfold primeB
  apply Hx.hs
  refine Hs.then (PrefixProg.Hs.valid (hs_rdM C sQ lQ a (by rw [hQ, hQc]; exact hk)) hP.valid (by omega))
    (fun e1 ⟨he1, w1⟩ n1 hn1 => ?_)
  have e1q : e1.env lQ = q := by
    rw [he1]; simp [DS.adv, DS.set, hQ, hQc, List.getElem?_eq_getElem hk, hqd]
  have p1 : Pre C r e1 := by
    rw [he1] at w1 ⊢
    exact (hP.set lQ _ (by decide) (by decide) (by decide) (by
      have := w1.env_lt lQ; simpa [DS.adv] using this)).adv w1
  have o1 : ∀ y, y ≠ lQ → e1.env y = a.env y := fun y hy => by rw [he1]; simp [DS.adv, DS.set, Function.update_of_ne hy]
  refine Hs.then (PrefixProg.Hs.valid (hs_copy C lQE v1 e1 (by decide)) w1 (by omega)) (fun e2 ⟨he2, w2⟩ n2 hn2 => ?_)
  have p2 : Pre C r e2 := by rw [he2] at w2 ⊢; exact p1.set lQE _ (by decide) (by decide) (by decide) (w2.env_lt lQE |>.trans_eq' (by simp))
  have e2E : e2.env wE = r.p.e := by rw [he2, DS.set_env_ne _ _ (by decide), o1 wE (by decide)]; exact hE
  have e2Q : e2.env lQ = q := by rw [he2, DS.set_env_ne _ _ (by decide)]; exact e1q
  have e2U : e2.env lQE = 1 := by rw [he2, DS.set_env_self]; exact p1.cst.one
  have hlt : r.p.e < 2 ^ C.Wd := by rw [← e2E]; exact w2.env_lt wE
  refine Hs.then (PrefixProg.Hs.valid (powP_spec C lQE lQ lI2 wE lTmp2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) e2 r.p.e 1 q e2E e2U e2Q hlt (by omega)) w2 (by omega))
    (fun e3 ⟨⟨v3, s3, f3⟩, w3⟩ n3 hn3 => ?_)
  have p3 : Pre C r e3 := Pre.of_fr p2 w3 s3 f3 (by decide)
  refine Hs.then (PrefixProg.Hs.valid (hs_copy C lQD v1 e3 (by decide)) w3 (by omega)) (fun e4 ⟨he4, w4⟩ n4 hn4 => ?_)
  have p4 : Pre C r e4 := by rw [he4] at w4 ⊢; exact p3.set lQD _ (by decide) (by decide) (by decide) (w4.env_lt lQD |>.trans_eq' (by simp))
  have e4D : e4.env kD = dOf r.c r.p := p4.d
  have e4Q : e4.env lQ = q := by rw [he4, DS.set_env_ne _ _ (by decide), f3 lQ (by decide)]; exact e2Q
  have e4U : e4.env lQD = 1 := by rw [he4, DS.set_env_self]; exact p3.cst.one
  have hDlt : dOf r.c r.p < 2 ^ C.Wd := by rw [← e4D]; exact w4.env_lt kD
  refine Hs.then (PrefixProg.Hs.valid (powP_spec C lQD lQ lI2 kD lTmp2 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) e4 (dOf r.c r.p) 1 q e4D e4U e4Q hDlt (by omega))
    w4 (by omega)) (fun e5 ⟨⟨v5, s5, f5⟩, w5⟩ n5 hn5 => ?_)
  have p5 : Pre C r e5 := Pre.of_fr p4 w5 s5 f5 (by decide)
  have g5 : ∀ y, y ∉ [lQ, lQE, lQD, lI2, lTmp2] → e5.env y = a.env y := fun y hy => by
    rw [f5 y (fun h => hy (by simp at h ⊢; tauto)), he4, DS.set_env_ne _ _ (fun h => hy (by simp [h])),
      f3 y (fun h => hy (by simp at h ⊢; tauto)), he2, DS.set_env_ne _ _ (fun h => hy (by simp [h])),
      o1 y (fun h => hy (by simp [h]))]
  refine Hs.last (resT_spec RK r Wd Lk Bk wb inp e5 part q hF p5 hpart hq
    (by rw [g5 lPC (by decide)]; exact hPC)
    (by rw [f5 lQ (by decide), he4, DS.set_env_ne _ _ (by decide), f3 lQ (by decide)]; exact e2Q)
    (by rw [f5 lQE (by decide), he4, DS.set_env_ne _ _ (by decide), v3]; ring) (by rw [v5]; ring))
    (fun e6 ⟨p6, r6, k6⟩ n6 hn6 => ?_)
  have sh5 : e5.ram = e1.ram ∧ e5.rc = e1.rc ∧ e5.out = e1.out ∧ e5.ip = e1.ip := by
    simp only [DS.sh, Prod.mk.injEq] at s5 s3
    rw [he4] at s5; rw [he2] at s3
    simp only [DS.set] at s5 s3
    exact ⟨s5.2.2.1.trans s3.2.2.1, s5.2.2.2.1.trans s3.2.2.2.1, s5.2.1.trans s3.2.1, s5.1.trans s3.1⟩
  have e1ram : e1.ram = a.ram := by rw [he1]; rfl
  have e1rc : e1.rc = Function.update a.rc sQ (a.rc sQ + 1) := by rw [he1]; rfl
  refine ⟨⟨p6, by rw [r6, sh5.1, e1ram]; rfl, ?_, ?_⟩, ?_⟩
  · rw [k6.rc sQ (by decide) (by decide) (by decide), sh5.2.1, e1rc, hQc]; simp
  · refine ⟨fun m h1 h2 => by rw [k6.ram m h1 h2, sh5.1, e1ram], fun m h1 h2 h3 h4 => by
      rw [k6.rc m h1 h2 h3, sh5.2.1, e1rc, Function.update_of_ne h4], by rw [k6.out, sh5.2.2.1, he1]; rfl,
      by rw [k6.ip, sh5.2.2.2, he1]; rfl, fun y h1 h2 => ?_⟩
    rw [k6.env y h1 (fun h => h2 (by simp at h; subst h; decide)),
      g5 y (fun h => h2 (by simp at h; rcases h with h | h | h | h | h <;> subst h <;> decide))]
  · have hq0 : q ^ dOf r.c r.p * (bodyCost Lk Bk wb r + 4) + 4 ≥ n6 := hn6
    omega

end NearCubicGates.Close.CounterMachine.CellTablesProg
