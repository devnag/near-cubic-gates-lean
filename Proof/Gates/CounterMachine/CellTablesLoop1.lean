import Proof.Gates.CounterMachine.CellTablesBody9
import Proof.Gates.CounterMachine.CellTablesCst4

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader (sN)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW sREC sTMP convP Frame)

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

theorem Pre.of_post {C : Ctx} {r : CellReq B1 B2 cT} {a e : DS VV MM} {id : ReqId} (hP : Pre C r a)
    (hp : Post C r a e id) : Pre C r e := by
  have nb : ∀ y : Fin VV, bodyVarB y = false → ¬ BodyVar y := fun y h => not_bodyVar h
  exact ⟨hp.valid, hp.cst, by rw [hp.ram sN (by decide) (by decide)]; exact hP.ramN,
    by rw [hp.fr CellTablesProg.wN (nb CellTablesProg.wN (by decide))]; exact hP.wN, by rw [hp.fr vS (nb vS (by decide))]; exact hP.s,
    by rw [hp.fr vH1 (nb vH1 (by decide))]; exact hP.h1, by rw [hp.fr vH0 (nb vH0 (by decide))]; exact hP.h0,
    by rw [hp.fr vSH (nb vSH (by decide))]; exact hP.sh, by rw [hp.fr kB2 (nb kB2 (by decide))]; exact hP.b2,
    by rw [hp.fr kD (nb kD (by decide))]; exact hP.d, by rw [hp.fr kVW2 (nb kVW2 (by decide))]; exact hP.vw2,
    by rw [hp.fr kPAD (nb kPAD (by decide))]; exact hP.pad, hp.kin, hp.rcR⟩

theorem Pre.set {C : Ctx} {r : CellReq B1 B2 cT} {a : DS VV MM} (hP : Pre C r a) (y : Fin VV) (v : ℕ)
    (hy3 : 3 ≤ y.val) (hy2 : y ≠ CellTablesProg.wN ∧ y ≠ kB2 ∧ y ≠ kD ∧ y ≠ kVW2 ∧ y ≠ kPAD)
    (hy4 : y.val < 40 ∨ 47 ≤ y.val) (hv : v < 2 ^ C.Wd) : Pre C r (a.set y v) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hy2
  have ne : ∀ z : Fin VV, (z.val = 40 ∨ z.val = 41 ∨ z.val = 42 ∨ z.val = 43) → y ≠ z := by
    intro z hz e; subst e; omega
  exact ⟨PrefixProg.Valid.set' hP.valid y v hv, cst_set hP.cst y v hy3, hP.ramN,
    by rw [DS.set_env_ne (y := CellTablesProg.wN) _ _ (Ne.symm h1)]; exact hP.wN, by rw [DS.set_env_ne _ _ (Ne.symm (ne vS (by decide)))]; exact hP.s,
    by rw [DS.set_env_ne _ _ (Ne.symm (ne vH1 (by decide)))]; exact hP.h1,
    by rw [DS.set_env_ne _ _ (Ne.symm (ne vH0 (by decide)))]; exact hP.h0,
    by rw [DS.set_env_ne _ _ (Ne.symm (ne vSH (by decide)))]; exact hP.sh,
    by rw [DS.set_env_ne _ _ (Ne.symm h2)]; exact hP.b2, by rw [DS.set_env_ne _ _ (Ne.symm h3)]; exact hP.d,
    by rw [DS.set_env_ne _ _ (Ne.symm h4)]; exact hP.vw2, by rw [DS.set_env_ne _ _ (Ne.symm h5)]; exact hP.pad,
    hP.kin, hP.rcR⟩

/-- What a run of bodies keeps: the stores but `sREC`, `sTMP`; the cursors but those and `sN`'s; the output, the
input cursor; the protected variables but the loop counter `i`. -/
structure Keep (a e : DS VV MM) (T : List (Fin VV)) : Prop where
  ram : ∀ m, m ≠ sREC → m ≠ sTMP → e.ram m = a.ram m
  rc : ∀ m, m ≠ sREC → m ≠ sTMP → m ≠ sN → e.rc m = a.rc m
  out : e.out = a.out
  ip : e.ip = a.ip
  env : ∀ y, ¬ BodyVar y → y ∉ T → e.env y = a.env y

theorem Keep.refl (a : DS VV MM) (T : List (Fin VV)) : Keep a a T := ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl,
  fun _ _ _ => rfl⟩

theorem Keep.trans {a b d : DS VV MM} {T : List (Fin VV)} (h1 : Keep a b T) (h2 : Keep b d T) : Keep a d T :=
  ⟨fun m h h' => (h2.ram m h h').trans (h1.ram m h h'), fun m h h' h'' => (h2.rc m h h' h'').trans (h1.rc m h h' h''),
    h2.out.trans h1.out, h2.ip.trans h1.ip, fun y h h' => (h2.env y h h').trans (h1.env y h h')⟩

theorem Keep.of_post {C : Ctx} {r : CellReq B1 B2 cT} {a e : DS VV MM} {id : ReqId} (hp : Post C r a e id)
    (T : List (Fin VV)) : Keep a e T :=
  ⟨hp.ram, hp.rc, hp.out, hp.ip, fun y h _ => hp.fr y h⟩

theorem Keep.set (a : DS VV MM) (T : List (Fin VV)) (y : Fin VV) (v : ℕ) (hy : y ∈ T) : Keep a (a.set y v) T :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ => rfl, rfl, rfl, fun _ _ hz => DS.set_env_ne _ _ (fun e => hz (e ▸ hy))⟩

theorem Keep.weaken {a e : DS VV MM} {T T' : List (Fin VV)} (h : Keep a e T) (hT : ∀ y ∈ T, y ∈ T') : Keep a e T' :=
  ⟨h.ram, h.rc, h.out, h.ip, fun y h1 h2 => h.env y h1 (fun hm => h2 (hT y hm))⟩

/-! ## The loop over the residue counter -/

theorem resT_spec (RK : TabCallMachine B1 B2 cT PolyTab) (r : CellReq B1 B2 cT) (Wd Lk Bk wb : ℕ) (inp : List Bool)
    (a : DS VV MM) (part : Option Bool) (q : ℕ) (hF : Fit RK r Wd Lk Bk wb) (hP : Pre (ctxK RK Wd inp Lk Bk) r a)
    (hpart : part ∈ parts r.c) (hq : q ∈ r.p.primes) (hPC : a.env lPC = partCode part) (hQ : a.env lQ = q)
    (hQE : a.env lQE = q ^ r.p.e) (hQD : a.env lQD = q ^ dOf r.c r.p) :
    Hs (ctxK RK Wd inp Lk Bk) (forS lT lQD resB) a (q ^ dOf r.c r.p * (bodyCost Lk Bk wb r + 4) + 4) (fun e =>
      Pre (ctxK RK Wd inp Lk Bk) r e ∧
      e.ram sREC = a.ram sREC ++ ((List.range (q ^ dOf r.c r.p)).map (resId r.c r.p part q)).flatMap
        (recsOf r.c r.p r.wt) ∧ Keep a e [lT]) := by
  set C := ctxK RK Wd inp Lk Bk with hC
  have hND : q ^ dOf r.c r.p < 2 ^ C.Wd := by rw [← hQD]; exact hP.valid.env_lt lQD
  let I : ℕ → DS VV MM → Prop := fun k d => Pre C r d ∧
    d.ram sREC = a.ram sREC ++ ((List.range k).map (resId r.c r.p part q)).flatMap (recsOf r.c r.p r.wt) ∧ Keep a d [lT]
  have nb : ∀ y : Fin VV, bodyVarB y = false → ¬ BodyVar y := fun y h => not_bodyVar h
  refine Hs.mono (PrefixProg.forS_specV (C := C) lT lQD (by decide) resB a _ hND I (bodyCost Lk Bk wb r)
    (fun k d v hv ⟨i1, i2, i3⟩ => ⟨i1.set lT v (by decide) (by decide) (by decide) (by omega), i2, i3.trans (Keep.set _ _ _ _ (by simp))⟩)
    ⟨hP, by simp, Keep.refl _ _⟩ hQD ?_) le_rfl (fun e ⟨h, _, _⟩ => h)
  intro k hk d ⟨i1, i2, i3⟩ hdk hdm
  have gv : ∀ y : Fin VV, bodyVarB y = false → y ≠ lT → d.env y = a.env y := fun y h1 h2 =>
    i3.env y (nb y h1) (by simpa using h2)
  refine Hs.mono (resB_spec RK r Wd Lk Bk wb inp d part q k hF i1 hpart hq hk
    (by rw [gv lPC (by decide) (by decide)]; exact hPC) (by rw [gv lQ (by decide) (by decide)]; exact hQ)
    (by rw [gv lQE (by decide) (by decide)]; exact hQE) (by rw [gv lQD (by decide) (by decide)]; exact hQD) hdk)
    le_rfl ?_
  intro e hp
  refine ⟨⟨i1.of_post hp, ?_, i3.trans (Keep.of_post hp _)⟩, by rw [hp.fr lT (nb lT (by decide))]; exact hdk,
    by rw [hp.fr lQD (nb lQD (by decide))]; exact hdm⟩
  rw [hp.ramR, i2, List.range_succ, List.map_append, List.flatMap_append, List.append_assoc]
  simp

end NearCubicGates.Close.CounterMachine.CellTablesProg
