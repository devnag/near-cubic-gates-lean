import Proof.Gates.CounterMachine.CellTablesLoop2

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader (sN gKd)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW sREC sTMP convP Frame)

def resPart (pc : ℕ) : St VV MM := .seq (PrefixLoader.setK lPC pc) (.seq (.op (.rwM sQ)) (forS lIQ wNP primeB))

def resL : St VV MM := .ite (.eq gKd v2) (.seq (resPart 1) (resPart 2)) (resPart 0)

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

/-- The per-prime cost bound. -/
def primeCost (Lk Bk wb : ℕ) (r : CellReq B1 B2 cT) : ℕ :=
  r.p.P ^ dOf r.c r.p * (bodyCost Lk Bk wb r + 4) + 7 * r.p.e + 7 * dOf r.c r.p + 30

def partCost (Lk Bk wb : ℕ) (r : CellReq B1 B2 cT) : ℕ :=
  (r.p.primes.sort (· ≤ ·)).length * (primeCost Lk Bk wb r + 4) + (r.p.primes.sort (· ≤ ·)).length + 20

theorem resPart_spec (RK : TabCallMachine B1 B2 cT PolyTab) (r : CellReq B1 B2 cT) (Wd Lk Bk wb : ℕ) (inp : List Bool)
    (a : DS VV MM) (part : Option Bool) (hF : Fit RK r Wd Lk Bk wb) (hP : Pre (ctxK RK Wd inp Lk Bk) r a)
    (hpart : part ∈ parts r.c) (hQ : a.ram sQ = r.p.primes.sort (· ≤ ·))
    (hQc : a.rc sQ ≤ (r.p.primes.sort (· ≤ ·)).length)
    (hNP : a.env wNP = (r.p.primes.sort (· ≤ ·)).length) (hE : a.env wE = r.p.e) :
    Hs (ctxK RK Wd inp Lk Bk) (resPart (partCode part)) a (partCost Lk Bk wb r) (fun e =>
      Pre (ctxK RK Wd inp Lk Bk) r e ∧
      e.ram sREC = a.ram sREC ++ (r.p.primes.sort (· ≤ ·)).flatMap (resRecs r.c r.p r.wt part) ∧
      e.rc sQ = (r.p.primes.sort (· ≤ ·)).length ∧ KeepQ a e (lPC :: primeT)) := by
  set C := ctxK RK Wd inp Lk Bk with hC
  set L := r.p.primes.sort (· ≤ ·) with hLd
  have hL : ∀ q ∈ L, q ∈ r.p.primes := fun q hq => (Finset.mem_sort _).mp hq
  have hWd : 4 ≤ C.Wd := by have := hF.wd; show 4 ≤ Wd; omega
  have hpc : partCode part ≤ 2 := by cases part with | none => decide | some b => cases b <;> decide
  have hpcW : partCode part < 2 ^ C.Wd := lt_of_le_of_lt hpc (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right
    (by norm_num) hWd))
  have hLW : L.length < 2 ^ C.Wd := by rw [← hNP]; exact hP.valid.env_lt wNP
  unfold resPart
  apply Hx.hs
  refine Hs.then (PrefixProg.Hs.valid (PrefixLoader.setK_spec (C := C) lPC (by decide) (partCode part) a hpcW) hP.valid (by omega))
    (fun e1 ⟨⟨v1', s1, f1⟩, w1⟩ n1 hn1 => ?_)
  have p1 : Pre C r e1 := Pre.of_fr hP w1 s1 f1 (by decide)
  refine Hs.then (PrefixProg.Hs.valid (hs_rwM C sQ e1) w1 (by omega)) (fun e2 ⟨he2, w2⟩ n2 hn2 => ?_)
  have p2 : Pre C r e2 := by
    rw [he2] at w2 ⊢
    exact ⟨w2, ⟨p1.cst.z, p1.cst.one, p1.cst.two⟩, p1.ramN, p1.wN, p1.s, p1.h1, p1.h0, p1.sh, p1.b2, p1.d, p1.vw2,
      p1.pad, p1.kin, by simp only [DS.rew]; rw [Function.update_of_ne (by decide)]; exact p1.rcR⟩
  have sh1 : e1.ram = a.ram ∧ e1.rc = a.rc ∧ e1.out = a.out ∧ e1.ip = a.ip := by
    simp only [DS.sh, Prod.mk.injEq] at s1; exact ⟨s1.2.2.1, s1.2.2.2.1, s1.2.1, s1.1⟩
  have e2ram : e2.ram = a.ram := by rw [he2]; exact sh1.1
  have e2rc : e2.rc = Function.update a.rc sQ 0 := by rw [he2]; simp only [DS.rew]; rw [sh1.2.1]
  have g2 : ∀ y, y ∉ [lPC, vJ] → e2.env y = a.env y := fun y hy => by rw [he2]; exact f1 y hy
  let I : ℕ → DS VV MM → Prop := fun k d => Pre C r d ∧ d.rc sQ = k ∧
    d.ram sREC = a.ram sREC ++ (L.take k).flatMap (resRecs r.c r.p r.wt part) ∧ KeepQ e2 d primeT
  have hl := PrefixProg.forS_specV (C := C) lIQ wNP (by decide) primeB e2 L.length hLW I (primeCost Lk Bk wb r)
    (fun k d v hv ⟨i1, i2, i3, i4⟩ => ⟨i1.set lIQ v (by decide) (by decide) (by decide) (by omega), i2, i3,
      i4.trans ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, rfl, rfl, fun z _ hz => DS.set_env_ne _ _
        (fun e => hz (by rw [e]; decide))⟩⟩)
    ⟨p2, by rw [e2rc]; simp, by simp [e2ram], KeepQ.refl _ _⟩ (by rw [g2 wNP (by decide)]; exact hNP) ?_
  · refine Hs.last hl (fun e3 ⟨⟨p3, r3, m3, k3⟩, _, _⟩ n3 hn3 => ?_)
    refine ⟨⟨p3, by rw [m3, List.take_of_length_le le_rfl], r3, ?_⟩, ?_⟩
    · refine ⟨fun m h1 h2 => by rw [k3.ram m h1 h2, e2ram], fun m h1 h2 h3 h4 => by
        rw [k3.rc m h1 h2 h3 h4, e2rc, Function.update_of_ne h4], by rw [k3.out, he2]; exact sh1.2.2.1,
        by rw [k3.ip, he2]; exact sh1.2.2.2, fun y h1 h2 => ?_⟩
      rw [k3.env y h1 (fun h => h2 (List.mem_cons_of_mem _ h)), g2 y (fun h => ?_)]
      simp at h; rcases h with h | h
      · exact h2 (by simp [h])
      · exact h1 (by rw [h]; exact bodyVar_of (by decide))
    · have : e1.rc sQ = a.rc sQ := by rw [sh1.2.1]
      unfold partCost; rw [← hLd]; omega
  · intro k hk d ⟨i1, i2, i3, i4⟩ hdk hdm
    refine Hs.mono (primeB_spec RK r Wd Lk Bk wb inp d part L k hk hF i1 hpart hL
      (by rw [i4.ram sQ (by decide) (by decide), e2ram]; exact hQ) i2
      (by rw [i4.env lPC (not_bodyVar (by decide)) (by decide), he2]; exact v1')
      (by rw [i4.env wE (not_bodyVar (by decide)) (by decide), g2 wE (by decide)]; exact hE)) ?_ ?_
    · have hq : L[k] ≤ r.p.P := (prime_le_P r (hL _ (List.getElem_mem hk))).1
      have : L[k] ^ dOf r.c r.p ≤ r.p.P ^ dOf r.c r.p := Nat.pow_le_pow_left hq _
      unfold primeCost
      have := Nat.mul_le_mul_right (bodyCost Lk Bk wb r + 4) this
      omega
    · rintro e ⟨p4, r4, c4, k4⟩
      refine ⟨⟨p4, c4, ?_, i4.trans (KeepQ.trans k4 (KeepQ.refl _ _) |> fun h =>
        ⟨h.ram, h.rc, h.out, h.ip, fun y h1 h2 => h.env y h1 (fun hm => h2 (List.mem_cons_of_mem _ hm))⟩)⟩, ?_, ?_⟩
      · rw [r4, i3, List.take_add_one, List.flatMap_append, List.append_assoc]
        simp [List.getElem?_eq_getElem hk]
      · rw [k4.env lIQ (not_bodyVar (by decide)) (by decide)]; exact hdk
      · rw [k4.env wNP (not_bodyVar (by decide)) (by decide)]; exact hdm

end NearCubicGates.Close.CounterMachine.CellTablesProg
