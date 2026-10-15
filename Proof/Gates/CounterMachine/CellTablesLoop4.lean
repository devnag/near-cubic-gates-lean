import Proof.Gates.CounterMachine.CellTablesLoop3

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader (sN gKd gJ gRC)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW sREC sTMP convP Frame)

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

theorem resL_spec (RK : TabCallMachine B1 B2 cT PolyTab) (r : CellReq B1 B2 cT) (Wd Lk Bk wb : ℕ) (inp : List Bool)
    (a : DS VV MM) (hF : Fit RK r Wd Lk Bk wb) (hP : Pre (ctxK RK Wd inp Lk Bk) r a)
    (hQ : a.ram sQ = r.p.primes.sort (· ≤ ·)) (hQc : a.rc sQ ≤ (r.p.primes.sort (· ≤ ·)).length)
    (hNP : a.env wNP = (r.p.primes.sort (· ≤ ·)).length) (hE : a.env wE = r.p.e)
    (hK : a.env gKd = kindTag r.c.kind) :
    Hs (ctxK RK Wd inp Lk Bk) resL a (2 * partCost Lk Bk wb r + 3) (fun e =>
      Pre (ctxK RK Wd inp Lk Bk) r e ∧
      e.ram sREC = a.ram sREC ++ (parts r.c).flatMap (fun part => (r.p.primes.sort (· ≤ ·)).flatMap
        (resRecs r.c r.p r.wt part)) ∧ KeepQ a e (lPC :: primeT)) := by
  unfold resL
  by_cases hk : r.c.kind = .parity
  · have hp : parts r.c = [some false, some true] := by simp [parts, hk]
    refine Hs.iteT (show gKd ≠ v2 by decide) (by simp [Cnd.eval, hK, hk, hP.cst.two, kindTag]) ?_
    refine Hs.mono (Hs.seq (t1 := partCost Lk Bk wb r) (t2 := partCost Lk Bk wb r) (resPart_spec RK r Wd Lk Bk wb inp a (some false) hF hP (by simp [hp]) hQ hQc hNP hE)
      (fun e1 ⟨p1, r1, c1, k1⟩ => ?_)) (by omega) (fun _ h => h)
    refine Hs.mono (resPart_spec RK r Wd Lk Bk wb inp e1 (some true) hF p1 (by simp [hp])
      (by rw [k1.ram sQ (by decide) (by decide)]; exact hQ) (by rw [c1])
      (by rw [k1.env wNP (not_bodyVar (by decide)) (by decide)]; exact hNP)
      (by rw [k1.env wE (not_bodyVar (by decide)) (by decide)]; exact hE)) le_rfl ?_
    rintro e ⟨p2, r2, _, k2⟩
    refine ⟨p2, by rw [r2, r1, hp]; simp, k1.trans k2⟩
  · have hp : parts r.c = [none] := by simp [parts, hk]
    refine Hs.iteF (show gKd ≠ v2 by decide) (by
      simp only [Cnd.eval, hK, hP.cst.two, decide_eq_false_iff_not]
      cases h : r.c.kind <;> simp_all [kindTag]) ?_
    refine Hs.mono (resPart_spec RK r Wd Lk Bk wb inp a none hF hP (by simp [hp]) hQ hQc hNP hE) (by omega) ?_
    rintro e ⟨p1, r1, _, k1⟩
    exact ⟨p1, by rw [r1, hp]; simp, k1⟩

/-! ## Table (b) -/

def momR : St VV MM := .seq (forS lJ gJ (momB false)) (momB true)

def momL : St VV MM := forS lR gRC momR

/-- The moment requests of role `ro`. -/
def momIds (J ro : ℕ) : List ReqId := (List.range J).map (fun j => ReqId.digitMoment ro j) ++ [ReqId.phiMoment ro]

theorem momR_spec (RK : TabCallMachine B1 B2 cT PolyTab) (r : CellReq B1 B2 cT) (Wd Lk Bk wb : ℕ) (inp : List Bool)
    (a : DS VV MM) (ro : ℕ) (hro : ro < roleCount r.c.kind) (hF : Fit RK r Wd Lk Bk wb)
    (hP : Pre (ctxK RK Wd inp Lk Bk) r a) (hR : a.env lR = ro) (hJ : a.env gJ = r.p.J) :
    Hs (ctxK RK Wd inp Lk Bk) momR a (r.p.J * (bodyCost Lk Bk wb r + 4) + bodyCost Lk Bk wb r + 5) (fun e =>
      Pre (ctxK RK Wd inp Lk Bk) r e ∧
      e.ram sREC = a.ram sREC ++ (momIds r.p.J ro).flatMap (recsOf r.c r.p r.wt) ∧ Keep a e [lJ]) := by
  set C := ctxK RK Wd inp Lk Bk with hC
  have hJW : r.p.J < 2 ^ C.Wd := by rw [← hJ]; exact hP.valid.env_lt gJ
  let I : ℕ → DS VV MM → Prop := fun k d => Pre C r d ∧
    d.ram sREC = a.ram sREC ++ ((List.range k).map (fun j => ReqId.digitMoment ro j)).flatMap (recsOf r.c r.p r.wt) ∧
    Keep a d [lJ]
  have hl := PrefixProg.forS_specV (C := C) lJ gJ (by decide) (momB false) a r.p.J hJW I (bodyCost Lk Bk wb r)
    (fun k d v hv ⟨i1, i2, i3⟩ => ⟨i1.set lJ v (by decide) (by decide) (by decide) (by omega), i2,
      i3.trans (Keep.set _ _ _ _ (by simp))⟩) ⟨hP, by simp, Keep.refl _ _⟩ hJ ?_
  · unfold momR
    refine Hs.mono (Hs.seq (t2 := bodyCost Lk Bk wb r) hl (fun d ⟨⟨i1, i2, i3⟩, _, _⟩ => ?_)) (by omega) (fun _ h => h)
    refine Hs.mono (momB_spec RK r Wd Lk Bk wb inp d true ro (d.env lJ) hF i1 hro (by intro h; cases h)
      (by rw [i3.env lR (not_bodyVar (by decide)) (by decide)]; exact hR) rfl) le_rfl ?_
    intro e hp
    refine ⟨i1.of_post hp, ?_, i3.trans (Keep.of_post hp _)⟩
    rw [hp.ramR, i2]
    simp [momIds, List.flatMap_append]
  · intro k hk d ⟨i1, i2, i3⟩ hdk hdm
    refine Hs.mono (momB_spec RK r Wd Lk Bk wb inp d false ro k hF i1 hro (fun _ => hk)
      (by rw [i3.env lR (not_bodyVar (by decide)) (by decide)]; exact hR) hdk) le_rfl ?_
    intro e hp
    refine ⟨⟨i1.of_post hp, ?_, i3.trans (Keep.of_post hp _)⟩, by rw [hp.fr lJ (not_bodyVar (by decide))]; exact hdk,
      by rw [hp.fr gJ (not_bodyVar (by decide))]; exact hdm⟩
    rw [hp.ramR, i2, List.range_succ, List.map_append, List.flatMap_append, List.append_assoc]
    simp

end NearCubicGates.Close.CounterMachine.CellTablesProg
