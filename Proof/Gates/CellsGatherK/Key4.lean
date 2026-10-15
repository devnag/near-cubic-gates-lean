import Proof.Gates.CellsGatherK.Key3
import Proof.Gates.CellsSys.Role

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.QueryKey

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

def kBody : St VV MM := .seq (digP kW kT) (.seq fetchP (.seq fieldP (accP kD)))
def kLoop : St VV MM := forS kI kN kBody

/-- The variables of the digit loop. -/
def kT_ : List (Fin VV) := [kKey, kTmp, kP, kD, t6, kX, kA, kB, c0, vJ, t7, t8, t9, kI]

theorem kT_scratch : ∀ x ∈ kT_, keyScratch x := by unfold keyScratch; decide

theorem take_snoc_getD (l : List ℕ) (k : ℕ) (hk : k < l.length) : l.take (k + 1) = l.take k ++ [l.getD k 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]; rfl

/-- The fixed data of the digit loop. -/
structure KD (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (kb t q : ℕ) (H : List ℕ) (a0 : DS VV MM) :
    Prop where
  W : a0.env kW = wWin p
  N : a0.env kN = nDig c p
  T : a0.env kT = t
  Q : a0.env kQ = q
  hE : a0.env vHE = p.hE
  KB : a0.env vKB = 2 ^ kb
  ctrs : a0.ram sE = ctrL c p wt y
  rcE : a0.rc sE ≤ (a0.ram sE).length
  q0 : 0 < q
  w1 : 1 ≤ wWin p
  wq : wWin p ≤ q
  pw : 2 * wWin p ^ nDig c p ≤ 2 ^ C.Wd
  fit : 2 ^ (kb * (H.length + nDig c p)) ≤ 2 ^ C.Wd
  lt : ∀ z ∈ H ++ QueryKey.kapL c p wt y t q, z < 2 ^ kb
  big : 8 * q + 2 * nDig c p + 4 < 2 ^ C.Wd

/-- The digit-loop invariant. -/
def KI (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (kb t q : ℕ) (H : List ℕ) (a0 : DS VV MM) (k : ℕ)
    (b : DS VV MM) : Prop :=
  b.env kKey = rk kb (H ++ (QueryKey.kapL c p wt y t q).take k) ∧ b.env kP = wWin p ^ (nDig c p - k) ∧ KG kT_ a0 b

theorem kBody_spec {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {kb t q : ℕ} {H : List ℕ}
    {a0 : DS VV MM} (D : KD (C := C) c p wt y kb t q H a0) (k : ℕ) (hk : k < nDig c p) (b : DS VV MM)
    (hI : KI c p wt y kb t q H a0 k b) (hbk : b.env kI = k) :
    Hs C kBody b (24 * nDig c p + 85) (fun d => KI c p wt y kb t q H a0 (k + 1) d ∧ d.env kI = k) := by
  obtain ⟨hK, hP, hG⟩ := hI
  have ev : ∀ x, x ∉ kT_ → b.env x = a0.env x := fun x hx => hG.fr x hx
  have hW : b.env kW = wWin p := by rw [ev kW (by decide), D.W]
  have hT : b.env kT = t := by rw [ev kT (by decide), D.T]
  have hm : nDig c p - k = (nDig c p - 1 - k) + 1 := by omega
  have hpw : wWin p ^ (nDig c p - k) ≤ wWin p ^ nDig c p := Nat.pow_le_pow_right D.w1 (by omega)
  obtain ⟨s1, n1, e1, hn1, r1P, r1D, f1, m1⟩ := digP_spec (C := C) kW kT (by decide) (by decide) b (wWin p) t
    (nDig c p - 1 - k) hW hT (by rw [hP, hm]) D.w1 (by rw [← hm]; have := D.pw; omega)
  have hlenE : (s1.ram sE).length = 2 * nDig c p := by
    rw [m1.ram, hG.ram, D.ctrs, SystemsPhase.ctrL_length]; unfold nDig; ring
  obtain ⟨s2, n2, e2, hn2, r2A, r2B, G2⟩ := fetchP_spec (C := C) s1 k (by rw [f1.ev (by decide), hbk])
    (by rw [hlenE]; omega) (by rw [m1.rc, m1.ram]; exact hG.rcE) (by have := D.big; omega)
  have hsE : s1.ram sE = ctrL c p wt y := by rw [m1.ram, hG.ram, D.ctrs]
  have hd2 : s2.env kD = t / wWin p ^ (nDig c p - 1 - k) % wWin p := by rw [G2.fr kD (by decide), r1D]
  have hq2 : s2.env kQ = q := by rw [G2.fr kQ (by decide), f1.ev (by decide), ev kQ (by decide), D.Q]
  have hh2 : s2.env vHE = p.hE := by rw [G2.fr vHE (by decide), f1.ev (by decide), ev vHE (by decide), D.hE]
  have hdw : t / wWin p ^ (nDig c p - 1 - k) % wWin p < wWin p := Nat.mod_lt _ (by have := D.w1; omega)
  obtain ⟨s3, n3, e3, hn3, r3, f3, m3⟩ := fieldP_spec (C := C) s2 _ _ _ _ q r2A r2B hh2 hd2 hq2 D.q0
    (by have := D.big; have := D.wq; omega)
  have hfield : s3.env kD = (QueryKey.kapL c p wt y t q).getD k 0 := by
    rw [r3, hsE, kfield_eq c p wt y t q D.q0 k hk]
  have hK3 : s3.env kKey = rk kb (H ++ (QueryKey.kapL c p wt y t q).take k) := by
    rw [f3.ev (by decide), G2.fr kKey (by decide), f1.ev (by decide), hK]
  have hKB3 : s3.env vKB = 2 ^ kb := by
    rw [f3.ev (by decide), G2.fr vKB (by decide), f1.ev (by decide), ev vKB (by decide), D.KB]
  have hlenK : (QueryKey.kapL c p wt y t q).length = nDig c p := kapL_length c p wt y t q
  have htk := take_snoc_getD (QueryKey.kapL c p wt y t q) k (by rw [hlenK]; exact hk)
  obtain ⟨s4, n4, e4, hn4, r4, f4, m4⟩ := accP_spec (C := C) kD (by decide) (by decide) s3 (2 ^ kb) hKB3
    (by
      rw [hK3, hfield]
      refine acc_fit kb C.Wd _ _ (fun z hz => D.lt z ?_) ((Nat.pow_le_pow_right (by norm_num) ?_).trans D.fit)
      · rcases List.mem_append.mp hz with h | h
        · rcases List.mem_append.mp h with h' | h'
          · exact List.mem_append_left _ h'
          · exact List.mem_append_right _ (List.mem_of_mem_take h')
        · rw [List.mem_singleton] at h
          rw [h, List.getD_eq_getElem _ _ (by rw [hlenK]; exact hk)]
          exact List.mem_append_right _ (List.getElem_mem _)
      · simp only [List.length_append, List.length_take, List.length_singleton, hlenK]
        apply Nat.mul_le_mul_left; omega)
  refine ⟨s4, n1 + (n2 + (n3 + n4 + 1) + 1) + 1, Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4)), ?_, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [m1.ram, hG.ram, D.ctrs] at hn2
    have : (ctrL c p wt y).length = 2 * nDig c p := by rw [← hsE]; exact hlenE
    rw [this] at hn2; omega
  · rw [r4, hK3, hfield, htk, ← List.append_assoc, rk_snoc]
  · rw [f4.ev (by decide), f3.ev (by decide), G2.fr kP (by decide), r1P]; congr 1; omega
  · have G1 : KG kT_ b s1 := KG.of_same (f1.weaken (by decide)) m1 hG.rcE
    have G3 : KG kT_ s2 s3 := KG.of_same (f3.weaken (by decide)) m3 G2.rcE
    have G4 : KG kT_ s3 s4 := KG.of_same (f4.weaken (by decide)) m4 G3.rcE
    exact ((hG.trans G1).trans (G2.weaken (by decide))).trans (G3.trans G4)
  · rw [f4.ev (by decide), f3.ev (by decide), G2.fr kI (by decide), f1.ev (by decide), hbk]

theorem kLoop_spec {c : Call} {p : Params} {wt : Wit c.n} {y : Cells wt.I} {kb t q : ℕ} {H : List ℕ}
    {a0 : DS VV MM} (D : KD (C := C) c p wt y kb t q H a0) (hK : a0.env kKey = rk kb H)
    (hP : a0.env kP = wWin p ^ nDig c p) :
    Hs C kLoop a0 (nDig c p * (24 * nDig c p + 89) + 4) (fun b =>
      b.env kKey = rk kb (H ++ QueryKey.kapL c p wt y t q) ∧ KG kT_ a0 b) := by
  have hNW : nDig c p < 2 ^ C.Wd := by have := D.big; omega
  refine Hs.mono (forS_spec' (C := C) kI kN (by decide) kBody a0 (nDig c p) hNW (KI c p wt y kb t q H a0)
    (24 * nDig c p + 85) (fun k b v ⟨h1, h2, h3⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact h1,
      by rw [DS.set_env_ne _ _ (by decide)]; exact h2, h3.set (by decide) v⟩)
    ⟨by rw [hK, List.take_zero, List.append_nil], by rw [hP, Nat.sub_zero], KG.of_same (Fr.refl a0 _) (Same.refl a0)
      D.rcE⟩ D.N ?_) (by ring_nf; omega) ?_
  · intro k hk b hI hbk hbN
    refine Hs.mono (kBody_spec D k hk b hI hbk) le_rfl (fun d ⟨hd, hdk⟩ => ⟨hd, hdk, ?_⟩)
    rw [hd.2.2.fr kN (by decide), D.N]
  · rintro b ⟨⟨h1, -, h3⟩, -, -⟩
    refine ⟨?_, h3⟩
    rw [h1, List.take_of_length_le (by rw [kapL_length])]

end NearCubicGates.Close.Cells.QueryKey
