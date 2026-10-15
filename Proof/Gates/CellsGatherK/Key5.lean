import Proof.Gates.CellsGatherK.Key4

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.QueryKey

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

def sBody : St VV MM := .seq (digP kQ kS) (accP kD)
def sLoop : St VV MM := forS kI gRC sBody

def sT_ : List (Fin VV) := [kKey, kTmp, kP, kD, t6, kI]

/-- The fixed data of the residue loop. -/
structure SD (rc kb q s : ℕ) (H : List ℕ) (a0 : DS VV MM) : Prop where
  Q : a0.env kQ = q
  S : a0.env kS = s
  RC : a0.env gRC = rc
  KB : a0.env vKB = 2 ^ kb
  rcE : a0.rc sE ≤ (a0.ram sE).length
  q1 : 1 ≤ q
  pw : 2 * q ^ rc ≤ 2 ^ C.Wd
  fit : 2 ^ (kb * (H.length + rc)) ≤ 2 ^ C.Wd
  lt : ∀ z ∈ H ++ digitsM (List.replicate rc q) s, z < 2 ^ kb
  rcW : rc < 2 ^ C.Wd

def SI (rc kb q s : ℕ) (H : List ℕ) (a0 : DS VV MM) (r : ℕ) (b : DS VV MM) : Prop :=
  b.env kKey = rk kb (H ++ (digitsM (List.replicate rc q) s).take r) ∧ b.env kP = q ^ (rc - r) ∧ KG sT_ a0 b

theorem sLoop_spec {rc kb q s : ℕ} {H : List ℕ} {a0 : DS VV MM} (D : SD (C := C) rc kb q s H a0)
    (hK : a0.env kKey = rk kb H) (hP : a0.env kP = q ^ rc) :
    Hs C sLoop a0 (rc * 17 + 4) (fun b => b.env kKey = rk kb (H ++ digitsM (List.replicate rc q) s) ∧
      KG sT_ a0 b) := by
  have hlen : (digitsM (List.replicate rc q) s).length = rc := by rw [digitsM_length, List.length_replicate]
  refine Hs.mono (forS_spec' (C := C) kI gRC (by decide) sBody a0 rc D.rcW (SI rc kb q s H a0) 13
    (fun k b v ⟨h1, h2, h3⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact h1,
      by rw [DS.set_env_ne _ _ (by decide)]; exact h2, h3.set (by decide) v⟩)
    ⟨by rw [hK, List.take_zero, List.append_nil], by rw [hP, Nat.sub_zero], KG.of_same (Fr.refl a0 _) (Same.refl a0)
      D.rcE⟩ D.RC ?_) (by omega) ?_
  · intro r hr b ⟨hK', hP', hG⟩ hbr hbN
    have ev : ∀ x, x ∉ sT_ → b.env x = a0.env x := fun x hx => hG.fr x hx
    have hm : rc - r = (rc - 1 - r) + 1 := by omega
    have hpw : q ^ (rc - r) ≤ q ^ rc := Nat.pow_le_pow_right D.q1 (by omega)
    obtain ⟨s1, n1, e1, hn1, r1P, r1D, f1, m1⟩ := digP_spec (C := C) kQ kS (by decide) (by decide) b q s
      (rc - 1 - r) (by rw [ev kQ (by decide), D.Q]) (by rw [ev kS (by decide), D.S]) (by rw [hP', hm]) D.q1
      (by rw [← hm]; have := D.pw; omega)
    have hsig : (digitsM (List.replicate rc q) s).getD r 0 = s / q ^ (rc - 1 - r) % q :=
      digitsM_rep_getD q rc s r hr
    have htk := take_snoc_getD (digitsM (List.replicate rc q) s) r (by rw [hlen]; exact hr)
    have hK1 : s1.env kKey = rk kb (H ++ (digitsM (List.replicate rc q) s).take r) := by
      rw [f1.ev (by decide), hK']
    obtain ⟨s2, n2, e2, hn2, r2, f2, m2⟩ := accP_spec (C := C) kD (by decide) (by decide) s1 (2 ^ kb)
      (by rw [f1.ev (by decide), ev vKB (by decide), D.KB])
      (by
        rw [hK1, r1D, ← hsig]
        refine acc_fit kb C.Wd _ _ (fun z hz => D.lt z ?_) ((Nat.pow_le_pow_right (by norm_num) ?_).trans D.fit)
        · rcases List.mem_append.mp hz with h | h
          · rcases List.mem_append.mp h with h' | h'
            · exact List.mem_append_left _ h'
            · exact List.mem_append_right _ (List.mem_of_mem_take h')
          · rw [List.mem_singleton] at h
            rw [h, List.getD_eq_getElem _ _ (by rw [hlen]; exact hr)]
            exact List.mem_append_right _ (List.getElem_mem _)
        · simp only [List.length_append, List.length_take, List.length_singleton, hlen]
          apply Nat.mul_le_mul_left; omega)
    refine ⟨s2, n1 + n2 + 1, Ex.seq e1 e2, by omega, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rw [r2, hK1, r1D, ← hsig, htk, ← List.append_assoc, rk_snoc]
    · rw [f2.ev (by decide), r1P]; congr 1; omega
    · exact (hG.trans (KG.of_same (f1.weaken (by decide)) m1 hG.rcE)).trans
        (KG.of_same (f2.weaken (by decide)) m2 (by rw [m1.rc, m1.ram]; exact hG.rcE))
    · rw [f2.ev (by decide), f1.ev (by decide), hbr]
    · rw [f2.ev (by decide), f1.ev (by decide), hbN]
  · rintro b ⟨⟨h1, -, h3⟩, -, -⟩
    refine ⟨?_, h3⟩
    rw [h1, List.take_of_length_le (by rw [hlen])]

end NearCubicGates.Close.Cells.QueryKey
