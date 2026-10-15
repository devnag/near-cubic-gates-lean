import Proof.Gates.CellsGatherK.Key5
import Proof.Gates.CellsGather.Final

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Cells.QueryKey

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

/-- **The key program.** -/
def keyP : St VV MM :=
  .seq hdrP (.seq setP (.seq (powK kW kN) (.seq kLoop (.seq (powK kQ gRC) sLoop))))

/-- **The key cost** (per query). -/
def keyCost (_C : Ctx) (c : Call) (_p : Params) (_Big : ℕ) : ℕ := 400 * (c.n + 2) ^ 2

theorem keyP_class : KeyClass keyCost :=
  ⟨400, 2, fun C c p Big => by
    unfold keyCost
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)⟩

theorem pw2 {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

/-- **The key program meets `KeyGoal`.** -/
theorem keyP_spec : KeyGoal keyP keyCost := by
  intro C cT c p wt y a Big part q t s hs hw hadm hbig hwd hpart hq ht hsl K
  obtain ⟨w, hw'⟩ := hw
  obtain ⟨B1, B2, hadm'⟩ := hadm
  -- numbers
  set kb := keyBits p with hkbdef
  set nD := nDig c p with hnD
  set rc := roleCount c.kind with hrcdef
  have hqmem : q ∈ p.primes := by simpa using hq
  have hq2 : 2 ≤ q := (primes_prime hs q hqmem).two_le
  have hqP : q ≤ p.P := primes_le hs q hqmem
  have hPkb : p.P + p.J + 3 < 2 ^ kb := Nat.lt_size_self _
  have hqkb : q < 2 ^ kb := by omega
  have hE1 : 1 ≤ p.hE := hE_pos c p hs
  have hwq : wWin p ≤ q := by have := digit_width hs q hqmem; unfold wWin; omega
  have hw1 : 1 ≤ wWin p := by unfold wWin; omega
  have hrc1 : 1 ≤ rc := roleCount_pos c.kind
  have hrc2 : rc ≤ 2 := roleCount_le_two c
  have hJn : p.J ≤ c.n + 1 := (J_le_Jmax c p hs).trans (Jmax_le c p hadm' hs)
  have hnDn : nD ≤ 2 * (c.n + 1) := by
    rw [hnD]; unfold nDig; exact Nat.mul_le_mul hrc2 hJn
  have hkL : keyLen c p = 3 + nD + rc := by rw [hnD, hrcdef]; unfold keyLen nDig; ring
  have hWd := GatherPhase.widths C c p wt Big hwd
  have hVW1 : 1 ≤ valueWidth c p := by unfold valueWidth; omega
  have hkW : keyW c p = kb * (3 + nD + rc) := by unfold keyW; rw [hkL]
  have hkWd : kb * (3 + nD + rc) + 4 ≤ C.Wd := by rw [← hkW]; omega
  have hpw : ∀ e, e ≤ 3 + nD + rc → 2 ^ (kb * e) ≤ 2 ^ (kb * (3 + nD + rc)) := fun e he =>
    pw2 (Nat.mul_le_mul_left _ he)
  have hKWd : 16 * 2 ^ (kb * (3 + nD + rc)) ≤ 2 ^ C.Wd := by
    rw [show 16 = 2 ^ 4 by norm_num, ← pow_add]; exact pw2 (by omega)
  have hkb1 : 1 ≤ kb := by
    rw [hkbdef]; unfold keyBits; exact Nat.size_pos.mpr (by omega)
  have hnDlt : nD < 2 ^ (kb * (3 + nD + rc)) := lt_of_lt_of_le Nat.lt_two_pow_self
    (pw2 (le_trans (by omega) (Nat.le_mul_of_pos_left _ hkb1)))
  have hpow : ∀ B e, B < 2 ^ kb → e ≤ 3 + nD + rc → B ^ e ≤ 2 ^ (kb * (3 + nD + rc)) := fun B e hB he =>
    (Nat.pow_le_pow_left hB.le e).trans (by rw [← pow_mul]; exact hpw e he)
  -- the fields
  have hκ : ∀ z ∈ kapL c p wt y t q, z < q := fun z hz =>
    vecs_lt q _ _ (GatherPhase.kmod_mem c p wt y _ q (by omega)) z hz
  have hσmem : sigL c q s ∈ vecs q rc := by
    rw [vecs_eq_vecsM, vecsM_eq, List.mem_map]
    exact ⟨s, List.mem_range.mpr (by rw [prod_replicate]; exact hsl), rfl⟩
  have hσ : ∀ z ∈ sigL c q s, z < q := fun z hz => vecs_lt q _ _ hσmem z hz
  have hpc : partCode part ≤ 2 := by unfold partCode; split <;> omega
  have hH : ∀ z ∈ [0, partCode part, q], z < 2 ^ kb := by
    intro z hz; simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl <;> omega
  -- 1. header
  have hc : Cst a := by exact K.cst
  obtain ⟨b1, n1, e1, hn1, h1K, f1, m1⟩ := hdrP_spec (C := C) a hc kb (partCode part) q K.KB K.pc K.q hH
    ((hpw 3 (by omega)).trans (by omega))
  have F1 : KF a b1 := by exact KF.of_same f1 m1 (by unfold keyScratch; decide) K.rcE
  -- 2. window, digits
  obtain ⟨b2, n2, e2, hn2, h2W, h2N, f2, m2⟩ := setP_spec (C := C) b1 (F1.cst hc) p.hE p.J rc
    (by rw [f1.ev (by decide), K.hE]) (by rw [f1.ev (by decide), K.J]) (by rw [f1.ev (by decide), K.rc]) hE1
    (by
      have : rc * p.J = nD := by rw [hnD, hrcdef]
      rw [this]
      have : p.hE < 2 ^ kb := by have := hs.hE_eq; omega
      have : 2 ^ kb ≤ 2 ^ (kb * (3 + nD + rc)) := by
        have := hpw 1 (by omega); rwa [mul_one] at this
      omega)
  have F2 : KF b1 b2 := by exact KF.of_same f2 m2 (by unfold keyScratch; decide) F1.rcE
  have hnD2 : b2.env kN = nD := by rw [h2N, hnD, hrcdef]
  -- 3. w^nD
  have hwlt : wWin p < 2 ^ kb := by have := hs.hE_eq; unfold wWin; omega
  obtain ⟨b3, n3, e3, hn3, h3P, f3, m3⟩ := powK_spec (C := C) kW kN (by decide) (by decide) b2 (F2.cst (F1.cst hc))
    (wWin p) nD (by rw [h2W]) hnD2 hw1
    (lt_of_le_of_lt (hpow _ _ hwlt (by omega)) (by omega)) (by omega)
  have F3 : KF b2 b3 := by exact KF.of_same f3 m3 (by unfold keyScratch; decide) F2.rcE
  have F13 : KF a b3 := by exact (F1.trans F2).trans F3
  -- 4. the digit fields
  have D : KD (C := C) c p wt y kb t q [0, partCode part, q] b3 := by
    refine ⟨by rw [f3.ev (by decide), h2W], by rw [f3.ev (by decide), hnD2], ?_, ?_, ?_, ?_, ?_,
      F3.rcE, by omega, hw1, hwq, ?_, ?_, ?_, ?_⟩
    · rw [F13.env kT (by unfold keyScratch; decide)]; exact K.t
    · rw [F13.env kQ (by unfold keyScratch; decide)]; exact K.q
    · rw [F13.env vHE (by unfold keyScratch; decide)]; exact K.hE
    · rw [F13.env vKB (by unfold keyScratch; decide)]; exact K.KB
    · rw [F13.ram]; exact K.ctrs
    · have := hpow _ _ hwlt (show nD ≤ 3 + nD + rc by omega); rw [← hnD]; omega
    · simp only [List.length_cons, List.length_nil]
      exact (hpw _ (by omega)).trans (by omega)
    · intro z hz
      rcases List.mem_append.mp hz with h | h
      · exact hH z h
      · exact lt_trans (hκ z h) hqkb
    · have : q ≤ 2 ^ (kb * (3 + nD + rc)) := by
        have := hpw 1 (by omega); rw [mul_one] at this; omega
      omega
  obtain ⟨b4, n4, e4, hn4, h4K, G4⟩ := kLoop_spec D (by rw [f3.ev (by decide), f2.ev (by decide)]; exact h1K)
    (by rw [h3P])
  have F4 : KF b3 b4 := by exact G4.toKF kT_scratch
  have F14 : KF a b4 := by exact F13.trans F4
  -- 5. q^rc
  have hrc4 : b4.env gRC = rc := by rw [F14.env gRC (by unfold keyScratch; decide)]; exact K.rc
  have hq4 : b4.env kQ = q := by rw [F14.env kQ (by unfold keyScratch; decide)]; exact K.q
  obtain ⟨b5, n5, e5, hn5, h5P, f5, m5⟩ := powK_spec (C := C) kQ gRC (by decide) (by decide) b4
    (F14.cst hc) q rc hq4 hrc4 (by omega) (lt_of_le_of_lt (hpow _ _ hqkb (by omega)) (by omega)) (by omega)
  have F5 : KF b4 b5 := by exact KF.of_same f5 m5 (by unfold keyScratch; decide) F4.rcE
  have F15 : KF a b5 := by exact F14.trans F5
  -- 6. the residue fields
  have SDf : SD (C := C) rc kb q s ([0, partCode part, q] ++ kapL c p wt y t q) b5 := by
    refine ⟨by rw [F15.env kQ (by unfold keyScratch; decide)]; exact K.q,
      by rw [F15.env kS (by unfold keyScratch; decide)]; exact K.s,
      by rw [F15.env gRC (by unfold keyScratch; decide)]; exact K.rc,
      by rw [F15.env vKB (by unfold keyScratch; decide)]; exact K.KB, F5.rcE, by omega, ?_, ?_, ?_, by omega⟩
    · have := hpow _ _ hqkb (show rc ≤ 3 + nD + rc by omega); omega
    · simp only [List.length_append, List.length_cons, List.length_nil, kapL_length]
      rw [← hnD]; exact (hpw _ (by omega)).trans (by omega)
    · intro z hz
      rcases List.mem_append.mp hz with h | h
      · rcases List.mem_append.mp h with h' | h'
        · exact hH z h'
        · exact lt_trans (hκ z h') hqkb
      · exact lt_trans (hσ z h) hqkb
  obtain ⟨b6, n6, e6, hn6, h6K, G6⟩ := sLoop_spec SDf
    (by rw [f5.ev (by decide)]; exact h4K) h5P
  have F6 : KF b5 b6 := G6.toKF (by unfold sT_ keyScratch; decide)
  have F16 : KF a b6 := F15.trans F6
  refine ⟨b6, n1 + (n2 + (n3 + (n4 + (n5 + n6 + 1) + 1) + 1) + 1) + 1,
    Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 (Ex.seq e5 e6)))), ?_, ?_, F16.ram, F16.rc, F16.rcE, F16.ip,
    F16.out, F16.kin, F16.kout, F16.kc, F16.env⟩
  · unfold keyCost
    rw [← hnD] at hn4
    have hA : nD * (24 * nD + 89) ≤ 2 * (c.n + 1) * (48 * (c.n + 1) + 89) := Nat.mul_le_mul hnDn (by omega)
    have hB : 2 * (c.n + 1) * (48 * (c.n + 1) + 89) = 96 * ((c.n + 1) * (c.n + 1)) + 178 * (c.n + 1) := by ring
    have hX : (c.n + 2) ^ 2 = (c.n + 1) * (c.n + 1) + 2 * (c.n + 1) + 1 := by ring
    rw [hX]
    omega
  · rw [h6K, qKey_eq, List.append_assoc, List.append_assoc]; rfl

end NearCubicGates.Close.Cells.QueryKey
