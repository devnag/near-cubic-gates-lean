import Proof.Gates.CounterMachine.CellTablesCst2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Cells.PrefixLoader
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW)

theorem cst_set {a : DS VV MM} (h : Cst a) (x : Fin VV) (v : ℕ) (hx : 3 ≤ x.val) : Cst (a.set x v) :=
  ⟨by rw [DS.set_env_ne _ _ (fun e => by rw [← e] at hx; simp [vZ] at hx)]; exact h.z,
   by rw [DS.set_env_ne _ _ (fun e => by rw [← e] at hx; simp [v1] at hx)]; exact h.one,
   by rw [DS.set_env_ne _ _ (fun e => by rw [← e] at hx; simp [v2] at hx)]; exact h.two⟩

theorem cst_fr {a b : DS VV MM} {T : List (Fin VV)} (h : Cst a) (hf : Fr a b T) (hT : ∀ y ∈ T, 3 ≤ y.val) :
    Cst b :=
  ⟨by rw [hf vZ (fun h' => by have := hT _ h'; simp [vZ] at this)]; exact h.z,
   by rw [hf v1 (fun h' => by have := hT _ h'; simp [v1] at this)]; exact h.one,
   by rw [hf v2 (fun h' => by have := hT _ h'; simp [v2] at this)]; exact h.two⟩

/-! ## Piece 1: `s`, `2^⌈s/2⌉`, `2^⌊s/2⌋` -/

def cst1 : St VV MM :=
  .seq (.op (.copy vS gN)) (.seq (.op (.sub vS wK)) (.seq (.op (.copy cA vS)) (.seq (.op (.inc cA))
  (.seq (.op (.half cA)) (.seq (pow2P vH1 cI cA) (.seq (.op (.copy cA vS)) (.seq (.op (.half cA))
  (pow2P vH0 cI cA))))))))

theorem cst1_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (n k : ℕ) (hn : a.env gN = n) (hk : a.env wK = k)
    (hkn : k ≤ n) (hW : n + 2 ≤ C.Wd) :
    Hs C cst1 a (5 * n + 40) (fun e => e.env vS = n - k ∧ e.env vH1 = 2 ^ ((n - k + 1) / 2) ∧
      e.env vH0 = 2 ^ ((n - k) / 2) ∧ e.sh = a.sh ∧ Fr a e [vS, cA, vH1, cI, vH0]) := by
  have hnW : n + 1 < 2 ^ C.Wd := lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self).le
  apply Hx.hs
  refine Hs.then (hs_copy C vS gN a (by decide)) (fun b1 hb1 n1 hn1 => ?_); subst hb1
  refine Hs.then (hs_sub C vS wK _ (by decide) (by vsimp [hn, hk]; omega)) (fun b2 hb2 n2 hn2 => ?_); subst hb2
  refine Hs.then (hs_copy C cA vS _ (by decide)) (fun b3 hb3 n3 hn3 => ?_); subst hb3
  refine Hs.then (hs_inc C cA _ (by vsimp [hn, hk]; omega)) (fun b4 hb4 n4 hn4 => ?_); subst hb4
  refine Hs.then (hs_half C cA _) (fun b5 hb5 n5 hn5 => ?_); subst hb5
  refine Hs.then (pow2P_spec C vH1 cI cA (by decide) (by decide) (by decide) (by decide) _
    (cst_set (cst_set (cst_set (cst_set (cst_set hc _ _ (by decide)) _ _ (by decide)) _ _ (by decide)) _ _ (by decide))
      _ _ (by decide)) ((n - k + 1) / 2) (by vsimp [hn, hk]) (by omega)) (fun b6 ⟨v6, s6, f6⟩ n6 hn6 => ?_)
  have b6c : Cst b6 := cst_fr (cst_set (cst_set (cst_set (cst_set (cst_set hc _ _ (by decide)) _ _ (by decide)) _ _
    (by decide)) _ _ (by decide)) _ _ (by decide)) f6 (by decide)
  have b6S : b6.env vS = n - k := by rw [f6 vS (by decide)]; vsimp [hn, hk]
  refine Hs.then (hs_copy C cA vS b6 (by decide)) (fun b7 hb7 n7 hn7 => ?_); subst hb7
  refine Hs.then (hs_half C cA _) (fun b8 hb8 n8 hn8 => ?_); subst hb8
  refine Hs.last (pow2P_spec C vH0 cI cA (by decide) (by decide) (by decide) (by decide) _
    (cst_set (cst_set b6c _ _ (by decide)) _ _ (by decide)) ((n - k) / 2) (by vsimp [b6S]) (by omega))
    (fun b9 ⟨v9, s9, f9⟩ n9 hn9 => ?_)
  refine ⟨⟨?_, ?_, v9, ?_, ?_⟩, by omega⟩
  · rw [f9 vS (by decide)]; vsimp [b6S]
  · rw [f9 vH1 (by decide)]; vsimp [v6]
  · rw [s9]; simp only [DS.sh_set]; rw [s6]; simp
  · refine Fr.trans (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))))
      (Fr.trans (Fr.weaken f6 (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.weaken f9 (by decide)))))

/-! ## Piece 2: `keyBits`, `B₂`, `D`, `keyLen` -/

def cst2 : St VV MM :=
  .seq (.op (.copy cA wP)) (.seq (.op (.add cA gJ)) (.seq (.op (.inc cA)) (.seq (.op (.inc cA)) (.seq (.op (.inc cA))
  (.seq (sizeP cA cKB) (.seq (pow2P kB2 cI cKB) (.seq (.op (.copy cA gJ)) (.seq (.op (.inc cA))
  (.seq (.op (.mul gRC cA kD)) (.seq (.op (.copy cKL kD)) (.seq (.op (.inc cKL)) (.seq (.op (.inc cKL))
  (.op (.inc cKL))))))))))))))

theorem cst2_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (P J rc : ℕ) (hP : a.env wP = P) (hJ : a.env gJ = J)
    (hrc : a.env gRC = rc) (hW : P + J + rc * (J + 1) + 4 ≤ C.Wd) :
    Hs C cst2 a (10 * (P + J + rc * (J + 1)) + 80) (fun e => e.env cKB = Nat.size (P + J + 3) ∧
      e.env kB2 = 2 ^ Nat.size (P + J + 3) ∧ e.env kD = rc * (J + 1) ∧ e.env cKL = rc * (J + 1) + 3 ∧
      e.sh = a.sh ∧ Fr a e [cA, cKB, kB2, cI, kD, cKL]) := by
  have hlt : P + J + rc * (J + 1) + 3 < 2 ^ C.Wd := lt_of_lt_of_le (by omega) (Nat.lt_two_pow_self).le
  have hsz : Nat.size (P + J + 3) ≤ P + J + 3 := Nat.size_le.mpr (Nat.lt_two_pow_self)
  apply Hx.hs
  refine Hs.then (hs_copy C cA wP a (by decide)) (fun b1 hb1 n1 hn1 => ?_); subst hb1
  refine Hs.then (hs_add C cA gJ _ (by decide) (by vsimp [hP, hJ] <;> omega)) (fun b2 hb2 n2 hn2 => ?_); subst hb2
  refine Hs.then (hs_inc C cA _ (by vsimp [hP, hJ] <;> omega)) (fun b3 hb3 n3 hn3 => ?_); subst hb3
  refine Hs.then (hs_inc C cA _ (by vsimp [hP, hJ] <;> omega)) (fun b4 hb4 n4 hn4 => ?_); subst hb4
  refine Hs.then (hs_inc C cA _ (by vsimp [hP, hJ] <;> omega)) (fun b5 hb5 n5 hn5 => ?_); subst hb5
  refine Hs.then (sizeP_spec C cA cKB (by decide) (by decide) (by decide) _ (cst_set (cst_set (cst_set (cst_set
    (cst_set hc cA _ (by decide)) cA _ (by decide)) cA _ (by decide)) cA _ (by decide)) cA _ (by decide))
    (P + J + 3) (by vsimp [hP, hJ] <;> omega) (by omega)) (fun b6 ⟨v6, _, s6, f6⟩ n6 hn6 => ?_)
  have c6 : Cst b6 := cst_fr (cst_set (cst_set (cst_set (cst_set (cst_set hc cA _ (by decide)) cA _ (by decide)) cA _
    (by decide)) cA _ (by decide)) cA _ (by decide)) f6 (by decide)
  refine Hs.then (pow2P_spec C kB2 cI cKB (by decide) (by decide) (by decide) (by decide) b6 c6 _ v6 (by omega))
    (fun b7 ⟨v7, s7, f7⟩ n7 hn7 => ?_)
  have b7J : b7.env gJ = J := by rw [f7 gJ (by decide), f6 gJ (by decide)]; vsimp [hJ]
  have b7R : b7.env gRC = rc := by rw [f7 gRC (by decide), f6 gRC (by decide)]; vsimp [hrc]
  have b7B : b7.env cKB = Nat.size (P + J + 3) := by rw [f7 cKB (by decide)]; exact v6
  refine Hs.then (hs_copy C cA gJ b7 (by decide)) (fun b8 hb8 n8 hn8 => ?_); subst hb8
  refine Hs.then (hs_inc C cA _ (by vsimp [b7J] <;> omega)) (fun b9 hb9 n9 hn9 => ?_); subst hb9
  have hm : rc * (J + 1) < 2 ^ C.Wd := by omega
  refine Hs.then (hs_mul C gRC cA kD _ (by decide) (by decide) (by decide) (by vsimp [b7J, b7R] <;> omega))
    (fun b10 hb10 n10 hn10 => ?_); subst hb10
  refine Hs.then (hs_copy C cKL kD _ (by decide)) (fun b11 hb11 n11 hn11 => ?_); subst hb11
  refine Hs.then (hs_inc C cKL _ (by vsimp [b7J, b7R] <;> omega)) (fun b12 hb12 n12 hn12 => ?_); subst hb12
  refine Hs.then (hs_inc C cKL _ (by vsimp [b7J, b7R] <;> omega)) (fun b13 hb13 n13 hn13 => ?_); subst hb13
  refine Hs.last (hs_inc C cKL _ (by vsimp [b7J, b7R] <;> omega)) (fun b14 hb14 n14 hn14 => ?_); subst hb14
  refine ⟨⟨by vsimp [b7B], by vsimp [v7], by vsimp [b7J, b7R],
    by vsimp [b7J, b7R] <;> ring, ?_, ?_⟩, by omega⟩
  · simp only [DS.sh_set]; rw [s7, s6]; simp
  · refine Fr.trans (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))))
      (Fr.trans (Fr.weaken f6 (by decide)) (Fr.trans (Fr.weaken f7 (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))))))))

/-! ## Piece 3: `deltaBound`, its size, `valueWidth`, `2^{valueWidth}` -/

def cst3 : St VV MM :=
  .seq (.op (.copy cA wM1)) (.seq (.op (.add cA wA)) (.seq (.op (.add cA wF)) (.seq (.op (.inc cA))
  (.seq (.op (.shl cA)) (.seq (.op (.copy cB wW)) (.seq (.op (.inc cB)) (.seq (.op (.mul cA cB cDB))
  (.seq (sizeP cDB cSD) (.seq (.op (.mul wK cSD cT)) (.seq (.op (.shl cT)) (.seq (.op (.add cT wK))
  (.seq (.op (.inc cT)) (pow2P kVW2 cI cT)))))))))))))

theorem cst3_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (M1 A F W k : ℕ) (hM : a.env wM1 = M1)
    (hA : a.env wA = A) (hF : a.env wF = F) (hWv : a.env wW = W) (hk : a.env wK = k)
    (hDB : 2 * (M1 + A + F + 1) * (W + 1) < 2 ^ C.Wd)
    (hW : k + 2 * k * Nat.size (2 * (M1 + A + F + 1) * (W + 1)) + 1 < C.Wd) :
    Hs C cst3 a (5 * Nat.size (2 * (M1 + A + F + 1) * (W + 1)) +
        5 * (k + 2 * k * Nat.size (2 * (M1 + A + F + 1) * (W + 1)) + 1) + 40) (fun e =>
      e.env cT = k + 2 * k * Nat.size (2 * (M1 + A + F + 1) * (W + 1)) + 1 ∧
      e.env kVW2 = 2 ^ (k + 2 * k * Nat.size (2 * (M1 + A + F + 1) * (W + 1)) + 1) ∧
      e.sh = a.sh ∧ Fr a e [cA, cB, cDB, cSD, cT, kVW2, cI]) := by
  obtain ⟨DB, hDBd⟩ : ∃ DB, DB = 2 * (M1 + A + F + 1) * (W + 1) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = k * Nat.size DB := ⟨_, rfl⟩
  have hVW : k + 2 * k * Nat.size DB + 1 = 2 * x + k + 1 := by rw [hx]; ring
  rw [← hDBd] at hDB hW ⊢
  rw [hVW] at hW ⊢
  have h1 : M1 + A + F + 1 ≤ DB := by rw [hDBd]; nlinarith
  have h2 : 2 * (M1 + A + F + 1) ≤ DB := by rw [hDBd]; nlinarith
  have h3 : W + 1 ≤ DB := by rw [hDBd]; nlinarith
  have hVWlt : 2 * x + k + 1 < 2 ^ C.Wd := lt_of_lt_of_le hW (Nat.lt_two_pow_self).le
  have hszW : Nat.size DB < 2 ^ C.Wd := lt_of_le_of_lt (Nat.size_le.mpr hDB) Nat.lt_two_pow_self
  apply Hx.hs
  refine Hs.then (hs_copy C cA wM1 a (by decide)) (fun b1 hb1 n1 hn1 => ?_); subst hb1
  refine Hs.then (hs_add C cA wA _ (by decide) (by vsimp [hM, hA] <;> omega)) (fun b2 hb2 n2 hn2 => ?_); subst hb2
  refine Hs.then (hs_add C cA wF _ (by decide) (by vsimp [hM, hA, hF] <;> omega)) (fun b3 hb3 n3 hn3 => ?_)
  subst hb3
  refine Hs.then (hs_inc C cA _ (by vsimp [hM, hA, hF] <;> omega)) (fun b4 hb4 n4 hn4 => ?_); subst hb4
  refine Hs.then (hs_shl C cA _ (by vsimp [hM, hA, hF] <;> omega)) (fun b5 hb5 n5 hn5 => ?_); subst hb5
  refine Hs.then (hs_copy C cB wW _ (by decide)) (fun b6 hb6 n6 hn6 => ?_); subst hb6
  refine Hs.then (hs_inc C cB _ (by vsimp [hWv] <;> omega)) (fun b7 hb7 n7 hn7 => ?_); subst hb7
  refine Hs.then (hs_mul C cA cB cDB _ (by decide) (by decide) (by decide)
    (by vsimp [hM, hA, hF, hWv]; rw [hDBd] at hDB; nlinarith)) (fun b8 hb8 n8 hn8 => ?_); subst hb8
  refine Hs.then (sizeP_spec C cDB cSD (by decide) (by decide) (by decide) _ (cst_set (cst_set (cst_set (cst_set
    (cst_set (cst_set (cst_set (cst_set hc cA _ (by decide)) cA _ (by decide)) cA _ (by decide)) cA _ (by decide)) cA _
    (by decide)) cB _ (by decide)) cB _ (by decide)) cDB _ (by decide)) DB
    (by vsimp [hM, hA, hF, hWv]; rw [hDBd]) hszW) (fun b9 ⟨v9, _, s9, f9⟩ n9 hn9 => ?_)
  have c9 : Cst b9 := cst_fr (cst_set (cst_set (cst_set (cst_set (cst_set (cst_set (cst_set (cst_set hc cA _
    (by decide)) cA _ (by decide)) cA _ (by decide)) cA _ (by decide)) cA _ (by decide)) cB _ (by decide)) cB _
    (by decide)) cDB _ (by decide)) f9 (by decide)
  have b9k : b9.env wK = k := by rw [f9 wK (by decide)]; vsimp [hk]
  have m10 : b9.env wK * b9.env cSD = x := by rw [b9k, v9, hx]
  refine Hs.then (hs_mul C wK cSD cT b9 (by decide) (by decide) (by decide) (by rw [m10]; omega))
    (fun b10 hb10 n10 hn10 => ?_); subst hb10
  refine Hs.then (hs_shl C cT _ (by rw [DS.set_env_self, m10]; omega)) (fun b11 hb11 n11 hn11 => ?_); subst hb11
  refine Hs.then (hs_add C cT wK _ (by decide) (by
    rw [DS.set_env_self, DS.set_env_self, DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), m10, b9k]
    omega)) (fun b12 hb12 n12 hn12 => ?_)
  subst hb12
  have v12 : ((((b9.set cT (b9.env wK * b9.env cSD)).set cT (2 * (b9.set cT (b9.env wK * b9.env cSD)).env cT)).set cT
      (((b9.set cT (b9.env wK * b9.env cSD)).set cT (2 * (b9.set cT (b9.env wK * b9.env cSD)).env cT)).env cT +
        ((b9.set cT (b9.env wK * b9.env cSD)).set cT (2 * (b9.set cT (b9.env wK * b9.env cSD)).env cT)).env wK)).env cT)
      = 2 * x + k := by
    rw [DS.set_env_self, DS.set_env_self, DS.set_env_self, DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide),
      m10, b9k]
  refine Hs.then (hs_inc C cT _ (by rw [v12]; omega)) (fun b13 hb13 n13 hn13 => ?_); subst hb13
  refine Hs.last (pow2P_spec C kVW2 cI cT (by decide) (by decide) (by decide) (by decide) _
    (cst_set (cst_set (cst_set (cst_set c9 cT _ (by decide)) cT _ (by decide)) cT _ (by decide)) cT _ (by decide))
    (2 * x + k + 1) (by rw [DS.set_env_self, v12]) hW) (fun b14 ⟨v14, s14, f14⟩ n14 hn14 => ?_)
  refine ⟨⟨by rw [f14 cT (by decide), DS.set_env_self, v12], v14, ?_, ?_⟩, ?_⟩
  · rw [s14]; simp only [DS.sh_set]; rw [s9]; simp
  · refine Fr.trans (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))))))))
      (Fr.trans (Fr.weaken f9 (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken f14 (by decide)))))))
  · omega

/-! ## Piece 4: `keyBits·keyLen`, `SH`, `recWidth`, `PAD` -/

def cst4 : St VV MM :=
  .seq (.op (.mul cKB cKL cKK)) (.seq (.op (.copy cA cKK)) (.seq (.op (.add cA cT)) (.seq (pow2P vSH cI cA)
  (.seq (.op (.copy vRW vS)) (.seq (.op (.add vRW cKK)) (.seq (.op (.add vRW cT)) (.seq (.op (.copy kPAD kVW2))
  (powP kPAD kB2 cI kD cB))))))))

theorem cst4_spec (C : Ctx) (a : DS VV MM) (hc : Cst a) (s KB KL VW D : ℕ) (hKB : a.env cKB = KB)
    (hKL : a.env cKL = KL) (hVW : a.env cT = VW) (hs : a.env vS = s) (hV2 : a.env kVW2 = 2 ^ VW)
    (hB2 : a.env kB2 = 2 ^ KB) (hD : a.env kD = D) (hDL : D ≤ KL) (hDW : D < C.Wd) (hW : s + KB * KL + VW + 1 < C.Wd) :
    Hs C cst4 a (5 * (KB * KL + VW) + 7 * D + 30) (fun e => e.env vSH = 2 ^ (KB * KL + VW) ∧
      e.env vRW = s + KB * KL + VW ∧ e.env kPAD = 2 ^ VW * (2 ^ KB) ^ D ∧ e.sh = a.sh ∧
      Fr a e [cKK, cA, vSH, cI, vRW, kPAD, cB]) := by
  have hlt : s + KB * KL + VW + 1 < 2 ^ C.Wd := lt_of_lt_of_le hW (Nat.lt_two_pow_self).le
  have hpad : 2 ^ VW * (2 ^ KB) ^ D < 2 ^ C.Wd := by
    rw [← pow_mul, ← pow_add]
    exact Nat.pow_lt_pow_right (by norm_num) (by have := Nat.mul_le_mul_left KB hDL; omega)
  apply Hx.hs
  refine Hs.then (hs_mul C cKB cKL cKK a (by decide) (by decide) (by decide) (by rw [hKB, hKL]; omega))
    (fun b1 hb1 n1 hn1 => ?_); subst hb1
  refine Hs.then (hs_copy C cA cKK _ (by decide)) (fun b2 hb2 n2 hn2 => ?_); subst hb2
  refine Hs.then (hs_add C cA cT _ (by decide) (by vsimp [hKB, hKL, hVW] <;> omega)) (fun b3 hb3 n3 hn3 => ?_); subst hb3
  refine Hs.then (pow2P_spec C vSH cI cA (by decide) (by decide) (by decide) (by decide) _
    (cst_set (cst_set (cst_set hc cKK _ (by decide)) cA _ (by decide)) cA _ (by decide)) (KB * KL + VW)
    (by vsimp [hKB, hKL, hVW]) (by omega)) (fun b4 ⟨v4, s4, f4⟩ n4 hn4 => ?_)
  have hb4v : ∀ y, y ≠ vSH → y ≠ cI → b4.env y = ((((a.set cKK (a.env cKB * a.env cKL)).set cA
      ((a.set cKK (a.env cKB * a.env cKL)).env cKK)).set cA (((a.set cKK (a.env cKB * a.env cKL)).set cA
      ((a.set cKK (a.env cKB * a.env cKL)).env cKK)).env cA + ((a.set cKK (a.env cKB * a.env cKL)).set cA
      ((a.set cKK (a.env cKB * a.env cKL)).env cKK)).env cT)).env y) := fun y h1 h2 =>
    f4 y (by simp [h1, h2])
  refine Hs.then (hs_copy C vRW vS b4 (by decide)) (fun b5 hb5 n5 hn5 => ?_); subst hb5
  refine Hs.then (hs_add C vRW cKK _ (by decide) (by
    vsimp [hb4v vS (by decide) (by decide), hb4v cKK (by decide) (by decide), hs, hKB, hKL] <;> omega))
    (fun b6 hb6 n6 hn6 => ?_); subst hb6
  refine Hs.then (hs_add C vRW cT _ (by decide) (by
    vsimp [hb4v vS (by decide) (by decide), hb4v cKK (by decide) (by decide), hb4v cT (by decide) (by decide), hs, hKB, hKL,
      hVW] <;> omega)) (fun b7 hb7 n7 hn7 => ?_); subst hb7
  refine Hs.then (hs_copy C kPAD kVW2 _ (by decide)) (fun b8 hb8 n8 hn8 => ?_); subst hb8
  refine Hs.last (powP_spec C kPAD kB2 cI kD cB (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) _ D (2 ^ VW) (2 ^ KB)
    (by vsimp [hb4v kD (by decide) (by decide), hD]) (by vsimp [hb4v kVW2 (by decide) (by decide), hV2])
    (by vsimp [hb4v kB2 (by decide) (by decide), hB2]) (hDW.trans Nat.lt_two_pow_self) hpad) (fun b9 ⟨v9, s9, f9⟩ n9 hn9 => ?_)
  refine ⟨⟨?_, ?_, v9, ?_, ?_⟩, by omega⟩
  · rw [f9 vSH (by decide)]; vsimp [v4]
  · rw [f9 vRW (by decide)]
    vsimp [hb4v vS (by decide) (by decide), hb4v cKK (by decide) (by decide), hb4v cT (by decide) (by decide), hs, hKB,
      hKL, hVW]
  · rw [s9]; simp only [DS.sh_set]; rw [s4]; simp
  · refine Fr.trans (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
      (Fr.trans (Fr.weaken f4 (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.trans (Fr.set _ _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.weaken f9 (by decide)))))))

end NearCubicGates.Close.CounterMachine.CellTablesProg
