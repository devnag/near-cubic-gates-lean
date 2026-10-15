import Proof.Gates.CounterMachine.CellTablesBody8

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.CellTablesProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader (sN)
open NearCubicGates.Close.CounterMachine.CellTables (vS vH1 vH0 vSH vKY vQE vRS vRW sREC sTMP convP Frame)

variable {B1 B2 cT : ℕ} {PolyTab : TabMachine}

theorem quad_le (X : ℕ) : X * (40 * X + 46) + 200 * X + 2000 ≤ 1000 * (X + 10) ^ 2 := by nlinarith

theorem momBody_spec (RK : TabCallMachine B1 B2 cT PolyTab) (r : CellReq B1 B2 cT) (Wd Lk Bk wb : ℕ) (inp : List Bool)
    (a : DS VV MM) (phi : Bool) (ro j τ jj : ℕ) (tg jv : Fin VV) (hF : Fit RK r Wd Lk Bk wb)
    (hP : Pre (ctxK RK Wd inp Lk Bk) r a) (hro : ro < roleCount r.c.kind) (hj : phi = false → j < r.p.J)
    (hτd : τ = if phi then 2 else 1) (hjjd : jj = if phi then 0 else j)
    (hR : a.env lR = ro) (htg : a.env tg = τ) (hjv : a.env jv = jj)
    (htgT : tg ∉ emT) (hjvT : jv ∉ emT) (h1 : tg ≠ bKey) (h2 : jv ≠ bKey) (h4 : jv ≠ bTmp) :
    Hs (ctxK RK Wd inp Lk Bk) (momBody tg jv) a (bodyCost Lk Bk wb r)
      (fun e => Post (ctxK RK Wd inp Lk Bk) r a e (momId phi ro j)) := by
  set C := ctxK RK Wd inp Lk Bk with hC
  set X := (cellInput r).length with hX
  have hWd : 4 ≤ C.Wd := by have := hF.wd; show 4 ≤ Wd; omega
  have hτ : τ ≤ 2 := by rw [hτd]; split <;> omega
  have hrc2 : roleCount r.c.kind ≤ 2 := by cases r.c.kind <;> decide
  have hro2 : ro ≤ 2 := by omega
  have hD := dOf_le r
  have hJX : r.p.J ≤ 2 * X + 2 := by
    have : r.p.J ≤ dOf r.c r.p := by unfold dOf; have := roleCount_pos r.c.kind; nlinarith
    omega
  have hjj : jj ≤ r.p.J := by
    rw [hjjd]; split
    · omega
    · rename_i h; exact (hj (by simpa using h)).le
  have hJB : r.p.J < 2 ^ keyBits r.p := by
    unfold keyBits; exact lt_of_le_of_lt (by omega) (Nat.lt_size_self (r.p.P + r.p.J + 3))
  have hKB2 := keyBits_two r.p
  have hB4 : 4 ≤ 2 ^ keyBits r.p := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ keyBits r.p := Nat.pow_le_pow_right (by norm_num) hKB2
  have hKL : keyLen r.c r.p = dOf r.c r.p + 3 := by unfold keyLen dOf; omega
  have hKBKL : 2 ^ (keyBits r.p * keyLen r.c r.p) ≤ 2 ^ C.Wd := by
    have := hF.wd; unfold lamW at this
    exact Nat.pow_le_pow_right (by norm_num) (by show _ ≤ Wd; omega)
  have hB3 : (2 ^ keyBits r.p) ^ 3 ≤ 2 ^ (keyBits r.p * keyLen r.c r.p) := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by rw [hKL]; nlinarith)
  obtain ⟨B, hBd⟩ : ∃ B, B = 2 ^ keyBits r.p := ⟨_, rfl⟩
  rw [← hBd] at hJB hB4 hB3
  have hk1 : τ * B + ro + 1 ≤ 3 * B := by
    have : τ * B ≤ 2 * B := Nat.mul_le_mul_right _ hτ
    omega
  have hk2 : (τ * B + ro) * B + jj < B ^ 3 := by
    have e1 : (τ * B + ro + 1) * B ≤ 3 * B * B := Nat.mul_le_mul_right _ hk1
    have e2 : 3 * B * B ≤ B * B * B := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
    have e3 : (τ * B + ro + 1) * B = (τ * B + ro) * B + B := by ring
    have e4 : B ^ 3 = B * B * B := by ring
    omega
  have hkW : B ^ 3 ≤ 2 ^ C.Wd := hB3.trans hKBKL
  have h3B : 3 * B ≤ B ^ 3 := by
    have : 3 * B ≤ B * B * B := by
      have : 3 * B ≤ B * B := Nat.mul_le_mul_right _ (by omega)
      calc 3 * B ≤ B * B := this
        _ ≤ B * B * B := Nat.le_mul_of_pos_right _ (by omega)
    calc 3 * B ≤ B * B * B := this
      _ = B ^ 3 := by ring
  have hτB : τ * B ≤ 2 * B := Nat.mul_le_mul_right _ hτ
  set x : TabCallReq B1 B2 cT := ⟨r, momId phi ro j, momId_mem r.c r.p phi ro j hro hj⟩ with hx
  have hLk : (tabCallInput x).length ≤ C.Lk := hF.lk x rfl
  have hRK : (tabCallInput x).length = (natWord τ).length + (natWord ro).length + (natWord jj).length + X := by
    show ((descN (momId phi ro j)).flatMap natWord ++ cellInput r).length = _
    rw [descN_mom, ← hτd, ← hjjd]; simp only [List.length_append]; omega
  have nb : ∀ y : Fin VV, bodyVarB y = false → ¬ BodyVar y := fun y h => not_bodyVar h
  have hn1 := (nbl_le_self τ).trans (by omega : τ + 1 ≤ 3)
  have hn2 := (nbl_le_self ro).trans (by omega : ro + 1 ≤ 3)
  have hn3 := (nbl_le_self jj).trans (by omega : jj + 1 ≤ 2 * X + 3)
  unfold momBody
  apply Hx.hs
  -- the head: three words
  refine Hs.then (PrefixProg.Hs.valid (emV_spec C tg (fun h => htgT (by rw [h]; decide)) a hP.cst (by omega) τ htg
    (by rw [← htg]; exact hP.valid.env_lt tg) (by rw [hP.kin]; simp only [List.length_nil, zero_add]; omega))
    hP.valid (by omega)) (fun e1 ⟨⟨k1, s1, c1, f1⟩, w1⟩ n1 hn1' => ?_)
  have e1R : e1.env lR = ro := by rw [f1 lR (by decide)]; exact hR
  refine Hs.then (PrefixProg.Hs.valid (emV_spec C lR (by decide) e1 c1 (by omega) ro e1R
    (by rw [← e1R]; exact w1.env_lt lR) (by rw [k1, hP.kin]; simp only [List.nil_append]; omega)) w1 (by omega))
    (fun e2 ⟨⟨k2, s2, c2, f2⟩, w2⟩ n2 hn2' => ?_)
  have e2j : e2.env jv = jj := by rw [f2 jv hjvT, f1 jv hjvT]; exact hjv
  refine Hs.then (PrefixProg.Hs.valid (emV_spec C jv (fun h => hjvT (by rw [h]; decide)) e2 c2 (by omega) jj e2j
    (by rw [← e2j]; exact w2.env_lt jv)
    (by rw [k2, k1, hP.kin]; simp only [List.nil_append, List.length_append]; omega)) w2 (by omega))
    (fun e3 ⟨⟨k3, s3, c3, f3⟩, w3⟩ n3 hn3' => ?_)
  have g3 : ∀ y, y ∉ emT → e3.env y = a.env y := fun y hy => by rw [f3 y hy, f2 y hy, f1 y hy]
  have e3tg : e3.env tg = τ := by rw [g3 tg htgT]; exact htg
  have e3jv : e3.env jv = jj := by rw [g3 jv hjvT]; exact hjv
  have e3R : e3.env lR = ro := by rw [g3 lR (by decide)]; exact hR
  have e3B : e3.env kB2 = B := by rw [g3 kB2 (by decide), hBd]; exact hP.b2
  -- the key
  refine Hs.then (PrefixProg.Hs.valid (hs_copy C bKey tg e3 (Ne.symm h1)) w3 (by omega)) (fun e4 ⟨he4, w4⟩ n4 hn4 => ?_)
  have o4 : ∀ y, y ≠ bKey → e4.env y = e3.env y := fun y hy => by rw [he4, DS.set_env_ne _ _ hy]
  have k4 : e4.env bKey = τ := by rw [he4, DS.set_env_self, e3tg]
  refine Hs.then (PrefixProg.Hs.valid (hs_mul C bKey kB2 bTmp e4 (by decide) (by decide) (by decide)
    (by rw [k4, o4 kB2 (by decide), e3B]; omega)) w4 (by omega)) (fun e5 ⟨he5, w5⟩ n5 hn5 => ?_)
  have o5 : ∀ y, y ≠ bTmp → e5.env y = e4.env y := fun y hy => by rw [he5, DS.set_env_ne _ _ hy]
  have t5 : e5.env bTmp = τ * B := by rw [he5, DS.set_env_self, k4, o4 kB2 (by decide), e3B]
  refine Hs.then (PrefixProg.Hs.valid (hs_copy C bKey bTmp e5 (by decide)) w5 (by omega)) (fun e6 ⟨he6, w6⟩ n6 hn6 => ?_)
  have o6 : ∀ y, y ≠ bKey → e6.env y = e5.env y := fun y hy => by rw [he6, DS.set_env_ne _ _ hy]
  have k6 : e6.env bKey = τ * B := by rw [he6, DS.set_env_self, t5]
  have e6R : e6.env lR = ro := by rw [o6 lR (by decide), o5 lR (by decide), o4 lR (by decide), e3R]
  refine Hs.then (PrefixProg.Hs.valid (hs_add C bKey lR e6 (by decide) (by rw [k6, e6R]; omega)) w6 (by omega))
    (fun e7 ⟨he7, w7⟩ n7 hn7 => ?_)
  have o7 : ∀ y, y ≠ bKey → e7.env y = e6.env y := fun y hy => by rw [he7, DS.set_env_ne _ _ hy]
  have k7 : e7.env bKey = τ * B + ro := by rw [he7, DS.set_env_self, k6, e6R]
  have e7B : e7.env kB2 = B := by
    rw [o7 kB2 (by decide), o6 kB2 (by decide), o5 kB2 (by decide), o4 kB2 (by decide), e3B]
  refine Hs.then (PrefixProg.Hs.valid (hs_mul C bKey kB2 bTmp e7 (by decide) (by decide) (by decide)
    (by rw [k7, e7B]; omega)) w7 (by omega)) (fun e8 ⟨he8, w8⟩ n8 hn8 => ?_)
  have o8 : ∀ y, y ≠ bTmp → e8.env y = e7.env y := fun y hy => by rw [he8, DS.set_env_ne _ _ hy]
  have t8 : e8.env bTmp = (τ * B + ro) * B := by rw [he8, DS.set_env_self, k7, e7B]
  refine Hs.then (PrefixProg.Hs.valid (hs_copy C bKey bTmp e8 (by decide)) w8 (by omega)) (fun e9 ⟨he9, w9⟩ n9 hn9 => ?_)
  have o9 : ∀ y, y ≠ bKey → e9.env y = e8.env y := fun y hy => by rw [he9, DS.set_env_ne _ _ hy]
  have k9 : e9.env bKey = (τ * B + ro) * B := by rw [he9, DS.set_env_self, t8]
  have e9j : e9.env jv = jj := by
    rw [o9 jv h2, o8 jv h4, o7 jv h2, o6 jv h2, o5 jv h4, o4 jv h2, e3jv]
  refine Hs.then (PrefixProg.Hs.valid (hs_add C bKey jv e9 (Ne.symm h2) (by rw [k9, e9j]; omega)) w9 (by omega))
    (fun e10 ⟨he10, w10⟩ n10 hn10 => ?_)
  have o10 : ∀ y, y ≠ bKey → e10.env y = e9.env y := fun y hy => by rw [he10, DS.set_env_ne _ _ hy]
  have k10 : e10.env bKey = (τ * B + ro) * B + jj := by rw [he10, DS.set_env_self, k9, e9j]
  -- the frame of the head
  have g10 : ∀ y, y ∉ emT → y ≠ bKey → y ≠ bTmp → e10.env y = a.env y := fun y hy h1' h2' => by
    rw [o10 y h1', o9 y h1', o8 y h2', o7 y h1', o6 y h1', o5 y h2', o4 y h1', g3 y hy]
  have bf10 : BF a e10 := by
    intro y hy
    have hT : y ∉ emT := fun hm => hy (bodyVar_of (List.all_eq_true.mp (show emT.all bodyVarB = true by decide) y hm))
    exact g10 y hT (fun h => hy (by rw [h]; exact bodyVar_of (by decide)))
      (fun h => hy (by rw [h]; exact bodyVar_of (by decide)))
  have sn10 : SameN a e10 := by
    rw [he10, he9, he8, he7, he6, he5, he4]
    exact s1.trans (s2.trans (s3.trans ((SameN.set _ _ _).trans ((SameN.set _ _ _).trans ((SameN.set _ _ _).trans
      ((SameN.set _ _ _).trans ((SameN.set _ _ _).trans ((SameN.set _ _ _).trans (SameN.set _ _ _)))))))))
  have c10 : Cst e10 := ⟨by rw [g10 vZ (by decide) (by decide) (by decide)]; exact hP.cst.z,
    by rw [g10 v1 (by decide) (by decide) (by decide)]; exact hP.cst.one,
    by rw [g10 v2 (by decide) (by decide) (by decide)]; exact hP.cst.two⟩
  have kin10 : e10.kin = (descN x.id).flatMap natWord := by
    rw [he10, he9, he8, he7, he6, he5, he4]
    show e3.kin = (descN (momId phi ro j)).flatMap natWord
    rw [k3, k2, k1, hP.kin, descN_mom, ← hτd, ← hjjd]; simp
  -- the tail
  refine Hs.last (tail_spec RK Wd Lk Bk wb inp x e10 kPAD vZ vZ 0 false hF (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) w10 c10
    (by rw [sn10.ram]; exact hP.ramN) (by rw [bf10 wN (nb wN (by decide))]; exact hP.wN)
    (by rw [bf10 vH1 (nb vH1 (by decide))]; exact hP.h1) (by rw [bf10 vH0 (nb vH0 (by decide))]; exact hP.h0)
    (by rw [bf10 vSH (nb vSH (by decide))]; exact hP.sh) kin10
    (by rw [k10, bf10 kPAD (nb kPAD (by decide)), hP.pad]
        show _ = reqKey r.c r.p (momId phi ro j) * _
        rw [reqKey_mom, ← hτd, ← hjjd, ← hBd, pow_mul, ← hBd]; ring)
    (by rw [c10.z]) (by rw [c10.z]; rfl)
    (by intro part q κ σ h; exfalso; simp only [hx, momId] at h; split at h <;> cases h)
    (fun _ => rfl) (by intro h; cases h) (by simp) (by rw [sn10.rc, sn10.ram]; exact hP.rcR))
    (fun e11 hp11 n11 hn11 => ?_)
  refine ⟨⟨by rw [hp11.ramR, sn10.ram], hp11.rcR, fun m h1' h2' => by rw [hp11.ram m h1' h2', sn10.ram], hp11.rcN,
    fun m h1' h2' h3' => by rw [hp11.rc m h1' h2' h3', sn10.rc], by rw [hp11.out, sn10.out],
    by rw [hp11.ip, sn10.ip], hp11.kin, hp11.valid, hp11.cst, BF.trans bf10 hp11.fr⟩, ?_⟩
  have hrcN : e10.rc sN ≤ X := by
    have := w10.rc_le sN; rw [sn10.ram, hP.ramN] at this; exact this.trans (cellN_len_le r)
  have hA : (cellN r.c r.p r.wt).length * (40 * X + 42 + 4) ≤ X * (40 * X + 46) :=
    Nat.mul_le_mul_right _ (cellN_len_le r)
  have hQ := quad_le X
  have hn11' : n11 ≤ e10.rc sN + tailCost Lk Bk wb r := hn11
  unfold tailCost at hn11'
  rw [← hX] at hn11'
  have c1 : n1 + n2 + n3 ≤ 500 + 80 * X := by omega
  have c2 : n11 ≤ X + X * (40 * X + 46) + Lk + Bk + 100 * 2 ^ (r.c.n - r.p.k) * (wb + 10) + 120 := by omega
  unfold bodyCost
  rw [← hX]
  omega

/-- **F-MOM** (CellTables-SPLIT2). -/
theorem momB_spec : MomBSpec momB := by
  intro B1 B2 cT PolyTab RK r Wd Lk Bk wb inp a phi ro j hF hP hro hj hR hJ
  cases phi with
  | false =>
    exact momBody_spec RK r Wd Lk Bk wb inp a false ro j 1 j v1 lJ hF hP hro hj rfl rfl hR hP.cst.one hJ
      (by decide) (by decide) (by decide) (by decide) (by decide)
  | true =>
    exact momBody_spec RK r Wd Lk Bk wb inp a true ro j 2 0 v2 vZ hF hP hro hj rfl rfl hR hP.cst.two hP.cst.z
      (by decide) (by decide) (by decide) (by decide) (by decide)

end NearCubicGates.Close.CounterMachine.CellTablesProg
