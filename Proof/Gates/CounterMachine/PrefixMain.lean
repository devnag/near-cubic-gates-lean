import Proof.Gates.CounterMachine.PrefixInst

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine.PrefixProg

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter NearCubicGates.Close.CounterMachine
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Cells.PrefixLoader
open NearCubicWires.RepairOrdinary (frame)

/-! ## The set-up -/

def clogP : St VV MM := .loop (.lt xp tt) (.seq (.op (.shl xp)) (.op (.inc xc)))

def setupT : List (Fin VV) := [xs, xc, xp, tt, xB, xK2, jx, xGr]

theorem clog_spec (C : Ctx) (n : ℕ) (b : DS VV MM) (hp : b.env xp = 1) (hc0 : b.env xc = 0) (ht : b.env tt = n + 1)
    (hW : 2 * (n + 1) ≤ 2 ^ C.Wd) :
    Hs C clogP b (Nat.clog 2 (n + 1) * (3 + 2) + 2) (fun d => d.env xc = Nat.clog 2 (n + 1) ∧
      Same b d ∧ Fr b d [xp, xc]) := by
  let I : ℕ → DS VV MM → Prop := fun t d => d.env xp = 2 ^ t ∧ d.env xc = t ∧ d.env tt = n + 1 ∧ Same b d ∧
    Fr b d [xp, xc]
  refine Hs.mono (Hs.loopN (C := C) (c := .lt xp tt) (s := .seq (.op (.shl xp)) (.op (.inc xc)))
    (show xp ≠ tt by decide) I (Nat.clog 2 (n + 1)) 3 ?_ ?_ b ⟨by rw [hp]; rfl, hc0, ht, Same.refl _, Fr.refl _ _⟩)
    le_rfl (fun d ⟨_, d2, _, d4, d5⟩ => ⟨d2, d4, d5⟩)
  · intro t ht' d ⟨d1, d2, d3, d4, d5⟩
    have hlt : 2 ^ t < n + 1 := Nat.pow_lt_of_lt_clog ht'
    refine ⟨by simp [Cnd.eval, d1, d3, hlt], ?_⟩
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_shl C xp d (by rw [d1]; omega)) (fun e he => ?_)
    subst he
    have htn : t < n + 1 := lt_of_le_of_lt (Nat.lt_two_pow_self).le hlt
    refine Hs.mono (hs_inc C xc _ (by rw [DS.set_env_ne _ _ (by decide), d2]; omega)) le_rfl ?_
    rintro f rfl
    refine ⟨by vsimp [d1]; ring, by vsimp [d2], by vsimp [d3], d4.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
      Fr.trans d5 (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))⟩
  · intro d ⟨d1, _, d3, _, _⟩
    have hle : n + 1 ≤ 2 ^ Nat.clog 2 (n + 1) := Nat.le_pow_clog (by norm_num) _
    simp only [Cnd.eval, d1, d3]
    exact decide_eq_false (by omega)

def preS : St VV MM :=
  .seq (.op (.copy xs gN)) (.seq (.op (.sub xs xk)) (.seq (.op (.zero xc)) (.seq (.op (.copy xp v1))
    (.seq (.op (.copy tt gN)) (.op (.inc tt))))))

theorem preS_spec (C : Ctx) (b : DS VV MM) (hc : Cst b) (n k : ℕ) (hn : b.env gN = n) (hk : b.env xk = k)
    (hkn : k ≤ n) (hnW : n + 1 < 2 ^ C.Wd) :
    Hs C preS b 11 (fun d => d.env xs = n - k ∧ d.env xc = 0 ∧ d.env xp = 1 ∧ d.env tt = n + 1 ∧ Same b d ∧
      Fr b d setupT) := by
  unfold preS
  refine Hs.seq (t1 := 1) (t2 := 9) (hs_copy C xs gN b (by decide)) (fun b1 hb1 => ?_)
  subst hb1
  refine Hs.seq (t1 := 1) (t2 := 7) (hs_sub C xs xk _ (by decide) (by vsimp [hn, hk]; omega)) (fun b2 hb2 => ?_)
  subst hb2
  refine Hs.seq (t1 := 1) (t2 := 5) (hs_zero C xc _) (fun b3 hb3 => ?_)
  subst hb3
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_copy C xp v1 _ (by decide)) (fun b4 hb4 => ?_)
  subst hb4
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C tt gN _ (by decide)) (fun b5 hb5 => ?_)
  subst hb5
  refine Hs.mono (hs_inc C tt _ (by vsimp [hn]; omega)) le_rfl ?_
  rintro d rfl
  refine ⟨by vsimp [hn, hk], by vsimp [], by vsimp [hc.one], by vsimp [hn], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro y hy
  simp only [setupT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  vsimp [Function.update_apply, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1]

def midS : St VV MM :=
  .seq (.op (.mul gN xc xB)) (.seq (.op (.shl xB)) (.seq (.op (.shl xB)) (.op (.copy xK2 v1))))

theorem midS_spec (C : Ctx) (b : DS VV MM) (hc : Cst b) (n : ℕ) (hn : b.env gN = n)
    (hxc : b.env xc = Nat.clog 2 (n + 1)) (hbig : 4 * (n * Nat.clog 2 (n + 1)) < 2 ^ C.Wd) :
    Hs C midS b 7 (fun d => d.env xB = Call.B0 n ∧ d.env xK2 = 1 ∧ Same b d ∧ Fr b d [xB, xK2]) := by
  unfold midS
  refine Hs.seq (t1 := 1) (t2 := 5) (hs_mul C gN xc xB b (by decide) (by decide) (by decide) (by
    rw [hn, hxc]; omega)) (fun b1 hb1 => ?_)
  subst hb1
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_shl C xB _ (by vsimp [hn, hxc]; omega)) (fun b2 hb2 => ?_)
  subst hb2
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_shl C xB _ (by vsimp [hn, hxc]; omega)) (fun b3 hb3 => ?_)
  subst hb3
  refine Hs.mono (hs_copy C xK2 v1 _ (by decide)) le_rfl ?_
  rintro d rfl
  refine ⟨by vsimp [hn, hxc]; unfold Call.B0; ring, by vsimp [hc.one], ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  vsimp [Function.update_apply, hy.1, hy.2]

theorem pow2_spec (C : Ctx) (b : DS VV MM) (k : ℕ) (hk : b.env xk = k) (h1 : b.env xK2 = 1) (hkW : k < C.Wd) :
    Hs C (forS jx xk (.op (.shl xK2))) b (k * (1 + 4) + 4) (fun d => d.env xK2 = 2 ^ k ∧ Same b d ∧
      Fr b d [jx, xK2]) := by
  let I : ℕ → DS VV MM → Prop := fun j d => d.env xK2 = 2 ^ j ∧ Same b d ∧ Fr b d [jx, xK2]
  have hl := forS_spec' (C := C) jx xk (by decide) (.op (.shl xK2)) b k (lt_of_lt_of_le hkW
    (Nat.lt_two_pow_self).le) I 1
    (fun j d v ⟨d1, d2, d3⟩ => ⟨by rw [DS.set_env_ne _ _ (by decide)]; exact d1, d2.trans (Same.set _ _ _),
      Fr.trans d3 (Fr.set d v (by decide))⟩) ⟨by rw [h1]; rfl, Same.refl _, Fr.refl _ _⟩ hk (by
      intro j hj d ⟨d1, d2, d3⟩ hdj hdk
      have : 2 * 2 ^ j < 2 ^ C.Wd := by
        rw [← pow_succ']; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
      refine Hs.mono (hs_shl C xK2 d (by rw [d1]; exact this)) le_rfl ?_
      rintro e rfl
      refine ⟨⟨by vsimp [d1]; ring, d2.trans (Same.set _ _ _), Fr.trans d3 (Fr.set d _ (by decide))⟩, ?_, ?_⟩
      · rw [DS.set_env_ne _ _ (by decide)]; exact hdj
      · rw [DS.set_env_ne _ _ (by decide)]; exact hdk)
  exact Hs.mono hl le_rfl (fun d ⟨h, _, _⟩ => h)

/-- The set-up program. -/
def setupG : St VV MM := .seq preS (.seq clogP (.seq midS (.seq (forS jx xk (.op (.shl xK2)))
  (.seq (.op (.copy xGr xG1)) (.op (.add xGr xG2))))))

theorem setupG_spec (C : Ctx) (b : DS VV MM) (hc : Cst b) (n k G1 G2 : ℕ) (hn : b.env gN = n) (hk : b.env xk = k)
    (hkn : k ≤ n) (h1 : b.env xG1 = G1) (h2 : b.env xG2 = G2) (hbig : 8 * (n + 1) ^ 2 < 2 ^ C.Wd) (hkW : k < C.Wd)
    (hG : G1 + G2 < 2 ^ C.Wd) :
    Hs C setupG b (5 * n + 5 * k + 60) (fun d => d.env xs = n - k ∧ d.env xB = Call.B0 n ∧ d.env xK2 = 2 ^ k ∧
      d.env xGr = G1 + G2 ∧ Same b d ∧ Fr b d setupT) := by
  have hclog : Nat.clog 2 (n + 1) ≤ n + 1 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self).le
  have hnW : n + 1 < 2 ^ C.Wd := by nlinarith
  have hW2 : 2 * (n + 1) ≤ 2 ^ C.Wd := by nlinarith
  have hmb : 4 * (n * Nat.clog 2 (n + 1)) < 2 ^ C.Wd := by
    have : n * Nat.clog 2 (n + 1) ≤ n * (n + 1) := Nat.mul_le_mul_left _ hclog
    nlinarith
  unfold setupG
  refine Hs.mono (Hs.seq (t1 := 11) (t2 := (Nat.clog 2 (n + 1) * (3 + 2) + 2) + (7 + ((k * (1 + 4) + 4) + (1 + 1 + 1)
    + 1) + 1) + 1) (preS_spec C b hc n k hn hk hkn hnW) (fun d1 ⟨s1, c1', p1, t1, m1, f1⟩ => ?_)) (by omega)
    (fun _ h => h)
  refine Hs.seq (t1 := Nat.clog 2 (n + 1) * (3 + 2) + 2) (clog_spec C n d1 p1 c1' t1 hW2)
    (fun d2 ⟨c2, m2, f2⟩ => ?_)
  have d2n : d2.env gN = n := by rw [f2 gN (by decide), f1 gN (by decide), hn]
  have d2c : Cst d2 := Cst.of_fr (Cst.of_fr hc f1 (by decide)) f2 (by decide)
  refine Hs.seq (t1 := 7) (midS_spec C d2 d2c n d2n c2 hmb) (fun d3 ⟨B3, K3, m3, f3⟩ => ?_)
  have d3k : d3.env xk = k := by rw [f3 xk (by decide), f2 xk (by decide), f1 xk (by decide), hk]
  refine Hs.seq (t1 := k * (1 + 4) + 4) (t2 := 1 + 1 + 1) (pow2_spec C d3 k d3k K3 hkW) (fun d4 ⟨K4, m4, f4⟩ => ?_)
  have d4G1 : d4.env xG1 = G1 := by
    rw [f4 xG1 (by decide), f3 xG1 (by decide), f2 xG1 (by decide), f1 xG1 (by decide), h1]
  have d4G2 : d4.env xG2 = G2 := by
    rw [f4 xG2 (by decide), f3 xG2 (by decide), f2 xG2 (by decide), f1 xG2 (by decide), h2]
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C xGr xG1 d4 (by decide)) (fun e he => ?_)
  subst he
  refine Hs.mono (hs_add C xGr xG2 _ (by decide) (by vsimp [d4G1, d4G2]; omega)) le_rfl ?_
  rintro r rfl
  refine ⟨?_, ?_, ?_, by vsimp [d4G1, d4G2], ?_, ?_⟩
  · vsimp []; rw [f4 xs (by decide), f3 xs (by decide), f2 xs (by decide), s1]
  · vsimp []; rw [f4 xB (by decide), B3]
  · vsimp [K4]
  · exact m1.trans (m2.trans (m3.trans (m4.trans ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩)))
  · intro y hy
    have hy' := hy
    simp only [setupT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
    obtain ⟨_, hxc, hxp, _, hxB, hxK, hjx, hGr⟩ := hy'
    vsimp [Function.update_apply, hGr]
    rw [f4 y (by simp; exact ⟨hjx, hxK⟩), f3 y (by simp; exact ⟨hxB, hxK⟩), f2 y (by simp; exact ⟨hxp, hxc⟩),
      f1 y hy]

/-! ## The blocks of prefixes -/

def resBlock : St VV MM := .ite (.eq gKd v2) (.seq (resPre (some false)) (resPre (some true))) (resPre none)
def momBlock : St VV MM := .seq (momPre 0) (.ite (.eq gKd v1) (momPre 1) (.op (.zero yJ)))

theorem GS.trX {C : Ctx} {a d : DS VV MM} {c : Call} {p : Params} {wt : Wit c.n} {Λ : ℕ} (h : GS C a c p wt Λ)
    (e : d.ram = a.ram) (f : Fr a d (x2G :: TA)) (v : Valid C d) : GS C d c p wt Λ := by
  refine ⟨v, Cst.of_fr h.cst f (by decide), h.W2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [e]; exact h.rG1, by rw [e]; exact h.rG2, by rw [e]; exact h.rP, by rw [e]; exact h.rI, h.card, h.resG,
    h.LW, h.Λn, h.Λk, h.Λs, h.ΛB, h.ΛK2, h.ΛG1, h.ΛG2, h.ΛGr, h.Λ2G1, h.Λ2G2, h.Λb1, h.Λb2, h.ΛI, h.Λkk⟩
  · rw [f gN (by decide)]; exact h.n
  · rw [f gKd (by decide)]; exact h.tag
  · rw [f xk (by decide)]; exact h.k
  · rw [f xs (by decide)]; exact h.s
  · rw [f xB (by decide)]; exact h.B
  · rw [f xK2 (by decide)]; exact h.K2
  · rw [f xG1 (by decide)]; exact h.G1
  · rw [f xG2 (by decide)]; exact h.G2
  · rw [f xGr (by decide)]; exact h.Gr
  · rw [f xm1 (by decide)]; exact h.m1
  · rw [f xm2 (by decide)]; exact h.m2
  · rw [f xnp (by decide)]; exact h.np
  · rw [f xkk (by decide)]; exact h.kk

theorem resBlockO (C : Ctx) {a : DS VV MM} {c : Call} {p : Params} {wt : Wit c.n} {Λ : ℕ} (h : GS C a c p wt Λ) :
    OutT C resBlock a (preCost c p wt Λ + preCost c p wt Λ + 1 + 1)
      ((parts c).flatMap (fun part => frame (resPrefix c p wt part))) TA := by
  unfold resBlock
  refine Hs.ite (c := .eq gKd v2) (show gKd ≠ v2 by decide) (fun hk => ?_) (fun hk => ?_)
  · have hpar : c.kind = .parity := by
      have : a.env gKd = 2 := by simpa [Cnd.eval, h.cst.two] using hk
      rw [h.tag] at this
      cases hc : c.kind <;> simp [hc, kindTag] at this ⊢
    refine (seqT (resPreO C h (some false)) (fun d e o f v => resPreO C (h.tr e f v) (some true))).eq ?_
    simp [parts, hpar]
  · have hpar : c.kind ≠ .parity := by
      have : a.env gKd ≠ 2 := by simpa [Cnd.eval, h.cst.two] using hk
      rw [h.tag] at this
      intro hc; rw [hc] at this; exact this rfl
    refine ((resPreO C h none).mono (by omega)).eq ?_
    simp [parts, hpar]

theorem momBlockO (C : Ctx) {a : DS VV MM} {c : Call} {p : Params} {wt : Wit c.n} {Λ : ℕ} (h : GS C a c p wt Λ)
    (h0 : 2 * (circ c 0).gates.length < 2 ^ C.Wd) (h1 : 2 * (circ c 1).gates.length < 2 ^ C.Wd) :
    OutT C momBlock a (preCost c p wt Λ + 3 + (preCost c p wt Λ + 3 + 1) + 1)
      ((List.range (roleCount c.kind)).flatMap (fun ro => frame (momPrefix c p wt ro))) (x2G :: TA) := by
  have hsecond : ∀ d, d.ram = a.ram → Oth a d → Fr a d (x2G :: TA) → Valid C d →
      OutT C (.ite (.eq gKd v1) (momPre 1) (.op (.zero yJ))) d (preCost c p wt Λ + 3 + 1)
        (if c.kind = .pair then frame (momPrefix c p wt 1) else []) (x2G :: TA) := by
    intro d e o f v
    have hd := h.trX e f v
    refine Hs.ite (c := .eq gKd v1) (show gKd ≠ v1 by decide) (fun hk => ?_) (fun hk => ?_)
    · have hpair : c.kind = .pair := by
        have : d.env gKd = 1 := by simpa [Cnd.eval, hd.cst.one] using hk
        rw [hd.tag] at this
        cases hc : c.kind <;> simp [hc, kindTag] at this ⊢
      rw [if_pos hpair]
      exact momPreO C hd 1 h1
    · have hpair : c.kind ≠ .pair := by
        have : d.env gKd ≠ 1 := by simpa [Cnd.eval, hd.cst.one] using hk
        rw [hd.tag] at this
        intro hc; rw [hc] at this; exact this rfl
      rw [if_neg hpair]
      refine Hs.mono (Hs.valid (hs_zero C yJ d) v (by have := h.W2; omega)) (by omega) ?_
      rintro g ⟨rfl, gv⟩
      exact ⟨by simp, rfl, ⟨rfl, rfl, rfl, rfl⟩, Fr.set d _ (by decide), gv⟩
  unfold momBlock
  refine (seqT (momPreO C h 0 h0) hsecond).eq ?_
  cases hc : c.kind <;> simp [roleCount, List.range_succ]

end NearCubicGates.Close.CounterMachine.PrefixProg
