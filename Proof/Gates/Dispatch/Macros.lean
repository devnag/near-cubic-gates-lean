import Proof.Gates.Dispatch.Hs
import Proof.Gates.Interfaces.Counter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces

/-- Number of variables of the dispatch program. -/
abbrev VV : ℕ := 256

def vZ : Fin VV := ⟨0, by decide⟩
def v1 : Fin VV := ⟨1, by decide⟩
def v2 : Fin VV := ⟨2, by decide⟩
def vJ : Fin VV := ⟨3, by decide⟩
def vPOS : Fin VV := ⟨4, by decide⟩
def t0 : Fin VV := ⟨5, by decide⟩
def t1 : Fin VV := ⟨6, by decide⟩
def t2 : Fin VV := ⟨7, by decide⟩
def t3 : Fin VV := ⟨8, by decide⟩
def t4 : Fin VV := ⟨9, by decide⟩
def t5 : Fin VV := ⟨10, by decide⟩
def t6 : Fin VV := ⟨11, by decide⟩
def t7 : Fin VV := ⟨12, by decide⟩
def t8 : Fin VV := ⟨13, by decide⟩
def t9 : Fin VV := ⟨14, by decide⟩

@[simp] theorem DS.env_set (a : DS VV) (x : Fin VV) (v : ℕ) : (a.set x v).env = Function.update a.env x v := rfl

/-- The program-wide constants. -/
structure Cst (a : DS VV) : Prop where
  z : a.env vZ = 0
  one : a.env v1 = 1
  two : a.env v2 = 2
  pos : a.env vPOS = a.cp

variable {C : Ctx}

/-! ## Basics -/

/-- No effect (clears the junk variable). -/
def skipS : St VV := .op (.zero vJ)

theorem skip_spec (a : DS VV) : Hs C skipS a 1 (· = a.set vJ 0) := hs_zero C vJ a

/-- Add a constant. -/
def incS (x : Fin VV) : ℕ → St VV
  | 0 => skipS
  | k + 1 => .seq (.op (.inc x)) (incS x k)

theorem incS_spec (x : Fin VV) (hx : x ≠ vJ) :
    ∀ (k : ℕ) (a : DS VV), a.env x + k < 2 ^ C.Wd →
      Hs C (incS x k) a (2 * k + 1) (fun b => b.env x = a.env x + k ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧
        Fr a b [x, vJ]) := by
  intro k
  induction k with
  | zero =>
    intro a _
    refine Hs.mono (skip_spec a) le_rfl ?_
    rintro b rfl
    refine ⟨by rw [DS.set_env_ne _ _ hx]; rfl, rfl, rfl, rfl, Fr.set a 0 (by simp)⟩
  | succ k ih =>
    intro a hk
    refine Hs.mono (Hs.seq (hs_inc C x a (by omega)) (fun b hb => ?_)) (by omega : 1 + (2 * k + 1) + 1 ≤ _) (fun _ h => h)
    subst hb
    refine Hs.mono (ih _ (by simp; omega)) le_rfl ?_
    rintro d ⟨h1, h2, h3, h4, h5⟩
    refine ⟨by simp at h1; omega, by simpa using h2, by simpa using h3, by simpa using h4, ?_⟩
    exact Fr.trans (Fr.set a _ (by simp)) h5

/-- `x := k`. -/
def setK (x : Fin VV) (k : ℕ) : St VV := .seq (.op (.zero x)) (incS x k)

theorem setK_spec (x : Fin VV) (hx : x ≠ vJ) (k : ℕ) (a : DS VV) (hk : k < 2 ^ C.Wd) :
    Hs C (setK x k) a (2 * k + 3) (fun b => b.env x = k ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧
      Fr a b [x, vJ]) := by
  refine Hs.mono (Hs.seq (hs_zero C x a) (fun b hb => ?_)) (by omega : 1 + (2 * k + 1) + 1 ≤ _) (fun _ h => h)
  subst hb
  refine Hs.mono (incS_spec x hx k _ (by simpa using hk)) le_rfl ?_
  rintro d ⟨h1, h2, h3, h4, h5⟩
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4,
    Fr.trans (Fr.set a 0 (by simp)) h5⟩

/-- Print a constant word. -/
def emitL : List Bool → St VV
  | [] => skipS
  | b :: bs => .seq (.op (.emit b)) (emitL bs)

theorem emitL_spec : ∀ (l : List Bool) (a : DS VV),
    Hs C (emitL l) a (2 * l.length + 1) (fun b => b.out = a.out ++ l ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ Fr a b [vJ]) := by
  intro l
  induction l with
  | nil =>
    intro a
    refine Hs.mono (skip_spec a) le_rfl ?_
    rintro b rfl
    exact ⟨by simp [DS.set], rfl, rfl, Fr.set a 0 (by simp)⟩
  | cons x l ih =>
    intro a
    refine Hs.mono (Hs.seq (hs_emit C x a) (fun b hb => ?_)) (by simp; omega : 1 + (2 * l.length + 1) + 1 ≤ _)
      (fun _ h => h)
    subst hb
    refine Hs.mono (ih _) le_rfl ?_
    rintro d ⟨h1, h2, h3, h4⟩
    exact ⟨by simp [h1], h2, h3, fun y hy => h4 y hy⟩

/-- Print the bit held (as `0`/`1`) in `x`. -/
def emitB (x : Fin VV) : St VV := .ite (.eq x v1) (.op (.emit true)) (.op (.emit false))

theorem emitB_spec (x : Fin VV) (hx : x ≠ v1) (a : DS VV) (hc : Cst a) :
    Hs C (emitB x) a 2 (fun b => b.out = a.out ++ [decide (a.env x = 1)] ∧ b.cp = a.cp ∧ b.wq = a.wq ∧ b.env = a.env) := by
  refine Hs.ite (c := .eq x v1) hx (fun he => ?_) (fun he => ?_)
  · refine Hs.mono (hs_emit C true a) le_rfl ?_
    rintro b rfl
    simp only [Cnd.eval, hc.one, decide_eq_true_eq] at he
    simp [he]
  · refine Hs.mono (hs_emit C false a) le_rfl ?_
    rintro b rfl
    simp only [Cnd.eval, hc.one, decide_eq_false_iff_not] at he
    simp [he]

/-! ## Reading the call word -/

/-- Read one call-word bit into `t0`, keeping `vPOS` equal to the cursor. -/
def rdc : St VV := .seq (.op (.rdC t0)) (.op (.inc vPOS))

theorem rdc_spec (a : DS VV) (hpos : a.env vPOS = a.cp) (hlt : a.cp < C.cw.length)
    (hW : C.cw.length < 2 ^ C.Wd) :
    Hs C rdc a 3 (fun b => b.env t0 = bitOf C.cw a.cp ∧ b.env vPOS = a.cp + 1 ∧ b.cp = a.cp + 1 ∧ b.wq = a.wq ∧
      b.out = a.out ∧ Fr a b [t0, vPOS]) := by
  refine Hs.mono (Hs.seq (t2 := 1) (hs_rdC C t0 a hlt) (fun b hb => ?_)) le_rfl (fun _ h => h)
  subst hb
  refine Hs.mono (hs_inc C vPOS _ (by vsimp [hpos]; omega)) le_rfl ?_
  rintro d rfl
  refine ⟨by vsimp [], by vsimp [hpos], rfl, rfl, rfl, ?_⟩
  intro y hy
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  vsimp [Function.update_of_ne hy.1, Function.update_of_ne hy.2]

/-! ### natWord facts -/

theorem natWord_eq (v : ℕ) : natWord v =
    List.replicate (natBitLength v) true ++ false :: List.ofFn (fun i : Fin (natBitLength v) => v.testBit i.val) := rfl

theorem natWord_length (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 := by
  rw [natWord_eq]; simp; ring

theorem natWord_one (v j : ℕ) (hj : j < natBitLength v) : (natWord v).getD j false = true := by
  rw [natWord_eq, List.getD_append _ _ _ _ (by simpa using hj)]
  simp [List.getD_eq_getElem?_getD, hj]

theorem natWord_zero (v : ℕ) : (natWord v).getD (natBitLength v) false = false := by
  rw [natWord_eq, List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem natWord_bit (v k : ℕ) (hk : k < natBitLength v) :
    (natWord v).getD (natBitLength v + 1 + k) false = v.testBit k := by
  rw [natWord_eq, List.getD_append_right _ _ _ _ (by simp; omega)]
  simp only [List.length_replicate, show natBitLength v + 1 + k - natBitLength v = k + 1 by omega,
    List.getD_cons_succ]
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]
  simp

theorem lt_natBitLength (v : ℕ) : v < 2 ^ natBitLength v := by
  unfold natBitLength; exact Nat.lt_pow_succ_log_self (by norm_num) v

theorem bitOf_drop {cw u rest : List Bool} {cp : ℕ} (h : cw.drop cp = u ++ rest) (j : ℕ) (hj : j < u.length) :
    bitOf cw (cp + j) = (u.getD j false).toNat := by
  unfold bitOf
  have : cw.getD (cp + j) false = (cw.drop cp).getD j false := by
    simp [List.getD_eq_getElem?_getD]
  rw [this, h, List.getD_append _ _ _ _ hj]

theorem lt_of_drop {cw u rest : List Bool} {cp : ℕ} (h : cw.drop cp = u ++ rest) (j : ℕ) (hj : j < u.length) :
    cp + j < cw.length := by
  have := congrArg List.length h
  simp at this; omega

theorem drop_adv {cw u rest : List Bool} {cp : ℕ} (h : cw.drop cp = u ++ rest) : cw.drop (cp + u.length) = rest := by
  rw [← List.drop_drop, h, List.drop_left]

theorem natBitLength_pos (v : ℕ) : 1 ≤ natBitLength v := by unfold natBitLength; omega

theorem Cst.of_fr {a b : DS VV} {T : List (Fin VV)} (hc : Cst a) (hf : Fr a b T) (hT : vZ ∉ T ∧ v1 ∉ T ∧ v2 ∉ T)
    (hp : b.env vPOS = b.cp) : Cst b :=
  ⟨by rw [hf vZ hT.1]; exact hc.z, by rw [hf v1 hT.2.1]; exact hc.one, by rw [hf v2 hT.2.2]; exact hc.two, hp⟩

/-- Read one `natWord` at the cursor: value into `t3`, its bit length into `t4`. Scratch `t0 t1 t2`. -/
def readNat : St VV :=
  .seq (.op (.zero t4)) (.seq rdc (.seq (.loop (.eq t0 v1) (.seq (.op (.inc t4)) rdc))
    (.seq (.op (.zero t3)) (.seq (.op (.copy t1 v1)) (.seq (.op (.zero t2))
      (.loop (.lt t2 t4) (.seq rdc (.seq (.ite (.eq t0 v1) (.op (.add t3 t1)) skipS)
        (.seq (.op (.shl t1)) (.op (.inc t2)))))))))))

/-- Its frame. -/
def readNatT : List (Fin VV) := [t0, t1, t2, t3, t4, vJ, vPOS]

theorem readNat_spec (a : DS VV) (hc : Cst a) (v : ℕ) (rest : List Bool) (hcw : C.cw.drop a.cp = natWord v ++ rest)
    (hW : natBitLength v + 2 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) :
    Hs C readNat a (30 * natBitLength v + 30) (fun b => b.env t3 = v ∧ b.env t4 = natBitLength v ∧
      b.cp = a.cp + (natWord v).length ∧ b.wq = a.wq ∧ b.out = a.out ∧ Cst b ∧ Fr a b readNatT) := by
  set ℓ := natBitLength v with hℓ
  have hlen := natWord_length v
  have hpw : 2 ^ (ℓ + 1) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hvl : v < 2 ^ ℓ := lt_natBitLength v
  have hℓW : ℓ + 1 < 2 ^ C.Wd := lt_of_lt_of_le (Nat.lt_two_pow_self) hpw
  have hv1 := hc.one
  -- phase 1: count the leading ones
  let I1 : ℕ → DS VV → Prop := fun k b => b.env t4 = k ∧ b.env t0 = bitOf C.cw (a.cp + k) ∧
      b.cp = a.cp + k + 1 ∧ b.env vPOS = b.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Fr a b readNatT
  have p1 : ∀ b, Fr (a.set t4 0) b [t0, vPOS] → b.env t0 = bitOf C.cw a.cp → b.env vPOS = a.cp + 1 →
      b.cp = a.cp + 1 → b.wq = a.wq → b.out = a.out → I1 0 b := by
    intro d h6 h1 h2 h3 h4 h5
    refine ⟨by rw [h6 t4 (by decide)]; vsimp [], by simpa using h1, by simpa using h3, by rw [h2, h3],
      h4, h5, Fr.trans (Fr.set a 0 (by decide)) (Fr.weaken h6 (by decide))⟩
  have l1 : ∀ b, I1 0 b → Hs C (.loop (.eq t0 v1) (.seq (.op (.inc t4)) rdc)) b (ℓ * (5 + 2) + 2) (I1 ℓ) := by
    refine Hs.loopN (c := .eq t0 v1) (show t0 ≠ v1 by decide) I1 ℓ 5 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7⟩
      have bv1 : b.env v1 = 1 := by rw [h7 v1 (by decide)]; exact hv1
      refine ⟨?_, ?_⟩
      · simp only [Cnd.eval, h2, bv1, decide_eq_true_eq]
        rw [bitOf_drop hcw k (by omega), natWord_one v k hk]; rfl
      · refine Hs.mono (Hs.seq (t2 := 3) (hs_inc C t4 b (by rw [h1]; omega)) (fun d hd => ?_)) le_rfl
          (fun _ h => h)
        subst hd
        refine Hs.mono (rdc_spec _ (by vsimp [h4]) (by
          show b.cp < _; rw [h3]; exact lt_of_drop hcw (k + 1) (by omega)) (by omega)) le_rfl ?_
        rintro e ⟨e1, e2, e3, e4, e5, e6⟩
        refine ⟨by rw [e6 t4 (by decide)]; vsimp [h1], by rw [e1]; show bitOf C.cw b.cp = _; rw [h3]; ring_nf,
          by rw [e3]; show b.cp + 1 = _; rw [h3]; ring, by rw [e2, e3], by simpa [h5] using e4,
          by simpa [h6] using e5, ?_⟩
        exact Fr.trans h7 (Fr.trans (Fr.set b _ (by decide)) (Fr.weaken e6 (by decide)))
    · intro b ⟨h1, h2, h3, h4, h5, h6, h7⟩
      have bv1 : b.env v1 = 1 := by rw [h7 v1 (by decide)]; exact hv1
      simp only [Cnd.eval, h2, bv1, decide_eq_false_iff_not]
      rw [bitOf_drop hcw ℓ (by omega), natWord_zero v]; simp
  -- phase 2: the bits
  let I2 : ℕ → DS VV → Prop := fun k b => b.env t2 = k ∧ b.env t4 = ℓ ∧ b.env t3 = v % 2 ^ k ∧ b.env t1 = 2 ^ k ∧
      b.cp = a.cp + ℓ + 1 + k ∧ b.env vPOS = b.cp ∧ b.wq = a.wq ∧ b.out = a.out ∧ Fr a b readNatT
  have l2 : ∀ b, I2 0 b → Hs C (.loop (.lt t2 t4) (.seq rdc (.seq (.ite (.eq t0 v1) (.op (.add t3 t1)) skipS)
      (.seq (.op (.shl t1)) (.op (.inc t2)))))) b (ℓ * (10 + 2) + 2) (I2 ℓ) := by
    refine Hs.loopN (c := .lt t2 t4) (show t2 ≠ t4 by decide) I2 ℓ 10 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      have bv1 : b.env v1 = 1 := by rw [h9 v1 (by decide)]; exact hv1
      refine ⟨by simp [Cnd.eval, h1, h2, hk], ?_⟩
      have hpk : 2 ^ (k + 1) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hk
      refine Hs.mono (Hs.seq (t2 := 6) (rdc_spec b h6 (by
          rw [h5]; have := lt_of_drop hcw (ℓ + 1 + k) (by omega); omega) (by omega)) (fun d hd => ?_)) le_rfl
        (fun _ h => h)
      obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
      have hbit : d.env t0 = (v.testBit k).toNat := by
        rw [d1, h5, show a.cp + ℓ + 1 + k = a.cp + (ℓ + 1 + k) by ring, bitOf_drop hcw _ (by omega),
          natWord_bit v k hk]
      have dt3 : d.env t3 = v % 2 ^ k := by rw [d6 t3 (by decide), h3]
      have dt1 : d.env t1 = 2 ^ k := by rw [d6 t1 (by decide), h4]
      have dv1 : d.env v1 = 1 := by rw [d6 v1 (by decide), bv1]
      have hmod : v % 2 ^ (k + 1) = v % 2 ^ k + (v.testBit k).toNat * 2 ^ k := by
        rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
        rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ k) with hm | hm <;> simp [hm] <;> ring
      have hsum : v % 2 ^ k + 2 ^ k < 2 ^ C.Wd := by
        have := Nat.mod_lt v (show 0 < 2 ^ k by positivity)
        have : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by ring
        omega
      -- the conditional add
      have step2 : Hs C (.ite (.eq t0 v1) (.op (.add t3 t1)) skipS) d 2 (fun e => e.env t3 = v % 2 ^ (k + 1) ∧
          e.cp = d.cp ∧ e.wq = d.wq ∧ e.out = d.out ∧ Fr d e [t3, vJ]) := by
        refine Hs.ite (c := .eq t0 v1) (show t0 ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
        · have hb : v.testBit k = true := by
            revert he; simp only [Cnd.eval, hbit, dv1]; cases v.testBit k <;> simp
          refine Hs.mono (hs_add C t3 t1 d (by decide) (by rw [dt3, dt1]; exact hsum)) le_rfl ?_
          rintro e rfl
          refine ⟨by vsimp [dt3, dt1, hmod, hb], rfl, rfl, rfl, Fr.set d _ (by decide)⟩
        · have hb : v.testBit k = false := by
            revert he; simp only [Cnd.eval, hbit, dv1]; cases v.testBit k <;> simp
          refine Hs.mono (skip_spec d) le_rfl ?_
          rintro e rfl
          refine ⟨by vsimp [dt3, hmod, hb], rfl, rfl, rfl, Fr.set d _ (by decide)⟩
      refine Hs.mono (Hs.seq (t2 := 3) step2 (fun e he => ?_)) le_rfl (fun _ h => h)
      obtain ⟨e1, e2, e3, e4, e5⟩ := he
      have et1 : e.env t1 = 2 ^ k := by rw [e5 t1 (by decide), dt1]
      have et2 : e.env t2 = k := by rw [e5 t2 (by decide), d6 t2 (by decide), h1]
      have et4 : e.env t4 = ℓ := by rw [e5 t4 (by decide), d6 t4 (by decide), h2]
      have ePOS : e.env vPOS = e.cp := by rw [e5 vPOS (by decide), d2, e2, d3]
      have h2k : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
      refine Hs.mono (Hs.seq (t2 := 1) (hs_shl C t1 e (by rw [et1]; omega)) (fun f hf => ?_)) le_rfl (fun _ h => h)
      subst hf
      refine Hs.mono (hs_inc C t2 _ (by vsimp [et2]; omega)) le_rfl ?_
      rintro g rfl
      refine ⟨by vsimp [et2], by vsimp [et4], by vsimp [e1], by vsimp [et1] <;> ring,
        by vsimp [e2, d3, h5] <;> ring, by vsimp [ePOS], by vsimp [e3, d4, h7], by vsimp [e4, d5, h8], ?_⟩
      refine Fr.trans h9 (Fr.trans (Fr.weaken d6 (by decide)) (Fr.trans (Fr.weaken e5 (by decide))
        (Fr.trans (Fr.set e _ (by decide)) (Fr.set _ _ (by decide)))))
    · intro b ⟨h1, h2, _⟩
      simp [Cnd.eval, h1, h2]
  -- the whole
  refine Hs.mono (Hs.seq (hs_zero C t4 a) (fun b0 hb0 => ?_)) (show 1 + (3 + (ℓ * (5 + 2) + 2 + (1 + (1 + (1 +
    (ℓ * (10 + 2) + 2) + 1) + 1) + 1) + 1) + 1) + 1 ≤ 30 * ℓ + 30 by omega) (fun _ h => h)
  subst hb0
  refine Hs.seq (rdc_spec _ (by vsimp [hc.pos]) (lt_of_drop hcw 0 (by omega)) (by omega)) (fun b1 hb1 => ?_)
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hb1
  have hI : I1 0 b1 := p1 b1 q6 q1 q2 (by simpa using q3) (by simpa using q4) (by simpa using q5)
  refine Hs.seq (l1 b1 hI) (fun d hd => ?_)
  obtain ⟨d1, d2, d3, d4, d5, d6, d7⟩ := hd
  have dv1 : d.env v1 = 1 := by rw [d7 v1 (by decide)]; exact hv1
  refine Hs.seq (hs_zero C t3 d) (fun e he => ?_)
  subst he
  refine Hs.seq (hs_copy C t1 v1 _ (by decide)) (fun f hf => ?_)
  subst hf
  refine Hs.seq (hs_zero C t2 _) (fun g hg => ?_)
  subst hg
  refine Hs.mono (l2 _ ⟨by vsimp [], by vsimp [d1], by vsimp [Nat.mod_one], by vsimp [dv1], by vsimp [d3], by vsimp [d4, d3],
    by vsimp [d5], by vsimp [d6], ?_⟩) le_rfl ?_
  · exact Fr.trans d7 (Fr.trans (Fr.set d _ (by decide)) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
  · rintro r ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9⟩
    refine ⟨by rw [r3, Nat.mod_eq_of_lt hvl], r2, by rw [r5, hlen]; ring, r7, r8, ?_, r9⟩
    exact Cst.of_fr hc r9 (by decide) r6

/-! ## Printing a `natWord` -/

theorem lt_div_iff_lt_log (v k : ℕ) (hk : k ≤ Nat.log 2 v) : (1 < v / 2 ^ k ↔ k < Nat.log 2 v) := by
  rcases Nat.eq_zero_or_pos v with hv | hv
  · subst hv; simp at hk; subst hk; simp
  · rw [show (1 < v / 2 ^ k) ↔ 2 ^ (k + 1) ≤ v from ?_, ← Nat.le_log_iff_pow_le (by norm_num) (by omega)]
    · omega
    · rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le (by positivity), pow_succ]; ring_nf

theorem ofFn_testBit (v ℓ : ℕ) : List.ofFn (fun i : Fin ℓ => v.testBit i.val) = (List.range ℓ).map v.testBit := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- Print `natWord (t3)`. Scratch `t5 … t9`. -/
def emitNat : St VV :=
  .seq (.op (.copy t5 t3)) (.seq (.op (.zero t6)) (.seq (.loop (.lt v1 t5) (.seq (.op (.half t5)) (.op (.inc t6))))
    (.seq (.op (.inc t6)) (.seq (.op (.zero t7)) (.seq (.loop (.lt t7 t6) (.seq (.op (.emit true)) (.op (.inc t7))))
      (.seq (.op (.emit false)) (.seq (.op (.copy t5 t3)) (.seq (.op (.zero t7))
        (.loop (.lt t7 t6) (.seq (.op (.dm t5 v2 t8 t9)) (.seq (emitB t9) (.seq (.op (.copy t5 t8))
          (.op (.inc t7))))))))))))))

def emitNatT : List (Fin VV) := [t5, t6, t7, t8, t9]

theorem emitNat_spec (a : DS VV) (hc : Cst a) (hW : 2 ≤ C.Wd) (hv : natBitLength (a.env t3) + 2 < 2 ^ C.Wd) :
    Hs C emitNat a (40 * natBitLength (a.env t3) + 40) (fun b => b.out = a.out ++ natWord (a.env t3) ∧
      b.cp = a.cp ∧ b.wq = a.wq ∧ Cst b ∧ Fr a b emitNatT) := by
  set v := a.env t3 with hvdef
  set ℓ := natBitLength v with hℓ
  have hℓl : ℓ = Nat.log 2 v + 1 := rfl
  have hv1 := hc.one
  have hv2 := hc.two
  have h4 : (4 : ℕ) ≤ 2 ^ C.Wd := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hW
  -- loop 1: the logarithm
  let I1 : ℕ → DS VV → Prop := fun k b => b.env t5 = v / 2 ^ k ∧ b.env t6 = k ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
    b.out = a.out ∧ Fr a b emitNatT
  have l1 : ∀ b, I1 0 b → Hs C (.loop (.lt v1 t5) (.seq (.op (.half t5)) (.op (.inc t6)))) b
      (Nat.log 2 v * (3 + 2) + 2) (I1 (Nat.log 2 v)) := by
    refine Hs.loopN (c := .lt v1 t5) (show v1 ≠ t5 by decide) I1 _ 3 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4', h5, h6⟩
      have bv1 : b.env v1 = 1 := by rw [h6 v1 (by decide)]; exact hv1
      refine ⟨by simp only [Cnd.eval, bv1, h1, decide_eq_true_eq]; exact (lt_div_iff_lt_log v k hk.le).2 hk, ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_half C t5 b) (fun d hd => ?_)
      subst hd
      refine Hs.mono (hs_inc C t6 _ (by vsimp [h2]; omega)) le_rfl ?_
      rintro e rfl
      refine ⟨by vsimp [h1, Nat.div_div_eq_div_mul, pow_succ], by vsimp [h2], h3, h4', h5, ?_⟩
      exact Fr.trans h6 (Fr.trans (Fr.set b _ (by decide)) (Fr.set _ _ (by decide)))
    · intro b ⟨h1, _, _, _, _, h6⟩
      have bv1 : b.env v1 = 1 := by rw [h6 v1 (by decide)]; exact hv1
      simp only [Cnd.eval, bv1, h1, decide_eq_false_iff_not]
      exact fun h => absurd ((lt_div_iff_lt_log v _ le_rfl).1 h) (lt_irrefl _)
  -- loop 2: ℓ ones
  let I2 : ℕ → DS VV → Prop := fun k b => b.env t7 = k ∧ b.env t6 = ℓ ∧ b.cp = a.cp ∧ b.wq = a.wq ∧
    b.out = a.out ++ List.replicate k true ∧ Fr a b emitNatT
  have l2 : ∀ b, I2 0 b → Hs C (.loop (.lt t7 t6) (.seq (.op (.emit true)) (.op (.inc t7)))) b (ℓ * (3 + 2) + 2)
      (I2 ℓ) := by
    refine Hs.loopN (c := .lt t7 t6) (show t7 ≠ t6 by decide) I2 _ 3 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4', h5, h6⟩
      refine ⟨by simp [Cnd.eval, h1, h2, hk], ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_emit C true b) (fun d hd => ?_)
      subst hd
      refine Hs.mono (hs_inc C t7 _ (by vsimp [h1]; omega)) le_rfl ?_
      rintro e rfl
      refine ⟨by vsimp [h1], by vsimp [h2], h3, h4', by vsimp [h5, List.replicate_succ'], ?_⟩
      exact Fr.trans h6 (Fr.set _ _ (by decide))
    · intro b ⟨h1, h2, _⟩
      simp [Cnd.eval, h1, h2]
  -- loop 3: the bits
  let I3 : ℕ → DS VV → Prop := fun k b => b.env t7 = k ∧ b.env t6 = ℓ ∧ b.env t5 = v / 2 ^ k ∧ b.cp = a.cp ∧
    b.wq = a.wq ∧ b.out = a.out ++ (List.replicate ℓ true ++ [false]) ++ (List.range k).map v.testBit ∧
    Fr a b emitNatT
  have l3 : ∀ b, I3 0 b → Hs C (.loop (.lt t7 t6) (.seq (.op (.dm t5 v2 t8 t9)) (.seq (emitB t9)
      (.seq (.op (.copy t5 t8)) (.op (.inc t7)))))) b (ℓ * (8 + 2) + 2) (I3 ℓ) := by
    refine Hs.loopN (c := .lt t7 t6) (show t7 ≠ t6 by decide) I3 _ 8 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4', h5, h6, h7⟩
      have bv1 : b.env v1 = 1 := by rw [h7 v1 (by decide)]; exact hv1
      have bv2 : b.env v2 = 2 := by rw [h7 v2 (by decide)]; exact hv2
      refine ⟨by simp [Cnd.eval, h1, h2, hk], ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 6) (hs_dm C t5 v2 t8 t9 b (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by rw [bv2]; norm_num) (by rw [bv2]; omega)) (fun d hd => ?_)
      subst hd
      have dc : Cst ((b.set t8 (b.env t5 / b.env v2)).set t9 (b.env t5 % b.env v2)) := by
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), h7 vZ (by decide)]; exact hc.z
        · vsimp [bv1]
        · vsimp [bv2]
        · rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), h7 vPOS (by decide)]
          simp [h4', hc.pos]
      refine Hs.seq (t1 := 2) (t2 := 3) (emitB_spec t9 (by decide) _ dc) (fun e he => ?_)
      obtain ⟨e1, e2, e3, e4⟩ := he
      have et8 : e.env t8 = v / 2 ^ k / 2 := by rw [e4]; vsimp [h3, bv2]
      have et9 : ((b.set t8 (b.env t5 / b.env v2)).set t9 (b.env t5 % b.env v2)).env t9 = v / 2 ^ k % 2 := by
        vsimp [h3, bv2]
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C t5 t8 e (by decide)) (fun f hf => ?_)
      subst hf
      have et7 : e.env t7 = k := by rw [e4]; vsimp [h1]
      refine Hs.mono (hs_inc C t7 _ (by vsimp [et7]; omega)) le_rfl ?_
      rintro g rfl
      have et6 : e.env t6 = ℓ := by rw [e4]; vsimp [h2]
      refine ⟨by vsimp [et7], by vsimp [et6], by vsimp [et8, Nat.div_div_eq_div_mul, pow_succ], by vsimp [e2, h4'],
        by vsimp [e3, h5], ?_, ?_⟩
      · have hb : decide (((b.set t8 (b.env t5 / b.env v2)).set t9 (b.env t5 % b.env v2)).env t9 = 1) =
            v.testBit k := by rw [et9, Nat.testBit_eq_decide_div_mod_eq]
        simp only [DS.set_out]
        rw [e1, hb]
        simp only [DS.set_out, h6, List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
      · intro y hy
        have hy' : y ∉ [t5, t6, t7, t8, t9] := hy
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
        vsimp [Function.update_of_ne hy'.1, Function.update_of_ne hy'.2.2.1, e4, Function.update_of_ne hy'.2.2.2.1,
          Function.update_of_ne hy'.2.2.2.2, h7 y hy]
    · intro b ⟨h1, h2, _⟩
      simp [Cnd.eval, h1, h2]
  -- the whole
  have hlogℓ : Nat.log 2 v < ℓ := by omega
  refine Hx.hs (Hs.then (hs_copy C t5 t3 a (by decide)) (fun b0 hb0 n0 hn0 => ?_))
  subst hb0
  refine Hs.then (hs_zero C t6 _) (fun b1 hb1 n1 hn1 => ?_)
  subst hb1
  refine Hs.then (l1 _ ⟨by vsimp [hvdef], by vsimp [], rfl, rfl, rfl,
    Fr.trans (Fr.set a _ (by decide)) (Fr.set _ _ (by decide))⟩) (fun b2 hb2 n2 hn2 => ?_)
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hb2
  refine Hs.then (hs_inc C t6 b2 (by rw [q2]; omega)) (fun b3 hb3 n3 hn3 => ?_)
  subst hb3
  refine Hs.then (hs_zero C t7 _) (fun b4 hb4 n4 hn4 => ?_)
  subst hb4
  refine Hs.then (l2 _ ⟨by vsimp [], by vsimp [q2, hℓl], q3, q4, by simp [q5],
    Fr.trans q6 (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))⟩) (fun b5 hb5 n5 hn5 => ?_)
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := hb5
  refine Hs.then (hs_emit C false b5) (fun b6 hb6 n6 hn6 => ?_)
  subst hb6
  have b5t3 : b5.env t3 = v := by rw [r6 t3 (by decide)]
  refine Hs.then (hs_copy C t5 t3 _ (by decide)) (fun b7 hb7 n7 hn7 => ?_)
  subst hb7
  refine Hs.then (hs_zero C t7 _) (fun b8 hb8 n8 hn8 => ?_)
  subst hb8
  refine Hs.last (l3 _ ⟨by vsimp [], by vsimp [r2], by vsimp [b5t3], r3, r4, by vsimp [r5], ?_⟩) ?_
  · exact Fr.trans r6 (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))
  · rintro g ⟨g1, g2, g3, g4, g5, g6, g7⟩ n9 hn9
    refine ⟨⟨by rw [g6, natWord_eq, ofFn_testBit, ← hℓ]; simp, g4, g5, ?_, g7⟩, by omega⟩
    exact ⟨by rw [g7 vZ (by decide)]; exact hc.z, by rw [g7 v1 (by decide)]; exact hc.one,
      by rw [g7 v2 (by decide)]; exact hc.two, by rw [g7 vPOS (by decide), g4]; exact hc.pos⟩

end NearCubicGates.Close.Dispatch
