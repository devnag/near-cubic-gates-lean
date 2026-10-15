import Proof.Gates.Cells.Mac

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicWires.RepairRepresentation NearCubicGates.Close.Interfaces

variable {V M : ℕ} {C : Ctx}

def Hx (C : Ctx) (s : St V M) (a : DS V M) (R : DS V M → ℕ → Prop) : Prop := ∃ b n, Ex C s a b n ∧ R b n

theorem Hs.then {s u : St V M} {a : DS V M} {t : ℕ} {R1 : DS V M → Prop} {R : DS V M → ℕ → Prop}
    (h1 : Hs C s a t R1) (h2 : ∀ b, R1 b → ∀ n, n ≤ t → Hx C u b (fun d k => R d (n + k + 1))) :
    Hx C (.seq s u) a R := by
  obtain ⟨b, n, he, hn, hb⟩ := h1
  obtain ⟨d, k, he2, hd⟩ := h2 b hb n hn
  exact ⟨d, n + k + 1, Ex.seq he he2, hd⟩

theorem Hs.last {s : St V M} {a : DS V M} {t : ℕ} {R1 : DS V M → Prop} {R : DS V M → ℕ → Prop}
    (h1 : Hs C s a t R1) (h2 : ∀ b, R1 b → ∀ n, n ≤ t → R b n) : Hx C s a R := by
  obtain ⟨b, n, he, hn, hb⟩ := h1
  exact ⟨b, n, he, h2 b hb n hn⟩

theorem Hx.hs {s : St V M} {a : DS V M} {t : ℕ} {R : DS V M → Prop} (h : Hx C s a (fun b n => R b ∧ n ≤ t)) :
    Hs C s a t R := by
  obtain ⟨b, n, he, hb, hn⟩ := h
  exact ⟨b, n, he, hn, hb⟩

/-! ## The non-variable part of a state -/

/-- Everything but the variables. -/
def DS.sh (a : DS V M) : ℕ × List Bool × (Fin M → List ℕ) × (Fin M → ℕ) × List Bool × List Bool × ℕ :=
  (a.ip, a.out, a.ram, a.rc, a.kin, a.kout, a.kc)

@[simp] theorem DS.sh_set (a : DS V M) (x : Fin V) (v : ℕ) : (a.set x v).sh = a.sh := rfl

theorem Same.of_sh {a b : DS V M} (h : b.sh = a.sh) : Same a b := by
  simp only [DS.sh, Prod.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩

/-- A bit source: a fixed word read at a cursor `pos` by the operation `op x` (into `x`), leaving the rest `rest`
of the state alone. -/
structure Src (C : Ctx) (R : Type) where
  word : List Bool
  pos : DS VV MM → ℕ
  rest : DS VV MM → R
  op : Fin VV → Op VV MM
  nxt : DS VV MM → Fin VV → DS VV MM
  ok : DS VV MM → Prop
  spec : ∀ a x, ok a → pos a < word.length → OpEx C (op x) a (nxt a x) 1
  env : ∀ a x, ok a → (nxt a x).env = Function.update a.env x (bitOf word (pos a))
  posn : ∀ a x, pos (nxt a x) = pos a + 1
  restn : ∀ a x, rest (nxt a x) = rest a
  pos_set : ∀ a y v, pos (a.set y v) = pos a
  rest_set : ∀ a y v, rest (a.set y v) = rest a
  ok_of : ∀ a b, rest b = rest a → ok a → ok b

/-- Read one `natWord`: value into `t3`, bit length into `t4`. Scratch `t0 t1 t2`. -/
def rdNat (rd : Fin VV → Op VV MM) : St VV MM :=
  .seq (.op (.zero t4)) (.seq (.op (rd t0)) (.seq (.loop (.eq t0 v1) (.seq (.op (.inc t4)) (.op (rd t0))))
    (.seq (.op (.zero t3)) (.seq (.op (.copy t1 v1)) (.seq (.op (.zero t2))
      (.loop (.lt t2 t4) (.seq (.op (rd t0)) (.seq (.ite (.eq t0 v1) (.op (.add t3 t1)) skipS)
        (.seq (.op (.shl t1)) (.op (.inc t2)))))))))))

def rdNatT : List (Fin VV) := [t0, t1, t2, t3, t4, vJ]

theorem cst_fr {a b : DS VV MM} (hc : Cst a) (hf : Fr a b rdNatT) : Cst b := Cst.of_fr hc hf (by decide)

theorem src_hs {R : Type} (S : Src C R) (a : DS VV MM) (x : Fin VV) (hok : S.ok a) (hp : S.pos a < S.word.length) :
    Hs C (.op (S.op x)) a 1 (· = S.nxt a x) := Hs.op (S.spec a x hok hp) rfl

theorem rdNat_spec {R : Type} (S : Src C R) (a : DS VV MM) (hc : Cst a) (hok : S.ok a) (v : ℕ) (rest : List Bool)
    (hcw : S.word.drop (S.pos a) = natWord v ++ rest) (hW : natBitLength v + 2 ≤ C.Wd) :
    Hs C (rdNat S.op) a (30 * natBitLength v + 30) (fun b => b.env t3 = v ∧ b.env t4 = natBitLength v ∧
      S.pos b = S.pos a + (natWord v).length ∧ S.rest b = S.rest a ∧ Fr a b rdNatT) := by
  set ℓ := natBitLength v with hℓ
  have hlen := natWord_length v
  have hpw : 2 ^ (ℓ + 1) ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hvl : v < 2 ^ ℓ := lt_natBitLength v
  have hℓW : ℓ + 1 < 2 ^ C.Wd := lt_of_lt_of_le Nat.lt_two_pow_self hpw
  have hv1 := hc.one
  have nenv : ∀ b y, S.ok b → y ≠ t0 → (S.nxt b t0).env y = b.env y := fun b y hb hy => by
    rw [S.env b t0 hb, Function.update_of_ne hy]
  have n0 : ∀ b, S.ok b → (S.nxt b t0).env t0 = bitOf S.word (S.pos b) := fun b hb => by
    rw [S.env b t0 hb, Function.update_self]
  -- phase 1: count the leading ones
  let I1 : ℕ → DS VV MM → Prop := fun k b => b.env t4 = k ∧ b.env t0 = bitOf S.word (S.pos a + k) ∧
      S.pos b = S.pos a + k + 1 ∧ S.rest b = S.rest a ∧ Fr a b rdNatT
  have l1 : ∀ b, I1 0 b → Hs C (.loop (.eq t0 v1) (.seq (.op (.inc t4)) (.op (S.op t0)))) b (ℓ * (3 + 2) + 2)
      (I1 ℓ) := by
    refine Hs.loopN (c := .eq t0 v1) (show t0 ≠ v1 by decide) I1 ℓ 3 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5⟩
      have bv1 : b.env v1 = 1 := by rw [h5 v1 (by decide)]; exact hv1
      refine ⟨?_, ?_⟩
      · simp only [Cnd.eval, h2, bv1, decide_eq_true_eq]
        rw [bitOf_drop hcw k (by omega), natWord_one v k hk]; rfl
      · refine Hs.seq (t1 := 1) (t2 := 1) (hs_inc C t4 b (by rw [h1]; omega)) (fun d hd => ?_)
        subst hd
        have hok' : S.ok (b.set t4 (b.env t4 + 1)) := S.ok_of _ _ (by rw [S.rest_set, h4]) hok
        refine Hs.mono (src_hs S _ t0 hok' (by
          rw [S.pos_set, h3]; have := lt_of_drop hcw (k + 1) (by omega); omega)) le_rfl ?_
        rintro e rfl
        refine ⟨by rw [nenv _ _ hok' (by decide)]; vsimp [h1], by rw [n0 _ hok', S.pos_set, h3]; ring_nf,
          by rw [S.posn, S.pos_set, h3]; ring, by rw [S.restn, S.rest_set, h4], ?_⟩
        refine Fr.trans h5 (Fr.trans (Fr.set b (x := t4) (b.env t4 + 1) (by decide)) ?_)
        intro y hy; exact nenv _ y hok' (fun h => hy (h ▸ by decide))
    · intro b ⟨h1, h2, _, _, h5⟩
      have bv1 : b.env v1 = 1 := by rw [h5 v1 (by decide)]; exact hv1
      simp only [Cnd.eval, h2, bv1, decide_eq_false_iff_not]
      rw [bitOf_drop hcw ℓ (by omega), natWord_zero v]; simp
  -- phase 2: the bits
  let I2 : ℕ → DS VV MM → Prop := fun k b => b.env t2 = k ∧ b.env t4 = ℓ ∧ b.env t3 = v % 2 ^ k ∧
      b.env t1 = 2 ^ k ∧ S.pos b = S.pos a + ℓ + 1 + k ∧ S.rest b = S.rest a ∧ Fr a b rdNatT
  have l2 : ∀ b, I2 0 b → Hs C (.loop (.lt t2 t4) (.seq (.op (S.op t0)) (.seq (.ite (.eq t0 v1) (.op (.add t3 t1))
      skipS) (.seq (.op (.shl t1)) (.op (.inc t2)))))) b (ℓ * (10 + 2) + 2) (I2 ℓ) := by
    refine Hs.loopN (c := .lt t2 t4) (show t2 ≠ t4 by decide) I2 ℓ 10 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h9⟩
      have bv1 : b.env v1 = 1 := by rw [h9 v1 (by decide)]; exact hv1
      have hok' : S.ok b := S.ok_of _ _ h6 hok
      refine ⟨by simp [Cnd.eval, h1, h2, hk], ?_⟩
      have hpk : 2 ^ (k + 1) ≤ 2 ^ ℓ := Nat.pow_le_pow_right (by norm_num) hk
      refine Hs.mono (Hs.seq (t2 := 6) (src_hs S b t0 hok' (by
          rw [h5]; have := lt_of_drop hcw (ℓ + 1 + k) (by omega); omega)) (fun d hd => ?_)) (by norm_num)
        (fun _ h => h)
      subst hd
      set d := S.nxt b t0 with hd
      have hbit : d.env t0 = (v.testBit k).toNat := by
        rw [hd, n0 b hok', h5, show S.pos a + ℓ + 1 + k = S.pos a + (ℓ + 1 + k) by ring, bitOf_drop hcw _ (by omega),
          natWord_bit v k hk]
      have dt3 : d.env t3 = v % 2 ^ k := by rw [hd, nenv b t3 hok' (by decide), h3]
      have dt1 : d.env t1 = 2 ^ k := by rw [hd, nenv b t1 hok' (by decide), h4]
      have dv1 : d.env v1 = 1 := by rw [hd, nenv b v1 hok' (by decide), bv1]
      have hmod : v % 2 ^ (k + 1) = v % 2 ^ k + (v.testBit k).toNat * 2 ^ k := by
        rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
        rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ k) with hm | hm <;> simp [hm] <;> ring
      have hsum : v % 2 ^ k + 2 ^ k < 2 ^ C.Wd := by
        have := Nat.mod_lt v (show 0 < 2 ^ k by positivity)
        have : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by ring
        omega
      have step2 : Hs C (.ite (.eq t0 v1) (.op (.add t3 t1)) skipS) d 2 (fun e => e.env t3 = v % 2 ^ (k + 1) ∧
          S.pos e = S.pos d ∧ S.rest e = S.rest d ∧ Fr d e [t3, vJ]) := by
        refine Hs.ite (c := .eq t0 v1) (show t0 ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
        · have hb : v.testBit k = true := by
            revert he; simp only [Cnd.eval, hbit, dv1]; cases v.testBit k <;> simp
          refine Hs.mono (hs_add C t3 t1 d (by decide) (by rw [dt3, dt1]; exact hsum)) le_rfl ?_
          rintro e rfl
          refine ⟨by vsimp [dt3, dt1, hmod, hb], S.pos_set _ _ _, S.rest_set _ _ _, Fr.set d _ (by decide)⟩
        · have hb : v.testBit k = false := by
            revert he; simp only [Cnd.eval, hbit, dv1]; cases v.testBit k <;> simp
          refine Hs.mono (skip_spec d) le_rfl ?_
          rintro e rfl
          refine ⟨by vsimp [dt3, hmod, hb], S.pos_set _ _ _, S.rest_set _ _ _, Fr.set d _ (by decide)⟩
      refine Hs.mono (Hs.seq (t2 := 3) step2 (fun e he => ?_)) le_rfl (fun _ h => h)
      obtain ⟨e1, e2, e3, e5⟩ := he
      have et1 : e.env t1 = 2 ^ k := by rw [e5 t1 (by decide), dt1]
      have et2 : e.env t2 = k := by rw [e5 t2 (by decide), hd, nenv b t2 hok' (by decide), h1]
      have et4 : e.env t4 = ℓ := by rw [e5 t4 (by decide), hd, nenv b t4 hok' (by decide), h2]
      have h2k : 2 * 2 ^ k = 2 ^ (k + 1) := by ring
      refine Hs.mono (Hs.seq (t2 := 1) (hs_shl C t1 e (by rw [et1]; omega)) (fun f hf => ?_)) le_rfl
        (fun _ h => h)
      subst hf
      refine Hs.mono (hs_inc C t2 _ (by vsimp [et2]; omega)) le_rfl ?_
      rintro g rfl
      refine ⟨by vsimp [et2], by vsimp [et4], by vsimp [e1], by vsimp [et1] <;> ring, ?_, ?_, ?_⟩
      · rw [S.pos_set, S.pos_set, e2, hd, S.posn, h5]; ring
      · rw [S.rest_set, S.rest_set, e3, hd, S.restn, h6]
      · refine Fr.trans h9 (Fr.trans ?_ (Fr.trans (Fr.weaken e5 (by decide))
          (Fr.trans (Fr.set e _ (by decide)) (Fr.set _ _ (by decide)))))
        intro y hy
        rw [hd]; exact nenv b y hok' (fun h => hy (h ▸ by decide))
    · intro b ⟨h1, h2, _⟩
      simp [Cnd.eval, h1, h2]
  -- the whole
  refine Hs.mono (Hs.seq (hs_zero C t4 a) (fun b0 hb0 => ?_)) (show 1 + (1 + (ℓ * (3 + 2) + 2 + (1 + (1 + (1 +
    (ℓ * (10 + 2) + 2) + 1) + 1) + 1) + 1) + 1) + 1 ≤ 30 * ℓ + 30 by omega) (fun _ h => h)
  subst hb0
  have hok0 : S.ok (a.set t4 0) := S.ok_of _ _ (S.rest_set _ _ _) hok
  refine Hs.seq (src_hs S _ t0 hok0 (by rw [S.pos_set]; exact lt_of_drop hcw 0 (by omega))) (fun b1 hb1 => ?_)
  subst hb1
  have hI : I1 0 (S.nxt (a.set t4 0) t0) := by
    refine ⟨by rw [nenv _ _ hok0 (by decide)]; vsimp [], by rw [n0 _ hok0, S.pos_set]; rfl, by rw [S.posn, S.pos_set],
      by rw [S.restn, S.rest_set], ?_⟩
    exact Fr.trans (Fr.set a 0 (by decide)) (fun y hy => nenv _ y hok0 (fun h => hy (h ▸ by decide)))
  refine Hs.seq (l1 _ hI) (fun d hd => ?_)
  obtain ⟨d1, d2, d3, d4, d7⟩ := hd
  have dv1 : d.env v1 = 1 := by rw [d7 v1 (by decide)]; exact hv1
  refine Hs.seq (hs_zero C t3 d) (fun e he => ?_)
  subst he
  refine Hs.seq (hs_copy C t1 v1 _ (by decide)) (fun f hf => ?_)
  subst hf
  refine Hs.seq (hs_zero C t2 _) (fun g hg => ?_)
  subst hg
  refine Hs.mono (l2 _ ⟨by vsimp [], by vsimp [d1], by vsimp [Nat.mod_one], by vsimp [dv1], ?_, ?_, ?_⟩) le_rfl ?_
  · rw [S.pos_set, S.pos_set, S.pos_set, d3]
  · rw [S.rest_set, S.rest_set, S.rest_set, d4]
  · exact Fr.trans d7 (Fr.trans (Fr.set d _ (by decide)) (Fr.trans (Fr.set _ _ (by decide))
      (Fr.set _ _ (by decide))))
  · rintro r ⟨r1, r2, r3, r4, r5, r6, r9⟩
    refine ⟨by rw [r3, Nat.mod_eq_of_lt hvl], r2, by rw [r5, hlen]; ring, r6, r9⟩

/-! ### The two sources -/

/-- The entry word (the cell input followed by the cell tables). -/
def srcI (C : Ctx) : Src C (List Bool × (Fin MM → List ℕ) × (Fin MM → ℕ) × List Bool × List Bool × ℕ) where
  word := C.inp
  pos := fun a => a.ip
  rest := fun a => (a.out, a.ram, a.rc, a.kin, a.kout, a.kc)
  op := .rdI
  nxt := fun a x => { a.set x (bitOf C.inp a.ip) with ip := a.ip + 1 }
  ok := fun _ => True
  spec := fun a x _ h => OpEx.rdI x a h
  env := fun _ _ _ => rfl
  posn := fun _ _ => rfl
  restn := fun _ _ => rfl
  pos_set := fun _ _ _ => rfl
  rest_set := fun _ _ _ => rfl
  ok_of := fun _ _ _ _ => trivial

def srcK (C : Ctx) (w : List Bool) :
    Src C (ℕ × List Bool × (Fin MM → List ℕ) × (Fin MM → ℕ) × List Bool × List Bool) where
  word := w
  pos := fun a => a.kc
  rest := fun a => (a.ip, a.out, a.ram, a.rc, a.kin, a.kout)
  op := .rdK
  nxt := fun a x => { a.set x (bitOf a.kout a.kc) with kc := a.kc + 1 }
  ok := fun a => a.kout = w
  spec := fun a x h hp => OpEx.rdK x a (by rw [h]; exact hp)
  env := fun a x h => by simp [DS.set, h]
  posn := fun _ _ => rfl
  restn := fun _ _ => rfl
  pos_set := fun _ _ _ => rfl
  rest_set := fun _ _ _ => rfl
  ok_of := fun a b h ha => by
    have : b.kout = a.kout := by simp only [Prod.mk.injEq] at h; exact h.2.2.2.2.2
    rw [this, ha]

def rdNatI : St VV MM := rdNat .rdI
def rdNatK : St VV MM := rdNat .rdK

theorem rdNatI_spec (a : DS VV MM) (hc : Cst a) (v : ℕ) (rest : List Bool)
    (hcw : C.inp.drop a.ip = natWord v ++ rest) (hW : natBitLength v + 2 ≤ C.Wd) :
    Hs C rdNatI a (30 * natBitLength v + 30) (fun b => b.env t3 = v ∧ b.env t4 = natBitLength v ∧
      b.ip = a.ip + (natWord v).length ∧ (b.out, b.ram, b.rc, b.kin, b.kout, b.kc) =
        (a.out, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Fr a b rdNatT) :=
  rdNat_spec (srcI C) a hc trivial v rest hcw hW

theorem rdNatK_spec (a : DS VV MM) (hc : Cst a) (v : ℕ) (rest : List Bool)
    (hcw : a.kout.drop a.kc = natWord v ++ rest) (hW : natBitLength v + 2 ≤ C.Wd) :
    Hs C rdNatK a (30 * natBitLength v + 30) (fun b => b.env t3 = v ∧ b.env t4 = natBitLength v ∧
      b.kc = a.kc + (natWord v).length ∧ (b.ip, b.out, b.ram, b.rc, b.kin, b.kout) =
        (a.ip, a.out, a.ram, a.rc, a.kin, a.kout) ∧ Fr a b rdNatT) :=
  rdNat_spec (srcK C a.kout) a hc rfl v rest hcw hW

/-- A bit sink: `op b` appends `b` to `word`, leaving the variables and `rest` alone, while `room` allows it. -/
structure Snk (C : Ctx) (R : Type) where
  word : DS VV MM → List Bool
  rest : DS VV MM → R
  op : Bool → Op VV MM
  nxt : DS VV MM → Bool → DS VV MM
  room : ℕ → Prop
  spec : ∀ a b, room (word a).length → OpEx C (op b) a (nxt a b) 1
  env : ∀ a b, (nxt a b).env = a.env
  wordn : ∀ a b, word (nxt a b) = word a ++ [b]
  restn : ∀ a b, rest (nxt a b) = rest a
  word_set : ∀ a y v, word (a.set y v) = word a
  rest_set : ∀ a y v, rest (a.set y v) = rest a

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

/-- Print the bit held (as `0`/`1`) in `x`. -/
def emitB (em : Bool → Op VV MM) (x : Fin VV) : St VV MM := .ite (.eq x v1) (.op (em true)) (.op (em false))

/-- Print `natWord (t3)`. Scratch `t5 … t9`. -/
def emitNat (em : Bool → Op VV MM) : St VV MM :=
  .seq (.op (.copy t5 t3)) (.seq (.op (.zero t6)) (.seq (.loop (.lt v1 t5) (.seq (.op (.half t5)) (.op (.inc t6))))
    (.seq (.op (.inc t6)) (.seq (.op (.zero t7)) (.seq (.loop (.lt t7 t6) (.seq (.op (em true)) (.op (.inc t7))))
      (.seq (.op (em false)) (.seq (.op (.copy t5 t3)) (.seq (.op (.zero t7))
        (.loop (.lt t7 t6) (.seq (.op (.dm t5 v2 t8 t9)) (.seq (emitB em t9) (.seq (.op (.copy t5 t8))
          (.op (.inc t7))))))))))))))

def emitNatT : List (Fin VV) := [t5, t6, t7, t8, t9]

theorem snk_hs {R : Type} (K : Snk C R) (a : DS VV MM) (b : Bool) (h : K.room (K.word a).length) :
    Hs C (.op (K.op b)) a 1 (· = K.nxt a b) := Hs.op (K.spec a b h) rfl

theorem emitB_spec {R : Type} (K : Snk C R) (x : Fin VV) (hx : x ≠ v1) (a : DS VV MM) (hc : Cst a)
    (h : K.room (K.word a).length) :
    Hs C (emitB K.op x) a 2 (fun b => K.word b = K.word a ++ [decide (a.env x = 1)] ∧ K.rest b = K.rest a ∧
      b.env = a.env) := by
  refine Hs.ite (c := .eq x v1) hx (fun he => ?_) (fun he => ?_)
  · refine Hs.mono (snk_hs K a true h) le_rfl ?_
    rintro b rfl
    simp only [Cnd.eval, hc.one, decide_eq_true_eq] at he
    exact ⟨by rw [K.wordn]; simp [he], K.restn _ _, K.env _ _⟩
  · refine Hs.mono (snk_hs K a false h) le_rfl ?_
    rintro b rfl
    simp only [Cnd.eval, hc.one, decide_eq_false_iff_not] at he
    exact ⟨by rw [K.wordn]; simp [he], K.restn _ _, K.env _ _⟩

theorem emitNat_spec {R : Type} (K : Snk C R) (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd)
    (hv : natBitLength (a.env t3) + 2 < 2 ^ C.Wd)
    (hroom : ∀ j < (natWord (a.env t3)).length, K.room ((K.word a).length + j)) :
    Hs C (emitNat K.op) a (40 * natBitLength (a.env t3) + 40) (fun b => K.word b = K.word a ++ natWord (a.env t3) ∧
      K.rest b = K.rest a ∧ Cst b ∧ Fr a b emitNatT) := by
  set v := a.env t3 with hvdef
  set ℓ := natBitLength v with hℓ
  have hℓl : ℓ = Nat.log 2 v + 1 := rfl
  have hv1 := hc.one
  have hv2 := hc.two
  have hlen := natWord_length v
  have h4 : (4 : ℕ) ≤ 2 ^ C.Wd := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hW
  have nfr : ∀ (b : DS VV MM) (c : Bool), Fr b (K.nxt b c) emitNatT := fun b c y _ => by rw [K.env]
  -- loop 1: the logarithm
  let I1 : ℕ → DS VV MM → Prop := fun k b => b.env t5 = v / 2 ^ k ∧ b.env t6 = k ∧ K.word b = K.word a ∧
    K.rest b = K.rest a ∧ Fr a b emitNatT
  have l1 : ∀ b, I1 0 b → Hs C (.loop (.lt v1 t5) (.seq (.op (.half t5)) (.op (.inc t6)))) b
      (Nat.log 2 v * (3 + 2) + 2) (I1 (Nat.log 2 v)) := by
    refine Hs.loopN (c := .lt v1 t5) (show v1 ≠ t5 by decide) I1 _ 3 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h5, h6⟩
      have bv1 : b.env v1 = 1 := by rw [h6 v1 (by decide)]; exact hv1
      refine ⟨by simp only [Cnd.eval, bv1, h1, decide_eq_true_eq]; exact (lt_div_iff_lt_log v k hk.le).2 hk, ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_half C t5 b) (fun d hd => ?_)
      subst hd
      refine Hs.mono (hs_inc C t6 _ (by vsimp [h2]; omega)) le_rfl ?_
      rintro e rfl
      refine ⟨by vsimp [h1, Nat.div_div_eq_div_mul, pow_succ], by vsimp [h2], by rw [K.word_set, K.word_set, h3],
        by rw [K.rest_set, K.rest_set, h5], ?_⟩
      exact Fr.trans h6 (Fr.trans (Fr.set b _ (by decide)) (Fr.set _ _ (by decide)))
    · intro b ⟨h1, _, _, _, h6⟩
      have bv1 : b.env v1 = 1 := by rw [h6 v1 (by decide)]; exact hv1
      simp only [Cnd.eval, bv1, h1, decide_eq_false_iff_not]
      exact fun h => absurd ((lt_div_iff_lt_log v _ le_rfl).1 h) (lt_irrefl _)
  -- loop 2: ℓ ones
  let I2 : ℕ → DS VV MM → Prop := fun k b => b.env t7 = k ∧ b.env t6 = ℓ ∧
    K.word b = K.word a ++ List.replicate k true ∧ K.rest b = K.rest a ∧ Fr a b emitNatT
  have l2 : ∀ b, I2 0 b → Hs C (.loop (.lt t7 t6) (.seq (.op (K.op true)) (.op (.inc t7)))) b (ℓ * (3 + 2) + 2)
      (I2 ℓ) := by
    refine Hs.loopN (c := .lt t7 t6) (show t7 ≠ t6 by decide) I2 _ 3 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h5, h6⟩
      refine ⟨by simp [Cnd.eval, h1, h2, hk], ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 1) (snk_hs K b true (by rw [h3]; simpa using hroom k (by omega)))
        (fun d hd => ?_)
      subst hd
      refine Hs.mono (hs_inc C t7 _ (by rw [K.env]; rw [h1]; omega)) le_rfl ?_
      rintro e rfl
      refine ⟨by vsimp [K.env, h1], by vsimp [K.env, h2], ?_, by rw [K.rest_set, K.restn, h5], ?_⟩
      · rw [K.word_set, K.wordn, h3, List.replicate_succ']; simp
      · exact Fr.trans h6 (Fr.trans (nfr b true) (Fr.set _ _ (by decide)))
    · intro b ⟨h1, h2, _⟩
      simp [Cnd.eval, h1, h2]
  -- loop 3: the bits
  let I3 : ℕ → DS VV MM → Prop := fun k b => b.env t7 = k ∧ b.env t6 = ℓ ∧ b.env t5 = v / 2 ^ k ∧
    K.word b = K.word a ++ (List.replicate ℓ true ++ [false]) ++ (List.range k).map v.testBit ∧
    K.rest b = K.rest a ∧ Fr a b emitNatT
  have l3 : ∀ b, I3 0 b → Hs C (.loop (.lt t7 t6) (.seq (.op (.dm t5 v2 t8 t9)) (.seq (emitB K.op t9)
      (.seq (.op (.copy t5 t8)) (.op (.inc t7)))))) b (ℓ * (8 + 2) + 2) (I3 ℓ) := by
    refine Hs.loopN (c := .lt t7 t6) (show t7 ≠ t6 by decide) I3 _ 8 ?_ ?_
    · intro k hk b ⟨h1, h2, h3, h5, h6, h7⟩
      have bv1 : b.env v1 = 1 := by rw [h7 v1 (by decide)]; exact hv1
      have bv2 : b.env v2 = 2 := by rw [h7 v2 (by decide)]; exact hv2
      refine ⟨by simp [Cnd.eval, h1, h2, hk], ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 6) (hs_dm C t5 v2 t8 t9 b (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by rw [bv2]; norm_num) (by rw [bv2]; omega)) (fun d hd => ?_)
      subst hd
      have dc : Cst ((b.set t8 (b.env t5 / b.env v2)).set t9 (b.env t5 % b.env v2)) := by
        refine ⟨?_, ?_, ?_⟩
        · rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), h7 vZ (by decide)]; exact hc.z
        · vsimp [bv1]
        · vsimp [bv2]
      have hroom' : K.room (K.word ((b.set t8 (b.env t5 / b.env v2)).set t9 (b.env t5 % b.env v2))).length := by
        rw [K.word_set, K.word_set, h5]
        have := hroom (ℓ + 1 + k) (by omega)
        convert this using 2
        simp only [List.length_append, List.length_replicate, List.length_singleton, List.length_map,
          List.length_range]
        omega
      refine Hs.seq (t1 := 2) (t2 := 3) (emitB_spec K t9 (by decide) _ dc hroom') (fun e he => ?_)
      obtain ⟨e1, e2, e4⟩ := he
      have et8 : e.env t8 = v / 2 ^ k / 2 := by rw [e4]; vsimp [h3, bv2]
      have et9 : ((b.set t8 (b.env t5 / b.env v2)).set t9 (b.env t5 % b.env v2)).env t9 = v / 2 ^ k % 2 := by
        vsimp [h3, bv2]
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C t5 t8 e (by decide)) (fun f hf => ?_)
      subst hf
      have et7 : e.env t7 = k := by rw [e4]; vsimp [h1]
      refine Hs.mono (hs_inc C t7 _ (by vsimp [et7]; omega)) le_rfl ?_
      rintro g rfl
      have et6 : e.env t6 = ℓ := by rw [e4]; vsimp [h2]
      refine ⟨by vsimp [et7], by vsimp [et6], by vsimp [et8, Nat.div_div_eq_div_mul, pow_succ], ?_,
        by rw [K.rest_set, K.rest_set, e2, K.rest_set, K.rest_set, h6], ?_⟩
      · have hb : decide (((b.set t8 (b.env t5 / b.env v2)).set t9 (b.env t5 % b.env v2)).env t9 = 1) =
            v.testBit k := by rw [et9, Nat.testBit_eq_decide_div_mod_eq]
        rw [K.word_set, K.word_set, e1, hb, K.word_set, K.word_set, h5]
        simp only [List.range_succ, List.map_append, List.map_singleton, List.append_assoc]
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
  refine Hs.then (l1 _ ⟨by vsimp [hvdef], by vsimp [], by rw [K.word_set, K.word_set],
    by rw [K.rest_set, K.rest_set], Fr.trans (Fr.set a _ (by decide)) (Fr.set _ _ (by decide))⟩)
    (fun b2 hb2 n2 hn2 => ?_)
  obtain ⟨q1, q2, q3, q5, q6⟩ := hb2
  refine Hs.then (hs_inc C t6 b2 (by rw [q2]; omega)) (fun b3 hb3 n3 hn3 => ?_)
  subst hb3
  refine Hs.then (hs_zero C t7 _) (fun b4 hb4 n4 hn4 => ?_)
  subst hb4
  refine Hs.then (l2 _ ⟨by vsimp [], by vsimp [q2, hℓl], by rw [K.word_set, K.word_set, q3]; simp,
    by rw [K.rest_set, K.rest_set, q5],
    Fr.trans q6 (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide)))⟩) (fun b5 hb5 n5 hn5 => ?_)
  obtain ⟨r1, r2, r5, r5', r6⟩ := hb5
  refine Hs.then (snk_hs K b5 false (by rw [r5]; simpa using hroom ℓ (by omega))) (fun b6 hb6 n6 hn6 => ?_)
  subst hb6
  have b5t3 : b5.env t3 = v := by rw [r6 t3 (by decide)]
  refine Hs.then (hs_copy C t5 t3 _ (by decide)) (fun b7 hb7 n7 hn7 => ?_)
  subst hb7
  refine Hs.then (hs_zero C t7 _) (fun b8 hb8 n8 hn8 => ?_)
  subst hb8
  refine Hs.last (l3 _ ⟨by vsimp [], by vsimp [K.env, r2], by vsimp [K.env, b5t3], ?_, ?_, ?_⟩) ?_
  · rw [K.word_set, K.word_set, K.wordn, r5]; simp
  · rw [K.rest_set, K.rest_set, K.restn, r5']
  · exact Fr.trans r6 (Fr.trans (nfr b5 false) (Fr.trans (Fr.set _ _ (by decide)) (Fr.set _ _ (by decide))))
  · rintro g ⟨g1, g2, g3, g4, g5, g7⟩ n9 hn9
    refine ⟨⟨by rw [g4, natWord_eq, ofFn_testBit, ← hℓ]; simp, g5, ?_, g7⟩, by omega⟩
    exact ⟨by rw [g7 vZ (by decide)]; exact hc.z, by rw [g7 v1 (by decide)]; exact hc.one,
      by rw [g7 v2 (by decide)]; exact hc.two⟩

/-! ### The two sinks -/

/-- The output word. -/
def snkO (C : Ctx) : Snk C (ℕ × (Fin MM → List ℕ) × (Fin MM → ℕ) × List Bool × List Bool × ℕ) where
  word := fun a => a.out
  rest := fun a => (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc)
  op := .emit
  nxt := fun a b => { a with out := a.out ++ [b] }
  room := fun _ => True
  spec := fun a b _ => OpEx.emit b a
  env := fun _ _ => rfl
  wordn := fun _ _ => rfl
  restn := fun _ _ => rfl
  word_set := fun _ _ _ => rfl
  rest_set := fun _ _ _ => rfl

def snkK (C : Ctx) : Snk C (ℕ × List Bool × (Fin MM → List ℕ) × (Fin MM → ℕ) × List Bool × ℕ) where
  word := fun a => a.kin
  rest := fun a => (a.ip, a.out, a.ram, a.rc, a.kout, a.kc)
  op := .kem
  nxt := fun a b => { a with kin := a.kin ++ [b] }
  room := fun l => l < C.Lk
  spec := fun a b h => OpEx.kem b a h
  env := fun _ _ => rfl
  wordn := fun _ _ => rfl
  restn := fun _ _ => rfl
  word_set := fun _ _ _ => rfl
  rest_set := fun _ _ _ => rfl

def emitNatO : St VV MM := emitNat .emit
def emitNatK : St VV MM := emitNat .kem

theorem emitNatO_spec (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd) (hv : natBitLength (a.env t3) + 2 < 2 ^ C.Wd) :
    Hs C emitNatO a (40 * natBitLength (a.env t3) + 40) (fun b => b.out = a.out ++ natWord (a.env t3) ∧
      (b.ip, b.ram, b.rc, b.kin, b.kout, b.kc) = (a.ip, a.ram, a.rc, a.kin, a.kout, a.kc) ∧ Cst b ∧
      Fr a b emitNatT) :=
  emitNat_spec (snkO C) a hc hW hv (fun _ _ => trivial)

theorem emitNatK_spec (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd) (hv : natBitLength (a.env t3) + 2 < 2 ^ C.Wd)
    (hk : a.kin.length + (natWord (a.env t3)).length ≤ C.Lk) :
    Hs C emitNatK a (40 * natBitLength (a.env t3) + 40) (fun b => b.kin = a.kin ++ natWord (a.env t3) ∧
      (b.ip, b.out, b.ram, b.rc, b.kout, b.kc) = (a.ip, a.out, a.ram, a.rc, a.kout, a.kc) ∧ Cst b ∧
      Fr a b emitNatT) :=
  emitNat_spec (snkK C) a hc hW hv (fun j hj => by show _ < C.Lk; simp only [snkK]; omega)

end NearCubicGates.Close.Cells
