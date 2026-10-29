import SourceAdapters.Compile.OraclePrintTerms

/-!
# Cell execution of the printer's postfix tokens

proof of `thm:short-pcp-ours` (the circuit is written by an ordinary polynomial-time machine). This module realizes the token
machine `PS.step` of `OraclePrintTemplate` in the cell language: the node counter is register `CNT`, the index stack
is store `STK` (height `HR`, cursor at the height), every emitted node is appended to store `NS` as its record
`nodeRec` (tag, two numeric fields, oracle arguments), the wire map is store `WM` (length `WL`) and the data bits are
store `DSt` (length `DL`). `exec_spec`: one token, exactly, at cost `tokCost` linear in the stack height and the
lengths of the wire map and the data.
-/

namespace NearCubicGates.Adapters.Compile.OraclePrint

open NearCubicWires NearCubicWires.Bindings.MW20 NearCubicGates.Close.Cells

set_option autoImplicit false

/-! ## Stores and machine registers -/

def NS : Fin MM := ⟨0, by decide⟩
def STK : Fin MM := ⟨1, by decide⟩
def WM : Fin MM := ⟨2, by decide⟩
def DSt : Fin MM := ⟨3, by decide⟩

def CNT : Fin VV := ⟨101, by decide⟩
def HR : Fin VV := ⟨102, by decide⟩
def WL : Fin VV := ⟨103, by decide⟩
def DL : Fin VV := ⟨104, by decide⟩
def XA : Fin VV := ⟨105, by decide⟩
def XB : Fin VV := ⟨106, by decide⟩
def BV : Fin VV := ⟨107, by decide⟩
def KX : Fin VV := ⟨108, by decide⟩
def SK : Fin VV := ⟨109, by decide⟩
def JK : Fin VV := ⟨110, by decide⟩
def TT : Fin VV := ⟨111, by decide⟩

@[simp] theorem NS_val : NS.val = 0 := rfl
@[simp] theorem STK_val : STK.val = 1 := rfl
@[simp] theorem WM_val : WM.val = 2 := rfl
@[simp] theorem DSt_val : DSt.val = 3 := rfl
@[simp] theorem CNT_val : CNT.val = 101 := rfl
@[simp] theorem HR_val : HR.val = 102 := rfl
@[simp] theorem WL_val : WL.val = 103 := rfl
@[simp] theorem DL_val : DL.val = 104 := rfl
@[simp] theorem XA_val : XA.val = 105 := rfl
@[simp] theorem XB_val : XB.val = 106 := rfl
@[simp] theorem BV_val : BV.val = 107 := rfl
@[simp] theorem KX_val : KX.val = 108 := rfl
@[simp] theorem SK_val : SK.val = 109 := rfl
@[simp] theorem JK_val : JK.val = 110 := rfl
@[simp] theorem TT_val : TT.val = 111 := rfl

/-- The record of a node in `NS`. -/
def nodeRec {n arity : ℕ} (nd : OracleNode n arity) : List ℕ :=
  [nodeTag nd, nodeLeft nd, nodeRight nd] ++ nodeArgs nd

/-! ## Frames -/

/-- Registers outside `T`, stores outside `R` (contents) and `M` (cursors), and the remaining components are
unchanged. -/
structure Keep (T : ℕ → Prop) (R M : ℕ → Prop) (a b : DS VV MM) : Prop where
  env : ∀ y : Fin VV, ¬ T y.val → b.env y = a.env y
  ram : ∀ m : Fin MM, ¬ R m.val → b.ram m = a.ram m
  rc : ∀ m : Fin MM, ¬ M m.val → b.rc m = a.rc m
  ip : b.ip = a.ip
  out : b.out = a.out
  kin : b.kin = a.kin
  kout : b.kout = a.kout
  kc : b.kc = a.kc

theorem Keep.refl (T R M : ℕ → Prop) (a : DS VV MM) : Keep T R M a a :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {T R M : ℕ → Prop} {a b c : DS VV MM} (h1 : Keep T R M a b) (h2 : Keep T R M b c) :
    Keep T R M a c :=
  ⟨fun y hy => (h2.env y hy).trans (h1.env y hy), fun m hm => (h2.ram m hm).trans (h1.ram m hm),
    fun m hm => (h2.rc m hm).trans (h1.rc m hm), h2.ip.trans h1.ip, h2.out.trans h1.out, h2.kin.trans h1.kin,
    h2.kout.trans h1.kout, h2.kc.trans h1.kc⟩

theorem Keep.mono {T R M T' R' M' : ℕ → Prop} {a b : DS VV MM} (h : Keep T R M a b) (hT : ∀ y, T y → T' y)
    (hR : ∀ m, R m → R' m) (hM : ∀ m, M m → M' m) : Keep T' R' M' a b :=
  ⟨fun y hy => h.env y (fun h' => hy (hT _ h')), fun m hm => h.ram m (fun h' => hm (hR _ h')),
    fun m hm => h.rc m (fun h' => hm (hM _ h')), h.ip, h.out, h.kin, h.kout, h.kc⟩

theorem Keep.set {T R M : ℕ → Prop} (a : DS VV MM) (x : Fin VV) (v : ℕ) (hx : T x.val) :
    Keep T R M a (a.set x v) :=
  ⟨fun _ hy => DS.set_env_ne a v (fun e => hy (e ▸ hx)), fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.cst {T R M : ℕ → Prop} {a b : DS VV MM} (h : Keep T R M a b) (hT : ¬ T 0 ∧ ¬ T 1 ∧ ¬ T 2)
    (hc : Cst a) : Cst b :=
  ⟨by rw [h.env vZ hT.1, hc.z], by rw [h.env v1 hT.2.1, hc.one], by rw [h.env v2 hT.2.2, hc.two]⟩

theorem neP {P : ℕ → Prop} {y x : Fin VV} (hy : ¬ P y.val) (hx : P x.val) : y ≠ x := fun e => by
  subst e; exact hy hx

theorem neM {z m : Fin MM} (hz : ¬ z.val = m.val) : z ≠ m := fun e => hz (congrArg Fin.val e)

variable {C : Ctx}

/-! ## Seek -/

/-- Move the cursor of store `m` to position `k` (rewind, then read `k` records). -/
def seek (m : Fin MM) (k : Fin VV) : St VV MM :=
  .seq (.op (.rwM m)) (.seq (.op (.zero SK)) (.loop (.lt SK k) (.seq (.op (.rdM m JK)) (.op (.inc SK)))))

/-- The seek scratch. -/
def SkT (y : ℕ) : Prop := y = 109 ∨ y = 110

theorem seek_spec (m : Fin MM) (k : Fin VV) (hk : ¬ SkT k.val) (a : DS VV MM)
    (hkl : a.env k ≤ (a.ram m).length) (hkW : a.env k < 2 ^ C.Wd) :
    Hs C (seek m k) a (a.rc m + 5 * a.env k + 6) (fun b => b.rc m = a.env k ∧
      Keep SkT (fun _ => False) (fun x => x = m.val) a b) := by
  have hkS : k ≠ SK := fun e => hk (by rw [e]; left; rfl)
  have hSK : SkT SK.val := by left; rfl
  have hJK : SkT JK.val := by right; rfl
  refine Hs.mono (t := (a.rc m + 1) + (1 + (a.env k * (3 + 2) + 2) + 1) + 1)
    (Hs.seq (hs_rwM C m a) (fun b hb => ?_)) (by omega) (fun x hx => hx)
  subst hb
  refine Hs.seq (hs_zero C SK _) (fun b' hb => ?_)
  subst hb
  set a0 := (a.rew m).set SK 0 with ha0
  have hk0 : a0.env k = a.env k := by rw [ha0, DS.set_env_ne _ _ hkS]; rfl
  let I : ℕ → DS VV MM → Prop := fun i x => x.env SK = i ∧ x.rc m = i ∧ x.env k = a.env k ∧
    Keep SkT (fun _ => False) (fun z => z = m.val) a x
  have h0 : I 0 a0 := by
    refine ⟨DS.set_env_self _ _ _, by simp [ha0, DS.rew], hk0, ?_⟩
    exact ⟨fun y hy => by rw [ha0, DS.set_env_ne _ _ (neP hy hSK)]; rfl, fun _ _ => rfl,
      fun z hz => by simp only [ha0, DS.set_rc, DS.rew]; exact Function.update_of_ne (neM hz) _ _,
      rfl, rfl, rfl, rfl, rfl⟩
  have hl := Hs.loopN (C := C) (c := .lt SK k) (s := .seq (.op (.rdM m JK)) (.op (.inc SK)))
    (show SK ≠ k from fun e => hkS e.symm) I (a.env k) 3 ?_ ?_ a0 h0
  · refine Hs.mono hl le_rfl ?_
    rintro x ⟨_, h2, _, h4⟩
    exact ⟨h2, h4⟩
  · intro i hi x ⟨h1, h2, h3, h4⟩
    refine ⟨by simp [Cnd.eval, h1, h3, hi], ?_⟩
    have hram : x.ram m = a.ram m := h4.ram m (fun h => h)
    refine Hs.mono (t := 1 + 1 + 1) (Hs.seq (hs_rdM C m JK x (by rw [h2, hram]; omega)) (fun y hy => ?_))
      le_rfl (fun x hx => hx)
    subst hy
    have hyS : ((x.set JK ((x.ram m).getD (x.rc m) 0)).adv m).env SK = i := by
      simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide), h1]
    refine Hs.mono (hs_inc C SK _ (by rw [hyS]; omega)) le_rfl ?_
    rintro z rfl
    refine ⟨by rw [DS.set_env_self, hyS], by simp [DS.adv, DS.set, h2], ?_, ?_⟩
    · rw [DS.set_env_ne _ _ hkS]; simp only [DS.adv]
      rw [DS.set_env_ne _ _ (neP hk hJK)]; exact h3
    · refine h4.trans ⟨fun y hy => ?_, fun _ _ => rfl, fun z hz => ?_, rfl, rfl, rfl, rfl, rfl⟩
      · have e1 : y ≠ SK := neP hy hSK
        have e2 : y ≠ JK := neP hy hJK
        rw [DS.set_env_ne _ _ e1]; simp only [DS.adv]; rw [DS.set_env_ne _ _ e2]
      · simp only [DS.set_rc, DS.adv, DS.set_rc]
        exact Function.update_of_ne (neM hz) _ _
  · intro x ⟨h1, _, h3, _⟩
    simp [Cnd.eval, h1, h3]

/-! ## The stack -/

theorem take_putAt (l : List ℕ) (i v : ℕ) (hi : i ≤ l.length) : (putAt l i v).take (i + 1) = l.take i ++ [v] := by
  unfold putAt
  split_ifs with h
  · rw [List.set_eq_take_append_cons_drop, if_pos h]
    have hl : (l.take i).length = i := List.length_take_of_le (by omega)
    rw [show i + 1 = (l.take i).length + 1 by omega, List.take_length_add_append]
    rfl
  · have he : i = l.length := by omega
    subst he
    rw [List.take_length, List.take_of_length_le (by simp)]

/-- The stack registers hold `stk` (top first): height `HR`, cursor of `STK` at the height, bottom-first records. -/
def StkOk (a : DS VV MM) (stk : List ℕ) : Prop :=
  a.env HR = stk.length ∧ a.rc STK = stk.length ∧ (a.ram STK).take stk.length = stk.reverse

theorem StkOk.le {a : DS VV MM} {stk : List ℕ} (h : StkOk a stk) : stk.length ≤ (a.ram STK).length := by
  have := congrArg List.length h.2.2
  simp only [List.length_take, List.length_reverse] at this
  omega

def push (x : Fin VV) : St VV MM := .seq (.op (.wrM STK x)) (.op (.inc HR))

def HrT (y : ℕ) : Prop := y = 102

theorem push_spec (x : Fin VV) (stk : List ℕ) (a : DS VV MM) (h : StkOk a stk)
    (hW : stk.length + 1 < 2 ^ C.Wd) :
    Hs C (push x) a 3 (fun b => StkOk b (a.env x :: stk) ∧ Keep HrT (· = 1) (· = 1) a b) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hle := StkOk.le ⟨h1, h2, h3⟩
  refine Hs.mono (t := 1 + 1 + 1) (Hs.seq (hs_wrM C STK x a (by omega)) (fun b hb => ?_)) le_rfl
    (fun b hb => hb)
  subst hb
  have hHR : (a.put STK (a.env x)).env HR = stk.length := h1
  refine Hs.mono (hs_inc C HR _ (by rw [hHR]; omega)) le_rfl ?_
  rintro b rfl
  refine ⟨⟨by rw [DS.set_env_self, hHR]; rfl, by simp [DS.put, h2], ?_⟩, ?_⟩
  · simp only [DS.set_ram, DS.put, Function.update_self, h2, List.length_cons, List.reverse_cons]
    rw [take_putAt _ _ _ hle, h3]
  · refine ⟨fun y hy => ?_, fun m hm => ?_, fun m hm => ?_, rfl, rfl, rfl, rfl, rfl⟩
    · rw [DS.set_env_ne _ _ (neP hy (show HrT HR.val from rfl))]; rfl
    · simp only [DS.set_ram, DS.put]; exact Function.update_of_ne (neM hm) _ _
    · simp only [DS.set_rc, DS.put]; exact Function.update_of_ne (neM hm) _ _

def pop (x : Fin VV) : St VV MM :=
  .ite (.eq HR vZ) (.op (.zero x))
    (.seq (.op (.sub HR v1)) (.seq (seek STK HR) (.seq (.op (.rdM STK x)) (seek STK HR))))

def PopT (x : ℕ) (y : ℕ) : Prop := y = x ∨ y = 102 ∨ SkT y

theorem pop_spec (x : Fin VV) (hx : ¬ (x.val = 102 ∨ SkT x.val ∨ x.val < 3)) (stk : List ℕ) (a : DS VV MM)
    (hc : Cst a) (h : StkOk a stk) (hW : stk.length < 2 ^ C.Wd) :
    Hs C (pop x) a (12 * stk.length + 30) (fun b => b.env x = stk.headD 0 ∧ StkOk b stk.tail ∧
      Keep (PopT x.val) (fun _ => False) (· = 1) a b) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hle := StkOk.le ⟨h1, h2, h3⟩
  have hxH : x ≠ HR := neP (P := fun y => y = 102) (by omega) rfl
  have hHz : HR ≠ vZ := by decide
  have hpopT : ∀ y : ℕ, SkT y → PopT x.val y := fun y hy => Or.inr (Or.inr hy)
  cases stk with
  | nil =>
      refine Hs.mono (Hs.iteT (C := C) hHz (by simp [Cnd.eval, h1, hc.z]) (hs_zero C x a)) (by omega) ?_
      rintro b rfl
      refine ⟨by rw [DS.set_env_self]; rfl, ⟨by rw [DS.set_env_ne _ _ hxH.symm, h1]; rfl, h2, by simp⟩, ?_⟩
      exact Keep.set a x 0 (Or.inl rfl)
  | cons v rest =>
      simp only [List.length_cons] at h1 h2 h3 hW hle
      have hR3 : (a.ram STK).take rest.length = rest.reverse := by
        rw [show rest.length = min rest.length (rest.length + 1) by omega, ← List.take_take, h3]
        simp
      have hv : (a.ram STK).getD rest.length 0 = v := by
        have e1 : (a.ram STK).getD rest.length 0 = ((a.ram STK).take (rest.length + 1)).getD rest.length 0 := by
          simp [List.getD_eq_getElem?_getD]
        rw [e1, h3]
        simp [List.getD_eq_getElem?_getD]
      have hHn : Cnd.eval a (.eq HR vZ) = false := by simp [Cnd.eval, h1, hc.z]
      have hSkH : ¬ SkT HR.val := by unfold SkT; decide
      have hSkx : ¬ SkT x.val := fun h => hx (Or.inr (Or.inl h))
      refine Hs.mono (Hs.iteF (C := C) hHz hHn ?_) (t := 12 * rest.length + 29) (by simp only [List.length_cons]; omega)
        (fun b hb => hb)
      refine Hs.mono (t := 1 + (6 * rest.length + 7 + (1 + (6 * rest.length + 7) + 1) + 1) + 1)
        (Hs.seq (hs_sub C HR v1 a (by decide) (by rw [hc.one, h1]; omega)) (fun b1 hb1 => ?_)) (by omega)
        (fun b hb => hb)
      subst hb1
      have e1 : (a.set HR (a.env HR - a.env v1)).env HR = rest.length := by
        rw [DS.set_env_self, h1, hc.one]; omega
      refine Hs.seq (Hs.mono (seek_spec STK HR hSkH _ (by rw [e1, DS.set_ram]; omega) (by rw [e1]; omega))
        (by rw [e1, DS.set_rc, h2]; omega) (fun b hb => hb)) (fun b2 hb2 => ?_)
      obtain ⟨r2, k2⟩ := hb2
      rw [e1] at r2
      have hram2 : b2.ram STK = a.ram STK := k2.ram STK (fun h => h)
      have hH2 : b2.env HR = rest.length := by rw [k2.env HR hSkH, e1]
      refine Hs.seq (hs_rdM C STK x b2 (by rw [r2, hram2]; omega)) (fun b3 hb3 => ?_)
      subst hb3
      set b3 := (b2.set x ((b2.ram STK).getD (b2.rc STK) 0)).adv STK with hb3
      have hH3 : b3.env HR = rest.length := by
        rw [hb3]; simp only [DS.adv]; rw [DS.set_env_ne _ _ hxH.symm, hH2]
      have hx3 : b3.env x = v := by
        rw [hb3]; simp only [DS.adv]; rw [DS.set_env_self, r2, hram2, hv]
      have hrc3 : b3.rc STK = rest.length + 1 := by simp [hb3, DS.adv, r2]
      have hram3 : b3.ram = b2.ram := rfl
      refine Hs.mono (seek_spec STK HR hSkH b3 (by rw [hH3, hram3, hram2]; omega) (by rw [hH3]; omega))
        (by rw [hH3, hrc3]; omega) ?_
      rintro b4 ⟨r4, k4⟩
      rw [hH3] at r4
      have k3 : Keep (PopT x.val) (fun _ => False) (· = 1) b2 b3 := by
        refine ⟨fun y hy => ?_, fun _ _ => rfl, fun m hm => ?_, rfl, rfl, rfl, rfl, rfl⟩
        · rw [hb3]; simp only [DS.adv]
          exact DS.set_env_ne _ _ (neP hy (show PopT x.val x.val from Or.inl rfl))
        · rw [hb3]; simp only [DS.adv, DS.set_rc]; exact Function.update_of_ne (neM hm) _ _
      have k1 : Keep (PopT x.val) (fun _ => False) (· = 1) a (a.set HR (a.env HR - a.env v1)) :=
        Keep.set a HR _ (Or.inr (Or.inl rfl))
      have kall : Keep (PopT x.val) (fun _ => False) (· = 1) a b4 :=
        k1.trans ((k2.mono (fun y hy => hpopT y hy) (fun _ h => h) (fun m hm => by rw [hm]; rfl)).trans
          (k3.trans (k4.mono (fun y hy => hpopT y hy) (fun _ h => h) (fun m hm => by rw [hm]; rfl))))
      refine ⟨by rw [k4.env x hSkx, hx3]; rfl, ⟨?_, by rw [r4]; rfl, ?_⟩, kall⟩
      · rw [k4.env HR hSkH, hH3]; rfl
      · rw [k4.ram STK (fun h => h), hram3, hram2]; exact hR3

/-! ## Node records -/

def rec3 (x y z : Fin VV) : St VV MM := .seq (.op (.wrM NS x)) (.seq (.op (.wrM NS y)) (.op (.wrM NS z)))

theorem put_end (a : DS VV MM) (m : Fin MM) (v : ℕ) (h : a.rc m = (a.ram m).length) :
    (a.put m v).ram m = a.ram m ++ [v] ∧ (a.put m v).rc m = ((a.put m v).ram m).length := by
  simp [DS.put, putAt, h]

theorem keep_put (a : DS VV MM) (m : Fin MM) (v : ℕ) : Keep (fun _ => False) (· = m.val) (· = m.val) a (a.put m v) :=
  ⟨fun _ _ => rfl, fun z hz => by simp only [DS.put]; exact Function.update_of_ne (neM hz) _ _,
    fun z hz => by simp only [DS.put]; exact Function.update_of_ne (neM hz) _ _, rfl, rfl, rfl, rfl, rfl⟩

theorem rec3_spec (x y z : Fin VV) (a : DS VV MM) (h : a.rc NS = (a.ram NS).length) :
    Hs C (rec3 x y z) a 5 (fun b => b.ram NS = a.ram NS ++ [a.env x, a.env y, a.env z] ∧
      b.rc NS = (b.ram NS).length ∧ Keep (fun _ => False) (· = 0) (· = 0) a b) := by
  refine Hs.mono (t := 1 + (1 + 1 + 1) + 1) (Hs.seq (hs_wrM C NS x a (by omega)) (fun b1 hb1 => ?_)) le_rfl
    (fun b hb => hb)
  subst hb1
  obtain ⟨p1, q1⟩ := put_end a NS (a.env x) h
  refine Hs.seq (hs_wrM C NS y _ (by omega)) (fun b2 hb2 => ?_)
  subst hb2
  obtain ⟨p2, q2⟩ := put_end _ NS ((a.put NS (a.env x)).env y) q1
  refine Hs.mono (hs_wrM C NS z _ (by omega)) le_rfl ?_
  rintro b rfl
  obtain ⟨p3, q3⟩ := put_end _ NS (((a.put NS (a.env x)).put NS ((a.put NS (a.env x)).env y)).env z) q2
  refine ⟨by rw [p3, p2, p1]; simp [DS.put], q3, ?_⟩
  exact (keep_put a NS _).trans ((keep_put _ NS _).trans (keep_put _ NS _))

/-- Append a Boolean node record (tag, left, right), push its index, advance the counter. -/
def emitN (tg l r : Fin VV) : St VV MM := .seq (rec3 tg l r) (.seq (push CNT) (.op (.inc CNT)))

/-! ## The representation of the token machine -/

/-- Everything but the stack. -/
structure RepB {n arity : ℕ} (w : List ℕ) (D : List Bool) (S : PS n arity) (a : DS VV MM) : Prop where
  cst : Cst a
  cnt : a.env CNT = S.cnt
  ns : a.ram NS = S.nodes.flatMap nodeRec
  nsc : a.rc NS = (a.ram NS).length
  wm : a.ram WM = w
  wl : a.env WL = w.length
  wc : a.rc WM ≤ w.length
  dsr : a.ram DSt = D.map Bool.toNat
  dl : a.env DL = D.length
  dc : a.rc DSt ≤ D.length

/-- **The cell state represents the token machine state `S`.** -/
structure Rep {n arity : ℕ} (w : List ℕ) (D : List Bool) (S : PS n arity) (a : DS VV MM) : Prop where
  base : RepB w D S a
  stk : StkOk a S.stk

/-- The machine registers. -/
def MachT (y : ℕ) : Prop := y = 101 ∨ y = 102 ∨ (105 ≤ y ∧ y ≤ 111)

/-- Stores whose contents change (`NS`, `STK`) and whose cursors change (also `WM`). -/
def MachR (m : ℕ) : Prop := m ≤ 1
def MachM (m : ℕ) : Prop := m ≤ 2

theorem RepB.congr {n arity : ℕ} {w : List ℕ} {D : List Bool} {S S' : PS n arity} {a : DS VV MM}
    (h : RepB w D S a) (hc : S'.cnt = S.cnt) (hn : S'.nodes = S.nodes) : RepB w D S' a :=
  ⟨h.cst, by rw [hc]; exact h.cnt, by rw [hn]; exact h.ns, h.nsc, h.wm, h.wl, h.wc, h.dsr, h.dl, h.dc⟩

theorem RepB.keep {n arity : ℕ} {w : List ℕ} {D : List Bool} {S : PS n arity} {a b : DS VV MM}
    (h : RepB w D S a) (k : Keep MachT MachR MachM a b) (hc : b.env CNT = a.env CNT)
    (hns : b.ram NS = a.ram NS) (hnc : b.rc NS = a.rc NS) (hwc : b.rc WM ≤ w.length) : RepB w D S b :=
  ⟨k.cst (by unfold MachT; omega) h.cst, by rw [hc, h.cnt], by rw [hns, h.ns], by rw [hnc, hns, h.nsc],
    by rw [k.ram WM (by unfold MachR; decide), h.wm], by rw [k.env WL (by unfold MachT; decide), h.wl], hwc,
    by rw [k.ram DSt (by unfold MachR; decide), h.dsr], by rw [k.env DL (by unfold MachT; decide), h.dl],
    by rw [k.rc DSt (by unfold MachM; decide)]; exact h.dc⟩

theorem emitN_spec {n arity : ℕ} (w : List ℕ) (D : List Bool) (S : PS n arity) (stk : List ℕ)
    (nd : OracleNode n arity) (hargs : nodeArgs nd = []) (tg l r : Fin VV) (a : DS VV MM) (h : RepB w D S a)
    (hs : StkOk a stk) (ht : a.env tg = nodeTag nd) (hl : a.env l = nodeLeft nd) (hr : a.env r = nodeRight nd)
    (hW1 : S.cnt + 1 < 2 ^ C.Wd) (hW2 : stk.length + 1 < 2 ^ C.Wd) :
    Hs C (emitN tg l r) a 11 (fun b => Rep w D (S.emit stk nd) b ∧ Keep MachT MachR MachM a b) := by
  refine Hs.mono (t := 5 + (3 + 1 + 1) + 1) (Hs.seq (rec3_spec tg l r a h.nsc) (fun b1 hb1 => ?_)) (by omega)
    (fun b hb => hb)
  obtain ⟨p1, q1, k1⟩ := hb1
  have hs1 : StkOk b1 stk := by
    obtain ⟨s1, s2, s3⟩ := hs
    exact ⟨by rw [k1.env HR (fun h => h)]; exact s1, by rw [k1.rc STK (by decide)]; exact s2,
      by rw [k1.ram STK (by decide)]; exact s3⟩
  have hc1 : b1.env CNT = S.cnt := by rw [k1.env CNT (fun h => h), h.cnt]
  refine Hs.seq (push_spec CNT stk b1 hs1 hW2) (fun b2 hb2 => ?_)
  obtain ⟨hs2, k2⟩ := hb2
  have hc2 : b2.env CNT = S.cnt := by rw [k2.env CNT (by unfold HrT; decide), hc1]
  refine Hs.mono (hs_inc C CNT b2 (by rw [hc2]; omega)) le_rfl ?_
  rintro b rfl
  have kk : Keep MachT MachR MachM a (b2.set CNT (b2.env CNT + 1)) :=
    (k1.mono (fun _ h => h.elim) (fun m hm => by unfold MachR; omega) (fun m hm => by unfold MachM; omega)).trans
      ((k2.mono (fun y hy => by unfold HrT at hy; unfold MachT; omega) (fun m hm => by unfold MachR; omega)
        (fun m hm => by unfold MachM; omega)).trans (Keep.set _ _ _ (by unfold MachT; decide)))
  have hns2 : b2.ram NS = b1.ram NS := k2.ram NS (by decide)
  have hnc2 : b2.rc NS = b1.rc NS := k2.rc NS (by decide)
  have hwc : (b2.set CNT (b2.env CNT + 1)).rc WM = a.rc WM := by
    rw [DS.set_rc, k2.rc WM (by decide), k1.rc WM (by decide)]
  refine ⟨⟨⟨kk.cst (by unfold MachT; omega) h.cst, by rw [DS.set_env_self, hc2]; rfl, ?_, ?_,
    by rw [kk.ram WM (by unfold MachR; decide), h.wm], by rw [kk.env WL (by unfold MachT; decide), h.wl],
    by rw [hwc]; exact h.wc, by rw [kk.ram DSt (by unfold MachR; decide), h.dsr],
    by rw [kk.env DL (by unfold MachT; decide), h.dl], by rw [kk.rc DSt (by unfold MachM; decide)]; exact h.dc⟩,
    ?_⟩, kk⟩
  · rw [DS.set_ram, hns2, p1, h.ns, ht, hl, hr]
    simp [PS.emit, nodeRec, hargs]
  · rw [DS.set_rc, DS.set_ram, hnc2, hns2, q1]
  · obtain ⟨s1, s2, s3⟩ := hs2
    refine ⟨by rw [DS.set_env_ne _ _ (by decide), s1, hc1]; rfl, by rw [DS.set_rc, s2, hc1]; rfl, ?_⟩
    rw [DS.set_ram, hc1] at *
    simpa [PS.emit] using s3

/-! ## Tokens -/

def execWir : St VV MM :=
  .seq (.ite (.lt KX WL) (.seq (seek WM KX) (.op (.rdM WM XA))) (.op (.zero XA))) (push XA)
def execNeg : St VV MM := .seq (pop XA) (emitN v2 XA vZ)
def tag3 : St VV MM := .seq (.op (.copy TT v2)) (.op (.inc TT))
def tag4 : St VV MM := .seq (.op (.copy TT v2)) (.op (.add TT v2))
def execBin (tag : St VV MM) : St VV MM := .seq (pop XB) (.seq (pop XA) (.seq tag (emitN TT XA XB)))

/-- The cell code of one token (its datum is in `BV` or `KX`). -/
def execTok : Tok → St VV MM
  | .cst _ => emitN vZ BV vZ
  | .wir _ => execWir
  | .neg => execNeg
  | .conj => execBin tag3
  | .disj => execBin tag4

/-- The datum of a token is in its register. -/
def TokReg (a : DS VV MM) : Tok → Prop
  | .cst b => a.env BV = b.toNat
  | .wir k => a.env KX = k
  | _ => True

/-- The cost of one token at stack height `h` and wire map length `wl`. -/
def tokCost (h wl : ℕ) : ℕ := 24 * h + 6 * wl + 80

theorem keep_pop_mach {x : ℕ} (hx : 105 ≤ x ∧ x ≤ 111) {a b : DS VV MM}
    (k : Keep (PopT x) (fun _ => False) (· = 1) a b) : Keep MachT MachR MachM a b :=
  k.mono (fun y hy => by unfold PopT SkT at hy; unfold MachT; omega) (fun _ h => h.elim)
    (fun m hm => by unfold MachM; omega)

theorem RepB.pop {n arity : ℕ} {w : List ℕ} {D : List Bool} {S : PS n arity} {a b : DS VV MM} {x : ℕ}
    (hx : 105 ≤ x ∧ x ≤ 111) (h : RepB w D S a) (k : Keep (PopT x) (fun _ => False) (· = 1) a b) :
    RepB w D S b :=
  h.keep (keep_pop_mach hx k) (k.env CNT (by unfold PopT SkT; rw [CNT_val]; omega)) (k.ram NS id) (k.rc NS (by decide))
    (by rw [k.rc WM (by decide)]; exact h.wc)

theorem pop_ok (x : Fin VV) (hx : 105 ≤ x.val ∧ x.val ≤ 108 ∨ x.val = 111) : ¬ (x.val = 102 ∨ SkT x.val ∨ x.val < 3) := by
  unfold SkT; omega

theorem tag3_spec (h8 : 8 ≤ 2 ^ C.Wd) (b : DS VV MM) (hc : Cst b) :
    Hs C tag3 b 3 (fun x => x.env TT = 3 ∧ Keep (· = 111) (fun _ => False) (fun _ => False) b x) := by
  refine Hs.mono (t := 1 + 1 + 1) (Hs.seq (hs_copy C TT v2 b (by decide)) (fun b1 hb1 => ?_)) le_rfl (fun x hx => hx)
  subst hb1
  refine Hs.mono (hs_inc C TT _ (by rw [DS.set_env_self, hc.two]; omega)) le_rfl ?_
  rintro x rfl
  exact ⟨by rw [DS.set_env_self, DS.set_env_self, hc.two],
    (Keep.set (T := (· = 111)) (R := fun _ => False) (M := fun _ => False) _ _ _ rfl).trans
      (Keep.set (T := (· = 111)) (R := fun _ => False) (M := fun _ => False) _ _ _ rfl)⟩

theorem tag4_spec (h8 : 8 ≤ 2 ^ C.Wd) (b : DS VV MM) (hc : Cst b) :
    Hs C tag4 b 3 (fun x => x.env TT = 4 ∧ Keep (· = 111) (fun _ => False) (fun _ => False) b x) := by
  refine Hs.mono (t := 1 + 1 + 1) (Hs.seq (hs_copy C TT v2 b (by decide)) (fun b1 hb1 => ?_)) le_rfl (fun x hx => hx)
  subst hb1
  have hlt : (b.set TT (b.env v2)).env TT + (b.set TT (b.env v2)).env v2 < 2 ^ C.Wd := by
    rw [DS.set_env_self, DS.set_env_ne _ _ (by decide), hc.two]; omega
  refine Hs.mono (hs_add C TT v2 _ (by decide) hlt) le_rfl ?_
  rintro x rfl
  exact ⟨by rw [DS.set_env_self, DS.set_env_self, DS.set_env_ne _ _ (by decide), hc.two],
    (Keep.set (T := (· = 111)) (R := fun _ => False) (M := fun _ => False) _ _ _ rfl).trans
      (Keep.set (T := (· = 111)) (R := fun _ => False) (M := fun _ => False) _ _ _ rfl)⟩

theorem execBin_spec {n arity : ℕ} (w : List ℕ) (D : List Bool) (S : PS n arity) (a : DS VV MM)
    (h : Rep w D S a) (tag : St VV MM) (code : ℕ)
    (htag : ∀ b, Cst b → Hs C tag b 3 (fun x => x.env TT = code ∧ Keep (· = 111) (fun _ => False) (fun _ => False) b x))
    (hW1 : S.cnt + 1 < 2 ^ C.Wd) (hW2 : S.stk.length + 1 < 2 ^ C.Wd)
    (mk : ℕ → ℕ → OracleNode n arity) (hT : ∀ x y, nodeTag (mk x y) = code) (hL : ∀ x y, nodeLeft (mk x y) = x)
    (hR : ∀ x y, nodeRight (mk x y) = y) (hA : ∀ x y, nodeArgs (mk x y) = [])
    (tk0 : Tok) (hstep : S.emit S.stk.tail.tail (mk (S.stk.tail.headD 0) (S.stk.headD 0)) = S.step w tk0) :
    Hs C (execBin tag) a (tokCost S.stk.length w.length) (fun b => Rep w D (S.step w tk0) b ∧
      Keep MachT MachR MachM a b) := by
  obtain ⟨hb, hs⟩ := h
  rw [← hstep]
  have hl1 : S.stk.tail.length ≤ S.stk.length := by rw [List.length_tail]; omega
  have hl2 : S.stk.tail.tail.length ≤ S.stk.length := by rw [List.length_tail, List.length_tail]; omega
  refine Hs.mono (t := (12 * S.stk.length + 30) + ((12 * S.stk.length + 30) + (3 + 11 + 1) + 1) + 1)
    (Hs.seq (pop_spec XB (pop_ok XB (by simp)) S.stk a hb.cst hs (by omega)) (fun b1 hb1 => ?_))
    (by unfold tokCost; omega) (fun x hx => hx)
  obtain ⟨v1, hs1, k1⟩ := hb1
  have hb1 := hb.pop (by simp) k1
  refine Hs.mono (t := (12 * S.stk.length + 30) + (3 + 11 + 1) + 1) (Hs.seq (Hs.mono (t' := 12 * S.stk.length + 30)
    (pop_spec (C := C) XA (pop_ok XA (by simp)) S.stk.tail b1 hb1.cst hs1 (by omega)) (by omega)
    (fun x hx => hx)) (fun b2 hb2 => ?_)) le_rfl (fun x hx => hx)
  obtain ⟨v2', hs2, k2⟩ := hb2
  have hb2 := hb1.pop (by simp) k2
  have hXB : b2.env XB = S.stk.headD 0 := by rw [k2.env XB (by unfold PopT SkT; simp), v1]
  refine Hs.mono (t := 3 + 11 + 1) (Hs.seq (htag b2 hb2.cst) (fun b3 hb3 => ?_)) le_rfl (fun x hx => hx)
  obtain ⟨t3, k3⟩ := hb3
  have k3' : Keep MachT MachR MachM b2 b3 := k3.mono (fun y hy => by unfold MachT; omega) (fun _ h => h.elim)
    (fun _ h => h.elim)
  have hb3 : RepB w D S b3 := hb2.keep k3' (k3.env CNT (by simp)) (k3.ram NS id) (k3.rc NS id)
    (by rw [k3.rc WM id]; exact hb2.wc)
  have hs3 : StkOk b3 S.stk.tail.tail := by
    obtain ⟨s1, s2, s3⟩ := hs2
    exact ⟨by rw [k3.env HR (by simp)]; exact s1, by rw [k3.rc STK id]; exact s2, by rw [k3.ram STK id]; exact s3⟩
  refine Hs.mono (emitN_spec w D S S.stk.tail.tail (mk (S.stk.tail.headD 0) (S.stk.headD 0)) (hA _ _) TT XA XB b3
    hb3 hs3 (by rw [t3, hT]) (by rw [k3.env XA (by simp), v2', hL]) (by rw [k3.env XB (by simp), hXB, hR]) hW1
    (by omega)) le_rfl ?_
  rintro x ⟨r, k⟩
  exact ⟨r, (keep_pop_mach (by simp) k1).trans ((keep_pop_mach (by simp) k2).trans (k3'.trans k))⟩

theorem exec_spec {n arity : ℕ} (w : List ℕ) (D : List Bool) (S : PS n arity) (tk : Tok) (a : DS VV MM)
    (h : Rep w D S a) (hreg : TokReg a tk) (hW1 : S.cnt + 1 < 2 ^ C.Wd) (hW2 : S.stk.length + 1 < 2 ^ C.Wd)
    (hW3 : w.length < 2 ^ C.Wd) (h8 : 8 ≤ 2 ^ C.Wd) :
    Hs C (execTok tk) a (tokCost S.stk.length w.length) (fun b => Rep w D (S.step w tk) b ∧
      Keep MachT MachR MachM a b) := by
  obtain ⟨hb, hs⟩ := h
  cases tk with
  | cst b =>
      simp only [TokReg] at hreg
      refine Hs.mono (emitN_spec w D S S.stk (.const b) rfl vZ BV vZ a hb hs (by rw [hb.cst.z]; rfl)
        (by rw [hreg]; rfl) (by rw [hb.cst.z]; rfl) hW1 hW2) (by unfold tokCost; omega) (fun x hx => hx)
  | wir k =>
      simp only [TokReg] at hreg
      have hKX : ¬ SkT KX.val := by unfold SkT; decide
      have hKW : KX ≠ WL := by decide
      -- the read value
      have key : Hs C (.ite (.lt KX WL) (.seq (seek WM KX) (.op (.rdM WM XA))) (.op (.zero XA))) a
          (6 * w.length + 9) (fun b => b.env XA = w.getD k 0 ∧ Keep MachT MachR MachM a b ∧ b.rc WM ≤ w.length ∧
            b.rc NS = a.rc NS ∧ b.rc STK = a.rc STK ∧ b.env CNT = a.env CNT ∧ b.env HR = a.env HR ∧
            b.ram = a.ram) := by
        refine Hs.ite (C := C) hKW (fun he => ?_) (fun he => ?_)
        · simp only [Cnd.eval, decide_eq_true_eq, hreg, hb.wl] at he
          have hk1 : a.env KX ≤ (a.ram WM).length := by rw [hreg, hb.wm]; omega
          refine Hs.mono (t := (a.rc WM + 5 * a.env KX + 6) + 1 + 1)
            (Hs.seq (seek_spec WM KX hKX a hk1 (by rw [hreg]; omega)) (fun b1 hb1 => ?_))
            (by rw [hreg]; have := hb.wc; omega) (fun x hx => hx)
          obtain ⟨r1, k1⟩ := hb1
          have hram : b1.ram WM = w := by rw [k1.ram WM id, hb.wm]
          refine Hs.mono (hs_rdM C WM XA b1 (by rw [r1, hram, hreg]; exact he)) le_rfl ?_
          rintro x rfl
          have k2 : Keep MachT MachR MachM b1 ((b1.set XA ((b1.ram WM).getD (b1.rc WM) 0)).adv WM) :=
            ⟨fun y hy => by simp only [DS.adv]; exact DS.set_env_ne _ _ (neP hy (show MachT XA.val by
                unfold MachT; decide)),
              fun _ _ => rfl, fun m hm => by
                simp only [DS.adv, DS.set_rc]
                exact Function.update_of_ne (neM (by rw [WM_val]; unfold MachM at hm; omega)) _ _,
              rfl, rfl, rfl, rfl, rfl⟩
          have k1' : Keep MachT MachR MachM a b1 := k1.mono (fun y hy => by unfold SkT at hy; unfold MachT; omega)
            (fun _ h => h.elim) (fun m hm => by rw [hm]; unfold MachM; decide)
          refine ⟨by simp only [DS.adv]; rw [DS.set_env_self, r1, hram, hreg], k1'.trans k2, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · simp only [DS.adv, DS.set_rc, Function.update_self, r1, hreg]; omega
          · simp only [DS.adv, DS.set_rc]; rw [Function.update_of_ne (by decide), k1.rc NS (by decide)]
          · simp only [DS.adv, DS.set_rc]; rw [Function.update_of_ne (by decide), k1.rc STK (by decide)]
          · simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide), k1.env CNT (by unfold SkT; decide)]
          · simp only [DS.adv]; rw [DS.set_env_ne _ _ (by decide), k1.env HR (by unfold SkT; decide)]
          · simp only [DS.adv, DS.set_ram]; exact funext fun m => k1.ram m id
        · simp only [Cnd.eval, decide_eq_false_iff_not, hreg, hb.wl, not_lt] at he
          refine Hs.mono (hs_zero C XA a) (by omega) ?_
          rintro x rfl
          refine ⟨by rw [DS.set_env_self, List.getD_eq_default _ _ he], Keep.set a XA 0 (by unfold MachT; decide),
            hb.wc, rfl, rfl, DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), rfl⟩
      refine Hs.mono (t := (6 * w.length + 9) + 3 + 1) (Hs.seq key (fun b1 hb1 => ?_))
        (by unfold tokCost; omega) (fun x hx => hx)
      obtain ⟨v1, k1, wc1, nc1, sc1, c1, h1, r1⟩ := hb1
      have hs1 : StkOk b1 S.stk := by
        obtain ⟨s1, s2, s3⟩ := hs
        exact ⟨by rw [h1, s1], by rw [sc1, s2], by rw [r1]; exact s3⟩
      refine Hs.mono (push_spec XA S.stk b1 hs1 hW2) le_rfl ?_
      rintro b2 ⟨hs2, k2⟩
      have k12 : Keep MachT MachR MachM a b2 := k1.trans (k2.mono (fun y hy => by unfold HrT at hy; unfold MachT; omega)
        (fun m hm => by unfold MachR; omega) (fun m hm => by unfold MachM; omega))
      refine ⟨⟨?_, by rw [v1] at hs2; exact hs2⟩, k12⟩
      refine RepB.congr (S := S) ?_ rfl rfl
      exact ⟨k12.cst (by unfold MachT; omega) hb.cst, by rw [k2.env CNT (by unfold HrT; decide), c1, hb.cnt],
        by rw [k2.ram NS (by decide), r1, hb.ns], by rw [k2.rc NS (by decide), nc1, k2.ram NS (by decide), r1, hb.nsc],
        by rw [k12.ram WM (by unfold MachR; decide), hb.wm], by rw [k12.env WL (by unfold MachT; decide), hb.wl],
        by rw [k2.rc WM (by decide)]; exact wc1, by rw [k12.ram DSt (by unfold MachR; decide), hb.dsr],
        by rw [k12.env DL (by unfold MachT; decide), hb.dl], by rw [k12.rc DSt (by unfold MachM; decide)]; exact hb.dc⟩
  | neg =>
      refine Hs.mono (t := (12 * S.stk.length + 30) + 11 + 1)
        (Hs.seq (pop_spec XA (pop_ok XA (by simp)) S.stk a hb.cst hs (by omega)) (fun b1 hb1 => ?_))
        (by unfold tokCost; omega) (fun x hx => hx)
      obtain ⟨v1, hs1, k1⟩ := hb1
      have hb1 := hb.pop (by simp) k1
      have c1 : Cst b1 := hb1.cst
      refine Hs.mono (emitN_spec w D S S.stk.tail (.not (S.stk.headD 0)) rfl v2 XA vZ b1 hb1 hs1 (by rw [c1.two]; rfl)
        (by rw [v1]; rfl) (by rw [c1.z]; rfl) hW1 (by rw [List.length_tail]; omega)) le_rfl ?_
      rintro x ⟨r, k⟩
      exact ⟨r, (keep_pop_mach (by simp) k1).trans k⟩
  | conj =>
      exact execBin_spec w D S a ⟨hb, hs⟩ tag3 3 (fun b hc => tag3_spec h8 b hc) hW1 hW2
        (fun x y => .and x y) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) .conj rfl
  | disj =>
      exact execBin_spec w D S a ⟨hb, hs⟩ tag4 4 (fun b hc => tag4_spec h8 b hc) hW1 hW2
        (fun x y => .or x y) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) .disj rfl

end NearCubicGates.Adapters.Compile.OraclePrint
