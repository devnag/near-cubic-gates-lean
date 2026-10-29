import SourceAdapters.Compile.CNFCodeBits
import Proof.Gates.Cells.Kit

/-!
# Cell-program helpers for the query printer

Support for `CNFAssembly.CNFProgramRuns` (proof of `lem:multitape-refuter`: the query is actually written; proof of `cor:framed-refuter`: within a
fixed polynomial). Contents:

* the fixed register/store layout of the printer;
* `wpc`: a weakest precondition with cost for loop-free cell code, sound for `Ex` (`hs_of_wpc`), so straight-line
  blocks are discharged by unfolding instead of chains of `Hs.seq`;
* `tcode`, `Ext`: the token log (store `sTT`) and its extension relation;
* `forP`, `anyP`, `allP`: counted loops that append `(range K).flatMap f`, `anyT K f`, `allT K f`, with specs generic
  in the body's spec and an invariant `P` stable under the loop's effects.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells
set_option autoImplicit false

/-! ## Register and store layout -/

def sCB : Fin MM := ⟨0, by decide⟩
def sIB : Fin MM := ⟨1, by decide⟩
def sTT : Fin MM := ⟨2, by decide⟩
def sWM : Fin MM := ⟨3, by decide⟩
def sNW : Fin MM := ⟨4, by decide⟩
def sSK : Fin MM := ⟨5, by decide⟩
def sCL : Fin MM := ⟨6, by decide⟩
def sTK : Fin MM := ⟨7, by decide⟩
def sVS : Fin MM := ⟨8, by decide⟩

def kc3 : Fin VV := ⟨14, by decide⟩
def kc4 : Fin VV := ⟨15, by decide⟩
def kc5 : Fin VV := ⟨16, by decide⟩
def kc6 : Fin VV := ⟨17, by decide⟩
def kc7 : Fin VV := ⟨18, by decide⟩
def kc8 : Fin VV := ⟨19, by decide⟩

def dT : Fin VV := ⟨20, by decide⟩
def dS : Fin VV := ⟨21, by decide⟩
def dWb : Fin VV := ⟨22, by decide⟩
def dN : Fin VV := ⟨23, by decide⟩
def dF : Fin VV := ⟨24, by decide⟩
def dH : Fin VV := ⟨25, by decide⟩
def dWd : Fin VV := ⟨26, by decide⟩
def dTW : Fin VV := ⟨27, by decide⟩
def dW : Fin VV := ⟨28, by decide⟩
def dM : Fin VV := ⟨29, by decide⟩
def dR : Fin VV := ⟨30, by decide⟩
def dO2 : Fin VV := ⟨31, by decide⟩
def dO3 : Fin VV := ⟨32, by decide⟩
def dIL : Fin VV := ⟨33, by decide⟩
def dSt : Fin VV := ⟨34, by decide⟩

def gJ : Fin VV := ⟨40, by decide⟩
def gQ : Fin VV := ⟨41, by decide⟩
def gM : Fin VV := ⟨42, by decide⟩
def gA : Fin VV := ⟨43, by decide⟩
def gB : Fin VV := ⟨44, by decide⟩
def gC : Fin VV := ⟨45, by decide⟩
def gX : Fin VV := ⟨46, by decide⟩
def gY : Fin VV := ⟨47, by decide⟩
def gZ : Fin VV := ⟨48, by decide⟩
def gU : Fin VV := ⟨49, by decide⟩
def gV : Fin VV := ⟨50, by decide⟩
def gP : Fin VV := ⟨51, by decide⟩
def gE : Fin VV := ⟨52, by decide⟩
def gK : Fin VV := ⟨53, by decide⟩
def gL : Fin VV := ⟨54, by decide⟩
def gR : Fin VV := ⟨55, by decide⟩
def gS : Fin VV := ⟨56, by decide⟩
def gT : Fin VV := ⟨57, by decide⟩

/-- Close `Fr a b T` when `b` is `a` with some registers set. -/
macro "fr_tac" : tactic =>
  `(tactic| (intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy; simp [DS.set, Function.update_apply, hy]))

/-- `fr_tac` unfolding the named register lists first. -/
macro "frx" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (intro y hy; simp only [$ls,*, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy; simp [DS.set, Function.update_apply, hy]))

/-- Split a conjunction goal into its conjuncts. -/
macro "and_split" : tactic => `(tactic| (repeat' apply And.intro))

/-! ## Weakest precondition with cost (loop-free code) -/

/-- One operation. Unsupported operations (input back-step, sort, calls) have precondition `False`. -/
def opwp (C : Ctx) : Op VV MM → (DS VV MM → ℕ → Prop) → DS VV MM → Prop
  | .zero x, R, a => R (a.set x 0) 1
  | .inc x, R, a => a.env x + 1 < 2 ^ C.Wd ∧ R (a.set x (a.env x + 1)) 1
  | .add x y, R, a => x ≠ y ∧ a.env x + a.env y < 2 ^ C.Wd ∧ R (a.set x (a.env x + a.env y)) 1
  | .sub x y, R, a => x ≠ y ∧ a.env y ≤ a.env x ∧ R (a.set x (a.env x - a.env y)) 1
  | .copy x y, R, a => x ≠ y ∧ R (a.set x (a.env y)) 1
  | .half x, R, a => R (a.set x (a.env x / 2)) 1
  | .shl x, R, a => 2 * a.env x < 2 ^ C.Wd ∧ R (a.set x (2 * a.env x)) 1
  | .mul x y z, R, a => x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ a.env x * a.env y < 2 ^ C.Wd ∧ R (a.set z (a.env x * a.env y)) 1
  | .dm x y q r, R, a => x ≠ y ∧ x ≠ q ∧ x ≠ r ∧ y ≠ q ∧ y ≠ r ∧ q ≠ r ∧ 0 < a.env y ∧ 2 * a.env y ≤ 2 ^ C.Wd ∧
      R ((a.set q (a.env x / a.env y)).set r (a.env x % a.env y)) 1
  | .rdI x, R, a => a.ip < C.inp.length ∧ R { a.set x (bitOf C.inp a.ip) with ip := a.ip + 1 } 1
  | .emit b, R, a => R { a with out := a.out ++ [b] } 1
  | .rdM m x, R, a => a.rc m < (a.ram m).length ∧ R ((a.set x ((a.ram m).getD (a.rc m) 0)).adv m) 1
  | .wrM m x, R, a => a.rc m ≤ (a.ram m).length ∧ R (a.put m (a.env x)) 1
  | .rwM m, R, a => R (a.rew m) (a.rc m + 1)
  | _, _, _ => False

/-- Loop-free programs; loops have precondition `False`. -/
def wpc (C : Ctx) : St VV MM → (DS VV MM → ℕ → Prop) → DS VV MM → Prop
  | .op o, R, a => opwp C o R a
  | .seq s t, R, a => wpc C s (fun b n => wpc C t (fun d k => R d (n + k + 1)) b) a
  | .ite c s t, R, a => c.wf ∧ (c.eval a = true → wpc C s (fun b n => R b (n + 1)) a) ∧
      (c.eval a = false → wpc C t (fun b n => R b (n + 1)) a)
  | .loop _ _, _, _ => False

theorem opwp_sound {C : Ctx} (o : Op VV MM) (R : DS VV MM → ℕ → Prop) (a : DS VV MM) (h : opwp C o R a) :
    ∃ b k, OpEx C o a b k ∧ R b k := by
  cases o with
  | zero x => exact ⟨_, _, OpEx.zero x a, h⟩
  | inc x => exact ⟨_, _, OpEx.inc x a h.1, h.2⟩
  | add x y => exact ⟨_, _, OpEx.add x y a h.1 h.2.1, h.2.2⟩
  | sub x y => exact ⟨_, _, OpEx.sub x y a h.1 h.2.1, h.2.2⟩
  | copy x y => exact ⟨_, _, OpEx.copy x y a h.1, h.2⟩
  | half x => exact ⟨_, _, OpEx.half x a, h⟩
  | shl x => exact ⟨_, _, OpEx.shl x a h.1, h.2⟩
  | mul x y z => exact ⟨_, _, OpEx.mul x y z a h.1 h.2.1 h.2.2.1 h.2.2.2.1, h.2.2.2.2⟩
  | dm x y q r =>
      exact ⟨_, _, OpEx.dm x y q r a h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1
        h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2⟩
  | rdI x => exact ⟨_, _, OpEx.rdI x a h.1, h.2⟩
  | bkI => exact h.elim
  | emit b => exact ⟨_, _, OpEx.emit b a, h⟩
  | rdM m x => exact ⟨_, _, OpEx.rdM m x a h.1, h.2⟩
  | wrM m x => exact ⟨_, _, OpEx.wrM m x a h.1, h.2⟩
  | rwM m => exact ⟨_, _, OpEx.rwM m a, h⟩
  | srtM m => exact h.elim
  | kem b => exact h.elim
  | kcall => exact h.elim
  | rdK x => exact h.elim

theorem wpc_sound {C : Ctx} (s : St VV MM) :
    ∀ (R : DS VV MM → ℕ → Prop) (a : DS VV MM), wpc C s R a → ∃ b n, Ex C s a b n ∧ R b n := by
  induction s with
  | op o => intro R a h; obtain ⟨b, k, h1, h2⟩ := opwp_sound o R a h; exact ⟨b, k, Ex.op h1, h2⟩
  | seq s t ihs iht =>
      intro R a h
      obtain ⟨b, n, h1, h2⟩ := ihs _ a h
      obtain ⟨d, k, h3, h4⟩ := iht _ b h2
      exact ⟨d, n + k + 1, Ex.seq h1 h3, h4⟩
  | ite c s t ihs iht =>
      intro R a h
      obtain ⟨hw, h1, h2⟩ := h
      cases he : c.eval a
      · obtain ⟨b, n, h3, h4⟩ := iht _ a (h2 he)
        exact ⟨b, n + 1, Ex.iteF hw he h3, h4⟩
      · obtain ⟨b, n, h3, h4⟩ := ihs _ a (h1 he)
        exact ⟨b, n + 1, Ex.iteT hw he h3, h4⟩
  | loop c s _ => intro R a h; exact h.elim

theorem hs_of_wpc {C : Ctx} {s : St VV MM} {a : DS VV MM} {t : ℕ} {R : DS VV MM → Prop}
    (h : wpc C s (fun b n => n ≤ t ∧ R b) a) : Hs C s a t R := by
  obtain ⟨b, n, h1, h2, h3⟩ := wpc_sound s _ a h
  exact ⟨b, n, h1, h2, h3⟩

/-- Sequencing with a total cost bound. -/
theorem Hs.seqc {C : Ctx} {s u : St VV MM} {a : DS VV MM} {t1 t2 t : ℕ} {R1 R2 : DS VV MM → Prop}
    (h1 : Hs C s a t1 R1) (h2 : ∀ b, R1 b → Hs C u b t2 R2) (ht : t1 + t2 + 1 ≤ t) : Hs C (.seq s u) a t R2 :=
  Hs.mono (Hs.seq h1 h2) ht (fun _ h => h)

/-! ## Token log -/

def tcode : RTok → ℕ
  | .cst b => 8 * b.toNat
  | .inp j => 8 * j + 1
  | .wir k => 8 * k + 2
  | .neg => 3
  | .conj => 4
  | .disj => 5
  | .save => 6
  | .swap => 7

/-- `b` extends the token log of `a` by `toks` and changes no other store or cursor, the input head or the
output. -/
structure Ext (a b : DS VV MM) (toks : List RTok) : Prop where
  tt : b.ram sTT = a.ram sTT ++ toks.map tcode
  rc : b.rc sTT = a.rc sTT + toks.length
  ram : ∀ m, m ≠ sTT → b.ram m = a.ram m
  rcs : ∀ m, m ≠ sTT → b.rc m = a.rc m
  ip : b.ip = a.ip
  out : b.out = a.out

theorem Ext.refl (a : DS VV MM) : Ext a a [] := ⟨by simp, by simp, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- No store, cursor, input head or output change. -/
theorem Ext.of_eq {a b : DS VV MM} (h1 : b.ram = a.ram) (h2 : b.rc = a.rc) (h3 : b.ip = a.ip) (h4 : b.out = a.out) :
    Ext a b [] := ⟨by simp [h1], by simp [h2], fun m _ => by rw [h1], fun m _ => by rw [h2], h3, h4⟩

theorem Ext.trans {a b d : DS VV MM} {t1 t2 : List RTok} (h1 : Ext a b t1) (h2 : Ext b d t2) :
    Ext a d (t1 ++ t2) :=
  ⟨by rw [h2.tt, h1.tt]; simp, by rw [h2.rc, h1.rc]; simp; omega, fun m hm => (h2.ram m hm).trans (h1.ram m hm),
    fun m hm => (h2.rcs m hm).trans (h1.rcs m hm), h2.ip.trans h1.ip, h2.out.trans h1.out⟩

theorem Ext.congr {a b : DS VV MM} {t1 t2 : List RTok} (h : Ext a b t1) (e : t1 = t2) : Ext a b t2 := e ▸ h

/-- Close the routine side goals of a straight-line block. -/
macro "wp_fin" : tactic =>
  `(tactic| (all_goals first | omega | exact Ext.of_eq rfl rfl rfl rfl | fr_tac | rfl | decide))

/-- Close `Ext a b toks` when `b` is `a` with registers set and codes appended to the token log by `wpc`. -/
macro "ext_tac" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (refine ⟨?_, ?_, fun m hm => by simp [Function.update_of_ne hm],
    fun m hm => by simp [Function.update_of_ne hm], rfl, rfl⟩ <;> simp [tcode, $ls,*] <;> (try and_split) <;> ring_nf))

/-- The token cursor is at the end of the log. -/
def TTend (a : DS VV MM) : Prop := a.rc sTT = (a.ram sTT).length

theorem TTend.of_ext {a b : DS VV MM} {toks : List RTok} (ha : TTend a) (h : Ext a b toks) : TTend b := by
  unfold TTend at *
  rw [h.rc, h.tt, ha]
  simp

/-- The program constants. -/
structure KC (a : DS VV MM) : Prop where
  z : a.env vZ = 0
  one : a.env v1 = 1
  two : a.env v2 = 2
  k3 : a.env kc3 = 3
  k4 : a.env kc4 = 4
  k5 : a.env kc5 = 5
  k6 : a.env kc6 = 6
  k7 : a.env kc7 = 7
  k8 : a.env kc8 = 8

/-- Registers holding the constants. -/
def kcRegs : List (Fin VV) := [vZ, v1, v2, kc3, kc4, kc5, kc6, kc7, kc8]

theorem KC.of_fr {a b : DS VV MM} {T : List (Fin VV)} (h : KC a) (hf : Fr a b T) (hT : ∀ y ∈ kcRegs, y ∉ T) :
    KC b := by
  have e : ∀ y ∈ kcRegs, b.env y = a.env y := fun y hy => hf y (hT y hy)
  exact ⟨by rw [e vZ (by decide)]; exact h.z, by rw [e v1 (by decide)]; exact h.one,
    by rw [e v2 (by decide)]; exact h.two, by rw [e kc3 (by decide)]; exact h.k3,
    by rw [e kc4 (by decide)]; exact h.k4, by rw [e kc5 (by decide)]; exact h.k5,
    by rw [e kc6 (by decide)]; exact h.k6, by rw [e kc7 (by decide)]; exact h.k7,
    by rw [e kc8 (by decide)]; exact h.k8⟩

/-! ## Emitting tokens -/

variable {C : Ctx}

/-- Append the token whose code is in `x`. -/
def emitR (x : Fin VV) : St VV MM := .op (.wrM sTT x)

theorem emitR_spec (x : Fin VV) (tok : RTok) (a : DS VV MM) (hT : TTend a) (hx : a.env x = tcode tok) :
    Hs C (emitR x) a 1 (fun b => Ext a b [tok] ∧ Fr a b []) := by
  unfold TTend at hT
  refine Hs.op (OpEx.wrM sTT x a (le_of_eq hT)) ⟨⟨?_, ?_, ?_, ?_, rfl, rfl⟩, fun _ _ => rfl⟩
  · simp [DS.put, putAt, hT, hx]
  · simp [DS.put]
  · intro m hm
    simp [DS.put, Function.update_of_ne hm]
  · intro m hm
    simp [DS.put, Function.update_of_ne hm]

/-- Append `wir (env r)`: `gX := 8·r + 2`. -/
def emitWir (r : Fin VV) : St VV MM := .seq (.op (.mul r kc8 gX)) (.seq (.op (.add gX v2)) (emitR gX))

theorem emitWir_spec (r : Fin VV) (hr1 : r ≠ kc8) (hr2 : r ≠ gX) (a : DS VV MM) (hT : TTend a) (hk : KC a)
    (hW : 8 * a.env r + 2 < 2 ^ C.Wd) :
    Hs C (emitWir r) a 5 (fun b => Ext a b [.wir (a.env r)] ∧ Fr a b [gX]) := by
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_mul C r kc8 gX a hr1 hr2 (by decide) (by rw [hk.k8]; omega))
    (fun b hb => ?_)
  subst hb
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_add C gX v2 _ (by decide) (by vsimp [hk.two, hk.k8]; omega))
    (fun d hd => ?_)
  subst hd
  refine Hs.mono (emitR_spec gX (.wir (a.env r)) _ (by unfold TTend at *; simpa using hT)
    (by vsimp [hk.two, hk.k8, tcode]; ring)) le_rfl ?_
  rintro e ⟨h1, h2⟩
  refine ⟨⟨by rw [h1.tt]; simp, by rw [h1.rc]; simp, fun m hm => by rw [h1.ram m hm]; simp,
    fun m hm => by rw [h1.rcs m hm]; simp, by rw [h1.ip]; simp, by rw [h1.out]; simp⟩, fun y hy => ?_⟩
  rw [h2 y (by simp)]
  have : y ≠ gX := by simpa using hy
  vsimp [this]

/-- Append `inp (env r)`: `gX := 8·r + 1`. -/
def emitInp (r : Fin VV) : St VV MM := .seq (.op (.mul r kc8 gX)) (.seq (.op (.inc gX)) (emitR gX))

theorem emitInp_spec (r : Fin VV) (hr1 : r ≠ kc8) (hr2 : r ≠ gX) (a : DS VV MM) (hT : TTend a) (hk : KC a)
    (hW : 8 * a.env r + 2 < 2 ^ C.Wd) :
    Hs C (emitInp r) a 5 (fun b => Ext a b [.inp (a.env r)] ∧ Fr a b [gX]) := by
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_mul C r kc8 gX a hr1 hr2 (by decide) (by rw [hk.k8]; omega))
    (fun b hb => ?_)
  subst hb
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_inc C gX _ (by vsimp [hk.k8]; omega)) (fun d hd => ?_)
  subst hd
  refine Hs.mono (emitR_spec gX (.inp (a.env r)) _ (by unfold TTend at *; simpa using hT)
    (by vsimp [hk.k8, tcode]; ring)) le_rfl ?_
  rintro e ⟨h1, h2⟩
  refine ⟨⟨by rw [h1.tt]; simp, by rw [h1.rc]; simp, fun m hm => by rw [h1.ram m hm]; simp,
    fun m hm => by rw [h1.rcs m hm]; simp, by rw [h1.ip]; simp, by rw [h1.out]; simp⟩, fun y hy => ?_⟩
  rw [h2 y (by simp)]
  have : y ≠ gX := by simpa using hy
  vsimp [this]

/-! ## Counted loops appending tokens -/

/-- `for c < lim: body`. -/
def forP (c lim : Fin VV) (body : St VV MM) : St VV MM :=
  .seq (.op (.zero c)) (.loop (.lt c lim) (.seq body (.op (.inc c))))

theorem forP_spec (c lim : Fin VV) (body : St VV MM) (T : List (Fin VV)) (hcl : c ≠ lim) (hcT : c ∉ T)
    (P : DS VV MM → Prop) (K t : ℕ) (f : ℕ → List RTok)
    (hPl : ∀ a, P a → a.env lim = K)
    (hP : ∀ a b toks, P a → Ext a b toks → Fr a b (c :: T) → P b)
    (hK : K < 2 ^ C.Wd)
    (hbody : ∀ i < K, ∀ a, P a → a.env c = i → Hs C body a t (fun b => Ext a b (f i) ∧ Fr a b T))
    (a : DS VV MM) (ha : P a) :
    Hs C (forP c lim body) a (K * (t + 4) + 4)
      (fun b => Ext a b ((List.range K).flatMap f) ∧ Fr a b (c :: T)) := by
  let I : ℕ → DS VV MM → Prop := fun k b =>
    P b ∧ b.env c = k ∧ Ext a b ((List.range k).flatMap f) ∧ Fr a b (c :: T)
  have h0 : I 0 (a.set c 0) := by
    refine ⟨hP a _ [] ha (Ext.of_eq rfl rfl rfl rfl) (Fr.set a 0 (by simp)), by simp,
      Ext.of_eq rfl rfl rfl rfl, Fr.set a 0 (by simp)⟩
  have hloop := Hs.loopN (C := C) (c := .lt c lim) (s := .seq body (.op (.inc c))) hcl I K (t + 2)
    (fun k hk b hb => by
      obtain ⟨hPb, hcb, hEb, hFb⟩ := hb
      refine ⟨by simp [Cnd.eval, hcb, hPl b hPb, hk], ?_⟩
      refine Hs.seq (t1 := t) (t2 := 1) (hbody k hk b hPb hcb) (fun d ⟨hEd, hFd⟩ => ?_)
      have hcd : d.env c = k := by rw [hFd c hcT, hcb]
      refine Hs.op (OpEx.inc c d (by rw [hcd]; omega)) ?_
      have hE' : Ext d (d.set c (d.env c + 1)) [] := Ext.of_eq rfl rfl rfl rfl
      have hF' : Fr d (d.set c (d.env c + 1)) (c :: T) := Fr.set d _ (by simp)
      have hFbd : Fr b d (c :: T) := Fr.weaken hFd (fun y hy => by simp [hy])
      refine ⟨hP d _ [] (hP b d (f k) hPb hEd hFbd) hE' hF', by simp [hcd], ?_, ?_⟩
      · refine (hEb.trans (hEd.trans hE')).congr ?_
        rw [List.range_succ, List.flatMap_append]
        simp
      · exact hFb.trans (hFbd.trans hF'))
    (fun b hb => by simp [Cnd.eval, hb.2.1, hPl b hb.1])
  have hfull : Hs C (forP c lim body) a (1 + (K * (t + 2 + 2) + 2) + 1)
      (fun b => Ext a b ((List.range K).flatMap f) ∧ Fr a b (c :: T)) := by
    refine Hs.seq (hs_zero C c a) (fun b hb => ?_)
    subst hb
    refine Hs.mono (hloop _ h0) le_rfl ?_
    rintro b ⟨_, _, hE, hF⟩
    exact ⟨hE, hF⟩
  exact Hs.mono hfull (by ring_nf; omega) (fun b h => h)

theorem flatMap_const_range (K : ℕ) (x : RTok) : (List.range K).flatMap (fun _ => [x]) = List.replicate K x := by
  induction K with
  | zero => rfl
  | succ K ih => rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ']; rfl

/-- Append `tok` `lim` times (the token code in `x`). -/
def repP (c lim x : Fin VV) : St VV MM := forP c lim (emitR x)

theorem repP_spec (c lim x : Fin VV) (hcl : c ≠ lim) (P : DS VV MM → Prop) (K : ℕ) (tok : RTok)
    (hPl : ∀ a, P a → a.env lim = K) (hPx : ∀ a, P a → TTend a ∧ a.env x = tcode tok)
    (hP : ∀ a b toks, P a → Ext a b toks → Fr a b [c] → P b) (hK : K < 2 ^ C.Wd) (a : DS VV MM) (ha : P a) :
    Hs C (repP c lim x) a (K * 5 + 4) (fun b => Ext a b (List.replicate K tok) ∧ Fr a b [c]) := by
  have := forP_spec (C := C) c lim (emitR x) [] hcl (by simp) P K 1 (fun _ => [tok]) hPl hP hK
    (fun i _ b hb _ => emitR_spec x tok b (hPx b hb).1 (hPx b hb).2) a ha
  rw [flatMap_const_range] at this
  exact this

/-- `anyT`: the body for `c < lim`, then `false`, then `lim` disjunctions. -/
def anyP (c lim : Fin VV) (body : St VV MM) : St VV MM :=
  .seq (forP c lim body) (.seq (emitR vZ) (repP c lim kc5))

/-- `allT`: the body for `c < lim`, then `true`, then `lim` conjunctions. -/
def allP (c lim : Fin VV) (body : St VV MM) : St VV MM :=
  .seq (forP c lim body) (.seq (emitR kc8) (repP c lim kc4))

theorem anyP_spec (c lim : Fin VV) (body : St VV MM) (T : List (Fin VV)) (hcl : c ≠ lim) (hcT : c ∉ T)
    (P : DS VV MM → Prop) (K t : ℕ) (f : ℕ → List RTok)
    (hPl : ∀ a, P a → a.env lim = K) (hPk : ∀ a, P a → TTend a ∧ KC a)
    (hP : ∀ a b toks, P a → Ext a b toks → Fr a b (c :: T) → P b)
    (hK : K < 2 ^ C.Wd)
    (hbody : ∀ i < K, ∀ a, P a → a.env c = i → Hs C body a t (fun b => Ext a b (f i) ∧ Fr a b T))
    (a : DS VV MM) (ha : P a) :
    Hs C (anyP c lim body) a (K * (t + 4) + K * 5 + 12) (fun b => Ext a b (anyT K f) ∧ Fr a b (c :: T)) := by
  refine Hs.mono (Hs.seq (t1 := K * (t + 4) + 4) (t2 := 1 + (K * 5 + 4) + 1)
    (R1 := fun b => Ext a b ((List.range K).flatMap f) ∧ Fr a b (c :: T))
    (R2 := fun b => Ext a b (anyT K f) ∧ Fr a b (c :: T))
    (forP_spec c lim body T hcl hcT P K t f hPl hP hK hbody a ha) (fun b hb => ?_)) (by omega) (fun b h => h)
  obtain ⟨hE1, hF1⟩ := hb
  have hPb : P b := hP a b _ ha hE1 hF1
  refine Hs.seq (t1 := 1) (t2 := K * 5 + 4) (R1 := fun d => Ext b d [.cst false] ∧ Fr b d [])
    (emitR_spec vZ (.cst false) b (hPk b hPb).1 (by rw [(hPk b hPb).2.z]; rfl)) (fun d hd => ?_)
  obtain ⟨hE2, hF2⟩ := hd
  have hPd : P d := hP b d _ hPb hE2 (Fr.weaken hF2 (by simp))
  refine Hs.mono (repP_spec c lim kc5 hcl P K .disj hPl
    (fun e he => ⟨(hPk e he).1, by rw [(hPk e he).2.k5]; rfl⟩)
    (fun e g toks he hE hF => hP e g toks he hE (Fr.weaken hF (by simp))) hK d hPd) le_rfl ?_
  rintro e ⟨hE3, hF3⟩
  refine ⟨(hE1.trans (hE2.trans hE3)).congr (by simp [anyT]), ?_⟩
  exact hF1.trans ((Fr.weaken hF2 (by simp)).trans (Fr.weaken hF3 (by simp)))

theorem allP_spec (c lim : Fin VV) (body : St VV MM) (T : List (Fin VV)) (hcl : c ≠ lim) (hcT : c ∉ T)
    (P : DS VV MM → Prop) (K t : ℕ) (f : ℕ → List RTok)
    (hPl : ∀ a, P a → a.env lim = K) (hPk : ∀ a, P a → TTend a ∧ KC a)
    (hP : ∀ a b toks, P a → Ext a b toks → Fr a b (c :: T) → P b)
    (hK : K < 2 ^ C.Wd)
    (hbody : ∀ i < K, ∀ a, P a → a.env c = i → Hs C body a t (fun b => Ext a b (f i) ∧ Fr a b T))
    (a : DS VV MM) (ha : P a) :
    Hs C (allP c lim body) a (K * (t + 4) + K * 5 + 12) (fun b => Ext a b (allT K f) ∧ Fr a b (c :: T)) := by
  refine Hs.mono (Hs.seq (t1 := K * (t + 4) + 4) (t2 := 1 + (K * 5 + 4) + 1)
    (R1 := fun b => Ext a b ((List.range K).flatMap f) ∧ Fr a b (c :: T))
    (R2 := fun b => Ext a b (allT K f) ∧ Fr a b (c :: T))
    (forP_spec c lim body T hcl hcT P K t f hPl hP hK hbody a ha) (fun b hb => ?_)) (by omega) (fun b h => h)
  obtain ⟨hE1, hF1⟩ := hb
  have hPb : P b := hP a b _ ha hE1 hF1
  refine Hs.seq (t1 := 1) (t2 := K * 5 + 4) (R1 := fun d => Ext b d [.cst true] ∧ Fr b d [])
    (emitR_spec kc8 (.cst true) b (hPk b hPb).1 (by rw [(hPk b hPb).2.k8]; rfl)) (fun d hd => ?_)
  obtain ⟨hE2, hF2⟩ := hd
  have hPd : P d := hP b d _ hPb hE2 (Fr.weaken hF2 (by simp))
  refine Hs.mono (repP_spec c lim kc4 hcl P K .conj hPl
    (fun e he => ⟨(hPk e he).1, by rw [(hPk e he).2.k4]; rfl⟩)
    (fun e g toks he hE hF => hP e g toks he hE (Fr.weaken hF (by simp))) hK d hPd) le_rfl ?_
  rintro e ⟨hE3, hF3⟩
  refine ⟨(hE1.trans (hE2.trans hE3)).congr (by simp [allT]), ?_⟩
  exact hF1.trans ((Fr.weaken hF2 (by simp)).trans (Fr.weaken hF3 (by simp)))

/-! ## Store lookup with the cursor restored -/

/-- `x := (ram m)[env p]`, cursor of `m` back at `0` (counter `gS`). -/
def lookP (m : Fin MM) (p x : Fin VV) : St VV MM :=
  .seq (.op (.zero gS)) (.seq (.loop (.lt gS p) (.seq (.op (.rdM m x)) (.op (.inc gS))))
    (.seq (.op (.rdM m x)) (.op (.rwM m))))

theorem lookP_spec (m : Fin MM) (p x : Fin VV) (hp : p ≠ gS) (hx : x ≠ gS) (hpx : p ≠ x) (a : DS VV MM)
    (h0 : a.rc m = 0) (hlen : a.env p < (a.ram m).length) (hW : a.env p + 1 < 2 ^ C.Wd) :
    Hs C (lookP m p x) a (6 * a.env p + 10) (fun b => b.env x = (a.ram m).getD (a.env p) 0 ∧
      Ext a b [] ∧ Fr a b [gS, x]) := by
  set P := a.env p with hP
  let I : ℕ → DS VV MM → Prop := fun k b => b.env gS = k ∧ b.rc m = k ∧ b.ram = a.ram ∧ b.ip = a.ip ∧
    b.out = a.out ∧ (∀ m', m' ≠ m → b.rc m' = a.rc m') ∧ Fr a b [gS, x]
  have hloop := Hs.loopN (C := C) (c := .lt gS p) (s := .seq (.op (.rdM m x)) (.op (.inc gS))) (Ne.symm hp) I P 3
    (fun k hk b hb => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hb
      have hpb : b.env p = P := by rw [h7 p (by simp [hp, hpx])]
      refine ⟨by simp [Cnd.eval, h1, hpb, hk], ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 1) (hs_rdM C m x b (by rw [h2, h3]; omega)) (fun b1 e1 => ?_)
      subst e1
      have g1 : ((b.set x ((b.ram m).getD (b.rc m) 0)).adv m).env gS = k := by
        simp [DS.adv, DS.set, Function.update_of_ne (Ne.symm hx), h1]
      refine Hs.op (OpEx.inc gS _ (by rw [g1]; omega)) ⟨by rw [DS.set_env_self, g1], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [DS.adv, h2]
      · simp [DS.adv, h3]
      · simp [DS.adv, h4]
      · simp [DS.adv, h5]
      · intro m' hm'
        simp [DS.adv, Function.update_of_ne hm', h6 m' hm']
      · intro y hy
        have hy' : y ≠ gS ∧ y ≠ x := by simpa using hy
        simp [DS.adv, DS.set, Function.update_apply, hy'.1, hy'.2, h7 y hy])
    (fun b hb => by
      obtain ⟨h1, _, _, _, _, _, h7⟩ := hb
      have hpb : b.env p = P := by rw [h7 p (by simp [hp, hpx])]
      simp [Cnd.eval, h1, hpb])
  refine Hs.mono (Hs.seq (t1 := 1) (t2 := P * (3 + 2) + 2 + (1 + (P + 1 + 1) + 1) + 1) (hs_zero C gS a)
    (fun b hb => ?_)) (by omega) (fun b h => h)
  subst hb
  refine Hs.seq (hloop _ ⟨by simp, by simp [h0], rfl, rfl, rfl, fun _ _ => rfl, Fr.set a 0 (by simp)⟩)
    (fun d hd => ?_)
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hd
  refine Hs.seq (t1 := 1) (t2 := P + 1 + 1) (hs_rdM C m x d (by rw [h2, h3]; omega)) (fun d1 e1 => ?_)
  subst e1
  have r1 : ((d.set x ((d.ram m).getD (d.rc m) 0)).adv m).rc m = P + 1 := by simp [DS.adv, h2]
  refine Hs.mono (hs_rwM C m _) (by rw [r1]) ?_
  rintro e rfl
  have hrc : ∀ m', (((d.set x ((d.ram m).getD (d.rc m) 0)).adv m).rew m).rc m' = a.rc m' := by
    intro m'
    by_cases e1 : m' = m
    · subst e1; simp [DS.rew, h0]
    · simp [DS.rew, DS.adv, Function.update_of_ne e1, h6 m' e1]
  have hram : (((d.set x ((d.ram m).getD (d.rc m) 0)).adv m).rew m).ram = a.ram := by simp [DS.rew, DS.adv, h3]
  refine ⟨?_, ⟨by rw [hram]; simp, by rw [hrc]; simp, fun m' _ => by rw [hram], fun m' _ => hrc m',
    by simp [DS.rew, DS.adv, h4], by simp [DS.rew, DS.adv, h5]⟩, ?_⟩
  · simp [DS.rew, DS.adv, DS.set, h2, h3]
  · intro y hy
    have hy' : y ≠ gS ∧ y ≠ x := by simpa using hy
    simp [DS.rew, DS.adv, DS.set, hy'.2, h7 y hy]

theorem lookP_at (m : Fin MM) (p x : Fin VV) (hp : p ≠ gS) (hx : x ≠ gS) (hpx : p ≠ x) (a : DS VV MM) (P : ℕ)
    (hpv : a.env p = P) (h0 : a.rc m = 0) (hlen : P < (a.ram m).length) (hW : P + 1 < 2 ^ C.Wd) :
    Hs C (lookP m p x) a (6 * P + 10) (fun b => b.env x = (a.ram m).getD P 0 ∧ Ext a b [] ∧ Fr a b [gS, x]) := by
  subst hpv
  exact lookP_spec m p x hp hx hpx a h0 hlen hW

end NearCubicGates.Adapters.Compile
