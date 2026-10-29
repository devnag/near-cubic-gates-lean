import Proof.Gates.Cells.Kit

/-!
# Cell-language routines for the top-level machine of input 6

The middle stage of P07 (proof of `thm:short-pcp-ours`, Step 4: "The algorithm `A` computes `T`, `M_n`, `par`, `S` and `C^O_x` in
`poly(n, log T)` time"; `app:short-pcp-proof`, "The exact Lean interface": "both computing and writing this word take `poly(n, log(t+2))` time") is one
program of the release's cell language (L `Proof/Gates/Cells/Lang.lean`, compiled to an ordinary machine by
`Cells.wordFunction_of_lang`). Its output is a doubly framed word, so every payload bit `b` is printed as
`[1, 1, 1, b]` (`dfr`), and a data counter `dR` counts the payload bits. This module gives the routines, on the
release's variable bank `VV` (`Cells.Mac`), with exact Hoare-style specifications (`Cells.Hs`):

* `lit w` prints a literal; `emitD x` prints `dfr [x]` and counts it; `setC x c` sets a constant;
* `copyTo e`: copy the input from the cursor (mirrored in `ipR`) up to the position in `e`, doubly framed;
* `rewindTo p`: move the cursor back to the position in `p`;
* `repL w cnt`: print `w` as many times as the value of `cnt`;
* `readNat`: read one `natWord` (L `Cells.Kit.rdNatI`), keeping `ipR` mirrored.

The parser of `frame x̄` and the copiers of the callee's output are in `AssemblyParse`.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Assembly

open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation NearCubicGates.Close.Cells

/-! ## Registers -/

/-- The mirror of the input cursor. -/
def ipR : Fin VV := ⟨40, by decide⟩
/-- The end of the input. -/
def endR : Fin VV := ⟨41, by decide⟩
/-- The start of `frame x̄`. -/
def p0R : Fin VV := ⟨42, by decide⟩
/-- The start of the code word. -/
def p1R : Fin VV := ⟨43, by decide⟩
/-- `n`. -/
def nR : Fin VV := ⟨44, by decide⟩
/-- `f`. -/
def fR : Fin VV := ⟨45, by decide⟩
/-- `natBitLength f`. -/
def kR : Fin VV := ⟨46, by decide⟩
/-- The number of payload bits printed so far. -/
def dR : Fin VV := ⟨47, by decide⟩
/-- `ℓ`. -/
def lR : Fin VV := ⟨48, by decide⟩
/-- The fuel. -/
def uR : Fin VV := ⟨49, by decide⟩
/-- Scratch. -/
def sA : Fin VV := ⟨50, by decide⟩
def sB : Fin VV := ⟨51, by decide⟩
def sC : Fin VV := ⟨52, by decide⟩
def sD : Fin VV := ⟨53, by decide⟩
def sE : Fin VV := ⟨54, by decide⟩
def sF : Fin VV := ⟨55, by decide⟩
def sG : Fin VV := ⟨56, by decide⟩
def sH : Fin VV := ⟨57, by decide⟩

variable {C : Ctx}

/-! ## State lemmas -/

theorem ds_ext {a b : DS VV MM} (he : a.env = b.env) (hi : a.ip = b.ip) (ho : a.out = b.out) (hr : a.ram = b.ram)
    (hc : a.rc = b.rc) (hki : a.kin = b.kin) (hko : a.kout = b.kout) (hkc : a.kc = b.kc) : a = b := by
  cases a; cases b; cases he; cases hi; cases ho; cases hr; cases hc; cases hki; cases hko; cases hkc; rfl

theorem set_self (a : DS VV MM) (x : Fin VV) (v : ℕ) (h : a.env x = v) : a.set x v = a := by
  refine ds_ext (a := a.set x v) (b := a) ?_ rfl rfl rfl rfl rfl rfl rfl
  funext y; by_cases hy : y = x
  · subst hy; simp [h]
  · simp [Function.update_of_ne hy]

theorem set_set (a : DS VV MM) (x : Fin VV) (u v : ℕ) : (a.set x u).set x v = a.set x v := by
  refine ds_ext (a := (a.set x u).set x v) (b := a.set x v) ?_ rfl rfl rfl rfl rfl rfl rfl
  funext y; by_cases hy : y = x
  · subst hy; simp
  · simp [Function.update_of_ne hy]

/-- The doubly framed payload: each bit `b` as `[1, 1, 1, b]`. -/
def dfr (l : List Bool) : List Bool := l.flatMap fun b => [true, true, true, b]

@[simp] theorem dfr_nil : dfr [] = [] := rfl
@[simp] theorem dfr_append (l m : List Bool) : dfr (l ++ m) = dfr l ++ dfr m := by simp [dfr]
@[simp] theorem dfr_cons (b : Bool) (l : List Bool) : dfr (b :: l) = [true, true, true, b] ++ dfr l := by simp [dfr]

theorem decide_bitOf (l : List Bool) (i : ℕ) : decide (bitOf l i = 1) = l.getD i false := by
  unfold bitOf; cases l.getD i false <;> simp

theorem bitOf_le_one (l : List Bool) (i : ℕ) : bitOf l i ≤ 1 := bitOf_le l i

theorem take_succ_drop (l : List Bool) (p k : ℕ) (h : p + k < l.length) :
    (l.drop p).take (k + 1) = (l.drop p).take k ++ [l.getD (p + k) false] := by
  rw [List.take_add_one]
  congr 1
  rw [List.getElem?_drop, List.getElem?_eq_getElem (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show p + k < l.length by omega)]

/-! ## Literals, payload bits, constants -/

/-- Print a literal word. -/
def lit : List Bool → St VV MM
  | [] => .op (.zero vZ)
  | b :: bs => .seq (.op (.emit b)) (lit bs)

theorem lit_spec (w : List Bool) (a : DS VV MM) (hz : a.env vZ = 0) :
    Hs C (lit w) a (2 * w.length + 1) (· = {a with out := a.out ++ w}) := by
  induction w generalizing a with
  | nil =>
    refine Hs.mono (hs_zero C vZ a) le_rfl ?_
    rintro b rfl
    rw [set_self a vZ 0 hz]; simp
  | cons b bs ih =>
    refine Hs.mono (Hs.seq (t1 := 1) (t2 := 2 * bs.length + 1) (hs_emit C b a) (fun d hd => ?_)) (by simp; omega)
      (fun _ h => h)
    subst hd
    refine Hs.mono (ih _ hz) le_rfl ?_
    rintro e rfl
    simp [List.append_assoc]

/-- Print `dfr [b]` for the bit `b` held (as `0`/`1`) in `x`, and count it. -/
def emitD (x : Fin VV) : St VV MM :=
  .seq (lit [true, true, true]) (.seq (.ite (.eq x v1) (.op (.emit true)) (.op (.emit false))) (.op (.inc dR)))

/-- The state after `emitD`. -/
def dState (a : DS VV MM) (b : Bool) : DS VV MM :=
  {a.set dR (a.env dR + 1) with out := a.out ++ [true, true, true, b]}

theorem emitD_spec (x : Fin VV) (hx : x ≠ v1) (a : DS VV MM) (hc : Cst a) (hd : a.env dR + 1 < 2 ^ C.Wd) :
    Hs C (emitD x) a 12 (· = dState a (decide (a.env x = 1))) := by
  refine Hs.seq (t1 := 7) (t2 := 4) (lit_spec [true, true, true] a hc.z) (fun d hd' => ?_)
  subst hd'
  refine Hs.seq (t1 := 2) (t2 := 1)
    (R1 := fun e => e = {a with out := a.out ++ [true, true, true] ++ [decide (a.env x = 1)]})
    (Hs.ite (c := .eq x v1) hx (fun he => ?_) (fun he => ?_)) (fun e he => ?_)
  · have hx1 : a.env x = 1 := by simpa [Cnd.eval, hc.one] using he
    exact Hs.mono (hs_emit C true _) le_rfl (fun e he' => by rw [he', hx1]; simp)
  · have hx1 : ¬ a.env x = 1 := by simpa [Cnd.eval, hc.one] using he
    exact Hs.mono (hs_emit C false _) le_rfl (fun e he' => by rw [he']; simp [hx1])
  · subst he
    refine Hs.mono (hs_inc C dR _ (by simp; omega)) le_rfl ?_
    rintro g rfl
    apply ds_ext <;> simp [dState, DS.set]

/-- Set `x` to the constant `c`. -/
def setC (x : Fin VV) : ℕ → St VV MM
  | 0 => .op (.zero x)
  | c + 1 => .seq (setC x c) (.op (.inc x))

theorem setC_spec (x : Fin VV) (c : ℕ) (a : DS VV MM) (h : c < 2 ^ C.Wd) :
    Hs C (setC x c) a (2 * c + 1) (· = a.set x c) := by
  induction c with
  | zero => exact hs_zero C x a
  | succ c ih =>
    refine Hs.mono (Hs.seq (t1 := 2 * c + 1) (t2 := 1) (ih (by omega)) (fun d hd => ?_)) (by omega) (fun _ h => h)
    subst hd
    refine Hs.mono (hs_inc C x _ (by simp; omega)) le_rfl ?_
    rintro e rfl
    rw [set_set]; simp

/-! ## Copying the input -/

/-- Copy the input from the cursor up to the position held in `e`, doubly framed and counted. -/
def copyTo (e : Fin VV) : St VV MM :=
  .loop (.lt ipR e) (.seq (.op (.rdI sB)) (.seq (.op (.inc ipR)) (emitD sB)))

/-- The registers `copyTo` may change. -/
def copyT : List (Fin VV) := [ipR, sB, dR]

theorem copyTo_spec (e : Fin VV) (he : e ∉ copyT) (a : DS VV MM) (hc : Cst a) (hip : a.env ipR = a.ip)
    (hle : a.ip ≤ a.env e) (hend : a.env e ≤ C.inp.length) (hW : a.env dR + (a.env e - a.ip) < 2 ^ C.Wd)
    (hW2 : C.inp.length < 2 ^ C.Wd) :
    Hs C (copyTo e) a ((a.env e - a.ip) * (16 + 2) + 2) (fun b => b.ip = a.env e ∧ b.env ipR = a.env e ∧
      b.env dR = a.env dR + (a.env e - a.ip) ∧ b.out = a.out ++ dfr ((C.inp.drop a.ip).take (a.env e - a.ip)) ∧
      b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b copyT) := by
  have heI : e ≠ ipR := fun h => he (by simp [copyT, h])
  have heB : e ≠ sB := fun h => he (by simp [copyT, h])
  have heD : e ≠ dR := fun h => he (by simp [copyT, h])
  set m := a.env e - a.ip with hm
  let I : ℕ → DS VV MM → Prop := fun k b => b.ip = a.ip + k ∧ b.env ipR = a.ip + k ∧ b.env dR = a.env dR + k ∧
    b.out = a.out ++ dfr ((C.inp.drop a.ip).take k) ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b copyT
  have hloop := Hs.loopN (C := C) (c := .lt ipR e) (s := .seq (.op (.rdI sB)) (.seq (.op (.inc ipR)) (emitD sB)))
    (show ipR ≠ e from fun h => heI h.symm) I m 16 ?_ ?_ a ⟨by simp, by simp [hip], by simp, by simp, rfl, rfl, rfl,
      Fr.refl _ _⟩
  · refine Hs.mono hloop le_rfl ?_
    rintro b ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨by rw [h1]; omega, by rw [h2]; omega, h3, h4, h5, h6, h7, h8⟩
  · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    have hbe : b.env e = a.env e := h8 e he
    have hc' : Cst b := Cst.of_fr hc h8 (by decide)
    refine ⟨by simp [Cnd.eval, h2, hbe]; omega, ?_⟩
    refine Hs.seq (t1 := 1) (t2 := 14) (hs_rdI C sB b (by rw [h1]; omega)) (fun d hd => ?_)
    subst hd
    refine Hs.seq (t1 := 1) (t2 := 12) (hs_inc C ipR _ (by vsimp [h2]; omega)) (fun d' hd' => ?_)
    subst hd'
    refine Hs.mono (emitD_spec sB (by decide) _ (Cst.of_fr hc' (T := [sB, ipR]) (fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy; vsimp [hy.1, hy.2]) (by decide))
      (by vsimp [h3]; omega)) le_rfl ?_
    rintro g rfl
    refine ⟨by simp [dState, h1]; omega, by vsimp [dState, h2]; omega, by vsimp [dState, h3]; omega, ?_, by
      simp [dState, h5], by simp [dState, h6], by simp [dState, h7], ?_⟩
    · simp only [dState]
      rw [take_succ_drop C.inp a.ip k (by omega), dfr_append]
      vsimp [h1, decide_bitOf, dfr]
      rw [h4]; simp [dfr, List.append_assoc]
    · intro y hy
      simp only [copyT, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      vsimp [dState, hy.1, hy.2.1, hy.2.2]
      exact h8 y (by simp [copyT, hy.1, hy.2.1, hy.2.2])
  · intro b hb
    obtain ⟨-, h2, -, -, -, -, -, h8⟩ := hb
    have hbe : b.env e = a.env e := h8 e he
    simp [Cnd.eval, h2, hbe]; omega

/-! ## Rewinding the input -/

/-- Move the cursor back to the position held in `p`. -/
def rewindTo (p : Fin VV) : St VV MM := .loop (.lt p ipR) (.seq (.op .bkI) (.op (.sub ipR v1)))

theorem rewindTo_spec (p : Fin VV) (hp : p ≠ ipR) (a : DS VV MM) (hc : Cst a) (hip : a.env ipR = a.ip)
    (hle : a.env p ≤ a.ip) :
    Hs C (rewindTo p) a ((a.ip - a.env p) * (3 + 2) + 2) (fun b => b.ip = a.env p ∧ b.env ipR = a.env p ∧
      b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [ipR]) := by
  set m := a.ip - a.env p with hm
  let I : ℕ → DS VV MM → Prop := fun k b => b.ip = a.ip - k ∧ b.env ipR = a.ip - k ∧ b.out = a.out ∧
    b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [ipR]
  have hloop := Hs.loopN (C := C) (c := .lt p ipR) (s := .seq (.op .bkI) (.op (.sub ipR v1))) hp I m 3 ?_ ?_ a
    ⟨by simp, by simp [hip], rfl, rfl, rfl, rfl, Fr.refl _ _⟩
  · refine Hs.mono hloop le_rfl ?_
    rintro b ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨by rw [h1]; omega, by rw [h2]; omega, h3, h4, h5, h6, h7⟩
  · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7⟩
    have hbp : b.env p = a.env p := h7 p (by simp [hp])
    have hb1 : b.env v1 = 1 := by rw [h7 v1 (by decide)]; exact hc.one
    refine ⟨by simp [Cnd.eval, h2, hbp]; omega, ?_⟩
    refine Hs.seq (t1 := 1) (t2 := 1) (Hs.op (OpEx.bkI b (by omega)) rfl) (fun d hd => ?_)
    subst hd
    refine Hs.mono (hs_sub C ipR v1 _ (by decide) (by simp [h2, hb1]; omega)) le_rfl ?_
    rintro g rfl
    refine ⟨by simp [h1]; omega, by vsimp [h2, hb1]; omega, by simp [h3], by simp [h4], by simp [h5], by simp [h6], ?_⟩
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    vsimp [hy]
    exact h7 y (by simp [hy])
  · intro b ⟨_, h2, _, _, _, _, h7⟩
    have hbp : b.env p = a.env p := h7 p (by simp [hp])
    simp [Cnd.eval, h2, hbp]; omega

/-! ## Repeated literals -/

/-- Print `w` as many times as the value of `cnt`. -/
def repL (w : List Bool) (cnt : Fin VV) : St VV MM :=
  .seq (.op (.zero sD)) (.loop (.lt sD cnt) (.seq (lit w) (.op (.inc sD))))

theorem repL_spec (w : List Bool) (cnt : Fin VV) (hcnt : cnt ≠ sD) (a : DS VV MM) (hc : Cst a)
    (hW : a.env cnt < 2 ^ C.Wd) :
    Hs C (repL w cnt) a (1 + (a.env cnt * (2 * w.length + 4 + 2) + 2) + 1) (fun b =>
      b.out = a.out ++ (List.replicate (a.env cnt) w).flatten ∧ b.ip = a.ip ∧ b.kin = a.kin ∧ b.kout = a.kout ∧
      b.kc = a.kc ∧ Fr a b [sD]) := by
  refine Hs.seq (hs_zero C sD a) (fun d hd => ?_)
  subst hd
  set m := a.env cnt with hm
  let I : ℕ → DS VV MM → Prop := fun k b => b.env sD = k ∧ b.out = a.out ++ (List.replicate k w).flatten ∧
    b.ip = a.ip ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b [sD]
  refine Hs.mono (Hs.loopN (C := C) (c := .lt sD cnt) (s := .seq (lit w) (.op (.inc sD))) (fun h => hcnt h.symm) I m
    (2 * w.length + 4) ?_ ?_ (a.set sD 0) ⟨by simp, by simp, rfl, rfl, rfl, rfl, Fr.set a (x := sD) 0 (by simp)⟩)
    le_rfl (fun b hb => hb.2)
  · intro k hk b ⟨h1, h2, h3, h4, h5, h6, h7⟩
    have hbc : b.env cnt = m := h7 cnt (by simp [hcnt])
    have hz : b.env vZ = 0 := by rw [h7 vZ (by decide)]; exact hc.z
    refine ⟨by simp [Cnd.eval, h1, hbc, hk], ?_⟩
    refine Hs.mono (Hs.seq (t1 := 2 * w.length + 1) (t2 := 1) (lit_spec w b hz) (fun d hd => ?_)) (by omega)
      (fun _ h => h)
    subst hd
    refine Hs.mono (hs_inc C sD _ (by simp [h1]; omega)) le_rfl ?_
    rintro g rfl
    refine ⟨by vsimp [h1], ?_, by simp [h3], by simp [h4], by simp [h5], by simp [h6], ?_⟩
    · simp [h2, List.replicate_succ', List.append_assoc]
    · intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      vsimp [hy]
      exact h7 y (by simp [hy])
  · intro b ⟨h1, _, _, _, _, _, h7⟩
    have hbc : b.env cnt = m := h7 cnt (by simp [hcnt])
    simp [Cnd.eval, h1, hbc]

/-! ## Reading a number from the input -/

/-- Read one `natWord` into `t3` (`t4 := natBitLength`), keeping `ipR` mirrored. -/
def readNat : St VV MM :=
  .seq rdNatI (.seq (.op (.add ipR t4)) (.seq (.op (.add ipR t4)) (.op (.inc ipR))))

/-- The registers `readNat` may change. -/
def readT : List (Fin VV) := [t0, t1, t2, t3, t4, vJ, ipR]

theorem readNat_spec (a : DS VV MM) (hc : Cst a) (hip : a.env ipR = a.ip) (v : ℕ) (rest : List Bool)
    (hcw : C.inp.drop a.ip = natWord v ++ rest) (hW : natBitLength v + 2 ≤ C.Wd)
    (hW2 : C.inp.length < 2 ^ C.Wd) :
    Hs C readNat a (30 * natBitLength v + 36) (fun b => b.env t3 = v ∧ b.env t4 = natBitLength v ∧
      b.ip = a.ip + (natWord v).length ∧ b.env ipR = b.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧
      b.kc = a.kc ∧ Fr a b readT ∧ Cst b) := by
  have hlen : a.ip + (natWord v).length ≤ C.inp.length := by
    have := congrArg List.length hcw
    have h2 := natWord_length v
    simp only [List.length_drop, List.length_append] at this; omega
  refine Hs.seq (t1 := 30 * natBitLength v + 30) (t2 := 5) (rdNatI_spec a hc v rest hcw hW) (fun b hb => ?_)
  obtain ⟨h1, h2, h3, h4, h5⟩ := hb
  simp only [Prod.mk.injEq] at h4
  have hbi : b.env ipR = a.ip := by rw [h5 ipR (by decide), hip]
  have hnw := natWord_length v
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_add C ipR t4 b (by decide) (by rw [hbi, h2]; omega)) (fun d hd => ?_)
  subst hd
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_add C ipR t4 _ (by decide) (by vsimp [hbi, h2]; omega)) (fun d hd => ?_)
  subst hd
  refine Hs.mono (hs_inc C ipR _ (by vsimp [hbi, h2]; omega)) le_rfl ?_
  rintro g rfl
  have hfr : Fr a (((b.set ipR (b.env ipR + b.env t4)).set ipR ((b.set ipR (b.env ipR + b.env t4)).env ipR +
      (b.set ipR (b.env ipR + b.env t4)).env t4)).set ipR
      (((b.set ipR (b.env ipR + b.env t4)).set ipR ((b.set ipR (b.env ipR + b.env t4)).env ipR +
      (b.set ipR (b.env ipR + b.env t4)).env t4)).env ipR + 1)) readT := by
    intro y hy
    have hy' : y ∉ rdNatT := fun h => hy (by simp only [readT, rdNatT, List.mem_cons] at h ⊢; tauto)
    have hyi : y ≠ ipR := fun h => hy (by simp [readT, h])
    vsimp [hyi]
    exact h5 y hy'
  refine ⟨by vsimp [h1], by vsimp [h2], by simp [h3], by vsimp [hbi, h2, h3, hnw]; omega, by simp [h4.1],
    by simp [h4.2.2.2.1], by simp [h4.2.2.2.2.1], by simp [h4.2.2.2.2.2], hfr, Cst.of_fr hc hfr (by decide)⟩

end NearCubicGates.Adapters.ShortPCP.Assembly
