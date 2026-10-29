import SourceAdapters.Amplification.EncVal

/-!
# The Hadamard bits and the loop over the table positions (X9, `app:sources`, "Full-range amplification interface")

* `hadP`: `HP := [hadBit t YY QC]` (parity of the common low `t` bits, by halving both numbers);
* `mainLoop`: for every table position `c < 2^ℓ` in order, the value at the point of `c` (`valP`) and its Hadamard
  bit (`hadP`) are computed and the bit is emitted: the output is
  `(List.range (2^ℓ)).map (fun c => hadBit t (valAt p t h m n T c) c)`, the body of `boolFunctionTable` of the
  rounded STV code (`EncRef.encoderOutput_eq`).
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells NearCubicWires.WireExponent3_5 Finset

abbrev vHA : Var := 64
abbrev vHB : Var := 65
abbrev vHS : Var := 66
abbrev vHP : Var := 67
abbrev vHQ : Var := 68
abbrev vHRa : Var := 69
abbrev vHRb : Var := 70

def hadS : List Var := [vHA, vHB, vHS, vHP, vHQ, vHRa, vHRb]

def hadFlip : Sc := .ite (.eq vHP vZ) (.op (.inc vHP)) (.op (.zero vHP))

def hadBody : Sc :=
  .seq (.op (.dm vHA vTWO vHQ vHRa)) <| .seq (.op (.copy vHA vHQ)) <|
  .seq (.op (.dm vHB vTWO vHQ vHRb)) <| .seq (.op (.copy vHB vHQ)) <|
  .seq (.op (.inc vHS)) (.ite (.eq vHRa vONE) (.ite (.eq vHRb vONE) hadFlip (.op (.zero vHQ))) (.op (.zero vHQ)))

def hadP : Sc :=
  .seq (.op (.copy vHA vYY)) <| .seq (.op (.copy vHB vQC)) <| .seq (.op (.zero vHS)) <| .seq (.op (.zero vHP)) <|
  .loop (.lt vHS vT) hadBody

def hadCost (t : ℕ) : ℕ := t * (30 + 2) + 20

/-- The number of common set bits below `j`. -/
def common (Y c j : ℕ) : ℕ := ((range j).filter fun s => Y.testBit s && c.testBit s).card

theorem common_succ (Y c j : ℕ) :
    common Y c (j + 1) = common Y c j + if Y.testBit j && c.testBit j then 1 else 0 := by
  unfold common
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem testBit_div (Y j : ℕ) : Y / 2 ^ j % 2 = if Y.testBit j then 1 else 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (Y / 2 ^ j) with h | h <;> simp [h]

/-- The state of `hadP` before round `j`. -/
def HadInv (a0 : Ds) (Y c j : ℕ) (b : Ds) : Prop :=
  Fr hadS [] a0 b ∧ b.env vHA = Y / 2 ^ j ∧ b.env vHB = c / 2 ^ j ∧ b.env vHP = common Y c j % 2 ∧ b.env vHS = j

theorem hadP_spec (C : Ctx) (g : Prm) (hw : WOk g C) (a : Ds) (hg : Glob g a) (Y c : ℕ) (hY : a.env vYY = Y)
    (hc : a.env vQC = c) :
    Runs C hadP a (hadCost g.t) hadS [] (fun b => b.env vHP = if hadBit g.t Y c then 1 else 0) := by
  have hW4 : 2 * 2 ≤ 2 ^ C.Wd := by
    have := pow_lt_W hw (x := 2) (by omega); simpa using this.le
  refine Runs.op1 (run_copy C hadS a vHA vYY (by decide) (by decide)) ?_ (by unfold hadCost; omega)
  refine Runs.op1 (run_copy C hadS _ vHB vQC (by decide) (by decide)) ?_ (by unfold hadCost; omega)
  refine Runs.op1 (run_zero C hadS _ vHS (by decide)) ?_ (by unfold hadCost; omega)
  refine Runs.op1 (run_zero C hadS _ vHP (by decide)) ?_ (by unfold hadCost; omega)
  norm_env
  rw [hY, hc]
  refine (Runs.loopN0 (C := C) (c := .lt vHS vT) (body := hadBody) (S := hadS) (by unfold Cnd.wf; decide)
    g.t 30 (HadInv a Y c) ?step ?stop _ ?init).mono ?cost (List.Subset.refl _) ?post
  case cost => unfold hadCost; omega
  case post =>
    rintro b - ⟨-, -, -, hP, -⟩
    rw [hP]
    change common Y c g.t % 2 = if decide (common Y c g.t % 2 = 1) then 1 else 0
    rcases Nat.mod_two_eq_zero_or_one (common Y c g.t) with h | h <;> simp [h]
  case stop =>
    rintro b ⟨hf, -, -, -, hS⟩
    have hgb : Glob g b := hg.of_fr hf (by decide)
    simp [Cnd.eval, hS, hgb.t]
  case init =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · repeat (first | exact Fr.refl hadS a | refine Fr.set_right ?_ _ _ (by decide))
    all_goals norm_env
    all_goals simp [common]
  case step =>
    rintro j hj b ⟨hf, hA, hB, hP, hS⟩
    have hgb : Glob g b := hg.of_fr hf (by decide)
    refine ⟨by simp [Cnd.eval, hS, hgb.t, hj], ?_⟩
    have hjW : j + 1 < 2 ^ C.Wd := lt_W hw (by
      have := Nat.lt_two_pow_self (n := g.L + 3); have := hw.2.1; omega)
    refine Runs.op1 (run_dm C hadS b vHA vTWO vHQ vHRa (by decide) (by decide) (by decide)
      (by rw [hgb.c.2.2]; norm_num) (by rw [hgb.c.2.2]; exact hW4)) ?_ (by omega)
    refine Runs.op1 (run_copy C hadS _ vHA vHQ (by decide) (by decide)) ?_ (by omega)
    norm_env
    refine Runs.op1 (run_dm C hadS _ vHB vTWO vHQ vHRb (by decide) (by decide) (by decide)
      (by norm_env; rw [hgb.c.2.2]; norm_num) (by norm_env; rw [hgb.c.2.2]; exact hW4)) ?_ (by omega)
    refine Runs.op1 (run_copy C hadS _ vHB vHQ (by decide) (by decide)) ?_ (by omega)
    norm_env
    rw [hgb.c.2.2, hA, hB, testBit_div, testBit_div]
    refine Runs.op1 (run_inc C hadS _ vHS (by decide) (by norm_env; rw [hS]; exact hjW)) ?_ (by omega)
    norm_env
    rw [hS]
    have hfin : ∀ (f : Ds), Fr hadS [] b f → f.env vHA = Y / 2 ^ j / 2 → f.env vHB = c / 2 ^ j / 2 →
        f.env vHP = common Y c (j + 1) % 2 → f.env vHS = j + 1 → HadInv a Y c (j + 1) f := by
      intro f hff h1 h2 h3 h4
      refine ⟨hf.trans0 hff, ?_, ?_, h3, h4⟩
      · rw [h1, Nat.div_div_eq_div_mul, ← pow_succ]
      · rw [h2, Nat.div_div_eq_div_mul, ← pow_succ]
    have hfr : ∀ (x : Var) (v : ℕ), x ∈ hadS → Fr hadS [] b
        ((((((b.set vHQ (Y / 2 ^ j / 2)).set vHRa (if Y.testBit j then 1 else 0)).set vHA (Y / 2 ^ j / 2)).set vHQ
          (c / 2 ^ j / 2)).set vHRb (if c.testBit j then 1 else 0)).set vHB (c / 2 ^ j / 2) |>.set vHS (j + 1)
          |>.set x v) := by
      intro x v hx
      refine Fr.set_right ?_ _ _ hx
      repeat (first | exact Fr.refl hadS b | refine Fr.set_right ?_ _ _ (by decide))
    by_cases hya : Y.testBit j = true
    · refine Runs.iteT' (by unfold Cnd.wf; decide)
        (by simp (config := { decide := true }) [Cnd.eval, env_set, hya, hgb.c.2.1]) ?_ (by omega)
      by_cases hcb : c.testBit j = true
      · refine Runs.iteT' (by unfold Cnd.wf; decide)
          (by simp (config := { decide := true }) [Cnd.eval, env_set, hcb, hgb.c.2.1]) ?_ (by omega)
        rcases Nat.mod_two_eq_zero_or_one (common Y c j) with hpar | hpar
        · refine Runs.iteT' (by unfold Cnd.wf; decide)
            (by simp (config := { decide := true }) [Cnd.eval, env_set, hP, hpar, hgb.c.1]) ?_ (by omega)
          refine Runs.last (run_inc C hadS _ vHP (by decide) (by norm_env; rw [hP, hpar]; omega)) ?_ (by omega)
          intro hff
          refine hfin _ ?_ ?_ ?_ ?_ ?_ <;> norm_env
          · exact hfr vHP _ (by decide)
          · rw [hP, common_succ, hya, hcb]; simp; omega
        · refine Runs.iteF' (by unfold Cnd.wf; decide)
            (by simp (config := { decide := true }) [Cnd.eval, env_set, hP, hpar, hgb.c.1]) ?_ (by omega)
          refine Runs.last (run_zero C hadS _ vHP (by decide)) ?_ (by omega)
          intro hff
          refine hfin _ ?_ ?_ ?_ ?_ ?_ <;> norm_env
          · exact hfr vHP _ (by decide)
          · rw [common_succ, hya, hcb]; simp; omega
      · refine Runs.iteF' (by unfold Cnd.wf; decide)
          (by simp (config := { decide := true }) [Cnd.eval, env_set, hcb, hgb.c.2.1]) ?_ (by omega)
        refine Runs.last (run_zero C hadS _ vHQ (by decide)) ?_ (by omega)
        intro hff
        refine hfin _ ?_ ?_ ?_ ?_ ?_ <;> norm_env
        · exact hfr vHQ _ (by decide)
        · rw [hP, common_succ, hya]; simp [hcb]
    · refine Runs.iteF' (by unfold Cnd.wf; decide)
        (by simp (config := { decide := true }) [Cnd.eval, env_set, hya, hgb.c.2.1]) ?_ (by omega)
      refine Runs.last (run_zero C hadS _ vHQ (by decide)) ?_ (by omega)
      intro hff
      refine hfin _ ?_ ?_ ?_ ?_ ?_ <;> norm_env
      · exact hfr vHQ _ (by decide)
      · rw [hP, common_succ]; simp [hya]

/-! ## The loop over the table positions -/

theorem Glob.with_out {g : Prm} {a : Ds} (h : Glob g a) (o : List Bool) : Glob g { a with out := o } :=
  ⟨h.c, h.t, h.tb, h.powt, h.h, h.powh, h.n, h.pown, h.m, h.L, h.powl, h.p, h.exp⟩

abbrev vCC : Var := 71

def mainS : List Var := [vCC, vQC] ++ valS ++ hadS

def mainBody : Sc :=
  .seq (.op (.copy vQC vCC)) <| .seq valP <| .seq hadP <| .seq (.op (.inc vCC)) <|
  .ite (.eq vHP vONE) (.op (.emit true)) (.op (.emit false))

def mainLoop : Sc := .seq (.op (.zero vCC)) (.loop (.lt vCC vPOWL) mainBody)

def mainBodyCost (t h m n : ℕ) : ℕ := valCost t h m n + hadCost t + 20

def mainCost (t h m n L : ℕ) : ℕ := 2 ^ L * (mainBodyCost t h m n + 2) + 10

/-- The table bits. -/
def tableBits (g : Prm) (T : ℕ → Bool) : List Bool :=
  (List.range (2 ^ g.L)).map fun c => hadBit g.t (valAt g.p g.t g.h g.m g.n T c) c

theorem flatMap_single {α β : Type} (l : List α) (f : α → β) : l.flatMap (fun x => [f x]) = l.map f := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.flatMap_cons, ih]

theorem mainLoop_spec (C : Ctx) (g : Prm) (hw : WOk g C) (hp : GF.ModulusOk g.p g.t) (a : Ds) (hg : Glob g a)
    (T : ℕ → Bool) (base : ℕ) (hT : TableAt C base g.n T) (hip : a.ip = base) :
    Runs C mainLoop a (mainCost g.t g.h g.m g.n g.L) mainS (tableBits g T) (fun _ => True) := by
  have hLW : 2 ^ g.L < 2 ^ C.Wd := pow_lt_W hw (by omega)
  have e := Runs.loopN (C := C) (c := .lt vCC vPOWL) (body := mainBody) (S := mainS) (by unfold Cnd.wf; decide)
    (2 ^ g.L) (mainBodyCost g.t g.h g.m g.n) (fun c => [hadBit g.t (valAt g.p g.t g.h g.m g.n T c) c])
    (fun j b => b.ip = base ∧ Glob g b ∧ b.env vCC = j) ?step ?stop (a.set vCC 0)
    ⟨by simp [DS.set, hip], hg.of_fr (Fr.set mainS a vCC 0 (by decide)) (by decide), by simp [env_set]⟩
  case stop =>
    rintro b ⟨-, hgb, hC⟩
    simp [Cnd.eval, hC, hgb.powl]
  case step =>
    rintro j hj b ⟨hbip, hgb, hC⟩
    refine ⟨by simp [Cnd.eval, hC, hgb.powl, hj], ?_⟩
    refine Runs.op1 (run_copy C mainS b vQC vCC (by decide) (by decide)) ?_ (by unfold mainBodyCost; omega)
    have hg1 : Glob g (b.set vQC (b.env vCC)) := hgb.of_fr (Fr.set mainS b vQC _ (by decide)) (by decide)
    refine Runs.callS (valP_spec C g hw hp _ hg1 T j base hT (by simp [DS.set, hbip]) (by norm_env; exact hC))
      (by decide) ?_ (by unfold mainBodyCost; omega)
    rintro d hd ⟨hdv, -⟩
    have hgd : Glob g d := hg1.of_fr hd (by decide)
    have hdc : d.env vQC = j := by rw [hd.env vQC (by decide)]; norm_env; exact hC
    refine Runs.callS (hadP_spec C g hw d hgd _ j hdv hdc) (by decide) ?_ (by unfold mainBodyCost; omega)
    intro e he hev
    have hge : Glob g e := hgd.of_fr he (by decide)
    have heC : e.env vCC = j := by
      rw [he.env vCC (by decide), hd.env vCC (by decide)]; norm_env; exact hC
    have heip : e.ip = base := by rw [he.ip, hd.ip]; simp [DS.set, hbip]
    refine Runs.op1 (run_inc C mainS e vCC (by decide) (by rw [heC]; omega)) ?_ (by unfold mainBodyCost; omega)
    have hge1 : Glob g (e.set vCC (e.env vCC + 1)) := hge.of_fr (Fr.set mainS e vCC _ (by decide)) (by decide)
    by_cases hb : hadBit g.t (valAt g.p g.t g.h g.m g.n T j) j = true
    · refine Runs.iteT' (by unfold Cnd.wf; decide)
        (by simp (config := { decide := true }) [Cnd.eval, env_set, hev, hb, hge.c.2.1]) ?_
        (by unfold mainBodyCost; omega)
      rw [hb]
      refine Runs.last (run_emit C mainS _ true) ?_ (by unfold mainBodyCost; omega)
      intro _
      exact ⟨by simp [DS.set, heip], hge1.with_out _, by simp [env_set, heC]⟩
    · have hb' : hadBit g.t (valAt g.p g.t g.h g.m g.n T j) j = false := by simpa using hb
      refine Runs.iteF' (by unfold Cnd.wf; decide)
        (by simp (config := { decide := true }) [Cnd.eval, env_set, hev, hb', hge.c.2.1]) ?_
        (by unfold mainBodyCost; omega)
      rw [hb']
      refine Runs.last (run_emit C mainS _ false) ?_ (by unfold mainBodyCost; omega)
      intro _
      exact ⟨by simp [DS.set, heip], hge1.with_out _, by simp [env_set, heC]⟩
  refine Runs.op1 (run_zero C mainS a vCC (by decide)) ?_ (by unfold mainCost; omega)
  have h2 := e.mono (n' := mainCost g.t g.h g.m g.n g.L - 2) (Q' := fun _ => True) (by unfold mainCost; omega)
    (List.Subset.refl _) (fun _ _ _ => trivial)
  unfold tableBits
  rw [← flatMap_single]
  exact h2

end NearCubicGates.Adapters.Amplification.Enc
