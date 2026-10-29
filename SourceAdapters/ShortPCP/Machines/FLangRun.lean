import SourceAdapters.ShortPCP.Machines.FLangComp
import Proof.Gates.CounterMachine.PrefixFinal

/-!
# A field-language program as an ordinary word function

A cell stage starts on `1^L 0 ++ rest` (the width prefix of `TimeStages.lean`).
The prelude reads the `L` leading ones and establishes the run context with
`W = 4·64^L`, `K = N = 2·64^L`, and `cap = 2^K − 1` (`zF`, `kOf`, `globOf`).
It sets the constants and default field, then runs the compiled `FL` program from
`s0` at input position `L + 1`. `flRun` proves the cell run; `flWF` packages the
ordinary word function with `Cells.wordFunction_of_lang`. Its budget is polynomial
in `64^L + |input|` (`flBudget_le`). The calling prefix construction chooses
`L = size |w|`, so this quantity is polynomial in the original input length
(proof of `thm:short-pcp-ours`, Step 4).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.ShortPCP.Machines.FL

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Close.CounterMachine.PrefixProg (noCallee lang_le)
open NearCubicGates.Adapters.Joins.FieldCells

/-- The width parameters: `W = 4 · 64^L` for `L` leading ones. -/
def zF : Sz := ⟨4, 6, 0, 0, 0, 0⟩

/-- The clamp exponent and pass bound of an input word: `K = 2 · 64^L`. -/
def kOf (inp : List Bool) : ℕ := 2 * 64 ^ leadOnes inp

/-- The run constants of an input word. -/
def globOf (inp : List Bool) : Glob := ⟨kOf inp, kOf inp, inp⟩

/-- The initial `FL` state, after the prefix `1^L 0`. -/
def s0 (inp : List Bool) : FS := ⟨fun _ => 0, [], 1, 2, leadOnes inp + 1, false⟩

/-- Constants and the default field; `N := 2`. -/
def initP : St VV MM :=
  .seq (.op (.inc r1)) (.seq (.op (.inc r2)) (.seq (.op (.inc r2)) (.seq (.op (.copy tR r2)) (.seq (.op (.copy pR r2))
    (.op (.copy nR r2))))))

/-- Six doublings. -/
def shl6 : St VV MM :=
  .seq (.op (.shl nR)) (.seq (.op (.shl nR)) (.seq (.op (.shl nR)) (.seq (.op (.shl nR)) (.seq (.op (.shl nR))
    (.op (.shl nR))))))

/-- Read the leading ones; `N := 64 N` for each. -/
def readP : St VV MM := .seq (.op (.rdI (sc 0))) (.loop (.eq (sc 0) r1) (.seq shl6 (.op (.rdI (sc 0)))))

/-- `K := N`, `2^K`, `cap := 2^K − 1`. -/
def powP : St VV MM :=
  .seq (.op (.copy kR nR)) (.seq (.op (.copy cap1R r1)) (.seq (.op (.zero (sc 1)))
    (.seq (.loop (.lt (sc 1) kR) (.seq (.op (.shl cap1R)) (.op (.inc (sc 1)))))
      (.seq (.op (.copy capR cap1R)) (.op (.sub capR r1))))))

/-- The prelude. -/
def preP : St VV MM := .seq initP (.seq readP powP)

/-- The whole cell program of an `FL` program. -/
def progOf (main : S) : St VV MM := .seq preP (compS main 0)

/-- The prelude's cost bound. -/
def preCost (inp : List Bool) : ℕ := 20 * leadOnes inp + 5 * kOf inp + 40

theorem wd_eq (inp : List Bool) : (ctxOf noCallee zF inp).Wd = 4 * 64 ^ leadOnes inp := by
  show 2 ^ (6 * leadOnes inp) * 4 = _; rw [pow_mul]; norm_num; ring

/-- What the prelude leaves: the fixed registers, the variables zero, input after the prefix. -/
structure PreOk (inp : List Bool) (b : DS VV MM) : Prop where
  env : Env (globOf inp) 1 2 b
  uv : ∀ i, b.env (uv i) = 0
  out : b.out = []
  ip : b.ip = leadOnes inp + 1

/-- Registers `≥ 16` are untouched by the prelude. -/
def Hi (a b : DS VV MM) : Prop := ∀ y : Fin VV, 16 ≤ y.val → b.env y = a.env y

theorem Hi.set {a b : DS VV MM} (h : Hi a b) (x : Fin VV) (hx : x.val < 16) (v : ℕ) : Hi a (b.set x v) :=
  fun y hy => (DS.set_env_ne _ _ (ne_of_val (by omega))).trans (h y hy)

/-- The registers fixed by `initP`, and the untouched rest, during the prelude. -/
structure Pre (b : DS VV MM) : Prop where
  c0 : b.env r0 = 0
  c1 : b.env r1 = 1
  c2 : b.env r2 = 2
  t : b.env tR = 2
  p : b.env pR = 2
  hi : Hi a0 b
  out : b.out = []

theorem Pre.set {b : DS VV MM} (h : Pre b) (x : Fin VV) (hx : x.val < 16) (h0 : x ≠ r0) (h1 : x ≠ r1) (h2 : x ≠ r2)
    (ht : x ≠ tR) (hp : x ≠ pR) (v : ℕ) : Pre (b.set x v) :=
  ⟨(DS.set_env_ne _ _ h0.symm).trans h.c0, (DS.set_env_ne _ _ h1.symm).trans h.c1,
    (DS.set_env_ne _ _ h2.symm).trans h.c2, (DS.set_env_ne _ _ ht.symm).trans h.t,
    (DS.set_env_ne _ _ hp.symm).trans h.p, h.hi.set x hx v, h.out⟩

theorem Pre.withIp {b : DS VV MM} (h : Pre b) (n : ℕ) : Pre { b with ip := n } :=
  ⟨h.c0, h.c1, h.c2, h.t, h.p, h.hi, h.out⟩

theorem Pre.rd {b : DS VV MM} (h : Pre b) (C : Ctx) :
    Pre { b.set (sc 0) (bitOf C.inp b.ip) with ip := b.ip + 1 } :=
  (h.set (sc 0) (by rw [sc_val (by norm_num)]; omega) (by decide) (by decide) (by decide) (by decide) (by decide)
    _).withIp _

section Prelude

variable (inp : List Bool)

theorem init_ok : Hs (ctxOf noCallee zF inp) initP (a0 : DS VV MM) 11
    (fun b => Pre b ∧ b.env nR = 2 ∧ b.ip = 0) := by
  have hW : 4 ≤ (ctxOf noCallee zF inp).Wd := by rw [wd_eq]; have := Nat.one_le_pow (leadOnes inp) 64 (by norm_num); omega
  have h8 : 8 ≤ 2 ^ (ctxOf noCallee zF inp).Wd := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold initP
  refine hs_step (OpEx.inc r1 _ (by show 0 + 1 < _; omega)) ?_
  refine hs_step (OpEx.inc r2 _ (by
    have : ((a0 : DS VV MM).set r1 ((a0 : DS VV MM).env r1 + 1)).env r2 = 0 := rfl
    omega)) ?_
  refine hs_step (OpEx.inc r2 _ (by
    have : ((a0 : DS VV MM).set r1 ((a0 : DS VV MM).env r1 + 1)).env r2 = 0 := rfl
    rw [DS.set_env_self]; omega)) ?_
  refine hs_step (OpEx.copy tR r2 _ (by decide)) ?_
  refine hs_step (OpEx.copy pR r2 _ (by decide)) ?_
  refine Hs.mono (hs_opq (OpEx.copy nR r2 _ (by decide))) le_rfl ?_
  rintro b rfl
  have e0 : ∀ y : Fin VV, (a0 : DS VV MM).env y = 0 := fun _ => rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, fun y hy => ?_, rfl⟩, ?_, rfl⟩ <;>
    simp (config := { decide := true }) only [DS.env_set, Function.update_apply, e0, if_true, if_false]
  all_goals first | rfl | (split_ifs <;> first | rfl | (exfalso; subst_vars; revert hy; decide))


theorem nR_ne : nR ≠ r0 ∧ nR ≠ r1 ∧ nR ≠ r2 ∧ nR ≠ tR ∧ nR ≠ pR := by decide

theorem shl1 {C : Ctx} {b : DS VV MM} (h : Pre b) (v : ℕ) (hv : b.env nR = v) (hw : 2 * v < 2 ^ C.Wd) :
    OpEx C (.shl nR) b (b.set nR (2 * v)) 1 := by
  have := OpEx.shl (C := C) nR b (by rw [hv]; exact hw); rwa [hv] at this

theorem preSet {b : DS VV MM} (h : Pre b) (v : ℕ) : Pre (b.set nR v) :=
  h.set nR (by unfold nR; rw [vr_val' (by simp only [VV]; omega)]; omega) nR_ne.1 nR_ne.2.1 nR_ne.2.2.1 nR_ne.2.2.2.1
    nR_ne.2.2.2.2 v

theorem shl6_ok {C : Ctx} (b : DS VV MM) (h : Pre b) (v : ℕ) (hv : b.env nR = v) (hw : 64 * v < 2 ^ C.Wd) :
    Hs C shl6 b 11 (fun c => Pre c ∧ c.env nR = 64 * v ∧ c.ip = b.ip) := by
  unfold shl6
  refine hs_step (shl1 h v hv (by omega)) ?_
  refine hs_step (shl1 (preSet h _) (2 * v) (by simp) (by omega)) ?_
  refine hs_step (shl1 (preSet (preSet h _) _) (2 * (2 * v)) (by simp) (by omega)) ?_
  refine hs_step (shl1 (preSet (preSet (preSet h _) _) _) (2 * (2 * (2 * v))) (by simp) (by omega)) ?_
  refine hs_step (shl1 (preSet (preSet (preSet (preSet h _) _) _) _) (2 * (2 * (2 * (2 * v)))) (by simp)
    (by omega)) ?_
  refine Hs.mono (hs_opq (shl1 (preSet (preSet (preSet (preSet (preSet h _) _) _) _) _)
    (2 * (2 * (2 * (2 * (2 * v))))) (by simp) (by omega))) le_rfl ?_
  rintro c rfl
  exact ⟨preSet (preSet (preSet (preSet (preSet (preSet h _) _) _) _) _) _, by simp; ring, rfl⟩

theorem bitOf_lead (j : ℕ) (hj : j < leadOnes inp) : bitOf inp j = 1 := by
  unfold bitOf; rw [leadOnes_true inp j hj]; rfl

theorem bitOf_lead_end : bitOf inp (leadOnes inp) = 0 := by
  unfold bitOf; rw [leadOnes_false inp]; rfl

theorem read_ok (hlt : leadOnes inp < inp.length) (b : DS VV MM) (h : Pre b) (hn : b.env nR = 2) (hi : b.ip = 0) :
    Hs (ctxOf noCallee zF inp) readP b (15 * leadOnes inp + 4)
      (fun c => Pre c ∧ c.env nR = kOf inp ∧ c.ip = leadOnes inp + 1) := by
  set C := ctxOf noCallee zF inp with hC
  set L := leadOnes inp with hL
  have hWd : C.Wd = 4 * 64 ^ L := wd_eq inp
  have hWlt : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  unfold readP
  refine hs_step (OpEx.rdI (sc 0) b (by rw [hi]; show 0 < inp.length; omega)) ?_
  let I : ℕ → DS VV MM → Prop := fun j c => Pre c ∧ c.env nR = 2 * 64 ^ j ∧ c.ip = j + 1 ∧
    c.env (sc 0) = bitOf inp j
  have hI0 : I 0 { b.set (sc 0) (bitOf C.inp b.ip) with ip := b.ip + 1 } :=
    ⟨h.rd C, by rw [show ({ b.set (sc 0) (bitOf C.inp b.ip) with ip := b.ip + 1 } : DS VV MM).env nR =
      (b.set (sc 0) (bitOf C.inp b.ip)).env nR from rfl, DS.set_env_ne _ _ (by decide), hn]; simp,
      by simp [hi], by simp [hi]; rfl⟩
  refine Hs.mono (Hs.loopN (c := .eq (sc 0) r1) (show sc 0 ≠ r1 by decide) I L 13 ?_ ?_ _ hI0) (by omega) ?_
  · intro j hj c ⟨cp, cn, ci, cs⟩
    refine ⟨by simp only [Cnd.eval, cs, cp.c1, bitOf_lead inp j hj, decide_true], ?_⟩
    have hpow : 64 * (2 * 64 ^ j) < 2 ^ C.Wd := by
      have : 64 ^ (j + 1) ≤ 64 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ] at this; omega
    refine hs_pre (t2 := 1) (shl6_ok c cp _ cn hpow) (fun c1 ⟨p1, n1, i1⟩ => ?_)
    refine Hs.mono (hs_opq (OpEx.rdI (sc 0) c1 (by rw [i1, ci]; show j + 1 < inp.length; omega))) le_rfl ?_
    rintro c2 rfl
    refine ⟨p1.rd C, ?_, by simp [i1, ci], by simp [i1, ci]; rfl⟩
    rw [show ({ c1.set (sc 0) (bitOf C.inp c1.ip) with ip := c1.ip + 1 } : DS VV MM).env nR =
      (c1.set (sc 0) (bitOf C.inp c1.ip)).env nR from rfl, DS.set_env_ne _ _ (by decide), n1, pow_succ]; ring
  · intro c ⟨cp, _, _, cs⟩
    have e := bitOf_lead_end inp
    rw [← hL] at e
    simp only [Cnd.eval, cs, cp.c1, e]; rfl
  · rintro c ⟨cp, cn, ci, _⟩
    exact ⟨cp, cn, ci⟩


theorem preSetR {b : DS VV MM} (h : Pre b) (x : Fin VV) (hx : x = kR ∨ x = cap1R ∨ x = sc 1 ∨ x = capR) (v : ℕ) :
    Pre (b.set x v) := by
  have h16 : x.val < 16 := by rcases hx with rfl | rfl | rfl | rfl <;> decide
  have hn : x ≠ r0 ∧ x ≠ r1 ∧ x ≠ r2 ∧ x ≠ tR ∧ x ≠ pR := by rcases hx with rfl | rfl | rfl | rfl <;> decide
  exact h.set x h16 hn.1 hn.2.1 hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2 v

theorem pow_ok (c : DS VV MM) (h : Pre c) (hn : c.env nR = kOf inp) (hi : c.ip = leadOnes inp + 1) :
    Hs (ctxOf noCallee zF inp) powP c (5 * kOf inp + 15) (PreOk inp) := by
  set C := ctxOf noCallee zF inp with hC
  set K := kOf inp with hK
  have hWd : C.Wd = 4 * 64 ^ leadOnes inp := wd_eq inp
  have hKW : K < C.Wd := by have : 1 ≤ 64 ^ leadOnes inp := Nat.one_le_pow _ _ (by norm_num); simp only [hK, kOf]; omega
  have hpK : 2 ^ K < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) hKW
  have hKl : K < 2 ^ K := Nat.lt_two_pow_self
  unfold powP
  refine hs_step (OpEx.copy kR nR c (by decide)) ?_
  set c1 := c.set kR (c.env nR)
  have p1 : Pre c1 := preSetR h kR (Or.inl rfl) _
  refine hs_step (OpEx.copy cap1R r1 c1 (by decide)) ?_
  set c2 := c1.set cap1R (c1.env r1)
  have p2 : Pre c2 := preSetR p1 cap1R (Or.inr (Or.inl rfl)) _
  refine hs_step (OpEx.zero (sc 1) c2) ?_
  set c3 := c2.set (sc 1) 0
  have p3 : Pre c3 := preSetR p2 (sc 1) (Or.inr (Or.inr (Or.inl rfl))) _
  have c3n : c3.env nR = K := by simp only [c3, c2, c1, DS.set_env_ne _ _ (show nR ≠ sc 1 by decide),
    DS.set_env_ne _ _ (show nR ≠ cap1R by decide), DS.set_env_ne _ _ (show nR ≠ kR by decide), hn]
  have c3k : c3.env kR = K := by simp only [c3, c2, c1, DS.set_env_ne _ _ (show kR ≠ sc 1 by decide),
    DS.set_env_ne _ _ (show kR ≠ cap1R by decide), DS.set_env_self, hn]
  have c3c : c3.env cap1R = 1 := by simp only [c3, c2, DS.set_env_ne _ _ (show cap1R ≠ sc 1 by decide),
    DS.set_env_self, p1.c1]
  let J : ℕ → DS VV MM → Prop := fun j d => Pre d ∧ d.env nR = K ∧ d.env kR = K ∧ d.env cap1R = 2 ^ j ∧
    d.env (sc 1) = j ∧ d.ip = leadOnes inp + 1
  have hJ0 : J 0 c3 := ⟨p3, c3n, c3k, by rw [c3c]; rfl, by simp [c3], by simp [c3, c2, c1, hi]⟩
  refine hs_pre (t1 := K * (3 + 2) + 2) (t2 := 3) (Hs.loopN (c := .lt (sc 1) kR) (show sc 1 ≠ kR by decide) J K 3
    ?_ ?_ c3 hJ0) (fun d hd => ?_) |>.mono (by omega) (fun _ h => h)
  · intro j hj d ⟨dp, dn, dk, dc, ds, di⟩
    refine ⟨by simp only [Cnd.eval, ds, dk, decide_eq_true_eq]; exact hj, ?_⟩
    have hj2 : 2 * 2 ^ j < 2 ^ C.Wd := by
      have : 2 ^ (j + 1) ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ] at this; omega
    refine hs_step (OpEx.shl cap1R d (by rw [dc]; exact hj2)) ?_
    set d1 := d.set cap1R (2 * d.env cap1R)
    have q1 : Pre d1 := preSetR dp cap1R (Or.inr (Or.inl rfl)) _
    refine Hs.mono (hs_opq (OpEx.inc (sc 1) d1 (by
      simp only [d1, DS.set_env_ne _ _ (show sc 1 ≠ cap1R by decide), ds]; omega))) le_rfl ?_
    rintro e rfl
    refine ⟨preSetR q1 (sc 1) (Or.inr (Or.inr (Or.inl rfl))) _, ?_, ?_, ?_, ?_, by simp [d1, di]⟩
    · simp only [d1, DS.set_env_ne _ _ (show nR ≠ sc 1 by decide), DS.set_env_ne _ _ (show nR ≠ cap1R by decide), dn]
    · simp only [d1, DS.set_env_ne _ _ (show kR ≠ sc 1 by decide), DS.set_env_ne _ _ (show kR ≠ cap1R by decide), dk]
    · simp only [d1, DS.set_env_ne _ _ (show cap1R ≠ sc 1 by decide), DS.set_env_self, dc, pow_succ]; ring
    · simp only [d1, DS.set_env_self, DS.set_env_ne _ _ (show sc 1 ≠ cap1R by decide), ds]
  · intro d ⟨_, _, dk, _, ds, _⟩
    simp only [Cnd.eval, ds, dk, decide_eq_false_iff_not]; omega
  · obtain ⟨dp, dn, dk, dc, ds, di⟩ := hd
    refine hs_step (OpEx.copy capR cap1R d (by decide)) ?_
    set d1 := d.set capR (d.env cap1R)
    have q1 : Pre d1 := preSetR dp capR (Or.inr (Or.inr (Or.inr rfl))) _
    refine Hs.mono (hs_opq (OpEx.sub capR r1 d1 (by decide) (by
      simp only [d1, DS.set_env_self, DS.set_env_ne _ _ (show r1 ≠ capR by decide), dp.c1, dc]
      exact Nat.one_le_two_pow))) le_rfl ?_
    rintro e rfl
    have q2 : Pre (d1.set capR (d1.env capR - d1.env r1)) := preSetR q1 capR (Or.inr (Or.inr (Or.inr rfl))) _
    have hreg : ∀ y : Fin VV, y ≠ capR → (d1.set capR (d1.env capR - d1.env r1)).env y = d.env y := fun y hy => by
      simp only [d1, DS.set_env_ne _ _ hy]
    refine ⟨⟨q2.c0, q2.c1, q2.c2, ?_, by rw [hreg _ (by decide), dc]; rfl, by rw [hreg _ (by decide), dk]; rfl,
      by rw [hreg _ (by decide), dn]; rfl, by rw [q2.t]; rfl, q2.p⟩, fun i => ?_, q2.out, by simp [d1, di]⟩
    · simp only [d1, DS.set_env_self, DS.set_env_ne _ _ (show r1 ≠ capR by decide), dp.c1, dc]; rfl
    · rw [q2.hi _ (by rw [uv_val]; omega)]; rfl

theorem pre_ok (hlt : leadOnes inp < inp.length) :
    Hs (ctxOf noCallee zF inp) preP (a0 : DS VV MM) (preCost inp) (PreOk inp) := by
  unfold preP
  refine hs_pre (t2 := 15 * leadOnes inp + 4 + (5 * kOf inp + 15) + 1) (init_ok inp) (fun b ⟨bp, bn, bi⟩ => ?_)
    |>.mono (by unfold preCost; omega) (fun _ h => h)
  exact hs_pre (read_ok inp hlt b bp bn bi) (fun c ⟨cp, cn, ci⟩ => pow_ok inp c cp cn ci)


theorem gok (h1 : 1 ≤ leadOnes inp) : GOk (ctxOf noCallee zF inp) (globOf inp) := by
  have hWd := wd_eq inp
  have hp : 64 ≤ 64 ^ leadOnes inp := by
    calc 64 = 64 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) h1
  refine ⟨show 3 ≤ kOf inp by unfold kOf; omega, show kOf inp + 1 ≤ _ by rw [hWd]; unfold kOf; omega, ?_⟩
  show kOf inp ≤ 2 ^ kOf inp - 1
  have := add_two_lt_pow (kOf inp) (by unfold kOf; omega); omega

theorem rel_s0 (h1 : 1 ≤ leadOnes inp) (b : DS VV MM) (h : PreOk inp b) : Rel (globOf inp) (s0 inp) b := by
  have hg := gok inp h1
  refine ⟨h.env, fun i => h.uv i, h.out, fun i => Nat.zero_le _, ?_, h.ip⟩
  show fieldOk (globOf inp) 1 2 = true
  have := hg.1
  simp only [fieldOk, decide_eq_true_eq]; refine ⟨le_rfl, ?_, by norm_num, by norm_num⟩
  show 1 + 2 ≤ kOf inp; exact this

end Prelude

/-- **An `FL` program runs as a cell program** on an input `1^L 0 ++ rest` (`L ≥ 1`), with its `FL` output, within
the prelude's cost and `costS` (proof of `thm:short-pcp-ours`). -/
theorem flRun (main : S) (hwf : wfS main 0 = true) (inp : List Bool) (h1 : 1 ≤ leadOnes inp)
    (hlt : leadOnes inp < inp.length) (hbad : (evalS (globOf inp) main (s0 inp)).bad = false) :
    ∃ b n, Ex (ctxOf noCallee zF inp) (progOf main) a0 b n ∧ b.out = (evalS (globOf inp) main (s0 inp)).out ∧
      n ≤ preCost inp + costS (globOf inp) main + 1 := by
  obtain ⟨b, n, hx, hn, hb⟩ := hs_pre (pre_ok inp hlt) (fun b hb =>
    (compS_ok (gok inp h1) rfl main 0 (s0 inp) b (by omega) hwf hbad (rel_s0 inp h1 b hb)).mono le_rfl
      (fun c hc => hc.rel))
  exact ⟨b, n, hx, hb.out, hn⟩

theorem one_le_wd (inp : List Bool) : 1 ≤ zF.W (leadOnes inp) := by
  show 1 ≤ 2 ^ (6 * leadOnes inp) * 4
  have := Nat.one_le_two_pow (n := 6 * leadOnes inp); omega

/-- **An `FL` program as an ordinary word function.** -/
noncomputable def flWF {Req : Type} (input : Req → List Bool) (main : S) (hwf : wfS main 0 = true)
    (h1 : ∀ r, 1 ≤ leadOnes (input r)) (hlt : ∀ r, leadOnes (input r) < (input r).length)
    (hbad : ∀ r, (evalS (globOf (input r)) main (s0 (input r))).bad = false) :
    WordFunction Req input (fun r => (evalS (globOf (input r)) main (s0 (input r))).out)
      (fun r => langBudget noCallee zF VV MM (input r) (preCost (input r) + costS (globOf (input r)) main + 1)) :=
  wordFunction_of_lang input _ noCallee zF (progOf main) _ (fun r => flRun main hwf (input r) (h1 r) (hlt r) (hbad r))
    (fun r => one_le_wd (input r))


/-- The constant of the budget bound of an `FL` program. -/
noncomputable def flConst (main : S) : ℕ :=
  10 ^ 6 * (89600 * szS main * 3 ^ dpS main + 72) * (16 + NearCubicGates.Close.Cells.TSK noCallee) ^ 2

/-- **The budget is polynomial**: in `64^L + |input|` for `L` leading ones (proof of `thm:short-pcp-ours`). -/
theorem flBudget_le (main : S) (inp : List Bool) :
    langBudget noCallee zF VV MM inp (preCost inp + costS (globOf inp) main + 1) ≤
      flConst main * (64 ^ leadOnes inp + inp.length + 1) ^ (dpS main + 5) := by
  have hl := lang_le noCallee 4 6 inp (preCost inp + costS (globOf inp) main + 1)
  have hcs := costS_le (globOf inp) main
  set L := leadOnes inp with hL
  have hLi : L ≤ inp.length := leadOnes_le inp
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 64 ^ L + inp.length + 1 := ⟨_, rfl⟩
  rw [← hY]
  set T := NearCubicGates.Close.Cells.TSK noCallee
  set d := dpS main
  set z := szS main
  have h64 : 2 ^ (6 * L) = 64 ^ L := by rw [pow_mul]; norm_num
  have hY1 : 1 ≤ Y := by rw [hY]; exact Nat.le_add_left 1 _
  have hK : (globOf inp).K = 2 * 64 ^ L := rfl
  have hN : (globOf inp).N = 2 * 64 ^ L := rfl
  have hK3 : (globOf inp).K + 1 ≤ 3 * Y := by rw [hK, hY]; omega
  have hopc : opc (globOf inp) ≤ 11200 * Y ^ 3 := by
    unfold opc
    have : ((globOf inp).K + 1) ^ 3 ≤ (3 * Y) ^ 3 := Nat.pow_le_pow_left hK3 3
    have : 1 ≤ Y ^ 3 := Nat.one_le_pow _ _ hY1
    rw [mul_pow] at *; norm_num at *; omega
  have hNp : ((globOf inp).N + 1) ^ d ≤ 3 ^ d * Y ^ d := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by rw [hN]; omega) d
  have hYd : 1 ≤ Y ^ d := Nat.one_le_pow _ _ hY1
  have hc : costS (globOf inp) main ≤ 89600 * z * 3 ^ d * Y ^ (3 + d) := by
    calc costS (globOf inp) main ≤ 8 * z * opc (globOf inp) * ((globOf inp).N + 1) ^ d := hcs
      _ ≤ 8 * z * (11200 * Y ^ 3) * (3 ^ d * Y ^ d) := by gcongr
      _ = 89600 * z * 3 ^ d * Y ^ (3 + d) := by rw [pow_add]; ring
  have hp : preCost inp + 1 ≤ 71 * Y ^ (3 + d) := by
    have e1 : preCost inp + 1 ≤ 71 * Y := by
      have : preCost inp = 20 * L + 5 * (2 * 64 ^ L) + 40 := rfl
      rw [this, hY]; omega
    have : Y ≤ Y ^ (3 + d) := Nat.le_self_pow (by omega) _
    omega
  have hNb : preCost inp + costS (globOf inp) main + 1 + 1 ≤ (89600 * z * 3 ^ d + 72) * Y ^ (3 + d) := by
    have : 1 ≤ Y ^ (3 + d) := Nat.one_le_pow _ _ hY1
    nlinarith
  have hin : 2 ^ (6 * L) * 4 + L + inp.length + 4 + 6 + T + 1 ≤ (16 + T) * Y := by
    rw [h64, hY]; nlinarith
  calc langBudget noCallee zF VV MM inp (preCost inp + costS (globOf inp) main + 1)
      ≤ 10 ^ 6 * ((preCost inp + costS (globOf inp) main + 1 + 1) *
          (2 ^ (6 * L) * 4 + L + inp.length + 4 + 6 + T + 1) ^ 2) := hl
    _ ≤ 10 ^ 6 * (((89600 * z * 3 ^ d + 72) * Y ^ (3 + d)) * ((16 + T) * Y) ^ 2) := by gcongr
    _ = flConst main * Y ^ (d + 5) := by unfold flConst; ring

end NearCubicGates.Adapters.ShortPCP.Machines.FL
