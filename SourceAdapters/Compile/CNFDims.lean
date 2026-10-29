import SourceAdapters.Compile.CNFKeep

/-!
# The dimensions of the request

proof of `lem:multitape-refuter` (the finite control is read from its code): from the stored code bits (`sCB`) the printer computes the
tape count `t` (leading ones), the state count `s` (next ones), `w = natBitLength s`, the start state (the next `w`
bits, least significant first: `CNFCodeBits.codeBits_start`), and the derived data registers of the generator
context `GC` (`CNFGenA`): width `fuel + 1`, `t·width`, `windowBits`, `2^t`, record length, the two table offsets.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
  NearCubicWires.RepairSource.VerifierEncoding
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-! ## Facts about the code bits -/

theorem code_length (v : Verifier) :
    (code v).length = codeO3 v + v.stateCount * 2 ^ v.tapeCount * codeR v := by
  rw [code_split, List.length_append, List.length_append, code_head_length, pairs_length,
    length_flatten_ofFn (2 ^ v.tapeCount * codeR v) _ _ (fun i => by
      rw [length_flatten_ofFn (codeR v) _ _ (fun mask => by rw [actionCode_length]; rfl)])]
  unfold codeO3; ring

theorem codeBits_length (v : Verifier) :
    (codeBits v).length = codeO3 v + v.stateCount * 2 ^ v.tapeCount * codeR v := by
  rw [codeBits, List.length_map, code_length]

theorem codeBits_getD (v : Verifier) (p : ℕ) : (codeBits v).getD p 0 = ((code v).getD p false).toNat := by
  rw [codeBits, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (code v)[p]? <;> rfl

theorem codeBits_le_one (v : Verifier) (p : ℕ) : (codeBits v).getD p 0 ≤ 1 := by
  rw [codeBits_getD]; cases (code v).getD p false <;> simp

theorem getD_app_right' {α : Type} (l₁ l₂ : List α) (d : α) (k : ℕ) : (l₁ ++ l₂).getD (l₁.length + k) d = l₂.getD k d := by
  rw [List.getD_append_right _ _ _ _ (by omega)]; simp

/-- The header: `1^t 0 1^s 0`. -/
theorem code_header (v : Verifier) :
    (∀ i < v.tapeCount, (codeBits v).getD i 0 = 1) ∧ (codeBits v).getD v.tapeCount 0 = 0 ∧
    (∀ i < v.stateCount, (codeBits v).getD (v.tapeCount + 1 + i) 0 = 1) ∧
    (codeBits v).getD (v.tapeCount + 1 + v.stateCount) 0 = 0 := by
  obtain ⟨rest, e⟩ : ∃ rest, code v = (List.replicate v.tapeCount true ++ [false]) ++
      ((List.replicate v.stateCount true ++ [false]) ++ rest) := by
    refine ⟨fixedBits (codeW v) v.machine.start.val ++
      (List.ofFn fun i : Fin v.stateCount => [v.machine.halted i, v.accepting i]).flatten ++
      (List.ofFn fun i : Fin v.stateCount =>
        (List.ofFn fun mask : Fin (2 ^ v.tapeCount) =>
          actionCode (codeW v) (v.machine.rule i (fun tape => mask.val.testBit tape.val))).flatten).flatten, ?_⟩
    rw [code_split]; simp [List.append_assoc]
  have hA : (List.replicate v.tapeCount true ++ [false]).length = v.tapeCount + 1 := by simp
  have hB : (List.replicate v.stateCount true ++ [false]).length = v.stateCount + 1 := by simp
  refine ⟨fun i hi => ?_, ?_, fun i hi => ?_, ?_⟩ <;> rw [codeBits_getD, e]
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by simpa using hi)]; simp [hi]
  · rw [List.getD_append _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by simp)]; simp
  · rw [show v.tapeCount + 1 + i = (List.replicate v.tapeCount true ++ [false]).length + i by rw [hA],
      getD_app_right', List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by simpa using hi)]; simp [hi]
  · rw [show v.tapeCount + 1 + v.stateCount = (List.replicate v.tapeCount true ++ [false]).length + v.stateCount by
      rw [hA], getD_app_right', List.getD_append _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by simp)]; simp

variable {C : Ctx}

/-! ## Counting ones -/

/-- Count consecutive `1` records of `sCB` from its cursor into `c` (reading the terminating `0`). -/
def onesP (c : Fin VV) : St VV MM :=
  .seq (.op (.zero c)) (.seq (.op (.rdM sCB pA)) (.loop (.eq pA v1) (.seq (.op (.inc c)) (.op (.rdM sCB pA)))))

theorem onesP_spec (c : Fin VV) (hc : c ∉ [pA, v1]) (cb : List ℕ) (p k : ℕ) (a : DS VV MM) (h1 : a.env v1 = 1)
    (hcb : a.ram sCB = cb) (hrc : a.rc sCB = p) (hones : ∀ i < k, cb.getD (p + i) 0 = 1)
    (hzero : cb.getD (p + k) 0 = 0) (hlen : p + k < cb.length) (hW : k + 1 < 2 ^ C.Wd) :
    Hs C (onesP c) a (5 * k + 6) (fun b => b.env c = k ∧ b.rc sCB = p + k + 1 ∧ b.ram = a.ram ∧
      b.env v1 = 1) := by
  have hc' : c ≠ pA ∧ c ≠ v1 := by simpa using hc
  let I : ℕ → DS VV MM → Prop := fun i b => b.env c = i ∧ b.rc sCB = p + i + 1 ∧ b.env pA = cb.getD (p + i) 0 ∧
    b.ram = a.ram ∧ b.env v1 = 1
  have hloop := Hs.loopN (C := C) (c := .eq pA v1) (s := .seq (.op (.inc c)) (.op (.rdM sCB pA)))
    (show pA ≠ v1 by decide) I k 3
    (fun i hi b ⟨b1, b2, b3, b4, b5⟩ => by
      refine ⟨by simp only [Cnd.eval, b3, b5, hones i hi]; decide, ?_⟩
      refine Hs.seqc (t1 := 1) (t2 := 1) (hs_inc C c b (by rw [b1]; omega)) (fun d hd => ?_) (by omega)
      subst hd
      refine Hs.op (OpEx.rdM sCB pA _ (by simp [b2, b4, hcb]; omega)) ⟨?_, ?_, ?_, ?_, ?_⟩
      · simp [DS.adv, DS.set, Function.update_apply, hc'.1, b1]
      · simp [DS.adv, b2]; omega
      · simp only [DS.adv, DS.set_ram, DS.set_rc, DS.env_set, Function.update_self, b2, b4, hcb]; rfl
      · simp [DS.adv, b4]
      · vsimp [DS.adv, Function.update_apply, Ne.symm hc'.2, b5])
    (fun b ⟨_, _, b3, _, b5⟩ => by simp only [Cnd.eval, b3, b5, hzero]; decide)
  refine Hs.seqc (t1 := 1) (t2 := 5 * k + 4) (hs_zero C c a) (fun b1 hb1 => ?_) (by omega)
  subst hb1
  refine Hs.seqc (t1 := 1) (t2 := k * (3 + 2) + 2) (hs_rdM C sCB pA _ (by simp [hrc, hcb]; omega)) (fun b2 hb2 => ?_)
    (by omega)
  subst hb2
  refine Hs.mono (hloop _ ⟨?_, ?_, ?_, ?_, ?_⟩) le_rfl (fun b ⟨q1, q2, _, q4, q5⟩ => ⟨q1, q2, by rw [q4],
    q5⟩)
  · simp [DS.adv, DS.set, Function.update_apply, hc'.1]
  · simp [DS.adv, hrc]
  · simp only [DS.adv, DS.set_ram, DS.set_rc, DS.env_set, Function.update_self, hrc, hcb, Nat.add_zero]
  · rfl
  · vsimp [DS.adv, Function.update_apply, Ne.symm hc'.2, h1]

/-! ## The bit length -/

/-- `dWb := natBitLength dS` (for `dS ≥ 1`), scratch `pA`. -/
def bitLenP : St VV MM :=
  .seq (.op (.copy pA dS)) (.seq (.op (.zero dWb)) (.loop (.lt vZ pA) (.seq (.op (.half pA)) (.op (.inc dWb)))))

theorem bitLenP_spec (s : ℕ) (hs : 1 ≤ s) (a : DS VV MM) (hS : a.env dS = s) (hz : a.env vZ = 0)
    (hW : natBitLength s + 1 < 2 ^ C.Wd) :
    Hs C bitLenP a (5 * natBitLength s + 6) (fun b => b.env dWb = natBitLength s ∧ b.ram = a.ram ∧ b.rc = a.rc) := by
  set w := natBitLength s with hw
  let I : ℕ → DS VV MM → Prop := fun k b => b.env pA = s / 2 ^ k ∧ b.env dWb = k ∧ b.env vZ = 0 ∧ b.ram = a.ram ∧
    b.rc = a.rc
  have hlog := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) s
  have hloop := Hs.loopN (C := C) (c := .lt vZ pA) (s := .seq (.op (.half pA)) (.op (.inc dWb)))
    (show vZ ≠ pA by decide) I w 3
    (fun k hk b ⟨b1, b2, b3, b4, b5⟩ => by
      have hk' : k ≤ Nat.log 2 s := by unfold natBitLength at hw; omega
      have hp : 2 ^ k ≤ s := le_trans (Nat.pow_le_pow_right (by norm_num) hk') (Nat.pow_log_le_self 2 (by omega))
      refine ⟨by simp only [Cnd.eval, b1, b3, decide_eq_true_eq]; exact Nat.div_pos hp (by positivity), ?_⟩
      refine Hs.seqc (t1 := 1) (t2 := 1) (hs_half C pA b) (fun d hd => ?_) (by omega)
      subst hd
      refine Hs.op (OpEx.inc dWb _ (by vsimp [b2]; omega)) ⟨?_, ?_, ?_, ?_, ?_⟩
      · vsimp [b1, pow_succ, Nat.div_div_eq_div_mul]
      · vsimp [b2]
      · vsimp [b3]
      · simp [b4]
      · simp [b5])
    (fun b ⟨b1, _, b3, _, _⟩ => by
      have : s / 2 ^ w = 0 := Nat.div_eq_of_lt (by rw [hw]; unfold natBitLength; exact hlog)
      simp [Cnd.eval, b1, b3, this])
  refine Hs.seqc (t1 := 1) (t2 := w * (3 + 2) + 2 + 1 + 1) (hs_copy C pA dS a (by decide)) (fun b1 hb1 => ?_)
    (by omega)
  subst hb1
  refine Hs.seqc (t1 := 1) (t2 := w * (3 + 2) + 2) (hs_zero C dWb _) (fun b2 hb2 => ?_) (by omega)
  subst hb2
  refine Hs.mono (hloop ((a.set pA (a.env dS)).set dWb 0) ⟨by vsimp [hS], by vsimp [], by vsimp [hz], rfl, rfl⟩) le_rfl
    (fun b ⟨_, q2, _, q4, q5⟩ => ⟨q2, q4, q5⟩)

/-! ## The start state -/

/-- `dSt := numAt (bitAt cb) cursor dWb` (least significant first), scratch `pB pC pA`, counter `pT`. -/
def startP : St VV MM :=
  .seq (.op (.zero dSt)) (.seq (.op (.copy pC v1))
    (forP pT dWb (.seq (.op (.rdM sCB pB)) (.seq (.ite (.eq pB v1) (.op (.add dSt pC)) (.op (.zero pA)))
      (.op (.shl pC))))))

theorem startP_spec (cb : List ℕ) (p w : ℕ) (a : DS VV MM) (hk : KC a) (hcb : a.ram sCB = cb) (hrc : a.rc sCB = p)
    (h01 : ∀ q, cb.getD q 0 ≤ 1) (hlen : p + w ≤ cb.length) (hw : a.env dWb = w) (hW : 2 ^ (w + 1) < 2 ^ C.Wd) :
    Hs C startP a (w * 10 + 8) (fun b => b.env dSt = numAt (bitAt cb) p w ∧ b.ram = a.ram ∧
      b.rc sCB = p + w ∧ KC b) := by
  have hwW : w < 2 ^ C.Wd := lt_of_lt_of_le (Nat.lt_two_pow_self) (le_trans (Nat.pow_le_pow_right (by omega)
    (Nat.le_succ w)) hW.le)
  refine Hs.seqc (t1 := 1) (t2 := w * 10 + 6) (hs_zero C dSt a) (fun a1 ha1 => ?_) (by omega)
  subst ha1
  refine Hs.seqc (t1 := 1) (t2 := w * (6 + 4) + 4) (hs_copy C pC v1 _ (by decide)) (fun a2 ha2 => ?_) (by omega)
  subst ha2
  let I : ℕ → DS VV MM → Prop := fun i b => b.env dSt = numAt (bitAt cb) p i ∧ b.env pC = 2 ^ i ∧
    b.ram = a.ram ∧ b.rc sCB = p + i ∧ KC b ∧ b.env dWb = w
  refine Hs.mono (forP_ind (C := C) pT dWb _ (by decide) w 6 I hwW (fun i b hb => hb.2.2.2.2.2)
    (fun i b v ⟨q1, q2, q3, q4, q5, q6⟩ => ⟨by vsimp [q1], by vsimp [q2], q3, q4, q5.set' pT (by decide) v, by vsimp [q6]⟩)
    (fun i hi b ⟨q1, q2, q3, q4, q5, q6⟩ hbJ => ?_) _ ⟨by vsimp [numAt], by vsimp [hk.one], rfl, hrc,
      (hk.set' dSt (by decide) 0).set' pC (by decide) _, by vsimp [hw]⟩) le_rfl
    (fun b ⟨q1, _, q3, q4, q5, _⟩ => ⟨q1, q3, q4, q5⟩)
  have hx := h01 (p + i)
  have hnum : numAt (bitAt cb) p i < 2 ^ i := numAt_lt _ _ i
  have hpi : 2 ^ (i + 1) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hi
  have hpw : 2 ^ w * 2 < 2 ^ C.Wd := by rw [pow_succ] at hW; exact hW
  rw [pow_succ] at hpi
  refine Hs.seqc (t1 := 1) (t2 := 4) (hs_rdM C sCB pB b (by rw [q4, q3, hcb]; omega)) (fun d hd => ?_) (by omega)
  subst hd
  set d := (b.set pB ((b.ram sCB).getD (b.rc sCB) 0)).adv sCB with hd
  have dB : d.env pB = cb.getD (p + i) 0 := by simp [hd, DS.adv, q3, q4, hcb]
  have dk : KC d := (q5.set' pB (by decide) ((b.ram sCB).getD (b.rc sCB) 0)).of_fr (b := d) (T := [])
    (fun y _ => rfl) (by decide)
  have dS' : d.env dSt = numAt (bitAt cb) p i := by vsimp [hd, DS.adv, q1]
  have dC : d.env pC = 2 ^ i := by vsimp [hd, DS.adv, q2]
  have dT : d.env pT = i := by vsimp [hd, DS.adv, hbJ]
  have dW' : d.env dWb = w := by vsimp [hd, DS.adv, q6]
  have dr : d.ram = a.ram := by simp [hd, DS.adv, q3]
  have drc : d.rc sCB = p + i + 1 := by simp [hd, DS.adv, q4]
  have hstep : numAt (bitAt cb) p (i + 1) = numAt (bitAt cb) p i + (bitAt cb (p + i)).toNat * 2 ^ i := rfl
  refine Hs.seqc (t1 := 2) (t2 := 1) (R1 := fun e => e.env dSt = numAt (bitAt cb) p (i + 1) ∧ e.env pC = 2 ^ i ∧
      e.ram = a.ram ∧ e.rc sCB = p + i + 1 ∧ KC e ∧ e.env dWb = w ∧ e.env pT = i)
    (Hs.ite (show pB ≠ v1 by decide) (fun hc => ?_) (fun hc => ?_)) (fun e ⟨e1, e2, e3, e4, e5, e6, e7⟩ => ?_) (by omega)
  · have h1 : cb.getD (p + i) 0 = 1 := by simp only [Cnd.eval, dB, dk.one, decide_eq_true_eq] at hc; exact hc
    refine Hs.mono (Hs.op (OpEx.add dSt pC d (by decide) (by rw [dS', dC]; omega)) rfl) (by omega) ?_
    rintro e rfl
    exact ⟨by rw [DS.set_env_self, dS', dC, hstep, bitAt, h1]; simp, by vsimp [dC], dr, drc, dk.set' dSt (by decide) _,
      by vsimp [dW'], by vsimp [dT]⟩
  · have h1 : ¬ cb.getD (p + i) 0 = 1 := by simp only [Cnd.eval, dB, dk.one, decide_eq_false_iff_not] at hc; exact hc
    refine Hs.mono (Hs.op (OpEx.zero pA d) rfl) (by omega) ?_
    rintro e rfl
    exact ⟨by rw [DS.set_env_ne _ _ (by decide), dS', hstep, bitAt, decide_eq_false h1]; simp, by vsimp [dC], dr, drc, dk.set' pA (by decide) _, by vsimp [dW'],
      by vsimp [dT]⟩
  · refine Hs.op (OpEx.shl pC e (by rw [e2]; omega)) ⟨⟨by vsimp [e1], by vsimp [e2, pow_succ]; ring, e3, by show e.rc sCB = p + (i + 1); omega,
      e5.set' pC (by decide) _, by vsimp [e6]⟩, by vsimp [e7]⟩

end NearCubicGates.Adapters.Compile
