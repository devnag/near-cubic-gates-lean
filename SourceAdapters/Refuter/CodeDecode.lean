import SourceAdapters.Refuter.ParseRecord

/-!
# The machine description from the record index (input 7, the record codec, part 3)

proof of `lem:multitape-refuter` (`𝒟` "parses its input as `⟨M,N,z⟩`") and proof of `cor:framed-refuter` ("The fixed-machine decoding cost
is `a_M`"). The record carries `M` as the unary count `A = machineIndex M`, whose binary expansion is
`1` followed by `VerifierEncoding.code M.verifier` (`machineIndex`, `Assembly.lean`). `decode` writes that
code onto the code stream: it counts the binary digits of `A` by halving a copy, places the head at the
last code cell and halves `A` again, writing each remainder and stepping left. `decode_spec`: the code
stream ends as exactly `code(M)` with its head at `0`; the cost depends only on `M` (it is part of
`a_M`).
-/

namespace NearCubicGates.Adapters.Refuter.Mach

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

variable (cap : ℕ)

/-! ## The index in binary -/

/-- The fold defining `machineIndex`. -/
def idxStep (acc : ℕ) (b : Bool) : ℕ := 2 * acc + if b then 1 else 0

theorem testBit_idxStep (acc : ℕ) (b : Bool) (j : ℕ) :
    (idxStep acc b).testBit j = if j = 0 then b else acc.testBit (j - 1) := by
  cases j with
  | zero => cases b <;> simp [idxStep, Nat.testBit_zero, Nat.add_mod]
  | succ j =>
    simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, Nat.testBit_succ]
    congr 1; cases b <;> simp [idxStep] <;> omega

theorem testBit_foldl (l : List Bool) : ∀ (acc j : ℕ), (l.foldl idxStep acc).testBit j =
    if h : j < l.length then l[l.length - 1 - j]'(by omega) else acc.testBit (j - l.length) := by
  induction l with
  | nil => intro acc j; simp
  | cons b l ih =>
    intro acc j
    simp only [List.foldl_cons, ih, List.length_cons]
    by_cases h1 : j < l.length
    · have h2 : j < l.length + 1 := by omega
      simp only [h1, h2, dite_true]
      rw [List.getElem_cons]
      split
      · omega
      · (congr 1) <;> omega
    · simp only [h1, dite_false, testBit_idxStep]
      by_cases h3 : j = l.length
      · subst h3; simp
      · have h2 : ¬ j < l.length + 1 := by omega
        simp only [h2, dite_false, show j - l.length ≠ 0 by omega, if_false]
        (congr 1) <;> omega

theorem foldl_bounds (l : List Bool) : ∀ acc, 0 < acc →
    acc * 2 ^ l.length ≤ l.foldl idxStep acc ∧ l.foldl idxStep acc < (acc + 1) * 2 ^ l.length := by
  induction l with
  | nil => intro acc _; simp
  | cons b l ih =>
    intro acc hacc
    simp only [List.foldl_cons, List.length_cons, pow_succ]
    obtain ⟨h1, h2⟩ := ih (idxStep acc b) (by unfold idxStep; omega)
    constructor
    · calc acc * (2 ^ l.length * 2) = (2 * acc) * 2 ^ l.length := by ring
        _ ≤ idxStep acc b * 2 ^ l.length := Nat.mul_le_mul_right _ (by unfold idxStep; omega)
        _ ≤ _ := h1
    · calc l.foldl idxStep (idxStep acc b) < (idxStep acc b + 1) * 2 ^ l.length := h2
        _ ≤ (2 * acc + 2) * 2 ^ l.length := Nat.mul_le_mul_right _ (by unfold idxStep; split <;> omega)
        _ = (acc + 1) * (2 ^ l.length * 2) := by ring

theorem machineIndex_eq (M : OrdinaryWeakMachine) :
    machineIndex M = (VerifierEncoding.code M.verifier).foldl idxStep 1 := rfl

/-! ## Halving a register -/

/-- `R := 0`, `Q += R/2`, `B += R%2`. -/
def halfLoop (R Q B : Fin NR) : Pg := .whr R (.seq (WMX.dec R) (.ifr R (.seq (WMX.dec R) (WMX.inc Q)) (WMX.inc B)))

theorem halfLoop_spec {R Q B : Fin NR} (hRQ : R ≠ Q) (hRB : R ≠ B) (hQB : Q ≠ B) :
    ∀ v (σ : St), σ.val R = v → σ.val Q + v ≤ cap → σ.val B < cap →
      WXExec cap (halfLoop R Q B) σ (((σ.setv R 0).setv Q (σ.val Q + v / 2)).setv B (σ.val B + v % 2)) (5 * v + 10) := by
  intro v
  induction v using Nat.strong_induction_on with
  | _ v ih =>
    intro σ hv hq hb
    rcases v with _ | _ | n
    ·
      refine (WXExec.whrF hv).cast cap ?_ (by omega)
      apply WState.eq <;> try rfl
      funext r; simp only [WState.setv_val, Function.update_apply]; split_ifs <;> simp_all
    ·
      have d1 := WXExec.dec cap R σ (by omega)
      have i1 := WXExec.inc cap B (σ.setv R (σ.val R - 1)) (by simp [Function.update_apply, Ne.symm hRB]; omega)
      have f1 : WXExec cap (.ifr R (.seq (WMX.dec R) (WMX.inc Q)) (WMX.inc B)) (σ.setv R (σ.val R - 1)) _ _ :=
        WXExec.ifrF (by simp [hv]) i1
      have e := WXExec.whrT (r := R) (by omega) (WXExec.seq d1 f1)
        (WXExec.whrF (P := .seq (WMX.dec R) (.ifr R (.seq (WMX.dec R) (WMX.inc Q)) (WMX.inc B)))
          (σ := ((σ.setv R (σ.val R - 1)).setv B ((σ.setv R (σ.val R - 1)).val B + 1)))
          (by simp [Function.update_apply, hRB, hv]))
      refine e.cast cap ?_ (by omega)
      apply WState.eq <;> try rfl
      funext r; simp only [WState.setv_val, Function.update_apply]; split_ifs <;> simp_all
    ·
      have d1 := WXExec.dec cap R σ (by omega)
      have d2 := WXExec.dec cap R (σ.setv R (σ.val R - 1)) (by simp; omega)
      have i1 := WXExec.inc cap Q ((σ.setv R (σ.val R - 1)).setv R ((σ.setv R (σ.val R - 1)).val R - 1))
        (by simp [Function.update_apply, Ne.symm hRQ]; omega)
      have f1 : WXExec cap (.ifr R (.seq (WMX.dec R) (WMX.inc Q)) (WMX.inc B)) (σ.setv R (σ.val R - 1)) _ _ :=
        WXExec.ifrT (by simp [hv]) (WXExec.seq d2 i1)
      set σ' := ((σ.setv R (σ.val R - 1)).setv R ((σ.setv R (σ.val R - 1)).val R - 1)).setv Q
        (((σ.setv R (σ.val R - 1)).setv R ((σ.setv R (σ.val R - 1)).val R - 1)).val Q + 1) with hσ'
      have r' := ih n (by omega) σ' (by simp [σ', Function.update_apply, hRQ, hv])
        (by simp [σ', Function.update_apply, hRQ, Ne.symm hRQ]; omega)
        (by simp [σ', Function.update_apply, hRB, Ne.symm hQB, Ne.symm hRB]; omega)
      have e := WXExec.whrT (r := R) (by omega) (WXExec.seq d1 f1) r'
      refine e.cast cap ?_ (by omega)
      apply WState.eq <;> try rfl
      funext r
      simp only [σ', WState.setv_val, Function.update_apply]
      have h2 : (n + 2) / 2 = n / 2 + 1 := by omega
      have h3 : (n + 2) % 2 = n % 2 := by omega
      split_ifs <;> simp_all <;> omega

/-! ## Writing the code right to left -/

theorem wtb_length (l : List Bool) (p : ℕ) (b : Bool) : (writeTapeBit l p b).length = max l.length (p + 1) := by
  induction l generalizing p with
  | nil =>
    induction p with
    | zero => rfl
    | succ p ih => simp only [writeTapeBit, List.length_cons] at ih ⊢; rw [ih]; simp
  | cons a l ih =>
    cases p with
    | zero => simp [writeTapeBit]
    | succ p => simp only [writeTapeBit, List.length_cons, ih]; omega

theorem list_eq_of_read {l₁ l₂ : List Bool} (hl : l₁.length = l₂.length)
    (h : ∀ p < l₁.length, readTapeBit l₁ p = readTapeBit l₂ p) : l₁ = l₂ := by
  apply List.ext_getElem hl
  intro p h1 h2
  have := h p h1
  simpa [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2]
    using this

/-- The code stream after `k` remainders, written at `L-1, L-2, …`. -/
def wlist (a L : ℕ) : ℕ → List Bool
  | 0 => []
  | k + 1 => writeTapeBit (wlist a L k) (L - 1 - k) (a.testBit k)

theorem wlist_spec (a L : ℕ) (hL : 1 ≤ L) : ∀ k, k ≤ L →
    (1 ≤ k → (wlist a L k).length = L) ∧
    ∀ p, readTapeBit (wlist a L k) p = if L - k ≤ p ∧ p < L then a.testBit (L - 1 - p) else false
  | 0, _ => ⟨fun h => absurd h (by omega), fun p => by
      simp only [wlist, readTapeBit, List.getD_nil]; split_ifs <;> first | rfl | omega⟩
  | k + 1, hk => by
    obtain ⟨h1, h2⟩ := wlist_spec a L hL k (by omega)
    refine ⟨fun _ => ?_, fun p => ?_⟩
    · simp only [wlist, wtb_length]
      by_cases hk0 : k = 0
      · subst hk0; simp [wlist]; omega
      · rw [h1 (by omega)]; omega
    · simp only [wlist]
      rw [readTapeBit_writeTapeBit, h2 p]
      by_cases hp : p = L - 1 - k
      · subst hp; simp only [if_true]
        rw [if_pos (by omega)]; congr 1; omega
      · simp only [hp, if_false]
        by_cases hq : L - k ≤ p ∧ p < L
        · rw [if_pos hq, if_pos (by omega)]
        · rw [if_neg hq, if_neg (by omega)]

theorem wlist_code (l : List Bool) (hl : 1 ≤ l.length) :
    wlist (l.foldl idxStep 1) l.length l.length = l := by
  obtain ⟨h1, h2⟩ := wlist_spec (l.foldl idxStep 1) l.length hl l.length le_rfl
  apply list_eq_of_read (h1 hl)
  intro p hp
  rw [h2 p, if_pos (by rw [h1 hl] at hp; omega), testBit_foldl, dif_pos (by rw [h1 hl] at hp; omega)]
  rw [h1 hl] at hp
  simp [readTapeBit, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp]
  congr 1; omega

/-! ## The program -/

def decCount : Pg :=
  .whr rTC (.seq (halfLoop rTC rQ rBIT) (.seq (clr rBIT) (.seq (WMX.inc rP) (.wm (WM.move rQ rTC)))))

def decBody : Pg :=
  .seq (halfLoop rAI rQ rBIT) (.seq (.ifr rBIT (WMX.wr sCODE true) (WMX.wr sCODE false)) (.seq (clr rBIT)
    (.seq (WMX.bwd sCODE) (.wm (WM.move rQ rAI)))))

def decode : Pg :=
  .seq (addR rAI rTC rTA) (.seq decCount (.seq (WMX.dec rP) (.seq (fwdK sCODE rP rTB) (.seq (WMX.bwd sCODE)
    (.seq (repK rP rTG decBody) (.seq (clr rAI) (clr rP)))))))

/-- One halving step: `v` in `R` becomes `v/2`, the remainder is consumed by `rest`. -/
theorem half_move (R : Fin NR) (hR : R ≠ rQ ∧ R ≠ rBIT) (σ : St) (hQ : σ.val rQ = 0) (hB : σ.val rBIT = 0)
    (hcap : σ.val R + 2 ≤ cap) :
    WXExec cap (halfLoop R rQ rBIT) σ (((σ.setv R 0).setv rQ (σ.val R / 2)).setv rBIT (σ.val R % 2))
      (5 * σ.val R + 10) := by
  have := halfLoop_spec cap (R := R) (Q := rQ) (B := rBIT) hR.1 hR.2 (by decide) (σ.val R) σ rfl
    (by rw [hQ]; omega) (by rw [hB]; omega)
  rw [hQ, hB, Nat.zero_add, Nat.zero_add] at this
  exact this

set_option maxHeartbeats 400000 in
theorem decCount_step (σ : St) (a k : ℕ) (hQ : σ.val rQ = 0) (hB : σ.val rBIT = 0) (hcap : 2 * a + 4 ≤ cap)
    (hk : k ≤ a) :
    WXExec cap (.seq (halfLoop rTC rQ rBIT) (.seq (clr rBIT) (.seq (WMX.inc rP) (.wm (WM.move rQ rTC)))))
      ((σ.setv rTC (a / 2 ^ k)).setv rP k) ((σ.setv rTC (a / 2 ^ (k + 1))).setv rP (k + 1)) (9 * a + 20) := by
  have hv : a / 2 ^ k ≤ a := Nat.div_le_self _ _
  obtain ⟨τ1, e1, h1⟩ := exEq cap (half_move cap rTC (by decide) ((σ.setv rTC (a / 2 ^ k)).setv rP k)
    (by simp [hQ]) (by simp [hB]) (by simp; omega))
  obtain ⟨τ2, e2, h2⟩ := exEq cap (clr_spec cap rBIT τ1 (by rw [h1]; simp; omega))
  obtain ⟨τ3, e3, h3⟩ := exEq cap (WXExec.inc cap rP τ2 (by rw [h2, h1]; simp; omega))
  have e4 := WXExec.wm (wmove_spec (cap := cap) rQ rTC (by decide) (a / 2 ^ k / 2) τ3
    (by rw [h3, h2, h1]; simp) (by rw [h3, h2, h1]; simp; omega) (by rw [h3, h2, h1]; simp; omega))
  refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).cast cap ?_ ?_
  · have hd : a / 2 ^ k / 2 = a / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
    rw [h3, h2, h1]
    apply WState.eq <;> try rfl
    funext r
    simp only [WState.setv_val]
    by_cases r1 : r = rTC
    · subst r1; simp [hd]
    · by_cases r2 : r = rP
      · subst r2; simp
      · by_cases r3 : r = rQ
        · subst r3; simp [hQ]
        · by_cases r4 : r = rBIT
          · subst r4; simp [hB]
          · simp [Function.update_apply, r1, r2, r3, r4]
  · rw [h1]; simp only [WState.setv_val, Function.update_self, Function.update_apply]
    simp
    generalize a / 2 ^ k = v at hv ⊢
    omega

theorem decCount_spec (σ : St) (l : List Bool) (hQ : σ.val rQ = 0) (hB : σ.val rBIT = 0)
    (hP : σ.val rP = 0) (hcap : 2 * l.foldl idxStep 1 + 4 ≤ cap) :
    WXExec cap decCount (σ.setv rTC (l.foldl idxStep 1)) ((σ.setv rTC 0).setv rP (l.length + 1))
      ((l.length + 1) * (9 * l.foldl idxStep 1 + 22) + 1) := by
  set a := l.foldl idxStep 1 with ha
  obtain ⟨b1, b2⟩ := foldl_bounds l 1 (by omega)
  simp only [one_mul, Nat.one_add, ← ha] at b1 b2
  have hlt : l.length < a := lt_of_lt_of_le (Nat.lt_two_pow_self) b1
  have e := whrE cap (r := rTC) (st := fun k => (σ.setv rTC (a / 2 ^ k)).setv rP k) (l.length + 1) (9 * a + 20)
    (fun k hk => by
      simp only [WState.setv_val, Function.update_apply, show rTC ≠ rP by decide, if_true, if_false]
      apply Nat.ne_of_gt
      apply Nat.div_pos (le_trans (Nat.pow_le_pow_right (by norm_num) (by omega)) b1) (by positivity))
    (by
      simp only [WState.setv_val, Function.update_apply, show rTC ≠ rP by decide, if_true, if_false]
      apply Nat.div_eq_of_lt
      calc a < (1 + 1) * 2 ^ l.length := b2
        _ = 2 ^ (l.length + 1) := by ring)
    (fun k hk => decCount_step cap σ a k hQ hB hcap (by omega))
  have e0 : (σ.setv rTC (a / 2 ^ 0)).setv rP 0 = σ.setv rTC a := by
    apply WState.eq <;> try rfl
    funext r; simp only [WState.setv_val, Function.update_apply]; split_ifs <;> simp_all
  have e1 : (σ.setv rTC (a / 2 ^ (l.length + 1))).setv rP (l.length + 1) = (σ.setv rTC 0).setv rP (l.length + 1) := by
    rw [Nat.div_eq_of_lt (by calc a < (1 + 1) * 2 ^ l.length := b2
        _ = 2 ^ (l.length + 1) := by ring)]
  rw [e0, e1] at e
  exact e

theorem testBit_eq_mod (a k : ℕ) : a.testBit k = decide (a / 2 ^ k % 2 ≠ 0) := by
  have e : a.testBit k = (a / 2 ^ k).testBit 0 := by rw [Nat.testBit_div_two_pow, Nat.zero_add]
  rw [e, Nat.testBit_zero]
  have := Nat.mod_two_eq_zero_or_one (a / 2 ^ k)
  rcases this with h | h <;> simp [h]

/-- The write-loop states. -/
def wSt (σ : St) (a L k : ℕ) : St := ((σ.setv rAI (a / 2 ^ k)).sets sCODE (wlist a L k)).seth sCODE (L - 1 - k)

set_option maxHeartbeats 400000 in
theorem decBody_step (σ : St) (a L k v1 v2 : ℕ) (hQ : σ.val rQ = 0) (hB : σ.val rBIT = 0) (hcap : 2 * a + 4 ≤ cap) :
    WXExec cap decBody (((wSt σ a L k).setv rP v1).setv rTG v2) (((wSt σ a L (k + 1)).setv rP v1).setv rTG v2)
      (9 * a + 20) := by
  have hv : a / 2 ^ k ≤ a := Nat.div_le_self _ _
  set τ0 := ((wSt σ a L k).setv rP v1).setv rTG v2 with hτ0
  have q0 : τ0.val rQ = 0 := by simp [τ0, wSt, hQ]
  have b0 : τ0.val rBIT = 0 := by simp [τ0, wSt, hB]
  have a0 : τ0.val rAI = a / 2 ^ k := by simp [τ0, wSt]
  obtain ⟨τ1, e1, h1⟩ := exEq cap (half_move cap rAI (by decide) τ0 q0 b0 (by rw [a0]; omega))
  have hbit : decide (τ1.val rBIT ≠ 0) = a.testBit k := by rw [h1]; simp [a0, testBit_eq_mod]
  have eIf : WXExec cap (.ifr rBIT (WMX.wr sCODE true) (WMX.wr sCODE false)) τ1
      (τ1.sets sCODE (writeTapeBit (τ1.st sCODE) (τ1.sh sCODE) (a.testBit k))) 2 := by
    by_cases hb : τ1.val rBIT = 0
    · have : a.testBit k = false := by rw [← hbit]; simp [hb]
      rw [this]; exact WXExec.ifrF hb (WXExec.wr cap sCODE false τ1)
    · have : a.testBit k = true := by rw [← hbit]; simp [hb]
      rw [this]; exact WXExec.ifrT hb (WXExec.wr cap sCODE true τ1)
  obtain ⟨τ2, eIf, h2⟩ := exEq cap eIf
  obtain ⟨τ3, e3, h3⟩ := exEq cap (clr_spec cap rBIT τ2 (by rw [h2, h1]; simp; omega))
  obtain ⟨τ4, e4, h4⟩ := exEq cap (WXExec.bwd cap sCODE τ3)
  have e5 := WXExec.wm (wmove_spec (cap := cap) rQ rAI (by decide) (a / 2 ^ k / 2) τ4
    (by rw [h4, h3, h2, h1]; simp [a0]) (by rw [h4, h3, h2, h1]; simp [a0]; omega)
    (by rw [h4, h3, h2, h1]; simp [a0]; omega))
  refine (WXExec.seq e1 (WXExec.seq eIf (WXExec.seq e3 (WXExec.seq e4 e5)))).cast cap ?_ ?_
  · have hd : a / 2 ^ k / 2 = a / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]
    rw [h4, h3, h2, h1]
    apply WState.eq
    · funext j
      by_cases j1 : j = sCODE
      · subst j1; simp [τ0, wSt]; omega
      · simp [τ0, wSt, Function.update_apply, j1]
    · funext j
      by_cases j1 : j = sCODE
      · subst j1; simp [τ0, wSt, wlist]
      · simp [τ0, wSt, Function.update_apply, j1]
    · funext r
      simp only [WState.setv_val, WState.sets_val, WState.seth_val]
      by_cases r1 : r = rAI
      · subst r1; simp [τ0, wSt, hd]
      · by_cases r3 : r = rQ
        · subst r3; simp [τ0, wSt, hQ]
        · by_cases r4 : r = rBIT
          · subst r4; simp [τ0, wSt, hB]
          · simp [τ0, wSt, Function.update_apply, r1, r3, r4]
    · rfl
  · rw [h2, h1]; simp only [WState.setv_val, WState.sets_val, Function.update_self, Function.update_apply]
    simp [a0]
    generalize a / 2 ^ k = v at hv ⊢
    omega

set_option maxHeartbeats 400000 in
/-- **Decoding `code(M)` from the record index** (proof of `lem:multitape-refuter`; proof of `cor:framed-refuter`): from `A = machineIndex M`
the code stream becomes exactly `code(M)`, head `0`; `A` is cleared; every other register and stream is
unchanged. The cost depends only on `M`. -/
theorem decode_spec (σ : St) (l : List Bool) (hl : 1 ≤ l.length) (hA : σ.val rAI = l.foldl idxStep 1)
    (hTC : σ.val rTC = 0) (hQ : σ.val rQ = 0) (hB : σ.val rBIT = 0) (hP : σ.val rP = 0) (hTA : σ.val rTA = 0)
    (hTB : σ.val rTB = 0) (hTG : σ.val rTG = 0) (hC : σ.st sCODE = []) (hCh : σ.sh sCODE = 0)
    (hcap : 2 * l.foldl idxStep 1 + 4 ≤ cap) :
    ∃ c, WXExec cap decode σ ((σ.setv rAI 0).sets sCODE l) c ∧
      c ≤ 30 * (l.length + 2) * (l.foldl idxStep 1 + 2) := by
  set a := l.foldl idxStep 1 with ha
  set L := l.length with hL
  obtain ⟨b1, b2⟩ := foldl_bounds l 1 (by omega)
  simp only [one_mul, ← ha, ← hL] at b1 b2
  have hlt : L < a := lt_of_lt_of_le (Nat.lt_two_pow_self) b1
  -- 1. copy A
  have e1 := addR_spec cap (A := rAI) (B := rTC) (T := rTA) (by decide) (by decide) (by decide) σ hTA
    (by rw [hTC, hA]; omega)
  rw [hTC, hA, Nat.zero_add] at e1
  -- 2. count the digits
  have e2 := decCount_spec cap σ l hQ hB hP hcap
  rw [← ha, ← hL] at e2
  -- 3–5. place the head at `L-1`
  have e3 := WXExec.dec cap rP ((σ.setv rTC 0).setv rP (L + 1)) (by simp; omega)
  simp only [WState.setv_val, Function.update_self, Nat.add_sub_cancel] at e3
  have hσ3 : ((σ.setv rTC 0).setv rP (L + 1)).setv rP L = (σ.setv rTC 0).setv rP L := by
    apply WState.eq <;> try rfl
    funext r; simp only [WState.setv_val, Function.update_apply]; split_ifs <;> rfl
  rw [hσ3] at e3
  have e4 := fwdK_spec cap (S := sCODE) (K := rP) (K2 := rTB) (by decide) ((σ.setv rTC 0).setv rP L)
    (by simp [hTB]) (by simp; omega)
  simp only [WState.setv_sh, WState.setv_val, Function.update_self, hCh, Nat.zero_add] at e4
  have e5 := WXExec.bwd cap sCODE (((σ.setv rTC 0).setv rP L).seth sCODE L)
  simp only [WState.seth_sh, Function.update_self] at e5
  -- 6. write the code
  set σ5 := (((σ.setv rTC 0).setv rP L).seth sCODE L).seth sCODE (L - 1) with hσ5
  have h50 : wSt σ5 a L 0 = σ5 := by
    apply WState.eq
    · funext j; by_cases j1 : j = sCODE
      · subst j1; simp [wSt, σ5]
      · simp [wSt, σ5, Function.update_apply, j1]
    · funext j; by_cases j1 : j = sCODE
      · subst j1; simp [wSt, σ5, wlist, hC]
      · simp [wSt, σ5, Function.update_apply, j1]
    · funext r; by_cases r1 : r = rAI
      · subst r1; simp [wSt, σ5, hA]
      · simp [wSt, σ5, Function.update_apply, r1]
    · rfl
  have e6 := Runs.repE (cap := cap) (K := rP) (K2 := rTG) (body := decBody) (by decide) (9 * a + 20) L
    (wSt σ5 a L) (by omega) (fun k => by simp [wSt]) (fun k => by simp [wSt])
    (fun k _ v1 v2 => decBody_step cap σ5 a L k v1 v2 (by simp [σ5, hQ]) (by simp [σ5, hB]) hcap)
    (by simp [wSt, σ5]) (by simp [wSt, σ5, hTG])
  rw [h50] at e6
  have hfin : wSt σ5 a L L = ((σ5.setv rAI 1).sets sCODE l).seth sCODE 0 := by
    have hd : a / 2 ^ L = 1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · calc a < (1 + 1) * 2 ^ L := b2
          _ = (1 + 1) * 2 ^ L := rfl
    unfold wSt
    rw [hd, hL, wlist_code l hl, ← hL, show L - 1 - L = 0 by omega]
  rw [hfin] at e6
  -- 7. clear
  obtain ⟨τ7, e7, h7⟩ := exEq cap (clr_spec cap rAI (((σ5.setv rAI 1).sets sCODE l).seth sCODE 0) (by simp; omega))
  obtain ⟨τ8, e8, h8⟩ := exEq cap (clr_spec cap rP τ7 (by rw [h7]; simp [σ5]; omega))
  refine ⟨_, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6
    (WXExec.seq e7 e8))))))).cast cap ?_ le_rfl, ?_⟩
  · rw [h8, h7]
    apply WState.eq
    · funext j; by_cases j1 : j = sCODE
      · subst j1; simp [σ5, hCh]
      · simp [σ5, Function.update_apply, j1]
    · funext j; by_cases j1 : j = sCODE
      · subst j1; simp [σ5]
      · simp [σ5, Function.update_apply, j1]
    · funext r
      simp only [WState.setv_val, WState.sets_val, WState.seth_val]
      by_cases r1 : r = rAI
      · subst r1; simp
      · by_cases r2 : r = rP
        · subst r2; simp [hP]
        · by_cases r3 : r = rTC
          · subst r3; simp [Function.update_apply, σ5, hTC]
          · simp [σ5, Function.update_apply, r1, r2, r3]
    · rfl
  · rw [h7]
    simp only [WState.setv_val, WState.sets_val, WState.seth_val, Function.update_self, Function.update_apply]
    simp [σ5]
    nlinarith

end NearCubicGates.Adapters.Refuter.Mach
