import Proof.Wire_3_5.FinalPassHashCell

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Hash4
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.SignedSortKey
open NearCubicWires.WireExponent3_5.GF2 NearCubicWires.WireExponent3_5.FinalPass.Tm

variable (cap : ℕ)

theorem writeTapeBit_end (l : List Bool) (b : Bool) : writeTapeBit l l.length b = l ++ [b] := by
  induction l with
  | nil => rfl
  | cons a l ih => simpa [writeTapeBit] using ih

/-- Write bit `b` at the end of the output and move on, counting in `OC`. -/
def emit (b : Bool) : HProg := .seq (.wr sO b) (WM.fwdC sO rOC)

theorem emit_spec (b : Bool) (σ : HState) (hO : σ.sh sO = (σ.st sO).length) (hc : σ.val rOC < cap) :
    WExec cap (emit b) σ (((σ.sets sO ((σ.st sO) ++ [b])).seth sO (σ.sh sO + 1)).setv rOC (σ.val rOC + 1)) 7 := by
  have h1 := WExec.wr (cap := cap) sO b σ
  rw [hO, writeTapeBit_end] at h1
  have h2 := wfwdC_spec cap sO rOC (σ.sets sO ((σ.st sO) ++ [b])) (by simpa using hc)
  exact WExec.mono (WExec.seq h1 (by simpa [hO] using h2)) (by omega)

/-! ## Binary increment of the coordinate label -/

def incOut (a _ c : Bool) : Bool := xor a c
def incNxt (a _ c : Bool) : Bool := a && c

theorem mapS_inc_false : ∀ (as bs : List Bool), as.length = bs.length → mapS incOut incNxt as bs false = (as, false)
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [mapS, incOut, incNxt, Bool.xor_false, Bool.and_false, mapS_inc_false as bs (by simpa using h)]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem mapS_inc : ∀ (ℓ i : ℕ) (bs : List Bool), bs.length = ℓ →
    (mapS incOut incNxt (binary ℓ i) bs true).1 = binary ℓ (i + 1)
  | 0, _, bs, _ => by simp [binary, mapS]
  | ℓ + 1, i, b :: bs, h => by
    have hb : bs.length = ℓ := by simpa using h
    have e1 : binary (ℓ + 1) i = (i % 2 == 1) :: binary ℓ (i / 2) := rfl
    have e2 : binary (ℓ + 1) (i + 1) = ((i + 1) % 2 == 1) :: binary ℓ ((i + 1) / 2) := rfl
    rw [e1, e2]
    simp only [mapS, incOut, incNxt]
    rcases Nat.mod_two_eq_zero_or_one i with h0 | h1
    · have hq : (i + 1) / 2 = i / 2 := by omega
      have hr : (i + 1) % 2 = 1 := by omega
      simp only [h0, hr, hq]
      rw [show ((0 == 1) && true) = false by rfl, mapS_inc_false _ _ (by simp [hb])]
      rfl
    · have hq : (i + 1) / 2 = i / 2 + 1 := by omega
      have hr : (i + 1) % 2 = 0 := by omega
      simp only [h1, hr, hq]
      rw [show ((1 == 1) && true) = true by rfl, mapS_inc ℓ (i / 2) bs hb]
      rfl
  | ℓ + 1, _, [], h => by simp at h

/-! ## The level test on the value bits -/

/-- The first `j` bits of a word are all zero. -/
def prefixZero : ℕ → List Bool → Bool
  | 0, _ => true
  | _ + 1, [] => true
  | j + 1, b :: bs => !b && prefixZero j bs

theorem prefixZero_binary (j ℓ v : ℕ) :
    prefixZero j (binary ℓ v) = decide (∀ b < ℓ, b < j → v.testBit b = false) := by
  induction j generalizing ℓ v with
  | zero => simp [prefixZero]
  | succ j ih =>
    cases ℓ with
    | zero => simp [prefixZero, binary]
    | succ ℓ =>
      have e1 : binary (ℓ + 1) v = (v % 2 == 1) :: binary ℓ (v / 2) := rfl
      rw [e1]
      simp only [prefixZero, ih]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq,
        decide_eq_true_eq]
      constructor
      · rintro ⟨h0, hrest⟩ b hb hbj
        cases b with
        | zero => rw [Nat.testBit_zero]; simp; omega
        | succ b => rw [Nat.testBit_succ]; exact hrest b (by omega) (by omega)
      · intro h
        refine ⟨?_, fun b hb hbj => ?_⟩
        · have := h 0 (by omega) (by omega)
          rw [Nat.testBit_zero] at this; simp at this; omega
        · have := h (b + 1) (by omega) (by omega)
          rwa [Nat.testBit_succ] at this

/-- Close an equality of stage-4 states field by field (literal stream and register indices). -/
syntax "hs_eq" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| hs_eq) => `(tactic| hs_eq [])
  | `(tactic| hs_eq [$ts,*]) => `(tactic| (refine WState.eq ?_ ?_ ?_ ?_ <;>
      first
        | (funext x; fin_cases x <;> (try simp [$ts,*]) <;> (try omega))
        | (try simp [$ts,*])))

/-- `simp`, then `omega` on whatever remains. -/
syntax "simpo" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| simpo [$ts,*]) => `(tactic| (simp [$ts,*] <;> try omega))

/-! ## Copying a unary field from `WIN` to `O` -/

/-- One unit: forward on `WIN`, write `1`, count into `r`. -/
def copyUnit (r : Fin 16) : HProg := .seq (WM.fwdC sWIN rWC) (.seq (emit true) (.inc r))

/-- Copy `1^n 0` from `WIN` to `O`, counting `n` into `r`. -/
def copyUR (r : Fin 16) : HProg := .seq (.whs sWIN (copyUnit r)) (.seq (WM.fwdC sWIN rWC) (emit false))

/-- The state after copying `n` units. -/
def copyState (r : Fin 16) (n : ℕ) (σ : HState) : HState :=
  (((((σ.sets sO (σ.st sO ++ List.replicate n true)).seth sO (σ.sh sO + n)).setv rOC (σ.val rOC + n)).seth sWIN
    (σ.sh sWIN + n)).setv rWC (σ.val rWC + n)).setv r (σ.val r + n)

theorem copyLoop_spec (r : Fin 16) (hr1 : r ≠ rOC) (hr2 : r ≠ rWC) (rest : List Bool) :
    ∀ (n : ℕ) (σ : HState), (σ.st sWIN).drop (σ.sh sWIN) = List.replicate n true ++ false :: rest →
      σ.sh sO = (σ.st sO).length → σ.val rOC + n ≤ cap → σ.val rWC + n ≤ cap → σ.val r + n ≤ cap →
      WExec cap (.whs sWIN (copyUnit r)) σ (copyState r n σ) (n * 19 + 1)
  | 0, σ, hd, _, _, _, _ => by
    have e : copyState r 0 σ = σ := by
      unfold copyState; simp only [List.replicate_zero, List.append_nil, Nat.add_zero]
      rw [wsets_same, wseth_same, wsetv_same, wseth_same, wsetv_same, wsetv_same]
    rw [e]
    refine WExec.whsF ?_
    unfold wbit
    have := readDrop (σ.st sWIN) (σ.sh sWIN) 0
    simp only [Nat.add_zero] at this
    rw [this, hd]; rfl
  | n + 1, σ, hd, hO, hOC, hWC, hR => by
    have hread : wbit σ sWIN = true := by
      unfold wbit
      have := readDrop (σ.st sWIN) (σ.sh sWIN) 0
      simp only [Nat.add_zero] at this
      rw [this, hd]; rfl
    have s1 := wfwdC_spec cap sWIN rWC σ (by omega)
    obtain ⟨σ1, hσ1⟩ : ∃ τ : HState, τ = (σ.seth sWIN (σ.sh sWIN + 1)).setv rWC (σ.val rWC + 1) := ⟨_, rfl⟩
    rw [← hσ1] at s1
    have s2 := emit_spec cap true σ1 (by rw [hσ1]; simpa using hO) (by rw [hσ1]; simp; omega)
    obtain ⟨σ2, hσ2⟩ : ∃ τ : HState,
        τ = ((σ1.sets sO ((σ1.st sO) ++ [true])).seth sO (σ1.sh sO + 1)).setv rOC (σ1.val rOC + 1) := ⟨_, rfl⟩
    rw [← hσ2] at s2
    have s3 := WExec.inc (cap := cap) r σ2 (by rw [hσ2, hσ1]; simp [Function.update_of_ne hr1, Function.update_of_ne hr2]; omega)
    have hd' : ((σ2.setv r (σ2.val r + 1)).st sWIN).drop ((σ2.setv r (σ2.val r + 1)).sh sWIN) =
        List.replicate n true ++ false :: rest := by
      rw [hσ2, hσ1]; simp
      exact dropSucc (a := true) (by rw [hd]; simp [List.replicate_succ])
    have ih := copyLoop_spec r hr1 hr2 rest n (σ2.setv r (σ2.val r + 1)) hd'
      (by rw [hσ2, hσ1]; simp [hO]) (by rw [hσ2, hσ1]; simp [Function.update_of_ne (Ne.symm hr1)]; omega)
      (by rw [hσ2, hσ1]; simp [Function.update_of_ne (Ne.symm hr2)]; omega)
      (by rw [hσ2, hσ1]; simp [Function.update_of_ne hr1, Function.update_of_ne hr2]; omega)
    refine WExec.cast cap (WExec.whsT hread (WExec.seq s1 (WExec.seq s2 s3)) ih) ?_ (by omega)
    subst hσ2 hσ1
    unfold copyState
    refine WState.eq ?_ ?_ ?_ rfl
    · funext j; by_cases hj : j = sWIN
      · subst hj; simp; omega
      · by_cases hj2 : j = sO
        · subst hj2; simp [hO]; omega
        · simp [hj, hj2]
    · funext j; by_cases hj : j = sO
      · subst hj; simp [List.replicate_succ, List.append_assoc]
      · simp [hj]
    · funext q
      by_cases hq : q = r
      · subst hq; simp [Function.update_of_ne hr1, Function.update_of_ne hr2]; omega
      · by_cases hq1 : q = rOC
        · subst hq1; simp [Function.update_of_ne (Ne.symm hr1)]; omega
        · by_cases hq2 : q = rWC
          · subst hq2; simp [Function.update_of_ne (Ne.symm hr2)]; omega
          · simp [hq, hq1, hq2]

/-- The state after copying the field `1^n 0`. -/
def copyState' (r : Fin 16) (n : ℕ) (σ : HState) : HState :=
  (((((σ.sets sO (σ.st sO ++ List.replicate n true ++ [false])).seth sO (σ.sh sO + n + 1)).setv rOC
    (σ.val rOC + n + 1)).seth sWIN (σ.sh sWIN + n + 1)).setv rWC (σ.val rWC + n + 1)).setv r (σ.val r + n)

theorem copyUR_spec (r : Fin 16) (hr1 : r ≠ rOC) (hr2 : r ≠ rWC) (rest : List Bool) (n : ℕ) (σ : HState)
    (hd : (σ.st sWIN).drop (σ.sh sWIN) = List.replicate n true ++ false :: rest) (hO : σ.sh sO = (σ.st sO).length)
    (hOC : σ.val rOC + n + 1 ≤ cap) (hWC : σ.val rWC + n + 1 ≤ cap) (hR : σ.val r + n ≤ cap) :
    WExec cap (copyUR r) σ (copyState' r n σ) (n * 19 + 15) := by
  have h1 := copyLoop_spec cap r hr1 hr2 rest n σ hd hO (by omega) (by omega) hR
  have hd1 : ((copyState r n σ).st sWIN).drop ((copyState r n σ).sh sWIN) = false :: rest := by
    unfold copyState; simp
    have := dropAppend hd; simpa using this
  have h2 := wfwdC_spec cap sWIN rWC (copyState r n σ) (by unfold copyState; simp [Function.update_of_ne (Ne.symm hr2)]; omega)
  obtain ⟨ρ, hρ⟩ : ∃ τ : HState, τ = ((copyState r n σ).seth sWIN ((copyState r n σ).sh sWIN + 1)).setv rWC
      ((copyState r n σ).val rWC + 1) := ⟨_, rfl⟩
  rw [← hρ] at h2
  have hO2 : ρ.sh sO = (ρ.st sO).length := by rw [hρ]; unfold copyState; simp [hO]
  have h3 := emit_spec cap false ρ hO2 (by rw [hρ]; unfold copyState; simp [Function.update_of_ne (Ne.symm hr1)]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
  subst hρ
  unfold copyState copyState'
  refine WState.eq ?_ ?_ ?_ rfl
  · funext j; by_cases hj : j = sWIN
    · subst hj; simp
    · by_cases hj2 : j = sO
      · subst hj2; simp
      · simp [hj, hj2]
  · funext j; by_cases hj : j = sO
    · subst hj; simp
    · simp [hj]
  · funext q
    by_cases hq : q = r
    · subst hq; simp [Function.update_of_ne hr1, Function.update_of_ne hr2]
    · by_cases hq1 : q = rOC
      · subst hq1; simp [Function.update_of_ne (Ne.symm hr1)]
      · by_cases hq2 : q = rWC
        · subst hq2; simp [Function.update_of_ne (Ne.symm hr2)]
        · simp [hq, hq1, hq2]

/-! ## Copying a register -/

section Dup
variable {ns nr : ℕ}

/-- `b += a; t += a; a := 0`. -/
def wdup (a b t : Fin nr) : WM ns nr := .whr a (.seq (.dec a) (.seq (.inc b) (.inc t)))

theorem wdup_spec (a b t : Fin nr) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val a = n → n ≤ cap → σ.val b + n ≤ cap → σ.val t + n ≤ cap →
      WExec cap (wdup a b t) σ (((σ.setv a 0).setv b (σ.val b + n)).setv t (σ.val t + n)) (11 * n + 1)
  | 0, σ, h0, _, _, _ => by
    have e : ((σ.setv a 0).setv b (σ.val b + 0)).setv t (σ.val t + 0) = σ := by
      rw [Nat.add_zero, Nat.add_zero]
      refine WState.eq rfl rfl ?_ rfl
      funext q
      by_cases hq1 : q = t
      · subst hq1; simp
      · by_cases hq2 : q = b
        · subst hq2; simp [hq1]
        · by_cases hq3 : q = a
          · subst hq3; simp [hq1, hq2, h0]
          · simp [hq1, hq2, hq3]
    rw [e]
    exact WExec.whrF h0
  | n + 1, σ, hn, hc, hb, ht => by
    have h1 := WExec.dec (cap := cap) a σ (by omega)
    obtain ⟨σ1, hσ1⟩ : ∃ τ : WState ns nr, τ = σ.setv a (σ.val a - 1) := ⟨_, rfl⟩
    rw [← hσ1] at h1
    have h2 := WExec.inc (cap := cap) b σ1 (by rw [hσ1]; simp [Function.update_of_ne (Ne.symm hab)]; omega)
    obtain ⟨σ2, hσ2⟩ : ∃ τ : WState ns nr, τ = σ1.setv b (σ1.val b + 1) := ⟨_, rfl⟩
    rw [← hσ2] at h2
    have h3 := WExec.inc (cap := cap) t σ2 (by
      rw [hσ2, hσ1]; simp [Function.update_of_ne (Ne.symm hbt), Function.update_of_ne (Ne.symm hat)]; omega)
    obtain ⟨σ3, hσ3⟩ : ∃ τ : WState ns nr, τ = σ2.setv t (σ2.val t + 1) := ⟨_, rfl⟩
    rw [← hσ3] at h3
    have hv3a : σ3.val a = n := by
      rw [hσ3, hσ2, hσ1]; simp [Function.update_of_ne hat, Function.update_of_ne hab]; omega
    have hv3b : σ3.val b = σ.val b + 1 := by
      rw [hσ3, hσ2, hσ1]; simp [Function.update_of_ne hbt, Function.update_of_ne (Ne.symm hab)]
    have hv3t : σ3.val t = σ.val t + 1 := by
      rw [hσ3, hσ2, hσ1]; simp [Function.update_of_ne (Ne.symm hbt), Function.update_of_ne (Ne.symm hat)]
    have ih := wdup_spec a b t hab hat hbt n σ3 hv3a (by omega) (by omega) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 (WExec.seq h2 h3)) ih) ?_ (by omega)
    have hsh : σ3.sh = σ.sh := by rw [hσ3, hσ2, hσ1]; rfl
    have hst : σ3.st = σ.st := by rw [hσ3, hσ2, hσ1]; rfl
    have hce : σ3.cell = σ.cell := by rw [hσ3, hσ2, hσ1]; rfl
    have hoth : ∀ q, q ≠ a → q ≠ b → q ≠ t → σ3.val q = σ.val q := by
      intro q h1 h2 h3; rw [hσ3, hσ2, hσ1]; simp [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
    refine WState.eq (by simp [hsh]) (by simp [hst]) ?_ (by simp [hce])
    funext q
    by_cases hq1 : q = t
    · subst hq1; simp only [WState.setv_val, Function.update_self]; omega
    · by_cases hq2 : q = b
      · subst hq2; simp only [WState.setv_val, Function.update_of_ne hq1, Function.update_self]; omega
      · by_cases hq3 : q = a
        · subst hq3; simp only [WState.setv_val, Function.update_of_ne hq1, Function.update_of_ne hq2,
            Function.update_self]
        · simp only [WState.setv_val, Function.update_of_ne hq1, Function.update_of_ne hq2, Function.update_of_ne hq3]
          exact hoth q hq3 hq2 hq1

/-- `b := a` from `b = 0`, keeping `a`, through the temporary `t = 0`. -/
def wcopyR (a b t : Fin nr) : WM ns nr := .seq (wdup a b t) (WM.move t a)

theorem wcopyR_spec (a b t : Fin nr) (hab : a ≠ b) (hat : a ≠ t) (hbt : b ≠ t) (σ : WState ns nr)
    (hb : σ.val b = 0) (ht : σ.val t = 0) (ha : σ.val a ≤ cap) :
    WExec cap (wcopyR a b t) σ (σ.setv b (σ.val a)) (18 * σ.val a + 3) := by
  have h1 := wdup_spec cap a b t hab hat hbt (σ.val a) σ rfl ha (by omega) (by omega)
  have h2 := wmove_spec cap t a (Ne.symm hat) (σ.val a) (((σ.setv a 0).setv b (σ.val b + σ.val a)).setv t
    (σ.val t + σ.val a)) (by simp [ht]) (by simp [ht]; omega) (by simp [Function.update_of_ne hat, Function.update_of_ne hab, ht]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext q
  by_cases hq1 : q = a
  · subst hq1; simp only [WState.setv_val, Function.update_self, Function.update_of_ne hat, Function.update_of_ne hab]
    simp [ht]
  · by_cases hq2 : q = t
    · subst hq2; simp only [WState.setv_val, Function.update_of_ne hq1, Function.update_self,
        Function.update_of_ne (Ne.symm hbt)]; exact ht.symm
    · by_cases hq3 : q = b
      · subst hq3; simp only [WState.setv_val, Function.update_of_ne hq1, Function.update_of_ne hq2, Function.update_self]
        simp [hb]
      · simp only [WState.setv_val, Function.update_of_ne hq1, Function.update_of_ne hq2, Function.update_of_ne hq3]

end Dup

/-! ## The level test -/

/-- One value bit of the level test: to the bit, flag it if set, to the next marker, count down. -/
def ptStep : HProg :=
  .seq (WM.fwdC sACC rK) (.seq (.ifs sACC (WM.setF rBAD) .skip) (.seq (WM.fwdC sACC rK) (.dec rTC)))

/-- Test the first `TC` value bits (stopping at the word's end). -/
def ptLoop : HProg := .whr rTC (.ifs sACC ptStep (WM.clear rTC))

/-- The state after testing `k` bits with flag `b`. -/
def ptState (k : ℕ) (b : Bool) (σ : HState) : HState :=
  (((σ.seth sACC (σ.sh sACC + 2 * k)).setv rK (σ.val rK + 2 * k)).setv rTC 0).setv rBAD b.toNat

theorem ptLoop_spec (pre rest : List Bool) (hcap : 1 ≤ cap) :
    ∀ (w : List Bool) (j : ℕ) (b : Bool) (σ : HState), σ.st sACC = pre ++ frameP w ++ false :: rest →
      σ.sh sACC = pre.length → σ.val rTC = j → j ≤ cap → σ.val rBAD = b.toNat →
      σ.val rK + 2 * min j w.length ≤ cap →
      WExec cap ptLoop σ (ptState (min j w.length) (b || !prefixZero j w) σ) (w.length * 25 + 3 * j + 8)
  | w, 0, b, σ, _, _, hj, _, hB, _ => by
    have e : ptState (min 0 w.length) (b || !prefixZero 0 w) σ = σ := by
      unfold ptState; simp only [Nat.zero_min, Nat.mul_zero, Nat.add_zero, prefixZero, Bool.not_true, Bool.or_false]
      rw [wseth_same, wsetv_same, ← hj, wsetv_same, ← hB, wsetv_same]
    rw [e]
    exact WExec.mono (WExec.whrF hj) (by omega)
  | [], j + 1, b, σ, hA, hhA, hj, hjc, hB, _ => by
    have hread : wbit σ sACC = false := by
      unfold wbit; rw [hA, hhA]; simpa using readTapeBit_mid pre rest false
    have h1 := wclear_spec cap rTC (j + 1) σ hj (by omega)
    have h2 := WExec.whrF (cap := cap) (r := rTC) (P := .ifs sACC ptStep (WM.clear rTC)) (σ := σ.setv rTC 0) (by simp)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.ifsF hread h1) h2) ?_ (by omega)
    unfold ptState
    simp only [List.length_nil, Nat.min_zero, Nat.mul_zero, Nat.add_zero, prefixZero, Bool.not_true, Bool.or_false]
    hs_eq [hB]
  | a :: w, j + 1, b, σ, hA, hhA, hj, hjc, hB, hK => by
    simp only [List.length_cons] at hK
    have hread : wbit σ sACC = true := by
      unfold wbit; rw [hA, hhA]; simpa using readTapeBit_mid pre (a :: (frameP w ++ false :: rest)) true
    have s1 := wfwdC_spec cap sACC rK σ (by omega)
    obtain ⟨σ1, hσ1⟩ : ∃ τ : HState, τ = (σ.seth sACC (σ.sh sACC + 1)).setv rK (σ.val rK + 1) := ⟨_, rfl⟩
    rw [← hσ1] at s1
    have hread1 : wbit σ1 sACC = a := by
      unfold wbit; rw [hσ1]; simp [hA, hhA]
      simpa using readTapeBit_mid (pre ++ [true]) (frameP w ++ false :: rest) a
    have s2 : WExec cap (.ifs sACC (WM.setF rBAD) .skip) σ1 (σ1.setv rBAD (b || a).toNat) 5 := by
      cases a
      · have e : σ1.setv rBAD (b || false).toNat = σ1 := by
          rw [Bool.or_false, ← hB]; rw [show σ.val rBAD = σ1.val rBAD by rw [hσ1]; simp]; exact wsetv_same σ1 rBAD
        rw [e]; exact WExec.mono (WExec.ifsF hread1 (WExec.skip σ1)) (by omega)
      · have hB1 : σ1.val rBAD ≤ 1 := by rw [hσ1]; simp [hB]; cases b <;> simp
        have := wsetF_spec cap rBAD σ1 hB1 hcap
        rw [Bool.or_true]
        exact WExec.mono (WExec.ifsT hread1 this) (by omega)
    obtain ⟨σ2, hσ2⟩ : ∃ τ : HState, τ = σ1.setv rBAD (b || a).toNat := ⟨_, rfl⟩
    rw [← hσ2] at s2
    have s3 := wfwdC_spec cap sACC rK σ2 (by rw [hσ2, hσ1]; simp; omega)
    obtain ⟨σ3, hσ3⟩ : ∃ τ : HState, τ = (σ2.seth sACC (σ2.sh sACC + 1)).setv rK (σ2.val rK + 1) := ⟨_, rfl⟩
    rw [← hσ3] at s3
    have s4 := WExec.dec (cap := cap) rTC σ3 (by rw [hσ3, hσ2, hσ1]; simp [hj]; omega)
    obtain ⟨σ4, hσ4⟩ : ∃ τ : HState, τ = σ3.setv rTC (σ3.val rTC - 1) := ⟨_, rfl⟩
    rw [← hσ4] at s4
    have h4A : σ4.st sACC = (pre ++ [true, a]) ++ frameP w ++ false :: rest := by
      rw [hσ4, hσ3, hσ2, hσ1]; simp [hA]
    have h4hA : σ4.sh sACC = (pre ++ [true, a]).length := by
      rw [hσ4, hσ3, hσ2, hσ1]; simp [hhA]
    have h4TC : σ4.val rTC = j := by rw [hσ4, hσ3, hσ2, hσ1]; simp [hj]
    have h4B : σ4.val rBAD = (b || a).toNat := by rw [hσ4, hσ3, hσ2]; simp
    have h4K : σ4.val rK = σ.val rK + 2 := by rw [hσ4, hσ3, hσ2, hσ1]; simp
    have ih := ptLoop_spec (pre ++ [true, a]) rest hcap w j (b || a) σ4 h4A h4hA h4TC (by omega) h4B
      (by rw [h4K]; have := Nat.min_le_right j w.length; have := Nat.min_le_left j w.length; omega)
    have body := WExec.ifsT (P := ptStep) (Q := WM.clear rTC) hread (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4)))
    refine WExec.cast cap (WExec.whrT (by omega) body ih) ?_ (by simp only [List.length_cons]; omega)
    unfold ptState
    have hmin : min (j + 1) (w.length + 1) = min j w.length + 1 := by omega
    simp only [List.length_cons]
    rw [hmin]
    have hbool : ((b || a) || !prefixZero j w) = (b || !prefixZero (j + 1) (a :: w)) := by
      simp only [prefixZero]; cases a <;> cases b <;> simp
    rw [hbool]
    refine WState.eq ?_ ?_ ?_ ?_
    · funext q; by_cases hq : q = sACC
      · subst hq; simp [h4hA, hhA]; omega
      · simp [hq, hσ4, hσ3, hσ2, hσ1]
    · rw [hσ4, hσ3, hσ2, hσ1]; rfl
    · funext q
      by_cases hq1 : q = rBAD
      · subst hq1; simp
      · by_cases hq2 : q = rTC
        · subst hq2; simp [hq1]
        · by_cases hq3 : q = rK
          · subst hq3; simp [hq1, hq2, h4K]; omega
          · simp [hq1, hq2, hq3, hσ4, hσ3, hσ2, hσ1]
    · rw [hσ4, hσ3, hσ2, hσ1]; rfl

/-- **The level test**: `BAD := [the first j value bits are not all zero]`. -/
def prefixTest : HProg := .seq (wcopyR rJC rTC rIC) (.seq ptLoop (WM.rewind sACC rK))

theorem prefixTest_spec (ℓ v j : ℕ) (σ : HState) (hcap : 1 ≤ cap) (hA : σ.st sACC = frame (binary ℓ v))
    (hhA : σ.sh sACC = 0) (hJ : σ.val rJC = j) (hj : j ≤ cap) (hTC : σ.val rTC = 0) (hIC : σ.val rIC = 0)
    (hB : σ.val rBAD = 0) (hK : σ.val rK = 0) (hl : 2 * ℓ ≤ cap) :
    WExec cap prefixTest σ (σ.setv rBAD (!prefixZero j (binary ℓ v)).toNat) (18 * j + ℓ * 25 + 3 * j + 8 + 10 * ℓ + 6) := by
  have h1 := wcopyR_spec cap rJC rTC rIC (by decide) (by decide) (by decide) σ hTC hIC (by omega)
  have h2 := ptLoop_spec cap [] [] hcap (binary ℓ v) j false (σ.setv rTC (σ.val rJC))
    (by simp [hA, frame_eq_frameP]) (by simp [hhA]) (by simp [hJ]) hj (by simp [hB])
    (by simp [hK]; have := Nat.min_le_right j ℓ; simp at this ⊢; omega)
  have h3 := wrewind_spec cap sACC rK (2 * min j ℓ)
    (ptState (min j (binary ℓ v).length) (false || !prefixZero j (binary ℓ v)) (σ.setv rTC (σ.val rJC)))
    (by unfold ptState; simp [hK]) (by unfold ptState; simp [hK]; have := Nat.min_le_right j ℓ; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by simp only [binary_length, hJ]; have := Nat.min_le_right j ℓ; omega)
  unfold ptState
  hs_eq [hhA, hTC, hK]

def incX : HProg := .seq (setFlag rF true) (.seq (mapPass incOut incNxt sX sP rF rR) (WM.clear rF))

theorem incX_spec (ℓ p i : ℕ) (σ : HState) (hcap : 1 ≤ cap) (hl : 2 * ℓ ≤ cap) (hX : σ.st sX = frame (binary ℓ i))
    (hhX : σ.sh sX = 0) (hP : σ.st sP = frame (binary ℓ p)) (hhP : σ.sh sP = 0) (hF : σ.val rF = 0)
    (hR : σ.val rR = 0) :
    WExec cap incX σ (σ.sets sX (frame (binary ℓ (i + 1)))) (ℓ * 41 + 15) := by
  have h1 := setFlag_spec cap rF true false σ (by simp [hF]) hcap
  have h2 := mapPass_spec cap incOut incNxt sX sP rF rR (by decide) (by decide) hcap (binary ℓ i) (binary ℓ p) [] [false]
    true (σ.setv rF (true).toNat) (by simp) (by simp [hX, frame_eq_frameP]) (by simp [hhX])
    (by simp [hP, frame_eq_frameP]) (by simp [hhP]) (by simp) (by simp [hR]) (by simp; omega)
  have hinc := mapS_inc ℓ i (binary ℓ p) (by simp)
  obtain ⟨c, hc⟩ : ∃ c, (mapS incOut incNxt (binary ℓ i) (binary ℓ p) true).2 = c := ⟨_, rfl⟩
  rw [hc] at h2
  have h3 := wclear_spec cap rF c.toNat (((σ.setv rF (true).toNat).sets sX
    (frameP (mapS incOut incNxt (binary ℓ i) (binary ℓ p) true).1 ++ false :: [])).setv rF c.toNat) (by simp)
    (by have : c.toNat ≤ 1 := by cases c <;> decide
        simp; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by
    have : c.toNat ≤ 1 := by cases c <;> decide
    simp only [binary_length]; omega)
  rw [hinc]
  hs_eq [hF, frame_eq_frameP]

/-! ## One coordinate of a row -/

/-- The row bit: the hash value's first `j` bits vanish (coordinates `i ≥ M` are in every level). -/
def rowBit (p ℓ M j i : ℕ) (all : List ℕ) : Bool :=
  if i < M then decide (∀ b < ℓ, b < j → (all.foldl (hornerStep p ℓ i) 0).testBit b = false) else true

/-- One coordinate: the row bit on `O`, then the next label. -/
def rowStep : HProg :=
  .seq (.ifr rT2 (.seq hornerW (.seq prefixTest (.ifr rBAD (.seq (emit false) (WM.clear rBAD)) (emit true))))
    (emit true)) (.seq (.dec rT1) (.seq (.dec rT2) incX))

/-- The row invariant before coordinate `i`. -/
def RowInv (p ℓ M L j : ℕ) (all : List ℕ) (i : ℕ) (preO : List Bool) (σ : HState) : Prop :=
  HReady p ℓ i all σ ∧ σ.st sO = preO ∧ σ.sh sO = preO.length ∧ σ.val rOC = preO.length ∧
  σ.val rT1 = L - i ∧ σ.val rT2 = M - i ∧ σ.val rJC = j ∧ σ.val rBAD = 0 ∧ σ.val rTC = 0 ∧ σ.val rIC = 0 ∧
  σ.val rK = 0

def rowS (q : Fin 8) : Prop := q = sSEED ∨ q = sACC ∨ q = sNEW ∨ q = sST ∨ q = sO ∨ q = sX
def rowR (r : Fin 16) : Prop := r = rSC ∨ r = rF ∨ r = rG ∨ r = rR ∨ r = rRY ∨ r = rOC ∨ r = rT1 ∨ r = rT2 ∨ r = rBAD ∨
  r = rTC ∨ r = rIC ∨ r = rK

theorem hornS_rowS (q : Fin 8) (h : hornS q) : rowS q := by
  rcases h with h | h | h | h <;> simp [rowS, h]

theorem hornR_rowR (r : Fin 16) (h : hornR r) : rowR r := by
  rcases h with h | h | h | h | h <;> simp [rowR, h]

/-- The cost of one coordinate. -/
def stepCost (ℓ n j : ℕ) : ℕ := hornerCost ℓ n + (18 * j + ℓ * 25 + 3 * j + 8 + 10 * ℓ + 6) + ℓ * 41 + 60

/-- The bit part of a coordinate. -/
def bitPart : HProg :=
  .ifr rT2 (.seq hornerW (.seq prefixTest (.ifr rBAD (.seq (emit false) (WM.clear rBAD)) (emit true)))) (emit true)

theorem bitPart_spec (p ℓ M L j : ℕ) (all : List ℕ) (i : ℕ) (preO : List Bool) (σ : HState) (hℓ : 1 ≤ ℓ)
    (hcapS : (seedWord ℓ all).length + 2 * ℓ + 2 ≤ cap) (hj : j ≤ cap) (hO : preO.length + 1 ≤ cap)
    (hI : RowInv p ℓ M L j all i preO σ) :
    ∃ τ, WExec cap bitPart σ τ (stepCost ℓ all.length j) ∧
      HReady p ℓ i all τ ∧ τ.st sO = preO ++ [rowBit p ℓ M j i all] ∧ τ.sh sO = preO.length + 1 ∧
      τ.val rOC = preO.length + 1 ∧ τ.val rT1 = L - i ∧ τ.val rT2 = M - i ∧ τ.val rJC = j ∧ τ.val rBAD = 0 ∧
      τ.val rTC = 0 ∧ τ.val rIC = 0 ∧ τ.val rK = 0 ∧ WFrame rowS rowR σ τ := by
  obtain ⟨hR, hO1, hO2, hOC, hT1, hT2, hJ, hB, hTC, hIC, hK⟩ := hI
  by_cases hiM : i < M
  · obtain ⟨τ1, s1, hR1, hA1, hF1⟩ := hornerW_spec cap p ℓ i all hℓ hcapS σ hR
    have fr := fun q (h : ¬ hornR q) => hF1.2.1 q h
    have hJ1 : τ1.val rJC = j := by rw [fr rJC (by simp [hornR]), hJ]
    have hTC1 : τ1.val rTC = 0 := by rw [fr rTC (by simp [hornR]), hTC]
    have hIC1 : τ1.val rIC = 0 := by rw [fr rIC (by simp [hornR]), hIC]
    have hB1 : τ1.val rBAD = 0 := by rw [fr rBAD (by simp [hornR]), hB]
    have hK1 : τ1.val rK = 0 := by rw [fr rK (by simp [hornR]), hK]
    have s2 := prefixTest_spec cap ℓ (all.foldl (hornerStep p ℓ i) 0) j τ1 (by omega) hA1 hR1.2.2.2.2.1 hJ1 hj
      hTC1 hIC1 hB1 hK1 (by omega)
    obtain ⟨b, hb⟩ : ∃ b, (!prefixZero j (binary ℓ (all.foldl (hornerStep p ℓ i) 0))) = b := ⟨_, rfl⟩
    rw [hb] at s2
    have hbit : rowBit p ℓ M j i all = !b := by
      rw [← hb]; simp [rowBit, hiM, prefixZero_binary]
    have hOst : (τ1.setv rBAD b.toNat).st sO = preO := by
      simp; rw [(hF1.1 sO (by simp [hornS])).1, hO1]
    have hOsh : (τ1.setv rBAD b.toNat).sh sO = preO.length := by
      simp; rw [(hF1.1 sO (by simp [hornS])).2, hO2]
    have hOC1 : (τ1.setv rBAD b.toNat).val rOC = preO.length := by
      simp; rw [fr rOC (by simp [hornR]), hOC]
    have s3 : ∃ τ, WExec cap (.ifr rBAD (.seq (emit false) (WM.clear rBAD)) (emit true)) (τ1.setv rBAD b.toNat) τ 15 ∧
        τ = (((τ1.sets sO (preO ++ [!b])).seth sO (preO.length + 1)).setv rOC (preO.length + 1)) := by
      cases b
      · have e := emit_spec cap true (τ1.setv rBAD (false).toNat) (by rw [hOst, hOsh]) (by rw [hOC1]; omega)
        refine ⟨_, WExec.mono (WExec.ifrF (by simp) e) (by omega), ?_⟩
        rw [hOst, hOsh, hOC1]
        hs_eq [hB1]
      · have e := emit_spec cap false (τ1.setv rBAD (true).toNat) (by rw [hOst, hOsh]) (by rw [hOC1]; omega)
        obtain ⟨ρ, hρ⟩ : ∃ ρ : HState, ρ = ((((τ1.setv rBAD (true).toNat).sets sO ((τ1.setv rBAD (true).toNat).st sO ++
            [false])).seth sO ((τ1.setv rBAD (true).toNat).sh sO + 1)).setv rOC ((τ1.setv rBAD (true).toNat).val rOC + 1))
          := ⟨_, rfl⟩
        rw [← hρ] at e
        have c1 := wclear_spec cap rBAD 1 ρ (by rw [hρ]; simp) (by rw [hρ]; simp; omega)
        refine ⟨_, WExec.mono (WExec.ifrT (by simp) (WExec.seq e c1)) (by omega), ?_⟩
        rw [hρ, hOst, hOsh, hOC1]
        hs_eq [hB1]
    obtain ⟨τ3, s3, hτ3⟩ := s3
    refine ⟨τ3, WExec.mono (WExec.ifrT (by omega) (WExec.seq s1 (WExec.seq s2 s3))) (by unfold stepCost; omega),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · subst hτ3
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hR1
      exact ⟨by simpa using a1, by simpa using a2, by simpa using a3, by simpa using a4, by simpa using a5,
        by simpa using a6, by simpa using a7, by simpa using a8, by simpa using a9, by simpa using a10,
        by simpa using a11, by simpa using a12, by simpa using a13, by simpa using a14, by simpa using a15,
        by simpa using a16, by simpa using a17⟩
    · subst hτ3; simp [hbit]
    · subst hτ3; simp
    · subst hτ3; simp
    · subst hτ3; simp; rw [fr rT1 (by simp [hornR]), hT1]
    · subst hτ3; simp; rw [fr rT2 (by simp [hornR]), hT2]
    · subst hτ3; simp [hJ1]
    · subst hτ3; simp [hB1]
    · subst hτ3; simp [hTC1]
    · subst hτ3; simp [hIC1]
    · subst hτ3; simp [hK1]
    · subst hτ3
      refine (hF1.mono hornS_rowS hornR_rowR).trans ⟨fun q hq => ?_, fun r hr => ?_, rfl⟩
      · have : q ≠ sO := fun h => hq (by simp [rowS, h])
        simp [Function.update_of_ne this]
      · have h1 : r ≠ rOC := fun h => hr (by simp [rowR, h])
        simp [Function.update_of_ne h1]
  · have hbit : rowBit p ℓ M j i all = true := by simp [rowBit, hiM]
    have e := emit_spec cap true σ (by rw [hO1, hO2]) (by rw [hOC]; omega)
    refine ⟨_, WExec.mono (WExec.ifrF (by rw [hT2]; omega) e) (by unfold stepCost; omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hR
      exact ⟨by simpa using a1, by simpa using a2, by simpa using a3, by simpa using a4, by simpa using a5,
        by simpa using a6, by simpa using a7, by simpa using a8, by simpa using a9, by simpa using a10,
        by simpa using a11, by simpa using a12, by simpa using a13, by simpa using a14, by simpa using a15,
        by simpa using a16, by simpa using a17⟩
    · simp [hO1, hbit]
    · simp [hO2]
    · simp [hOC]
    · simp [hT1]
    · simp [hT2]
    · simp [hJ]
    · simp [hB]
    · simp [hTC]
    · simp [hIC]
    · simp [hK]
    · refine ⟨fun q hq => ?_, fun r hr => ?_, rfl⟩
      · have : q ≠ sO := fun h => hq (by simp [rowS, h])
        simp [Function.update_of_ne this]
      · have h1 : r ≠ rOC := fun h => hr (by simp [rowR, h])
        simp [Function.update_of_ne h1]

theorem rowStep_eq : rowStep = .seq bitPart (.seq (.dec rT1) (.seq (.dec rT2) incX)) := rfl

theorem rowStep_spec (p ℓ M L j : ℕ) (all : List ℕ) (i : ℕ) (preO : List Bool) (σ : HState) (hℓ : 1 ≤ ℓ)
    (hcapS : (seedWord ℓ all).length + 2 * ℓ + 2 ≤ cap) (hj : j ≤ cap) (hO : preO.length + 1 ≤ cap)
    (hL : L ≤ cap) (hM : M ≤ cap) (hI : RowInv p ℓ M L j all i preO σ) :
    ∃ τ, WExec cap rowStep σ τ (stepCost ℓ all.length j + ℓ * 41 + 25) ∧
      RowInv p ℓ M L j all (i + 1) (preO ++ [rowBit p ℓ M j i all]) τ ∧ WFrame rowS rowR σ τ := by
  obtain ⟨τ1, s1, hR1, hO1, hO2, hOC, hT1, hT2, hJ, hB, hTC, hIC, hK, hF1⟩ :=
    bitPart_spec cap p ℓ M L j all i preO σ hℓ hcapS hj hO hI
  have s2 := WExec.dec (cap := cap) rT1 τ1 (by rw [hT1]; omega)
  have s3 := WExec.dec (cap := cap) rT2 (τ1.setv rT1 (τ1.val rT1 - 1)) (by simp [hT2]; omega)
  obtain ⟨τ3, hτ3⟩ : ∃ τ : HState, τ = (τ1.setv rT1 (τ1.val rT1 - 1)).setv rT2
      ((τ1.setv rT1 (τ1.val rT1 - 1)).val rT2 - 1) := ⟨_, rfl⟩
  rw [← hτ3] at s3
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17⟩ := hR1
  have s4 := incX_spec cap ℓ p i τ3 (by omega) (by omega) (by rw [hτ3]; simpa using a10) (by rw [hτ3]; simpa using a11)
    (by rw [hτ3]; simpa using a12) (by rw [hτ3]; simpa using a13) (by rw [hτ3]; simpa using a14)
    (by rw [hτ3]; simpa using a16)
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by omega), ?_, ?_⟩
  · subst hτ3
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simpo [a1, a2, a3, a5, a7, a9, a11, a12, a13, a14, a15, a16, a17, hO1, hO2, hOC, hT1, hT2, hJ, hB, hTC,
      hIC, hK]
  · refine hF1.trans ?_
    subst hτ3
    refine ⟨fun q hq => ?_, fun r hr => ?_, rfl⟩
    · have : q ≠ sX := fun h => hq (by simp [rowS, h])
      simp [Function.update_of_ne this]
    · have h1 : r ≠ rT1 := fun h => hr (by simp [rowR, h])
      have h2 : r ≠ rT2 := fun h => hr (by simp [rowR, h])
      simp [Function.update_of_ne h1, Function.update_of_ne h2]

theorem rowLoop_spec (p ℓ M L j : ℕ) (all : List ℕ) (hℓ : 1 ≤ ℓ)
    (hcapS : (seedWord ℓ all).length + 2 * ℓ + 2 ≤ cap) (hj : j ≤ cap) (hL : L ≤ cap) (hM : M ≤ cap) :
    ∀ (n i : ℕ) (preO : List Bool) (σ : HState), i + n = L → preO.length + n ≤ cap →
      RowInv p ℓ M L j all i preO σ →
      ∃ τ, WExec cap (.whr rT1 rowStep) σ τ (n * (stepCost ℓ all.length j + ℓ * 41 + 27) + 1) ∧
        RowInv p ℓ M L j all L (preO ++ (List.range' i n).map (fun k => rowBit p ℓ M j k all)) τ ∧
        WFrame rowS rowR σ τ
  | 0, i, preO, σ, hn, _, hI => by
    refine ⟨σ, WExec.mono (WExec.whrF ?_) (by omega), ?_, WFrame.refl _ _ σ⟩
    · rw [hI.2.2.2.2.1]; omega
    · simp only [List.range'_zero, List.map_nil, List.append_nil]
      have hLi : i = L := by omega
      subst hLi; exact hI
  | n + 1, i, preO, σ, hn, hO, hI => by
    obtain ⟨τ1, s1, hI1, hF1⟩ := rowStep_spec cap p ℓ M L j all i preO σ hℓ hcapS hj (by omega) hL hM hI
    obtain ⟨τ, s2, hI2, hF2⟩ := rowLoop_spec p ℓ M L j all hℓ hcapS hj hL hM n (i + 1) _ τ1 (by omega)
      (by simp; omega) hI1
    refine ⟨τ, WExec.mono (WExec.whrT (by rw [hI.2.2.2.2.1]; omega) s1 s2) (by ring_nf; omega), ?_, hF1.trans hF2⟩
    rw [List.range'_succ, List.map_cons]
    simpa using hI2

end NearCubicWires.WireExponent3_5.FinalPass.Hash4
