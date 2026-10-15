import Proof.Wire_3_5.FinalPassWords

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

variable {ns nr : ℕ} (cap : ℕ)

theorem WExec.cast {P : WM ns nr} {σ τ τ' : WState ns nr} {n n' : ℕ} (h : WExec cap P σ τ n) (e : τ = τ')
    (hn : n ≤ n') : WExec cap P σ τ' n' := by
  subst e; exact WExec.mono h hn

@[simp] theorem wsetv_val_self (σ : WState ns nr) (r : Fin nr) (x : ℕ) : (σ.setv r x).val r = x := by simp

@[simp] theorem wsetv_val_ne (σ : WState ns nr) {r r' : Fin nr} (x : ℕ) (h : r' ≠ r) : (σ.setv r x).val r' = σ.val r' := by
  simp [Function.update_of_ne h]

theorem wsetv_same (σ : WState ns nr) (r : Fin nr) : σ.setv r (σ.val r) = σ :=
  WState.eq rfl rfl (by simp) rfl

theorem wsetv_setv (σ : WState ns nr) (r : Fin nr) (x y : ℕ) : (σ.setv r x).setv r y = σ.setv r y :=
  WState.eq rfl rfl (by simp) rfl

theorem wsetv_comm (σ : WState ns nr) {r r' : Fin nr} (x y : ℕ) (h : r ≠ r') :
    (σ.setv r x).setv r' y = (σ.setv r' y).setv r x :=
  WState.eq rfl rfl (by simp [Function.update_comm h]) rfl

/-! ## Moving and clearing registers -/

/-- `b += a; a := 0`. -/
def WM.move (a b : Fin nr) : WM ns nr := .whr a (.seq (.dec a) (.inc b))

/-- `a := 0`. -/
def WM.clear (a : Fin nr) : WM ns nr := .whr a (.dec a)

/-- `f := 1` for a flag `f ∈ {0, 1}`. -/
def WM.setF (f : Fin nr) : WM ns nr := .ifr f .skip (.inc f)

theorem wmove_spec (a b : Fin nr) (hab : a ≠ b) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val a = n → σ.val a ≤ cap → σ.val b + σ.val a ≤ cap →
      WExec cap (WM.move a b) σ ((σ.setv a 0).setv b (σ.val b + σ.val a)) (7 * n + 1)
  | 0, σ, h0, _, _ => by
    have e : (σ.setv a 0).setv b (σ.val b + σ.val a) = σ := by
      rw [h0, Nat.add_zero, ← h0, wsetv_same, wsetv_same]
    rw [e]
    exact WExec.whrF h0
  | n + 1, σ, hn, ha, hb => by
    have h1 := WExec.dec (cap := cap) a σ ha
    have hba : (σ.setv a (σ.val a - 1)).val b = σ.val b := wsetv_val_ne _ _ (Ne.symm hab)
    have h2 := WExec.inc (cap := cap) b (σ.setv a (σ.val a - 1)) (by rw [hba]; omega)
    have hb' := wmove_spec a b hab n ((σ.setv a (σ.val a - 1)).setv b ((σ.setv a (σ.val a - 1)).val b + 1))
      (by rw [wsetv_val_ne _ _ hab]; simp; omega) (by rw [wsetv_val_ne _ _ hab]; simp; omega)
      (by rw [wsetv_val_ne _ _ hab]; simp [hba]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 h2) hb') ?_ (by omega)
    apply WState.eq
    · rfl
    · rfl
    · funext j
      by_cases hja : j = a
      · subst hja
        simp [Function.update_of_ne hab]
      · by_cases hjb : j = b
        · subst hjb
          simp [Function.update_of_ne hab, Function.update_of_ne (Ne.symm hab)]
          omega
        · simp [Function.update_of_ne hja, Function.update_of_ne hjb]
    · rfl

theorem wclear_spec (a : Fin nr) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val a = n → σ.val a ≤ cap →
      WExec cap (WM.clear a) σ (σ.setv a 0) (3 * n + 1)
  | 0, σ, h0, _ => by
    have e : σ.setv a 0 = σ := by rw [← h0, wsetv_same]
    rw [e]
    exact WExec.whrF h0
  | n + 1, σ, hn, ha => by
    have h1 := WExec.dec (cap := cap) a σ ha
    have h2 := wclear_spec a n (σ.setv a (σ.val a - 1)) (by simp; omega) (by simp; omega)
    rw [wsetv_setv] at h2
    exact WExec.mono (WExec.whrT (by omega) h1 h2) (by omega)

theorem wsetF_spec (f : Fin nr) (σ : WState ns nr) (hf : σ.val f ≤ 1) (hcap : 1 ≤ cap) :
    WExec cap (WM.setF f) σ (σ.setv f 1) 4 := by
  by_cases h : σ.val f = 0
  · have hi := WExec.inc (cap := cap) f σ (by omega)
    rw [h] at hi
    exact WExec.ifrF h hi
  · have e : σ.setv f 1 = σ := by rw [show 1 = σ.val f by omega, wsetv_same]
    rw [e]
    exact WExec.mono (WExec.ifrT h (WExec.skip σ)) (by omega)

/-! ## Streams -/

/-- Forward one cell on stream `i`, counting the position in register `c`. -/
def WM.fwdC (i : Fin (ns + 1)) (c : Fin nr) : WM ns nr := .seq (.fwd i) (.inc c)

/-- Read a unary field `1^n 0` of stream `i` into register `r` (`r += n`), moving past its `0`. -/
def WM.readU (i : Fin (ns + 1)) (c r : Fin nr) : WM ns nr := .seq (.whs i (.seq (WM.fwdC i c) (.inc r))) (WM.fwdC i c)

/-- Return stream `i` by its position counter `c`. -/
def WM.rewind (i : Fin (ns + 1)) (c : Fin nr) : WM ns nr := .whr c (.seq (.dec c) (.bwd i))

theorem wsbit_seth (σ : WState ns nr) (i : Fin (ns + 1)) (x : ℕ) : wbit (σ.seth i x) i = readTapeBit (σ.st i) x := by
  simp [wbit]

theorem wsbit_setv (σ : WState ns nr) (i : Fin (ns + 1)) (r : Fin nr) (x : ℕ) : wbit (σ.setv r x) i = wbit σ i := rfl

theorem wfwdC_spec (i : Fin (ns + 1)) (c : Fin nr) (σ : WState ns nr) (hc : σ.val c < cap) :
    WExec cap (WM.fwdC i c) σ ((σ.seth i (σ.sh i + 1)).setv c (σ.val c + 1)) 5 :=
  WExec.seq (WExec.fwd i σ) (WExec.inc c _ hc)

theorem wseth_setv (σ : WState ns nr) (i : Fin (ns + 1)) (r : Fin nr) (x y : ℕ) :
    (σ.seth i x).setv r y = (σ.setv r y).seth i x := rfl

theorem wseth_seth (σ : WState ns nr) (i : Fin (ns + 1)) (x y : ℕ) : (σ.seth i x).seth i y = σ.seth i y :=
  WState.eq (by simp) rfl rfl rfl

@[simp] theorem wseth_sh_self (σ : WState ns nr) (i : Fin (ns + 1)) (x : ℕ) : (σ.seth i x).sh i = x := by simp

theorem wreadU_loop (i : Fin (ns + 1)) (c r : Fin nr) (hcr : c ≠ r) :
    ∀ (n : ℕ) (σ : WState ns nr), (∀ k < n, readTapeBit (σ.st i) (σ.sh i + k) = true) →
      readTapeBit (σ.st i) (σ.sh i + n) = false → σ.val c + n ≤ cap → σ.val r + n ≤ cap →
      WExec cap (.whs i (.seq (WM.fwdC i c) (.inc r))) σ
        (((σ.seth i (σ.sh i + n)).setv c (σ.val c + n)).setv r (σ.val r + n)) (11 * n + 1)
  | 0, σ, _, hend, _, _ => by
    have e : ((σ.seth i (σ.sh i + 0)).setv c (σ.val c + 0)).setv r (σ.val r + 0) = σ :=
      WState.eq (by simp) rfl (by simp) rfl
    rw [e]
    exact WExec.whsF (by simpa [wbit] using hend)
  | n + 1, σ, hones, hend, hc, hr => by
    have h1 := wfwdC_spec cap i c σ (by omega)
    have hrv : ((σ.seth i (σ.sh i + 1)).setv c (σ.val c + 1)).val r = σ.val r := by
      simp [Function.update_of_ne (Ne.symm hcr)]
    have h2 := WExec.inc (cap := cap) r ((σ.seth i (σ.sh i + 1)).setv c (σ.val c + 1)) (by rw [hrv]; omega)
    set τ := ((σ.seth i (σ.sh i + 1)).setv c (σ.val c + 1)).setv r
      (((σ.seth i (σ.sh i + 1)).setv c (σ.val c + 1)).val r + 1) with hτ
    have hτs : τ.sh i = σ.sh i + 1 := by simp [τ]
    have hτc : τ.val c = σ.val c + 1 := by simp [τ, Function.update_of_ne hcr]
    have hτr : τ.val r = σ.val r + 1 := by simp [τ, hrv]
    have h3 := wreadU_loop i c r hcr n τ (fun k hk => by rw [hτs]; have := hones (k + 1) (by omega); rwa [Nat.add_assoc,
      Nat.add_comm 1 k]) (by rw [hτs, Nat.add_assoc, Nat.add_comm 1 n]; exact hend) (by omega) (by omega)
    refine WExec.cast cap (WExec.whsT (by simpa [wbit] using hones 0 (by omega)) (WExec.seq h1 h2) h3) ?_
      (by omega)
    apply WState.eq
    · funext j
      by_cases hji : j = i
      · subst hji
        simp only [WState.setv_sh, WState.seth_sh, Function.update_self]
        rw [hτs]; omega
      · simp [τ, Function.update_of_ne hji]
    · rfl
    · funext j
      by_cases hjr : j = r
      · subst hjr
        simp only [WState.setv_val, Function.update_self]
        rw [hτr]; omega
      · by_cases hjc : j = c
        · subst hjc
          simp only [WState.setv_val, WState.seth_val, Function.update_of_ne hjr, Function.update_self]
          rw [hτc]; omega
        · simp [τ, Function.update_of_ne hjr, Function.update_of_ne hjc]
    · rfl

theorem wreadU_spec (i : Fin (ns + 1)) (c r : Fin nr) (hcr : c ≠ r) (n : ℕ) (σ : WState ns nr)
    (hones : ∀ k < n, readTapeBit (σ.st i) (σ.sh i + k) = true) (hend : readTapeBit (σ.st i) (σ.sh i + n) = false)
    (hc : σ.val c + n + 1 ≤ cap) (hr : σ.val r + n ≤ cap) :
    WExec cap (WM.readU i c r) σ
      (((σ.seth i (σ.sh i + n + 1)).setv c (σ.val c + n + 1)).setv r (σ.val r + n)) (11 * n + 7) := by
  have h1 := wreadU_loop cap i c r hcr n σ hones hend (by omega) hr
  set τ := ((σ.seth i (σ.sh i + n)).setv c (σ.val c + n)).setv r (σ.val r + n) with hτ
  have h2 := wfwdC_spec cap i c τ (by simp [τ, Function.update_of_ne hcr]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  apply WState.eq
  · funext j
    by_cases hji : j = i
    · subst hji
      simp [τ]
    · simp [τ, Function.update_of_ne hji]
  · rfl
  · funext j
    by_cases hjr : j = r
    · subst hjr
      simp [τ, Function.update_of_ne (Ne.symm hcr)]
    · by_cases hjc : j = c
      · subst hjc
        simp [τ, Function.update_of_ne hjr]
      · simp [τ, Function.update_of_ne hjr, Function.update_of_ne hjc]
  · rfl

theorem wrewind_spec (i : Fin (ns + 1)) (c : Fin nr) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val c = n → σ.val c ≤ cap →
      WExec cap (WM.rewind i c) σ ((σ.setv c 0).seth i (σ.sh i - n)) (5 * n + 1)
  | 0, σ, h0, _ => by
    have e : (σ.setv c 0).seth i (σ.sh i - 0) = σ := WState.eq (by simp) rfl (by rw [← h0]; simp) rfl
    rw [e]
    exact WExec.whrF h0
  | n + 1, σ, hn, hc => by
    have h1 := WExec.dec (cap := cap) c σ hc
    have h2 := WExec.bwd (cap := cap) i (σ.setv c (σ.val c - 1))
    have h3 := wrewind_spec i c n ((σ.setv c (σ.val c - 1)).seth i ((σ.setv c (σ.val c - 1)).sh i - 1))
      (by simp; omega) (by simp; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 h2) h3) ?_ (by omega)
    apply WState.eq
    · funext j
      by_cases hji : j = i
      · subst hji
        simp
        omega
      · simp [Function.update_of_ne hji]
    · rfl
    · funext j
      by_cases hjc : j = c
      · subst hjc
        simp
      · simp [Function.update_of_ne hjc]
    · rfl

end NearCubicWires.WireExponent3_5.FinalPass.Tm
