import Proof.Wire_3_5.FinalPassRegister

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary

variable {ns nr : ℕ} (inp : Fin (ns + 1) → List Bool) (cap : ℕ)

theorem RState.eq {σ τ : RState ns nr} (h1 : σ.sh = τ.sh) (h2 : σ.val = τ.val) (h3 : σ.cell = τ.cell) : σ = τ := by
  cases σ; cases τ; simp_all

theorem RExec.cast {P : RM ns nr} {σ τ τ' : RState ns nr} {n n' : ℕ} (h : RExec inp cap P σ τ n) (e : τ = τ')
    (hn : n ≤ n') : RExec inp cap P σ τ' n' := by
  subst e; exact RExec.mono h hn

@[simp] theorem setv_val_self (σ : RState ns nr) (r : Fin nr) (x : ℕ) : (σ.setv r x).val r = x := by simp

@[simp] theorem setv_val_ne (σ : RState ns nr) {r r' : Fin nr} (x : ℕ) (h : r' ≠ r) : (σ.setv r x).val r' = σ.val r' := by
  simp [Function.update_of_ne h]

theorem setv_same (σ : RState ns nr) (r : Fin nr) : σ.setv r (σ.val r) = σ :=
  RState.eq rfl (by simp) rfl

theorem setv_setv (σ : RState ns nr) (r : Fin nr) (x y : ℕ) : (σ.setv r x).setv r y = σ.setv r y :=
  RState.eq rfl (by simp) rfl

theorem setv_comm (σ : RState ns nr) {r r' : Fin nr} (x y : ℕ) (h : r ≠ r') :
    (σ.setv r x).setv r' y = (σ.setv r' y).setv r x :=
  RState.eq rfl (by simp [Function.update_comm h]) rfl

/-! ## Moving and clearing registers -/

/-- `b += a; a := 0`. -/
def RM.move (a b : Fin nr) : RM ns nr := .whr a (.seq (.dec a) (.inc b))

/-- `a := 0`. -/
def RM.clear (a : Fin nr) : RM ns nr := .whr a (.dec a)

/-- `f := 1` for a flag `f ∈ {0, 1}`. -/
def RM.setF (f : Fin nr) : RM ns nr := .ifr f .skip (.inc f)

theorem move_spec (a b : Fin nr) (hab : a ≠ b) :
    ∀ (n : ℕ) (σ : RState ns nr), σ.val a = n → σ.val a ≤ cap → σ.val b + σ.val a ≤ cap →
      RExec inp cap (RM.move a b) σ ((σ.setv a 0).setv b (σ.val b + σ.val a)) (7 * n + 1)
  | 0, σ, h0, _, _ => by
    have e : (σ.setv a 0).setv b (σ.val b + σ.val a) = σ := by
      rw [h0, Nat.add_zero, ← h0, setv_same, setv_same]
    rw [e]
    exact RExec.whrF h0
  | n + 1, σ, hn, ha, hb => by
    have h1 := RExec.dec (inp := inp) (cap := cap) a σ ha
    have hba : (σ.setv a (σ.val a - 1)).val b = σ.val b := setv_val_ne _ _ (Ne.symm hab)
    have h2 := RExec.inc (inp := inp) (cap := cap) b (σ.setv a (σ.val a - 1)) (by rw [hba]; omega)
    have hb' := move_spec a b hab n ((σ.setv a (σ.val a - 1)).setv b ((σ.setv a (σ.val a - 1)).val b + 1))
      (by rw [setv_val_ne _ _ hab]; simp; omega) (by rw [setv_val_ne _ _ hab]; simp; omega)
      (by rw [setv_val_ne _ _ hab]; simp [hba]; omega)
    refine RExec.cast inp cap (RExec.whrT (by omega) (RExec.seq h1 h2) hb') ?_ (by omega)
    apply RState.eq
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

theorem clear_spec (a : Fin nr) :
    ∀ (n : ℕ) (σ : RState ns nr), σ.val a = n → σ.val a ≤ cap →
      RExec inp cap (RM.clear a) σ (σ.setv a 0) (3 * n + 1)
  | 0, σ, h0, _ => by
    have e : σ.setv a 0 = σ := by rw [← h0, setv_same]
    rw [e]
    exact RExec.whrF h0
  | n + 1, σ, hn, ha => by
    have h1 := RExec.dec (inp := inp) (cap := cap) a σ ha
    have h2 := clear_spec a n (σ.setv a (σ.val a - 1)) (by simp; omega) (by simp; omega)
    rw [setv_setv] at h2
    exact RExec.mono (RExec.whrT (by omega) h1 h2) (by omega)

theorem setF_spec (f : Fin nr) (σ : RState ns nr) (hf : σ.val f ≤ 1) (hcap : 1 ≤ cap) :
    RExec inp cap (RM.setF f) σ (σ.setv f 1) 4 := by
  by_cases h : σ.val f = 0
  · have hi := RExec.inc (inp := inp) (cap := cap) f σ (by omega)
    rw [h] at hi
    exact RExec.ifrF h hi
  · have e : σ.setv f 1 = σ := by rw [show 1 = σ.val f by omega, setv_same]
    rw [e]
    exact RExec.mono (RExec.ifrT h (RExec.skip σ)) (by omega)

/-! ## Streams -/

/-- Forward one cell on stream `i`, counting the position in register `c`. -/
def RM.fwdC (i : Fin (ns + 1)) (c : Fin nr) : RM ns nr := .seq (.fwd i) (.inc c)

/-- Read a unary field `1^n 0` of stream `i` into register `r` (`r += n`), moving past its `0`. -/
def RM.readU (i : Fin (ns + 1)) (c r : Fin nr) : RM ns nr := .seq (.whs i (.seq (RM.fwdC i c) (.inc r))) (RM.fwdC i c)

/-- Return stream `i` by its position counter `c`. -/
def RM.rewind (i : Fin (ns + 1)) (c : Fin nr) : RM ns nr := .whr c (.seq (.dec c) (.bwd i))

theorem sbit_seth (σ : RState ns nr) (i : Fin (ns + 1)) (x : ℕ) : sbit inp (σ.seth i x) i = readTapeBit (inp i) x := by
  simp [sbit]

theorem sbit_setv (σ : RState ns nr) (i : Fin (ns + 1)) (r : Fin nr) (x : ℕ) : sbit inp (σ.setv r x) i = sbit inp σ i := rfl

theorem fwdC_spec (i : Fin (ns + 1)) (c : Fin nr) (σ : RState ns nr) (hc : σ.val c < cap) :
    RExec inp cap (RM.fwdC i c) σ ((σ.seth i (σ.sh i + 1)).setv c (σ.val c + 1)) 5 :=
  RExec.seq (RExec.fwd i σ) (RExec.inc c _ hc)

theorem seth_setv (σ : RState ns nr) (i : Fin (ns + 1)) (r : Fin nr) (x y : ℕ) :
    (σ.seth i x).setv r y = (σ.setv r y).seth i x := rfl

theorem seth_seth (σ : RState ns nr) (i : Fin (ns + 1)) (x y : ℕ) : (σ.seth i x).seth i y = σ.seth i y :=
  RState.eq (by simp) rfl rfl

@[simp] theorem seth_sh_self (σ : RState ns nr) (i : Fin (ns + 1)) (x : ℕ) : (σ.seth i x).sh i = x := by simp

theorem readU_loop (i : Fin (ns + 1)) (c r : Fin nr) (hcr : c ≠ r) :
    ∀ (n : ℕ) (σ : RState ns nr), (∀ k < n, readTapeBit (inp i) (σ.sh i + k) = true) →
      readTapeBit (inp i) (σ.sh i + n) = false → σ.val c + n ≤ cap → σ.val r + n ≤ cap →
      RExec inp cap (.whs i (.seq (RM.fwdC i c) (.inc r))) σ
        (((σ.seth i (σ.sh i + n)).setv c (σ.val c + n)).setv r (σ.val r + n)) (11 * n + 1)
  | 0, σ, _, hend, _, _ => by
    have e : ((σ.seth i (σ.sh i + 0)).setv c (σ.val c + 0)).setv r (σ.val r + 0) = σ :=
      RState.eq (by simp) (by simp) rfl
    rw [e]
    exact RExec.whsF (by simpa [sbit] using hend)
  | n + 1, σ, hones, hend, hc, hr => by
    have h1 := fwdC_spec inp cap i c σ (by omega)
    have hrv : ((σ.seth i (σ.sh i + 1)).setv c (σ.val c + 1)).val r = σ.val r := by
      simp [Function.update_of_ne (Ne.symm hcr)]
    have h2 := RExec.inc (inp := inp) (cap := cap) r ((σ.seth i (σ.sh i + 1)).setv c (σ.val c + 1)) (by rw [hrv]; omega)
    set τ := ((σ.seth i (σ.sh i + 1)).setv c (σ.val c + 1)).setv r
      (((σ.seth i (σ.sh i + 1)).setv c (σ.val c + 1)).val r + 1) with hτ
    have hτs : τ.sh i = σ.sh i + 1 := by simp [τ]
    have hτc : τ.val c = σ.val c + 1 := by simp [τ, Function.update_of_ne hcr]
    have hτr : τ.val r = σ.val r + 1 := by simp [τ, hrv]
    have h3 := readU_loop i c r hcr n τ (fun k hk => by rw [hτs]; have := hones (k + 1) (by omega); rwa [Nat.add_assoc,
      Nat.add_comm 1 k]) (by rw [hτs, Nat.add_assoc, Nat.add_comm 1 n]; exact hend) (by omega) (by omega)
    refine RExec.cast inp cap (RExec.whsT (by simpa [sbit] using hones 0 (by omega)) (RExec.seq h1 h2) h3) ?_
      (by omega)
    apply RState.eq
    · funext j
      by_cases hji : j = i
      · subst hji
        simp only [RState.setv_sh, RState.seth_sh, Function.update_self]
        rw [hτs]; omega
      · simp [τ, Function.update_of_ne hji]
    · funext j
      by_cases hjr : j = r
      · subst hjr
        simp only [RState.setv_val, Function.update_self]
        rw [hτr]; omega
      · by_cases hjc : j = c
        · subst hjc
          simp only [RState.setv_val, RState.seth_val, Function.update_of_ne hjr, Function.update_self]
          rw [hτc]; omega
        · simp [τ, Function.update_of_ne hjr, Function.update_of_ne hjc]
    · rfl

theorem readU_spec (i : Fin (ns + 1)) (c r : Fin nr) (hcr : c ≠ r) (n : ℕ) (σ : RState ns nr)
    (hones : ∀ k < n, readTapeBit (inp i) (σ.sh i + k) = true) (hend : readTapeBit (inp i) (σ.sh i + n) = false)
    (hc : σ.val c + n + 1 ≤ cap) (hr : σ.val r + n ≤ cap) :
    RExec inp cap (RM.readU i c r) σ
      (((σ.seth i (σ.sh i + n + 1)).setv c (σ.val c + n + 1)).setv r (σ.val r + n)) (11 * n + 7) := by
  have h1 := readU_loop inp cap i c r hcr n σ hones hend (by omega) hr
  set τ := ((σ.seth i (σ.sh i + n)).setv c (σ.val c + n)).setv r (σ.val r + n) with hτ
  have h2 := fwdC_spec inp cap i c τ (by simp [τ, Function.update_of_ne hcr]; omega)
  refine RExec.cast inp cap (RExec.seq h1 h2) ?_ (by omega)
  apply RState.eq
  · funext j
    by_cases hji : j = i
    · subst hji
      simp [τ]
    · simp [τ, Function.update_of_ne hji]
  · funext j
    by_cases hjr : j = r
    · subst hjr
      simp [τ, Function.update_of_ne (Ne.symm hcr)]
    · by_cases hjc : j = c
      · subst hjc
        simp [τ, Function.update_of_ne hjr]
      · simp [τ, Function.update_of_ne hjr, Function.update_of_ne hjc]
  · rfl

theorem rewind_spec (i : Fin (ns + 1)) (c : Fin nr) :
    ∀ (n : ℕ) (σ : RState ns nr), σ.val c = n → σ.val c ≤ cap →
      RExec inp cap (RM.rewind i c) σ ((σ.setv c 0).seth i (σ.sh i - n)) (5 * n + 1)
  | 0, σ, h0, _ => by
    have e : (σ.setv c 0).seth i (σ.sh i - 0) = σ := RState.eq (by simp) (by rw [← h0]; simp) rfl
    rw [e]
    exact RExec.whrF h0
  | n + 1, σ, hn, hc => by
    have h1 := RExec.dec (inp := inp) (cap := cap) c σ hc
    have h2 := RExec.bwd (inp := inp) (cap := cap) i (σ.setv c (σ.val c - 1))
    have h3 := rewind_spec i c n ((σ.setv c (σ.val c - 1)).seth i ((σ.setv c (σ.val c - 1)).sh i - 1))
      (by simp; omega) (by simp; omega)
    refine RExec.cast inp cap (RExec.whrT (by omega) (RExec.seq h1 h2) h3) ?_ (by omega)
    apply RState.eq
    · funext j
      by_cases hji : j = i
      · subst hji
        simp
        omega
      · simp [Function.update_of_ne hji]
    · funext j
      by_cases hjc : j = c
      · subst hjc
        simp
      · simp [Function.update_of_ne hjc]
    · rfl

end NearCubicWires.WireExponent3_5.FinalPass.Tm
