import Proof.Wire_3_5.FinalPassWordAux
import Proof.Wire_3_5.UnionMachineSeedIdx

/-! # X1, part (b): the binary writer `binW` (a register's value as a framed binary word)

The walk bank reads the seed's index word `frame (binary (160n + 2r) g)` on its port `9` (T's `WalkBankIface`); the
FILTER setup holds the seed index `g` in a register (`FiltSetup.FsIn.vSeed`). `binW O Rg` writes, for the registers
`Rg 0 = g` and `Rg 1 = k` (both kept, scratch `Rg 2 … Rg 7` back to `0`), the word `frame (binary k g)` on the blank
stream `O` with its head back at `0`: `k` rounds of halving (`halveR`: quotient and parity), each appending the
marker `true` and the parity bit (`bitE`), then the end marker and a rewind (**`binW_spec`**, exact final state,
cost `binCost g k = 60(g+1)(k+1)`). With X1 (a) (`SeedIdx.seedIndex_cast`) the seed of index `g` gives the walk
bank's index word (**`seedIndex_write`**).

Paper quantity of the main type: the seed's index word (`binary k g`, the walk sample's start vertex and labels). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.BinW
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey NearCubicWires.WireExponent3_5.FinalPass.Tm

variable {ns nr : ℕ} (cap : ℕ)

theorem bsetv_self (σ : WState ns nr) (r : Fin nr) (x : ℕ) (h : σ.val r = x) : σ.setv r x = σ := by
  rw [← h, wsetv_same]

/-! ## Copying a register -/

/-- `Y := X` (`X` kept), through the scratch `T`. -/
def dupR (X Y T : Fin nr) : WM ns nr := .seq (.whr X (.seq (.dec X) (.seq (.inc Y) (.inc T)))) (WM.move T X)

theorem dupL_spec (X Y T : Fin nr) (hXY : X ≠ Y) (hXT : X ≠ T) (hYT : Y ≠ T) :
    ∀ (n : ℕ) (σ : WState ns nr), σ.val X = n → σ.val X ≤ cap → σ.val Y + n ≤ cap → σ.val T + n ≤ cap →
      WExec cap (.whr X (.seq (.dec X) (.seq (.inc Y) (.inc T)))) σ
        (((σ.setv X 0).setv Y (σ.val Y + n)).setv T (σ.val T + n)) (11 * n + 1)
  | 0, σ, h0, _, _, _ => by
    rw [Nat.add_zero, Nat.add_zero, bsetv_self σ X 0 h0, wsetv_same, wsetv_same]
    exact WExec.whrF h0
  | n + 1, σ, hn, hX, hY, hT => by
    have h1 := WExec.dec (cap := cap) X σ hX
    have h2 := WExec.inc (cap := cap) Y (σ.setv X (σ.val X - 1)) (by rw [wsetv_val_ne _ _ (Ne.symm hXY)]; omega)
    have h3 := WExec.inc (cap := cap) T ((σ.setv X (σ.val X - 1)).setv Y ((σ.setv X (σ.val X - 1)).val Y + 1))
      (by rw [wsetv_val_ne _ _ (Ne.symm hYT), wsetv_val_ne _ _ (Ne.symm hXT)]; omega)
    have ih := dupL_spec X Y T hXY hXT hYT n
      (((σ.setv X (σ.val X - 1)).setv Y ((σ.setv X (σ.val X - 1)).val Y + 1)).setv T
        (((σ.setv X (σ.val X - 1)).setv Y ((σ.setv X (σ.val X - 1)).val Y + 1)).val T + 1))
      (by simp [hXY, hXT] <;> omega) (by simp [hXY, hXT] <;> omega) (by simp [hYT, Ne.symm hXY] <;> omega)
      (by simp [Ne.symm hYT, Ne.symm hXT] <;> omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq h1 (WExec.seq h2 h3)) ih) ?_ (by omega)
    apply WState.eq
    · rfl
    · rfl
    · funext j
      simp only [WState.setv_val, Function.update_apply]
      by_cases hjT : j = T
      · subst hjT; simp [Ne.symm hXT, Ne.symm hYT, hXT, hYT] <;> omega
      · by_cases hjY : j = Y
        · subst hjY; simp [hjT, Ne.symm hXY, hXY] <;> omega
        · by_cases hjX : j = X
          · subst hjX; simp [hjT, hjY]
          · simp [hjT, hjY, hjX]
    · rfl

theorem dupR_spec (X Y T : Fin nr) (hXY : X ≠ Y) (hXT : X ≠ T) (hYT : Y ≠ T) (σ : WState ns nr) (x : ℕ)
    (hx : σ.val X = x) (hy : σ.val Y = 0) (ht : σ.val T = 0) (hc : x ≤ cap) :
    WExec cap (dupR X Y T) σ (σ.setv Y x) (18 * x + 3) := by
  have h1 := dupL_spec cap X Y T hXY hXT hYT x σ hx (by omega) (by omega) (by omega)
  rw [hy, ht, Nat.zero_add] at h1
  have h2 := wmove_spec cap T X (Ne.symm hXT) x (((σ.setv X 0).setv Y x).setv T x) (by simp)
    (by simp <;> omega) (by simp [hXT, hXY] <;> omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  apply WState.eq
  · rfl
  · rfl
  · funext j
    simp only [WState.setv_val, Function.update_apply]
    by_cases hjX : j = X
    · subst hjX; simp [hXY, hXT, hx]
    · by_cases hjY : j = Y
      · subst hjY; simp [hjX, hYT]
      · by_cases hjT : j = T
        · subst hjT; simp [hjX, hjY, ht]
        · simp [hjX, hjY, hjT]
  · rfl

/-! ## Halving -/

/-- `Q += A / 2`, `B := A mod 2`, `A := 0` (`B` zero at entry). -/
def halveR (A Q B : Fin nr) : WM ns nr := .whr A (.seq (.dec A) (.ifr A (.seq (.dec A) (.inc Q)) (.inc B)))

theorem halve_spec (A Q B : Fin nr) (hAQ : A ≠ Q) (hAB : A ≠ B) (hQB : Q ≠ B) :
    ∀ (a : ℕ) (σ : WState ns nr), σ.val A = a → a ≤ cap → σ.val Q + a / 2 ≤ cap → σ.val B = 0 → 1 ≤ cap →
      WExec cap (halveR A Q B) σ (((σ.setv A 0).setv Q (σ.val Q + a / 2)).setv B (a % 2)) (5 * a + 4)
  | 0, σ, h0, _, _, hB, _ => by
    simp only [Nat.zero_div, Nat.zero_mod, Nat.add_zero]
    rw [bsetv_self σ A 0 h0, wsetv_same, bsetv_self σ B 0 hB]
    exact WExec.mono (WExec.whrF h0) (by omega)
  | 1, σ, h1, hc, _, hB, hcap => by
    have hd := WExec.dec (cap := cap) A σ (by omega)
    have hA0 : (σ.setv A (σ.val A - 1)).val A = 0 := by simp [h1]
    have hi := WExec.inc (cap := cap) B (σ.setv A (σ.val A - 1)) (by rw [wsetv_val_ne _ _ (Ne.symm hAB)]; omega)
    have hA0' : ((σ.setv A (σ.val A - 1)).setv B ((σ.setv A (σ.val A - 1)).val B + 1)).val A = 0 := by
      simp [hAB, h1]
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq hd (WExec.ifrF hA0 hi)) (WExec.whrF hA0')) ?_ (by omega)
    apply WState.eq
    · rfl
    · rfl
    · funext j
      simp only [WState.setv_val, Function.update_apply]
      by_cases hjB : j = B
      · subst hjB; simp [Ne.symm hAB, Ne.symm hQB, hB]
      · by_cases hjQ : j = Q
        · subst hjQ; simp [hjB, Ne.symm hAQ]
        · by_cases hjA : j = A
          · subst hjA; simp [hjB, hjQ, h1]
          · simp [hjB, hjQ, hjA]
    · rfl
  | a + 2, σ, ha, hc, hq, hB, hcap => by
    have hd := WExec.dec (cap := cap) A σ (by omega)
    have hA1 : (σ.setv A (σ.val A - 1)).val A ≠ 0 := by simp <;> omega
    have hd2 := WExec.dec (cap := cap) A (σ.setv A (σ.val A - 1)) (by simp <;> omega)
    have hi := WExec.inc (cap := cap) Q ((σ.setv A (σ.val A - 1)).setv A ((σ.setv A (σ.val A - 1)).val A - 1))
      (by simp [Ne.symm hAQ] <;> omega)
    have ih := halve_spec A Q B hAQ hAB hQB a
      (((σ.setv A (σ.val A - 1)).setv A ((σ.setv A (σ.val A - 1)).val A - 1)).setv Q
        (((σ.setv A (σ.val A - 1)).setv A ((σ.setv A (σ.val A - 1)).val A - 1)).val Q + 1))
      (by simp [hAQ] <;> omega) (by omega) (by simp [Ne.symm hAQ] <;> omega)
      (by simp [Ne.symm hQB, Ne.symm hAB, hB]) hcap
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq hd (WExec.ifrT hA1 (WExec.seq hd2 hi))) ih) ?_
      (by omega)
    apply WState.eq
    · rfl
    · rfl
    · funext j
      simp only [WState.setv_val, Function.update_apply]
      by_cases hjB : j = B
      · subst hjB; simp [Ne.symm hAB, Ne.symm hQB] <;> omega
      · by_cases hjQ : j = Q
        · subst hjQ; simp [hjB, Ne.symm hAQ] <;> omega
        · by_cases hjA : j = A
          · subst hjA; simp [hjB, hjQ]
          · simp [hjB, hjQ, hjA]
    · rfl

/-! ## One output bit -/

/-- Append the marker `true`, then the bit `[B ≠ 0]`, to `O` (counting in `P`); `B` back to `0`. -/
def bitE (O : Fin (ns + 1)) (B P : Fin nr) : WM ns nr :=
  .seq (emitC O P true) (.ifr B (.seq (emitC O P true) (.dec B)) (emitC O P false))

theorem bitE_spec (O : Fin (ns + 1)) (B P : Fin nr) (hBP : B ≠ P) (σ : WState ns nr) (c : Bool)
    (hb : σ.val B = if c then 1 else 0) (hO : σ.sh O = (σ.st O).length) (hP : σ.val P + 2 ≤ cap) (hB : 1 ≤ cap) :
    WExec cap (bitE O B P) σ
      ((((σ.sets O (σ.st O ++ [true, c])).seth O (σ.sh O + 2)).setv P (σ.val P + 2)).setv B 0) 18 := by
  have h1 := emitC_spec cap O P true σ hO (by omega)
  have hO1 : (((σ.sets O (σ.st O ++ [true])).seth O (σ.sh O + 1)).setv P (σ.val P + 1)).sh O =
      ((((σ.sets O (σ.st O ++ [true])).seth O (σ.sh O + 1)).setv P (σ.val P + 1)).st O).length := by
    simp [hO]
  cases c with
  | true =>
    have h2 := emitC_spec cap O P true (((σ.sets O (σ.st O ++ [true])).seth O (σ.sh O + 1)).setv P (σ.val P + 1))
      hO1 (by simp <;> omega)
    have hB1 : (((σ.sets O (σ.st O ++ [true])).seth O (σ.sh O + 1)).setv P (σ.val P + 1)).val B ≠ 0 := by
      simp [hBP, hb]
    have h3 := WExec.dec (cap := cap) B
      (((((((σ.sets O (σ.st O ++ [true])).seth O (σ.sh O + 1)).setv P (σ.val P + 1)).sets O
        ((((σ.sets O (σ.st O ++ [true])).seth O (σ.sh O + 1)).setv P (σ.val P + 1)).st O ++ [true])).seth O
        ((((σ.sets O (σ.st O ++ [true])).seth O (σ.sh O + 1)).setv P (σ.val P + 1)).sh O + 1)).setv P
        ((((σ.sets O (σ.st O ++ [true])).seth O (σ.sh O + 1)).setv P (σ.val P + 1)).val P + 1)))
      (by simp [hBP, hb] <;> omega)
    refine WExec.cast cap (WExec.seq h1 (WExec.ifrT hB1 (WExec.seq h2 h3))) ?_ (by omega)
    apply WState.eq
    · funext j
      by_cases hj : j = O
      · subst hj; simp <;> omega
      · simp [hj]
    · funext j
      by_cases hj : j = O
      · subst hj; simp
      · simp [hj]
    · funext j
      simp only [WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
      by_cases hjB : j = B
      · subst hjB; simp [hBP, hb]
      · by_cases hjP : j = P
        · subst hjP; simp [hjB] <;> omega
        · simp [hjB, hjP]
    · rfl
  | false =>
    have h2 := emitC_spec cap O P false (((σ.sets O (σ.st O ++ [true])).seth O (σ.sh O + 1)).setv P (σ.val P + 1))
      hO1 (by simp <;> omega)
    have hB0 : (((σ.sets O (σ.st O ++ [true])).seth O (σ.sh O + 1)).setv P (σ.val P + 1)).val B = 0 := by
      simp [hBP, hb]
    refine WExec.cast cap (WExec.seq h1 (WExec.ifrF hB0 h2)) ?_ (by omega)
    apply WState.eq
    · funext j
      by_cases hj : j = O
      · subst hj; simp <;> omega
      · simp [hj]
    · funext j
      by_cases hj : j = O
      · subst hj; simp
      · simp [hj]
    · funext j
      simp only [WState.setv_val, WState.sets_val, WState.seth_val, Function.update_apply]
      by_cases hjB : j = B
      · subst hjB; simp [hBP, hb]
      · by_cases hjP : j = P
        · subst hjP; simp [hjB] <;> omega
        · simp [hjB, hjP]
    · rfl

/-! ## Words -/

theorem bin_succ (w n : ℕ) : binary (w + 1) n = (n % 2 == 1) :: binary w (n / 2) := rfl

/-- The next bit goes at the end (low bit first). -/
theorem binary_snoc : ∀ (i g : ℕ), binary (i + 1) g = binary i g ++ [g / 2 ^ i % 2 == 1]
  | 0, g => by simp [binary]
  | i + 1, g => by
    rw [bin_succ (i + 1) g, binary_snoc i (g / 2), bin_succ i g, Nat.div_div_eq_div_mul, ← pow_succ']
    rfl

theorem frameP_snoc (w : List Bool) (b : Bool) : frameP (w ++ [b]) = frameP w ++ [true, b] := by
  simp [frameP]

theorem frameP_length : ∀ w : List Bool, (frameP w).length = 2 * w.length
  | [] => rfl
  | b :: w => by
    rw [frameP_cons, List.length_cons, List.length_cons, List.length_cons, frameP_length w]
    omega

/-! ## The rounds -/

/-- One round: count down `Rg 2`, halve `Rg 3` into `Rg 4` (quotient) and `Rg 5` (parity), append the marker and
the bit to `O` (counting in `Rg 7`), move the quotient back to `Rg 3`. -/
def stepB (O : Fin (ns + 1)) (Rg : Fin 8 → Fin nr) : WM ns nr :=
  .seq (.dec (Rg 2)) (.seq (halveR (Rg 3) (Rg 4) (Rg 5)) (.seq (bitE O (Rg 5) (Rg 7)) (WM.move (Rg 4) (Rg 3))))

/-- **The binary writer**: `Rg 3 := g`, `Rg 2 := k` (copies through `Rg 6`), `k` rounds, then clear `Rg 3`, append
the end marker and rewind `O` (by the position count `Rg 7`). -/
def binW (O : Fin (ns + 1)) (Rg : Fin 8 → Fin nr) : WM ns nr :=
  .seq (dupR (Rg 0) (Rg 3) (Rg 6)) (.seq (dupR (Rg 1) (Rg 2) (Rg 6)) (.seq (.whr (Rg 2) (stepB O Rg))
    (.seq (WM.clear (Rg 3)) (.seq (emitC O (Rg 7) false) (WM.rewind O (Rg 7))))))

/-- The writer's time bound. -/
def binCost (g k : ℕ) : ℕ := 60 * (g + 1) * (k + 1)

/-- The state after `i` rounds. -/
def stB (σ : WState ns nr) (O : Fin (ns + 1)) (Rg : Fin 8 → Fin nr) (g k i : ℕ) : WState ns nr :=
  ((((σ.sets O (frameP (binary i g))).seth O (2 * i)).setv (Rg 3) (g / 2 ^ i)).setv (Rg 2) (k - i)).setv (Rg 7)
    (2 * i)

theorem step_spec (O : Fin (ns + 1)) (Rg : Fin 8 → Fin nr) (hRg : Function.Injective Rg) (σ : WState ns nr)
    (g k i : ℕ) (hi : i < k) (h4 : σ.val (Rg 4) = 0) (h5 : σ.val (Rg 5) = 0) (hcap : g + 2 * k + 2 ≤ cap) :
    WExec cap (stepB O Rg) (stB σ O Rg g k i) (stB σ O Rg g k (i + 1)) (9 * g + 30) := by
  have hne : ∀ a b : Fin 8, a ≠ b → Rg a ≠ Rg b := fun a b h => hRg.ne h
  obtain ⟨a, ha_def⟩ : ∃ a, a = g / 2 ^ i := ⟨_, rfl⟩
  have ha : a ≤ g := by rw [ha_def]; exact Nat.div_le_self _ _
  have hdiv : a / 2 = g / 2 ^ (i + 1) := by rw [ha_def, Nat.div_div_eq_div_mul, pow_succ]
  have e2 : (stB σ O Rg g k i).val (Rg 2) = k - i := by simp [stB, Function.update_apply, hRg.eq_iff]
  have e3 : (stB σ O Rg g k i).val (Rg 3) = a := by simp [stB, Function.update_apply, hRg.eq_iff, ha_def]
  have e4 : (stB σ O Rg g k i).val (Rg 4) = 0 := by simp [stB, Function.update_apply, hRg.eq_iff, h4]
  have e5 : (stB σ O Rg g k i).val (Rg 5) = 0 := by simp [stB, Function.update_apply, hRg.eq_iff, h5]
  have e7 : (stB σ O Rg g k i).val (Rg 7) = 2 * i := by simp [stB, Function.update_apply, hRg.eq_iff]
  have eO : (stB σ O Rg g k i).st O = frameP (binary i g) := by simp [stB]
  have eH : (stB σ O Rg g k i).sh O = 2 * i := by simp [stB]
  -- count down
  obtain ⟨S1, hS1⟩ : ∃ S : WState ns nr, S = (stB σ O Rg g k i).setv (Rg 2) (k - i - 1) := ⟨_, rfl⟩
  have hd : WExec cap (.dec (Rg 2)) (stB σ O Rg g k i) S1 1 := by
    have h := WExec.dec (cap := cap) (Rg 2) (stB σ O Rg g k i) (by rw [e2]; omega)
    rw [e2] at h
    rw [hS1]
    exact h
  have f3 : S1.val (Rg 3) = a := by rw [hS1, wsetv_val_ne _ _ (hne 3 2 (by decide)), e3]
  have f4 : S1.val (Rg 4) = 0 := by rw [hS1, wsetv_val_ne _ _ (hne 4 2 (by decide)), e4]
  have f5 : S1.val (Rg 5) = 0 := by rw [hS1, wsetv_val_ne _ _ (hne 5 2 (by decide)), e5]
  -- halve
  obtain ⟨S2, hS2⟩ : ∃ S : WState ns nr, S = ((S1.setv (Rg 3) 0).setv (Rg 4) (0 + a / 2)).setv (Rg 5) (a % 2) :=
    ⟨_, rfl⟩
  have hh : WExec cap (halveR (Rg 3) (Rg 4) (Rg 5)) S1 S2 (5 * a + 4) := by
    have h := halve_spec cap (Rg 3) (Rg 4) (Rg 5) (hne 3 4 (by decide)) (hne 3 5 (by decide)) (hne 4 5 (by decide))
      a S1 f3 (by omega) (by rw [f4]; omega) f5 (by omega)
    rw [f4] at h
    rw [hS2]
    exact h
  have f2O : S2.st O = frameP (binary i g) := by rw [hS2, hS1]; simp only [WState.setv_st]; exact eO
  have f2H : S2.sh O = 2 * i := by rw [hS2, hS1]; simp only [WState.setv_sh]; exact eH
  have f25 : S2.val (Rg 5) = if (a % 2 == 1) then 1 else 0 := by
    rw [hS2, wsetv_val_self]
    rcases Nat.mod_two_eq_zero_or_one a with h | h <;> simp [h]
  have f27 : S2.val (Rg 7) = 2 * i := by
    rw [hS2, wsetv_val_ne _ _ (hne 7 5 (by decide)), wsetv_val_ne _ _ (hne 7 4 (by decide)),
      wsetv_val_ne _ _ (hne 7 3 (by decide)), hS1, wsetv_val_ne _ _ (hne 7 2 (by decide)), e7]
  -- the bit
  obtain ⟨S3, hS3⟩ : ∃ S : WState ns nr, S = (((S2.sets O (frameP (binary i g) ++ [true, a % 2 == 1])).seth O
      (2 * i + 2)).setv (Rg 7) (2 * i + 2)).setv (Rg 5) 0 := ⟨_, rfl⟩
  have hb : WExec cap (bitE O (Rg 5) (Rg 7)) S2 S3 18 := by
    have h := bitE_spec cap O (Rg 5) (Rg 7) (hne 5 7 (by decide)) S2 (a % 2 == 1) f25
      (by rw [f2H, f2O, frameP_length, binary_length]) (by rw [f27]; omega) (by omega)
    rw [f2O, f2H, f27] at h
    rw [hS3]
    exact h
  have f34 : S3.val (Rg 4) = a / 2 := by
    rw [hS3, hS2]; simp [Function.update_apply, hRg.eq_iff]
  have f33 : S3.val (Rg 3) = 0 := by
    rw [hS3, hS2]; simp [Function.update_apply, hRg.eq_iff]
  -- the quotient back
  obtain ⟨S4, hS4⟩ : ∃ S : WState ns nr, S = (S3.setv (Rg 4) 0).setv (Rg 3) (0 + a / 2) := ⟨_, rfl⟩
  have hm : WExec cap (WM.move (Rg 4) (Rg 3)) S3 S4 (7 * (a / 2) + 1) := by
    have h := wmove_spec cap (Rg 4) (Rg 3) (hne 4 3 (by decide)) (a / 2) S3 f34 (by rw [f34]; omega)
      (by rw [f33, f34]; omega)
    rw [f33, f34] at h
    rw [hS4]
    exact h
  refine WExec.cast cap (WExec.seq hd (WExec.seq hh (WExec.seq hb hm))) ?_ (by omega)
  rw [hS4, hS3, hS2, hS1]
  apply WState.eq
  · funext j
    by_cases hj : j = O
    · subst hj; simp [stB] <;> omega
    · simp [stB, hj]
  · funext j
    by_cases hj : j = O
    · subst hj; simp [stB, binary_snoc, frameP_snoc, ha_def]
    · simp [stB, hj]
  · funext j
    by_cases j2 : j = Rg 2
    · subst j2; simp [stB, Function.update_apply, hRg.eq_iff] <;> omega
    · by_cases j3 : j = Rg 3
      · subst j3; simp [stB, Function.update_apply, hRg.eq_iff, hdiv]
      · by_cases j4 : j = Rg 4
        · subst j4; simp [stB, Function.update_apply, hRg.eq_iff, h4]
        · by_cases j5 : j = Rg 5
          · subst j5; simp [stB, Function.update_apply, hRg.eq_iff, h5]
          · by_cases j7 : j = Rg 7
            · subst j7; simp [stB, Function.update_apply, hRg.eq_iff] <;> omega
            · simp [stB, Function.update_apply, j2, j3, j4, j5, j7]
  · rfl

theorem loop_spec (O : Fin (ns + 1)) (Rg : Fin 8 → Fin nr) (hRg : Function.Injective Rg) (σ : WState ns nr)
    (g k c : ℕ) (hc : 9 * g + 32 ≤ c) (h4 : σ.val (Rg 4) = 0) (h5 : σ.val (Rg 5) = 0) (hcap : g + 2 * k + 2 ≤ cap) :
    ∀ j i : ℕ, i + j = k →
      WExec cap (.whr (Rg 2) (stepB O Rg)) (stB σ O Rg g k i) (stB σ O Rg g k k) (j * c + 1)
  | 0, i, h => by
    have hi : i = k := by omega
    subst hi
    exact WExec.mono (WExec.whrF (by simp [stB, Function.update_apply, hRg.eq_iff])) (by omega)
  | j + 1, i, h => by
    have hs := step_spec cap O Rg hRg σ g k i (by omega) h4 h5 hcap
    have ih := loop_spec O Rg hRg σ g k c hc h4 h5 hcap j (i + 1) (by omega)
    refine WExec.mono (WExec.whrT ?_ hs ih) ?_
    · simp [stB, Function.update_apply, hRg.eq_iff] <;> omega
    · have e : (j + 1) * c = j * c + c := by ring
      rw [e]; omega

/-- **The binary writer** (X1 (b)): from `Rg 0 = g`, `Rg 1 = k`, the scratch `Rg 2 … Rg 7` at `0` and the blank
stream `O` (head `0`), exactly `frame (binary k g)` on `O` (head `0`), everything else as at entry. -/
theorem binW_spec (O : Fin (ns + 1)) (Rg : Fin 8 → Fin nr) (hRg : Function.Injective Rg) (σ : WState ns nr)
    (g k : ℕ) (hG : σ.val (Rg 0) = g) (hK : σ.val (Rg 1) = k) (hz : ∀ j : Fin 8, 2 ≤ j.val → σ.val (Rg j) = 0)
    (hO : σ.st O = []) (hOh : σ.sh O = 0) (hcap : g + 2 * k + 2 ≤ cap) :
    WExec cap (binW O Rg) σ (σ.sets O (frame (binary k g))) (binCost g k) := by
  have hne : ∀ a b : Fin 8, a ≠ b → Rg a ≠ Rg b := fun a b h => hRg.ne h
  have z2 := hz 2 (by decide)
  have z3 := hz 3 (by decide)
  have z4 := hz 4 (by decide)
  have z5 := hz 5 (by decide)
  have z6 := hz 6 (by decide)
  have z7 := hz 7 (by decide)
  have d1 := dupR_spec cap (Rg 0) (Rg 3) (Rg 6) (hne 0 3 (by decide)) (hne 0 6 (by decide)) (hne 3 6 (by decide))
    σ g hG z3 z6 (by omega)
  have d2 := dupR_spec cap (Rg 1) (Rg 2) (Rg 6) (hne 1 2 (by decide)) (hne 1 6 (by decide)) (hne 2 6 (by decide))
    (σ.setv (Rg 3) g) k (by rw [wsetv_val_ne _ _ (hne 1 3 (by decide)), hK])
    (by rw [wsetv_val_ne _ _ (hne 2 3 (by decide)), z2]) (by rw [wsetv_val_ne _ _ (hne 6 3 (by decide)), z6])
    (by omega)
  have e0 : (σ.setv (Rg 3) g).setv (Rg 2) k = stB σ O Rg g k 0 := by
    apply WState.eq
    · funext j
      by_cases hj : j = O
      · subst hj; simp [stB, hOh]
      · simp [stB, hj]
    · funext j
      by_cases hj : j = O
      · subst hj; simp [stB, hO, binary]
      · simp [stB, hj]
    · funext j
      by_cases j7 : j = Rg 7
      · subst j7; simp [stB, Function.update_apply, hRg.eq_iff, z7]
      · simp [stB, Function.update_apply, j7]
    · rfl
  rw [e0] at d2
  have lp := loop_spec cap O Rg hRg σ g k (9 * g + 32) le_rfl z4 z5 hcap k 0 (by omega)
  obtain ⟨b, hb_def⟩ : ∃ b, b = g / 2 ^ k := ⟨_, rfl⟩
  have hb : b ≤ g := by rw [hb_def]; exact Nat.div_le_self _ _
  have k3 : (stB σ O Rg g k k).val (Rg 3) = b := by simp [stB, Function.update_apply, hRg.eq_iff, hb_def]
  have cl := wclear_spec cap (Rg 3) b (stB σ O Rg g k k) k3 (by rw [k3]; omega)
  have k5O : ((stB σ O Rg g k k).setv (Rg 3) 0).sh O = (((stB σ O Rg g k k).setv (Rg 3) 0).st O).length := by
    simp [stB, frameP_length]
  have k57 : ((stB σ O Rg g k k).setv (Rg 3) 0).val (Rg 7) = 2 * k := by
    simp [stB, Function.update_apply, hRg.eq_iff]
  have em := emitC_spec cap O (Rg 7) false ((stB σ O Rg g k k).setv (Rg 3) 0) k5O (by rw [k57]; omega)
  rw [k57] at em
  have rw7 := wrewind_spec cap O (Rg 7) (2 * k + 1)
    (((((stB σ O Rg g k k).setv (Rg 3) 0).sets O (((stB σ O Rg g k k).setv (Rg 3) 0).st O ++ [false])).seth O
      (((stB σ O Rg g k k).setv (Rg 3) 0).sh O + 1)).setv (Rg 7) (2 * k + 1)) (by simp) (by simp <;> omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq lp (WExec.seq cl (WExec.seq em rw7))))) ?_ ?_
  · apply WState.eq
    · funext j
      by_cases hj : j = O
      · subst hj; simp [stB, hOh]
      · simp [stB, hj]
    · funext j
      by_cases hj : j = O
      · subst hj; simp [stB, frame_eq_frameP]
      · simp [stB, hj]
    · funext j
      by_cases j2 : j = Rg 2
      · subst j2; simp [stB, Function.update_apply, hRg.eq_iff, z2]
      · by_cases j3 : j = Rg 3
        · subst j3; simp [stB, Function.update_apply, hRg.eq_iff, z3]
        · by_cases j7 : j = Rg 7
          · subst j7; simp [stB, Function.update_apply, hRg.eq_iff, z7]
          · simp [stB, Function.update_apply, j2, j3, j7]
    · rfl
  · unfold binCost
    have e1 : k * (9 * g + 32) = 9 * (g * k) + 32 * k := by ring
    have e2 : 60 * (g + 1) * (k + 1) = 60 * (g * k) + 60 * g + 60 * k + 60 := by ring
    rw [e1, e2]
    omega

/-- **The walk bank's index word of the seed of index `g`** (X1 (c)): `binW` at `k = 160·n + 2r`
(`n = 2(errExp/4)`, `r = wOf fieldBits labelBits · 128`) writes `frame (seedIndexWord r n (seedCopy P e))` for the seed
`e = (gapSeedEquiv P).symm g` (`SeedIdx.seedIndex_cast`). -/
theorem seedIndex_write (O : Fin (ns + 1)) (Rg : Fin 8 → Fin nr) (hRg : Function.Injective Rg) (σ : WState ns nr)
    (P : WireExponent3_5.Filters.GapParams) (g : ℕ) (hg : g < Fintype.card (WireExponent3_5.Filters.GapSeed P))
    (hG : σ.val (Rg 0) = g)
    (hK : σ.val (Rg 1) = 160 * (2 * (P.errExp / 4)) + 2 * (FinalPass.Filt.wOf P.fieldBits P.labelBits * 128))
    (hz : ∀ j : Fin 8, 2 ≤ j.val → σ.val (Rg j) = 0) (hO : σ.st O = []) (hOh : σ.sh O = 0)
    (hcap : g + 2 * (160 * (2 * (P.errExp / 4)) + 2 * (FinalPass.Filt.wOf P.fieldBits P.labelBits * 128)) + 2 ≤ cap) :
    WExec cap (binW O Rg) σ
      (σ.sets O (frame (PrimT.WalkBank.seedIndexWord (FinalPass.Filt.wOf P.fieldBits P.labelBits * 128)
        (2 * (P.errExp / 4)) (SeedIdx.seedCopy P ((PrimAsm.Enum.gapSeedEquiv P).symm ⟨g, hg⟩)))))
      (binCost g (160 * (2 * (P.errExp / 4)) + 2 * (FinalPass.Filt.wOf P.fieldBits P.labelBits * 128))) := by
  rw [SeedIdx.seedIndex_cast]
  exact binW_spec cap O Rg hRg σ g _ hG hK hz hO hOh hcap

end NearCubicWires.WireExponent3_5.UnionMachine.BinW
