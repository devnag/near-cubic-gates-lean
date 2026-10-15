import Proof.Gates.WorkerArith.VerdictFinal
import Proof.Gates.Codec.Unframe
import Proof.Wire_3_5.CompilerMachineEmitPad
import Proof.Gates.Interfaces.WordFn

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.RepairRepresentation (natWord)

variable {ns nr : ℕ}

/-! ## A width-`k` zero from a register (same program as `Expand.initNum`) -/

theorem writeTapeBit_mid' : ∀ (p q : List Bool) (b : Bool), writeTapeBit (p ++ q) p.length b = p ++ b :: q.drop 1
  | [], [], b => rfl
  | [], _ :: q, b => rfl
  | a :: p, q, b => by
    show a :: writeTapeBit (p ++ q) p.length b = a :: (p ++ b :: q.drop 1)
    rw [writeTapeBit_mid' p q b]

theorem writeTapeBit_end (p : List Bool) (b : Bool) : writeTapeBit p p.length b = p ++ [b] := by
  have := writeTapeBit_mid' p [] b; simpa using this

/-- `[true, false]` repeated. -/
def zpfx (j : ℕ) : List Bool := (List.replicate j [true, false]).flatten

theorem zpfx_length (j : ℕ) : (zpfx j).length = 2 * j := by
  induction j with
  | zero => rfl
  | succ j ih => simp [zpfx, List.replicate_succ', List.flatten_append] at ih ⊢; omega

theorem zpfx_succ (j : ℕ) : zpfx (j + 1) = zpfx j ++ [true, false] := by
  simp [zpfx, List.replicate_succ', List.flatten_append]

theorem frame_binary_zero (k : ℕ) : frame (binary k 0) = zpfx k ++ [false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have : binary (k + 1) 0 = false :: binary k 0 := by simp [binary]
    rw [this, frame, ih]
    simp [zpfx, List.replicate_succ]

section Init
variable (X : Fin (ns + 1)) (K K2 : Fin nr)

def initNum : WMX ns nr :=
  .seq (repK K K2 (.seq (WMX.wr X true) (.seq (WMX.fwd X) (.seq (WMX.wr X false) (WMX.fwd X)))))
    (.seq (WMX.wr X false) (repK K K2 (.seq (WMX.bwd X) (WMX.bwd X))))

def initCost (k : ℕ) : ℕ := (k * (7 + 8) + 7 * k + 3) + 1 + (1 + 1 + (k * (3 + 8) + 7 * k + 3))

variable {X K K2}

theorem initNum_spec (cap : ℕ) (hK : K ≠ K2) (σ : WState ns nr) (k : ℕ) (hlen : (σ.st X).length ≤ 2 * k + 1)
    (hXh : σ.sh X = 0) (hKv : σ.val K = k) (hK2 : σ.val K2 = 0) (hcap : 2 * k ≤ cap) :
    WXExec cap (initNum X K K2) σ (σ.sets X (frame (binary k 0))) (initCost k) := by
  set old := σ.st X with hold
  have h1 := Runs.repE (cap := cap) (body := .seq (WMX.wr X true) (.seq (WMX.fwd X) (.seq (WMX.wr X false)
    (WMX.fwd X)))) hK 7 k (fun j => (σ.sets X (zpfx j ++ old.drop (2 * j))).seth X (2 * j)) hcap
    (fun j => by simp) (fun j => by simp)
    (fun j _ v1 v2 => by
      set τ := (((σ.sets X (zpfx j ++ old.drop (2 * j))).seth X (2 * j)).setv K v1).setv K2 v2 with hτ
      have e1 := WXExec.wr cap X true τ
      have hp1 : writeTapeBit (τ.st X) (τ.sh X) true = zpfx j ++ true :: (old.drop (2 * j)).drop 1 := by
        rw [hτ]; simp only [WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          Function.update_self]
        rw [← zpfx_length j, writeTapeBit_mid']
      rw [hp1] at e1
      set τ1 := τ.sets X (zpfx j ++ true :: (old.drop (2 * j)).drop 1) with hτ1
      have e2 := WXExec.fwd cap X τ1
      set τ2 := τ1.seth X (τ1.sh X + 1) with hτ2
      have e3 := WXExec.wr cap X false τ2
      have hp3 : writeTapeBit (τ2.st X) (τ2.sh X) false =
          zpfx (j + 1) ++ (old.drop (2 * (j + 1))) := by
        rw [hτ2, hτ1, hτ]
        simp only [WState.seth_st, WState.sets_st, WState.setv_st, WState.seth_sh, WState.sets_sh, WState.setv_sh,
          Function.update_self]
        have : 2 * j + 1 = (zpfx j ++ [true]).length := by simp [zpfx_length]
        rw [this, show zpfx j ++ true :: (old.drop (2 * j)).drop 1 = (zpfx j ++ [true]) ++ (old.drop (2 * j)).drop 1
          by simp, writeTapeBit_mid', zpfx_succ]
        simp only [List.drop_drop, List.append_assoc, List.cons_append, List.singleton_append, List.nil_append]
        rw [show 2 * j + 1 + 1 = 2 * (j + 1) by ring]
      rw [hp3] at e3
      have e4 := WXExec.fwd cap X (τ2.sets X (zpfx (j + 1) ++ old.drop (2 * (j + 1))))
      refine (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))).cast cap ?_ (by omega)
      apply WState.eq
      · funext i; by_cases hi : i = X
        · subst hi; simp [hτ2, hτ1, hτ]; ring
        · simp [hτ2, hτ1, hτ, Function.update_of_ne hi]
      · funext i; by_cases hi : i = X
        · subst hi; simp [hτ2, hτ1, hτ]
        · simp [hτ2, hτ1, hτ, Function.update_of_ne hi]
      · simp [hτ2, hτ1, hτ]
      · simp [hτ2, hτ1, hτ]) (by simp [hKv]) (by simp [hK2])
  have e0 : (σ.sets X (zpfx 0 ++ old.drop (2 * 0))).seth X (2 * 0) = σ := by
    apply WState.eq
    · funext i; by_cases hi : i = X
      · subst hi; simp [hXh]
      · simp [Function.update_of_ne hi]
    · funext i; by_cases hi : i = X
      · subst hi; simp [zpfx, hold]
      · simp [Function.update_of_ne hi]
    · rfl
    · rfl
  rw [e0] at h1
  set ρ := (σ.sets X (zpfx k ++ old.drop (2 * k))).seth X (2 * k) with hρ
  have hw := WXExec.wr cap X false ρ
  have hfin : writeTapeBit (ρ.st X) (ρ.sh X) false = frame (binary k 0) := by
    rw [hρ]; simp only [WState.seth_st, WState.sets_st, WState.seth_sh, Function.update_self]
    rw [← zpfx_length k, writeTapeBit_mid', frame_binary_zero]
    have : (old.drop (zpfx k).length).drop 1 = [] := by
      rw [List.drop_drop, zpfx_length]; exact List.drop_eq_nil_of_le (by omega)
    rw [this]
  rw [hfin] at hw
  have h2 := Runs.repE (cap := cap) (body := .seq (WMX.bwd X) (WMX.bwd X)) hK 3 k
    (fun j => (σ.sets X (frame (binary k 0))).seth X (2 * k - 2 * j)) hcap (fun j => by simp) (fun j => by simp)
    (fun j _ v1 v2 => by
      refine (WXExec.seq (WXExec.bwd cap X _) (WXExec.bwd cap X _)).cast cap ?_ (by omega)
      apply WState.eq
      · funext i; by_cases hi : i = X
        · subst hi; simp; omega
        · simp [Function.update_of_ne hi]
      · rfl
      · rfl
      · rfl) (by simp [hKv]) (by simp [hK2])
  have e5 : (σ.sets X (frame (binary k 0))).seth X (2 * k - 2 * 0) = ρ.sets X (frame (binary k 0)) := by
    apply WState.eq
    · funext i; by_cases hi : i = X
      · subst hi; simp [hρ]
      · simp [hρ, Function.update_of_ne hi]
    · funext i; by_cases hi : i = X
      · subst hi; simp [hρ]
      · simp [hρ, Function.update_of_ne hi]
    · rfl
    · rfl
  have e6 : (σ.sets X (frame (binary k 0))).seth X (2 * k - 2 * k) = σ.sets X (frame (binary k 0)) := by
    apply WState.eq
    · funext i; by_cases hi : i = X
      · subst hi; simp [hXh]
      · simp [Function.update_of_ne hi]
    · rfl
    · rfl
    · rfl
  rw [e5, e6] at h2
  exact (WXExec.seq h1 (WXExec.seq hw h2)).mono (by unfold initCost; omega)

end Init

/-! ## All number streams -/

/-- `initNum` on every stream of a list (width in register `7`, scratch `9`). -/
def initAll : List (Fin 30) → WMX 29 16
  | [] => WMX.skip
  | X :: l => .seq (initNum X 7 9) (initAll l)

/-- The streams of a list set to the width-`W` zero. -/
def setsZ (W : ℕ) : List (Fin 30) → WState 29 16 → WState 29 16
  | [], σ => σ
  | X :: l, σ => setsZ W l (σ.sets X (frame (binary W 0)))

theorem setsZ_sh (W : ℕ) : ∀ (l : List (Fin 30)) (σ : WState 29 16), (setsZ W l σ).sh = σ.sh
  | [], _ => rfl
  | X :: l, σ => by rw [setsZ, setsZ_sh W l]; rfl

theorem setsZ_val (W : ℕ) : ∀ (l : List (Fin 30)) (σ : WState 29 16), (setsZ W l σ).val = σ.val
  | [], _ => rfl
  | X :: l, σ => by rw [setsZ, setsZ_val W l]; rfl

theorem setsZ_cell (W : ℕ) : ∀ (l : List (Fin 30)) (σ : WState 29 16), (setsZ W l σ).cell = σ.cell
  | [], _ => rfl
  | X :: l, σ => by rw [setsZ, setsZ_cell W l]; rfl

theorem setsZ_st (W : ℕ) : ∀ (l : List (Fin 30)) (σ : WState 29 16) (i : Fin 30),
    (setsZ W l σ).st i = if i ∈ l then frame (binary W 0) else σ.st i
  | [], _, i => by simp [setsZ]
  | X :: l, σ, i => by
    rw [setsZ, setsZ_st W l]
    by_cases h : i ∈ l
    · simp [h]
    · by_cases hX : i = X
      · subst hX; simp [h]
      · simp [h, hX, Function.update_of_ne hX]

theorem initAllM (W cap : ℕ) (hcap : 2 * W ≤ cap) : ∀ (l : List (Fin 30)) (σ : WState 29 16),
    (∀ X ∈ l, (σ.st X).length ≤ 2 * W + 1 ∧ σ.sh X = 0) → σ.val 7 = W → σ.val 9 = 0 →
      WXExec cap (initAll l) σ (setsZ W l σ) (l.length * (initCost W + 1))
  | [], σ, _, _, _ => by simpa [initAll, setsZ] using WXExec.skip cap σ
  | X :: l, σ, hl, h7, h9 => by
    have e1 := initNum_spec cap (X := X) (K := 7) (K2 := 9) (by decide) σ W (hl X (by simp)).1 (hl X (by simp)).2
      h7 h9 hcap
    have e2 := initAllM W cap hcap l (σ.sets X (frame (binary W 0)))
      (fun Y hY => by
        by_cases hYX : Y = X
        · subst hYX; refine ⟨by simp [frame_binary_zero, zpfx_length], (hl Y (by simp)).2⟩
        · exact ⟨by simpa [Function.update_of_ne hYX] using (hl Y (by simp [hY])).1, (hl Y (by simp [hY])).2⟩)
      h7 h9
    refine (WXExec.seq e1 e2).mono ?_
    simp only [List.length_cons]; ring_nf; omega

/-! ## The ruler `0 1^L` on stream `3` -/

/-- Write `0 1^L` (`L` in register `8`) on the empty stream `3` and rewind it (scratch `9`, `14`, `4`). -/
def rulerP : WMX 29 16 :=
  .seq (WMX.wr 3 false) (.seq (WMX.fwd 3) (.seq (repK 8 9 (.seq (WMX.wr 3 true) (WMX.fwd 3)))
    (.seq (addR 8 14 4) (.seq (WMX.inc 14) (.wm (WM.rewind 3 14))))))

theorem rulerM (cap L : ℕ) (σ : WState 29 16) (h3 : σ.st 3 = []) (h3h : σ.sh 3 = 0) (h8 : σ.val 8 = L)
    (h9 : σ.val 9 = 0) (h14 : σ.val 14 = 0) (h4 : σ.val 4 = 0) (hcap : 2 * L + 2 ≤ cap) :
    WXExec cap rulerP σ (σ.sets 3 (ruler L)) (50 * L + 50) := by
  have e1 := WXExec.wr cap 3 false σ
  rw [h3, h3h] at e1
  have e2 := WXExec.fwd cap 3 (σ.sets 3 (writeTapeBit [] 0 false))
  set st : ℕ → WState 29 16 := fun j => (σ.sets 3 (false :: List.replicate j true)).seth 3 (j + 1) with hst
  have e2' : WXExec cap (WMX.fwd 3) (σ.sets 3 (writeTapeBit [] 0 false)) (st 0) 1 := by
    refine e2.cast cap ?_ le_rfl
    apply WState.eq <;> try rfl
    funext i; by_cases hi : i = 3
    · subst hi; simp [hst, h3h]
    · simp [hst, Function.update_of_ne hi]
  have e3 := Runs.repE (cap := cap) (body := .seq (WMX.wr 3 true) (WMX.fwd 3)) (K := 8) (K2 := 9) (by decide) 3 L st
    (by omega) (fun k => by simp [hst]) (fun k => by simp [hst])
    (fun j _ v1 v2 => by
      have a1 := WXExec.wr cap 3 true (((st j).setv 8 v1).setv 9 v2)
      have hw : writeTapeBit ((((st j).setv 8 v1).setv 9 v2).st 3) ((((st j).setv 8 v1).setv 9 v2).sh 3) true =
          false :: List.replicate (j + 1) true := by
        simp only [hst, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_sh, WState.seth_sh,
          Function.update_self]
        have := writeTapeBit_end (false :: List.replicate j true) true
        simp only [List.length_cons, List.length_replicate] at this
        rw [this, List.replicate_succ']; rfl
      rw [hw] at a1
      refine (WXExec.seq a1 (WXExec.fwd cap 3 _)).cast cap ?_ (by omega)
      apply WState.eq
      · funext i; by_cases hi : i = 3
        · subst hi; simp [hst]
        · simp [hst, Function.update_of_ne hi]
      · funext i; by_cases hi : i = 3
        · subst hi; simp [hst]
        · simp [hst, Function.update_of_ne hi]
      · rfl
      · rfl) (by simp [hst, h8]) (by simp [hst, h9])
  have e4 := addR_spec cap (A := 8) (B := 14) (T := 4) (by decide) (by decide) (by decide) (st L)
    (by simp [hst, h4]) (by simp [hst, h14, h8]; omega)
  have v14 : (st L).val 14 + (st L).val 8 = L := by simp [hst, h14, h8]
  rw [v14] at e4
  have e5 := WXExec.inc cap 14 ((st L).setv 14 L) (by simp; omega)
  have e6 := wrewind_spec (cap := cap) (3 : Fin 30) (14 : Fin 16) (L + 1)
    (((st L).setv 14 L).setv 14 (((st L).setv 14 L).val 14 + 1)) (by simp) (by simp; omega)
  refine (WXExec.seq e1 (WXExec.seq e2' (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.wm e6)))))).cast cap
    ?_ (by simp [hst, h8]; omega)
  apply WState.eq
  · funext i; by_cases hi : i = 3
    · subst hi; simp [hst, h3h]
    · simp [hst, Function.update_of_ne hi]
  · funext i; by_cases hi : i = 3
    · subst hi; simp [hst, ruler]
    · simp [hst, Function.update_of_ne hi]
  · funext q; by_cases hq : q = 14
    · subst hq; simp [hst, h14]
    · simp [hst, Function.update_of_ne hq]
  · simp [hst]

/-! ## Register arithmetic of the set-up -/

/-- `k` times `B := B + A` (scratch register `4`). -/
def addRs (A B : Fin 16) : ℕ → WMX 29 16
  | 0 => WMX.skip
  | k + 1 => .seq (addRs A B k) (addR A B 4)

theorem addRsM (cap : ℕ) {A B : Fin 16} (hAB : A ≠ B) (hA4 : A ≠ 4) (hB4 : B ≠ 4) :
    ∀ (k : ℕ) (σ : WState 29 16), σ.val 4 = 0 → σ.val B + k * σ.val A ≤ cap →
      WXExec cap (addRs A B k) σ (σ.setv B (σ.val B + k * σ.val A)) (k * (18 * σ.val A + 4))
  | 0, σ, _, _ => by simpa [addRs, wsetv_same] using WXExec.skip cap σ
  | k + 1, σ, h4, hc => by
    have e1 := addRsM cap hAB hA4 hB4 k σ h4 (by nlinarith)
    set τ := σ.setv B (σ.val B + k * σ.val A) with hτ
    have e2 := addR_spec cap (A := A) (B := B) (T := 4) hAB hA4 hB4 τ (by simp [hτ, Function.update_of_ne
      (Ne.symm hB4), h4]) (by simp [hτ, Function.update_of_ne hAB]; nlinarith)
    have v : τ.val B + τ.val A = σ.val B + (k + 1) * σ.val A := by simp [hτ, Function.update_of_ne hAB]; ring
    have vA : τ.val A = σ.val A := by simp [hτ, Function.update_of_ne hAB]
    rw [v, vA, hτ, wsetv_setv] at e2
    exact (WXExec.seq e1 e2).mono (by nlinarith)

/-- `k` increments of register `B`. -/
def rincs (B : Fin 16) : ℕ → WMX 29 16
  | 0 => WMX.skip
  | k + 1 => .seq (rincs B k) (WMX.inc B)

theorem rincsM (cap : ℕ) (B : Fin 16) : ∀ (k : ℕ) (σ : WState 29 16), σ.val B + k ≤ cap →
    WXExec cap (rincs B k) σ (σ.setv B (σ.val B + k)) (4 * k)
  | 0, σ, _ => by simpa [rincs, wsetv_same] using WXExec.skip cap σ
  | k + 1, σ, hc => by
    have e1 := rincsM cap B k σ (by omega)
    have e2 := WXExec.inc cap B (σ.setv B (σ.val B + k)) (by simp; omega)
    simp only [WState.setv_val, Function.update_self, wsetv_setv] at e2
    rw [show σ.val B + k + 1 = σ.val B + (k + 1) by ring] at e2
    exact (WXExec.seq e1 e2).mono (by omega)

/-! ## The set-up -/

/-- The number streams `4 … 29`. -/
def numList : List (Fin 30) := (List.finRange 30).filter (fun i => decide (4 ≤ i.val))

theorem mem_numList (i : Fin 30) : i ∈ numList ↔ 4 ≤ i.val := by simp [numList]

/-- The set-up program (`B` the width slack: `W = 10L + B`). -/
def setupP (B : ℕ) : WMX 29 16 :=
  .seq (BinW.width 0 8 4) (.seq (addR 8 14 4) (.seq (addRs 8 15 2) (.seq (addRs 8 7 10) (.seq (rincs 7 B)
    (.seq (addRs 7 6 2) (.seq (WMX.inc 6) (.seq (.wm (Codec.unframeW 0 2 13 14)) (.seq (.wm (WM.rewind 0 15))
      (.seq (.wm (WM.rewind 2 13)) (.seq rulerP (initAll numList)))))))))))

theorem prefixBits_self (w : List Bool) : Codec.prefixBits w w.length = w := by
  apply List.ext_getElem
  · simp [Codec.prefixBits]
  · intro n h1 h2; simp [Codec.prefixBits, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

/-- **The set-up**: from the cold start to the state at rest with all numbers `0`. -/
theorem setupM (w : List Bool) (B cap : ℕ) (hcap : 4 * (10 * w.length + B) + 4 ≤ cap) :
    WXExec cap (setupP B) (NearCubicGates.Close.Interfaces.startState 29 16 w)
      (mk w (10 * w.length + B) (fun _ => 0) 0 0 0) (2000 * (10 * w.length + B + 1) ^ 2) := by
  set L := w.length with hL
  set W := 10 * L + B with hW
  set σ0 := NearCubicGates.Close.Interfaces.startState 29 16 w with hσ0
  have hA : NumOn σ0 0 L (NearCubicWires.RepairOrdinary.RadixSemantics.value w) := by
    refine ⟨?_, rfl⟩
    show (if (0 : Fin 30).val = 0 then frame w else []) = _
    simp only [Fin.val_zero, ↓reduceIte]
    rw [hL, NearCubicWires.WireExponent3_5.CompilerMachine.Emit.binary_value_self]
  have e1 := BinW.width_spec cap (A := 0) (K := 8) (T := 4) (by decide) L _ σ0 hA rfl rfl (by omega)
  set σ1 := σ0.setv 8 L with hσ1
  have e2 := addR_spec cap (A := 8) (B := 14) (T := 4) (by decide) (by decide) (by decide) σ1 (by simp [hσ1, hσ0,
    NearCubicGates.Close.Interfaces.startState]) (by simp [hσ1, hσ0, NearCubicGates.Close.Interfaces.startState]; omega)
  have v2 : σ1.val 14 + σ1.val 8 = L := by simp [hσ1, hσ0, NearCubicGates.Close.Interfaces.startState]
  rw [v2] at e2
  set σ2 := σ1.setv 14 L with hσ2
  have e3 := addRsM cap (A := 8) (B := 15) (by decide) (by decide) (by decide) 2 σ2
    (by simp [hσ2, hσ1, hσ0, NearCubicGates.Close.Interfaces.startState])
    (by simp [hσ2, hσ1, hσ0, NearCubicGates.Close.Interfaces.startState]; omega)
  have v3 : σ2.val 15 + 2 * σ2.val 8 = 2 * L := by simp [hσ2, hσ1, hσ0, NearCubicGates.Close.Interfaces.startState]
  have v3' : σ2.val 8 = L := by simp [hσ2, hσ1]
  rw [v3, v3'] at e3
  set σ3 := σ2.setv 15 (2 * L) with hσ3
  have e4 := addRsM cap (A := 8) (B := 7) (by decide) (by decide) (by decide) 10 σ3
    (by simp [hσ3, hσ2, hσ1, hσ0, NearCubicGates.Close.Interfaces.startState])
    (by simp [hσ3, hσ2, hσ1, hσ0, NearCubicGates.Close.Interfaces.startState]; omega)
  have v4 : σ3.val 7 + 10 * σ3.val 8 = 10 * L := by simp [hσ3, hσ2, hσ1, hσ0, NearCubicGates.Close.Interfaces.startState]
  have v4' : σ3.val 8 = L := by simp [hσ3, hσ2, hσ1]
  rw [v4, v4'] at e4
  set σ4 := σ3.setv 7 (10 * L) with hσ4
  have e5 := rincsM cap 7 B σ4 (by simp [hσ4]; omega)
  have v5 : σ4.val 7 + B = W := by simp [hσ4, hW]
  rw [v5] at e5
  set σ5 := σ4.setv 7 W with hσ5
  have e6 := addRsM cap (A := 7) (B := 6) (by decide) (by decide) (by decide) 2 σ5
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, hσ0, NearCubicGates.Close.Interfaces.startState])
    (by simp [hσ5, hσ4, hσ3, hσ2, hσ1, hσ0, NearCubicGates.Close.Interfaces.startState]; omega)
  have v6 : σ5.val 6 + 2 * σ5.val 7 = 2 * W := by
    simp [hσ5, hσ4, hσ3, hσ2, hσ1, hσ0, NearCubicGates.Close.Interfaces.startState]
  have v6' : σ5.val 7 = W := by simp [hσ5]
  rw [v6, v6'] at e6
  set σ6 := σ5.setv 6 (2 * W) with hσ6
  have e7 := WXExec.inc cap 6 σ6 (by simp [hσ6]; omega)
  have v7 : σ6.val 6 + 1 = 2 * W + 1 := by simp [hσ6]
  rw [v7] at e7
  set σ7 := σ6.setv 6 (2 * W + 1) with hσ7
  have base : ∀ i : Fin 30, σ7.st i = σ0.st i := fun i => rfl
  have bsh : ∀ i : Fin 30, σ7.sh i = 0 := fun i => rfl
  have e8 := Codec.unframeW_spec cap (0 : Fin 30) (2 : Fin 30) (by decide) (13 : Fin 16) (14 : Fin 16) (by decide) w L σ7
    (by rw [base]; simp [hσ0, NearCubicGates.Close.Interfaces.startState]) (bsh 0)
    (by rw [bsh, base]; simp [hσ0, NearCubicGates.Close.Interfaces.startState])
    (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2]) (by omega)
    (by simp [hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hσ0, NearCubicGates.Close.Interfaces.startState]; omega)
  rw [← hL, prefixBits_self, min_self] at e8
  set σ8 := ((NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO σ7 2 13 w).seth 0 (2 * L)).setv 14 0 with hσ8
  have e9 := wrewind_spec (cap := cap) (0 : Fin 30) (15 : Fin 16) (2 * L) σ8
    (by simp [hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hσ7, hσ6, hσ5, hσ4, hσ3])
    (by simp [hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hσ7, hσ6, hσ5, hσ4, hσ3]; omega)
  set σ9 := (σ8.setv 15 0).seth 0 (σ8.sh 0 - 2 * L) with hσ9
  have e10 := wrewind_spec (cap := cap) (2 : Fin 30) (13 : Fin 16) L σ9
    (by simp [hσ9, hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1,
      hσ0, NearCubicGates.Close.Interfaces.startState, hL])
    (by simp [hσ9, hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1,
      hσ0, NearCubicGates.Close.Interfaces.startState]; omega)
  set σ10 := (σ9.setv 13 0).seth 2 (σ9.sh 2 - L) with hσ10
  have e11 := rulerM cap L σ10
    (by simp [hσ10, hσ9, hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2,
      hσ1, hσ0, NearCubicGates.Close.Interfaces.startState])
    (by simp [hσ10, hσ9, hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2,
      hσ1, hσ0, NearCubicGates.Close.Interfaces.startState])
    (by simp [hσ10, hσ9, hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2,
      hσ1])
    (by simp [hσ10, hσ9, hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2,
      hσ1, hσ0, NearCubicGates.Close.Interfaces.startState])
    (by simp [hσ10, hσ9, hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO])
    (by simp [hσ10, hσ9, hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2,
      hσ1, hσ0, NearCubicGates.Close.Interfaces.startState]) (by omega)
  set σ11 := σ10.sets 3 (ruler L) with hσ11
  have e12 := initAllM W cap (by omega) numList σ11
    (fun X hX => by
      have hX4 := (mem_numList X).1 hX
      have h0 : X ≠ 0 := by intro e; subst e; simp at hX4
      have h2 : X ≠ 2 := by intro e; subst e; simp at hX4
      have h3 : X ≠ 3 := by intro e; subst e; simp at hX4
      constructor
      · simp [hσ11, hσ10, hσ9, hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hσ7, hσ6, hσ5, hσ4,
          hσ3, hσ2, hσ1, hσ0, NearCubicGates.Close.Interfaces.startState, h0, h2, h3, Function.update_of_ne h3,
          Function.update_of_ne h2]
      · simp [hσ11, hσ10, hσ9, hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hσ7, hσ6, hσ5, hσ4,
          hσ3, hσ2, hσ1, hσ0, NearCubicGates.Close.Interfaces.startState, Function.update_of_ne h0,
          Function.update_of_ne h2])
    (by simp [hσ11, hσ10, hσ9, hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hσ7, hσ6, hσ5])
    (by simp [hσ11, hσ10, hσ9, hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hσ7, hσ6, hσ5, hσ4,
      hσ3, hσ2, hσ1, hσ0, NearCubicGates.Close.Interfaces.startState])
  have E := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6 (WXExec.seq e7
    (WXExec.seq (WXExec.wm e8) (WXExec.seq (WXExec.wm e9) (WXExec.seq (WXExec.wm e10) (WXExec.seq e11 e12))))))))))
  refine E.cast cap ?_ ?_
  · apply WState.eq
    · funext i
      rw [setsZ_sh]
      fin_cases i <;> simp [mk, hσ11, hσ10, hσ9, hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hσ7,
        hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hσ0, NearCubicGates.Close.Interfaces.startState, hL]
    · funext i
      rw [setsZ_st]
      fin_cases i <;> simp [mk, mem_numList, hσ11, hσ10, hσ9, hσ8,
        NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hσ0,
        NearCubicGates.Close.Interfaces.startState, hL]
    · funext q
      rw [setsZ_val]
      fin_cases q <;> simp [mk, regs, hσ11, hσ10, hσ9, hσ8, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO,
        hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, hσ0, NearCubicGates.Close.Interfaces.startState, hL]
    · rw [setsZ_cell]; rfl
  · have hn : numList.length = 26 := by decide
    have a1 : σ1.val 8 = L := by simp [hσ1]
    rw [hn, a1]
    unfold initCost
    have := one_le_sq W
    have hLW : L ≤ W := by omega
    have hBW : B ≤ W := by omega
    nlinarith

end NearCubicGates.Close.WorkerArith
