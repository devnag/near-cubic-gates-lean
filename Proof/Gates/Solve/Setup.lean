import Proof.Gates.Solve.ElimLoop
import Proof.Gates.Codec.Unframe
import Proof.Gates.Interfaces.WordFn

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Solve

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicGates.Close.WordPrograms.SInt
open StablePartition.Workspace (overlay)
open NearCubicGates.Close.Interfaces (startState)

abbrev rOP : Reg := 12
abbrev rP2 : Reg := 13
abbrev rLL : Reg := 33
abbrev rWL : Reg := 34
abbrev rR2 : Reg := 35
abbrev rT1 : Reg := 36
abbrev rT3 : Reg := 37
abbrev wTWO : Str := 27

/-- The width parameter: `W = 8(ℓ+1)²`. -/
def wOf (ℓ : ℕ) : ℕ := 8 * (ℓ + 1) ^ 2

/-! ## Unframing the input -/

/-- One marked bit of the framed input: copy its payload raw to `sRAW`. -/
def ufBody : WM NS NR :=
  .seq (.fwd sIN) (.seq (.ifs sIN (emitC sRAW rOP true) (emitC sRAW rOP false))
    (.seq (.fwd sIN) (.seq (.inc rP2) (.inc rP2))))

/-- The state after unframing `x` from position `pre.length`. -/
def ufSt (σ : MS) (x pre : List Bool) : MS :=
  ((((σ.sets sRAW (σ.st sRAW ++ x)).seth sRAW (σ.sh sRAW + x.length)).setv rOP (σ.val rOP + x.length)).setv rP2
    (σ.val rP2 + 2 * x.length)).seth sIN (pre.length + 2 * x.length)

theorem uf_loop (cap : ℕ) (rest : List Bool) : ∀ (x pre : List Bool) (σ : MS),
    σ.st sIN = pre ++ frame x ++ rest → σ.sh sIN = pre.length → σ.sh sRAW = (σ.st sRAW).length →
    σ.val rOP + x.length ≤ cap → σ.val rP2 + 2 * x.length ≤ cap →
    WExec cap (.whs sIN ufBody) σ (ufSt σ x pre) (30 * x.length + 1)
  | [], pre, σ, hst, hsh, _, _, _ => by
    have hb : wbit σ sIN = false := by
      unfold wbit readTapeBit; rw [hst, hsh]; simp [frame, List.getD_append_right]
    have e : ufSt σ [] pre = σ := by
      apply WState.eq
      · funext y; by_cases hy : y = sIN
        · subst hy; simp (config := {decide := true}) [ufSt, hsh]
        · by_cases hyr : y = sRAW
          · subst hyr; simp (config := {decide := true}) [ufSt]
          · simp [ufSt, Function.update_of_ne hy, Function.update_of_ne hyr]
      · funext y; by_cases hyr : y = sRAW
        · subst hyr; simp [ufSt]
        · simp [ufSt, Function.update_of_ne hyr]
      · funext r; by_cases h1 : r = rOP
        · subst h1; simp (config := {decide := true}) [ufSt]
        · by_cases h2 : r = rP2
          · subst h2; simp [ufSt]
          · simp [ufSt, Function.update_of_ne h1, Function.update_of_ne h2]
      · rfl
    rw [e]
    exact WExec.mono (WExec.whsF hb) (by simp)
  | b :: x, pre, σ, hst, hsh, hraw, hc1, hc2 => by
    have hb : wbit σ sIN = true := by
      unfold wbit readTapeBit; rw [hst, hsh]; simp [frame, List.getD_append_right]
    have e1 := WExec.fwd (cap := cap) sIN σ
    set σ1 := σ.seth sIN (σ.sh sIN + 1) with hσ1
    have hdata : wbit σ1 sIN = b := by
      unfold wbit readTapeBit
      simp only [hσ1, WState.seth_st, WState.seth_sh, Function.update_self]
      rw [hst, hsh]; simp [frame, List.getD_append_right]
    have hraw1 : σ1.sh sRAW = (σ1.st sRAW).length := by simp (config := {decide := true}) [hσ1, hraw]
    have hc1' : σ1.val rOP < cap := by simp [hσ1]; simp at hc1; omega
    have e2 : WExec cap (.ifs sIN (emitC sRAW rOP true) (emitC sRAW rOP false)) σ1
        (((σ1.sets sRAW (σ1.st sRAW ++ [b])).seth sRAW (σ1.sh sRAW + 1)).setv rOP (σ1.val rOP + 1)) 8 := by
      cases b
      · exact WExec.mono (WExec.ifsF hdata (emitC_spec cap sRAW rOP false σ1 hraw1 hc1')) (by omega)
      · exact WExec.mono (WExec.ifsT hdata (emitC_spec cap sRAW rOP true σ1 hraw1 hc1')) (by omega)
    set σ2 := ((σ1.sets sRAW (σ1.st sRAW ++ [b])).seth sRAW (σ1.sh sRAW + 1)).setv rOP (σ1.val rOP + 1) with hσ2
    have e3 := WExec.fwd (cap := cap) sIN σ2
    set σ3 := σ2.seth sIN (σ2.sh sIN + 1) with hσ3
    have e4 := WExec.inc (cap := cap) rP2 σ3 (by simp (config := {decide := true}) [hσ3, hσ2, hσ1]; simp at hc2; omega)
    set σ4 := σ3.setv rP2 (σ3.val rP2 + 1) with hσ4
    have e5 := WExec.inc (cap := cap) rP2 σ4 (by simp (config := {decide := true}) [hσ4, hσ3, hσ2, hσ1]; simp at hc2; omega)
    set σ5 := σ4.setv rP2 (σ4.val rP2 + 1) with hσ5
    have ih := uf_loop cap rest x (pre ++ [true, b]) σ5
      (by simp (config := {decide := true}) [hσ5, hσ4, hσ3, hσ2, hσ1, hst, frame])
      (by simp (config := {decide := true}) [hσ5, hσ4, hσ3, hσ2, hσ1, hsh] <;> omega)
      (by simp (config := {decide := true}) [hσ5, hσ4, hσ3, hσ2, hσ1, hraw])
      (by simp (config := {decide := true}) [hσ5, hσ4, hσ3, hσ2, hσ1]; simp at hc1; omega)
      (by simp (config := {decide := true}) [hσ5, hσ4, hσ3, hσ2, hσ1]; simp at hc2; omega)
    have e := WExec.whsT hb (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ih
    refine WExec.cast cap e ?_ (by simp; omega)
    apply WState.eq
    · funext y; by_cases hy : y = sIN
      · subst hy; simp (config := {decide := true}) [ufSt, hσ5, hσ4, hσ3, hσ2, hσ1, hsh]; omega
      · by_cases hyr : y = sRAW
        · subst hyr; simp (config := {decide := true}) [ufSt, hσ5, hσ4, hσ3, hσ2, hσ1]; omega
        · simp [ufSt, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hy, Function.update_of_ne hyr]
    · funext y; by_cases hyr : y = sRAW
      · subst hyr; simp (config := {decide := true}) [ufSt, hσ5, hσ4, hσ3, hσ2, hσ1]
      · simp [ufSt, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hyr]
    · funext r; by_cases h1 : r = rOP
      · subst h1; simp (config := {decide := true}) [ufSt, hσ5, hσ4, hσ3, hσ2, hσ1]; omega
      · by_cases h2 : r = rP2
        · subst h2; simp (config := {decide := true}) [ufSt, hσ5, hσ4, hσ3, hσ2, hσ1]; omega
        · simp [ufSt, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne h1, Function.update_of_ne h2]
    · rfl

/-! ## Emitting constant bits -/

def emitsW (O : Str) (OP : Reg) : List Bool → WM NS NR
  | [] => .skip
  | b :: bs => .seq (emitC O OP b) (emitsW O OP bs)

def appS (σ : MS) (O : Str) (OP : Reg) (bs : List Bool) : MS :=
  ((σ.sets O (σ.st O ++ bs)).seth O (σ.sh O + bs.length)).setv OP (σ.val OP + bs.length)

theorem appS_nil (σ : MS) (O : Str) (OP : Reg) : appS σ O OP [] = σ := by
  apply WState.eq
  · funext y; by_cases hy : y = O
    · subst hy; simp [appS]
    · simp [appS, Function.update_of_ne hy]
  · funext y; by_cases hy : y = O
    · subst hy; simp [appS]
    · simp [appS, Function.update_of_ne hy]
  · funext r; by_cases hr : r = OP
    · subst hr; simp [appS]
    · simp [appS, Function.update_of_ne hr]
  · rfl

theorem appS_appS (σ : MS) (O : Str) (OP : Reg) (bs cs : List Bool) :
    appS (appS σ O OP bs) O OP cs = appS σ O OP (bs ++ cs) := by
  apply WState.eq
  · funext y; by_cases hy : y = O
    · subst hy; simp [appS]; omega
    · simp [appS, Function.update_of_ne hy]
  · funext y; by_cases hy : y = O
    · subst hy; simp [appS]
    · simp [appS, Function.update_of_ne hy]
  · funext r; by_cases hr : r = OP
    · subst hr; simp [appS]; omega
    · simp [appS, Function.update_of_ne hr]
  · rfl

theorem emitsW_spec (cap : ℕ) (O : Str) (OP : Reg) : ∀ (bs : List Bool) (σ : MS), σ.sh O = (σ.st O).length →
    σ.val OP + bs.length ≤ cap → WExec cap (emitsW O OP bs) σ (appS σ O OP bs) (8 * bs.length)
  | [], σ, _, _ => by rw [appS_nil]; exact WExec.skip σ
  | b :: bs, σ, hO, hc => by
    have e1 := emitC_spec cap O OP b σ hO (by simp at hc; omega)
    have e2 := emitsW_spec cap O OP bs (appS σ O OP [b]) (by simp [appS, hO])
      (by simp [appS]; simp at hc; omega)
    rw [appS_appS] at e2
    refine WExec.mono (WExec.seq e1 (by simpa [appS] using e2)) (by simp; omega)

def emitLoop (K : Reg) (O : Str) (OP : Reg) (bs : List Bool) : WM NS NR := .whr K (.seq (.dec K) (emitsW O OP bs))

theorem emitLoop_spec (cap : ℕ) (K : Reg) (O : Str) (OP : Reg) (hKO : K ≠ OP) (bs : List Bool) :
    ∀ (k : ℕ) (σ : MS), σ.val K = k → σ.sh O = (σ.st O).length → σ.val OP + k * bs.length ≤ cap → k ≤ cap →
      WExec cap (emitLoop K O OP bs) σ ((appS σ O OP (List.replicate k bs).flatten).setv K 0)
        (k * (8 * bs.length + 4) + 1)
  | 0, σ, hK, _, _, _ => by
    have e : (appS σ O OP (List.replicate 0 bs).flatten).setv K 0 = σ := by
      rw [List.replicate_zero, List.flatten_nil, appS_nil, ← hK, wsetv_same]
    rw [e]; exact WExec.mono (WExec.whrF hK) (by simp)
  | k + 1, σ, hK, hO, hc, hk => by
    have e1 := WExec.dec (cap := cap) K σ (by omega)
    set σ1 := σ.setv K (σ.val K - 1) with hσ1
    have e2 := emitsW_spec cap O OP bs σ1 (by simp [hσ1, hO])
      (by simp [hσ1, Function.update_of_ne (Ne.symm hKO)]; have := Nat.le_mul_of_pos_left bs.length
            (show 0 < k + 1 by omega); nlinarith)
    have ih := emitLoop_spec cap K O OP hKO bs k (appS σ1 O OP bs)
      (by simp [appS, hσ1, Function.update_of_ne hKO, hK])
      (by simp [appS, hσ1, hO]) (by simp [appS, hσ1, Function.update_of_ne (Ne.symm hKO)]; nlinarith) (by omega)
    have e := WExec.whrT (by omega) (WExec.seq e1 e2) ih
    refine WExec.cast cap e ?_ (by ring_nf; omega)
    rw [appS_appS, List.replicate_succ, List.flatten_cons]
    apply WState.eq
    · funext y; by_cases hy : y = O
      · subst hy; simp [appS, hσ1]
      · simp [appS, hσ1, Function.update_of_ne hy]
    · funext y; by_cases hy : y = O
      · subst hy; simp [appS, hσ1]
      · simp [appS, hσ1, Function.update_of_ne hy]
    · funext r; by_cases hr : r = K
      · subst hr; simp [appS, hσ1]
      · by_cases hr2 : r = OP
        · subst hr2; simp [appS, hσ1, Function.update_of_ne hKO.symm]
        · simp [appS, hσ1, Function.update_of_ne hr, Function.update_of_ne hr2]
    · rfl

theorem frame_binary_zero : ∀ k : ℕ, frame (binary k 0) = (List.replicate k [true, false]).flatten ++ [false]
  | 0 => rfl
  | k + 1 => by
    rw [List.replicate_succ', List.flatten_append]
    simp only [SignedSortKey.binary, Nat.zero_mod, Nat.zero_div, frame, List.flatten_cons, List.flatten_nil,
      List.append_nil]
    rw [frame_binary_zero k]
    have : ∀ j : ℕ, (List.replicate j [true, false]).flatten ++ [true, false] =
        true :: false :: (List.replicate j [true, false]).flatten := by
      intro j; induction j with
      | zero => rfl
      | succ j ih => simp [List.replicate_succ, ih]
    simp [← List.append_assoc, this]

end NearCubicGates.Close.Solve
