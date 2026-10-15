import Proof.Wire_3_5.CompilerMachineEmitWords
import Proof.Wire_3_5.CompilerMachinePoolLoop
import Proof.Wire_3_5.BlockArith

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.CompilerMachine.Emit
open NearCubicWires NearCubicWires.WireExponent3_5.CompilerMachine NearCubicWires.WireExponent3_5.CompilerMachine.Pool
open NearCubicWires.WireExponent3_5.Block NearCubicWires.WireExponent3_5.GF2
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RadixSemantics
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)

/-! ## Moves and loops -/

/-- One move to the left. -/
def moveLM : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q _ => if q.val = 0 then some ⟨1, fun _ => none, fun _ => .left⟩ else none

theorem moveLStep (T : List Bool) (h : ℕ) : Step moveLM 1 ![h + 1] ![T] ![h] ![T] := by
  have hs : step moveLM ⟨moveLM.start, ![h + 1], ![T]⟩ = some ⟨1, ![h], ![T]⟩ := by
    simp [step, moveLM]
    apply configuration_ext
    · rfl
    · funext i; fin_cases i; simp [applyAction, HeadMove.apply]
    · funext i; fin_cases i; simp [applyAction]
  obtain ⟨r, hr, hf, hs'⟩ := (RecoveryExecution.Timed.single (p := moveLM) rfl hs).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

/-- **A uniform body once per entry of a framed list behind a prefix**: the source head reads cell `|P| + 2j`
before pass `j`. -/
theorem frameRunAt {t s : ℕ} (body : Machine t s) (src : Fin t) (P l tl : List Bool) (bH : ℕ → Fin t → ℕ)
    (bA : ℕ → Fin t → List Bool) (hsrcA : ∀ j, bA j src = P ++ (frame l ++ tl)) (hsrcH : ∀ j, bH j src = P.length + 2 * j)
    (c : ℕ) (hstep : ∀ j, j < l.length → Step body c (bH j) (bA j) (bH (j + 1)) (bA (j + 1))) :
    Step (StreamController.machine body src) (l.length * (c + 2) + 1) (bH 0) (bA 0) (bH l.length) (bA l.length) := by
  let W : WhileBody t s :=
    { body := body
      tape := src
      bound := l.length
      H := bH
      A := bA
      cost := fun _ => c
      step := fun j hj => hstep j hj
      cont := fun j hj => by
        show readTapeBit (bA j src) (bH j src) = true
        rw [hsrcA, hsrcH, read_suffix, read_prefix _ _ _ (by simp; omega)]
        exact read_frame_mark l j hj
      halt := by
        show readTapeBit (bA l.length src) (bH l.length src) = false
        rw [hsrcA, hsrcH, read_suffix, read_prefix _ _ _ (by simp)]
        exact read_frame_end l }
  have hW := W.run
  rw [W.rest_const c (fun _ => rfl)] at hW
  exact hW

/-! ## Subtraction -/

theorem binary_not : ∀ (L y : ℕ), y < 2 ^ L → (binary L y).map not = binary L (2 ^ L - 1 - y)
  | 0, _, _ => rfl
  | L + 1, y, hy => by
    have hy2 : y / 2 < 2 ^ L := by rw [pow_succ] at hy; omega
    simp only [binary, List.map_cons, binary_not L (y / 2) hy2]
    have hp : 0 < 2 ^ L := Nat.two_pow_pos L
    have e1 : (2 ^ (L + 1) - 1 - y) / 2 = 2 ^ L - 1 - y / 2 := by rw [pow_succ]; omega
    have e2 : (!(y % 2 == 1)) = ((2 ^ (L + 1) - 1 - y) % 2 == 1) := by
      rw [pow_succ]
      rcases Nat.mod_two_eq_zero_or_one y with h | h
      · have : (2 ^ L * 2 - 1 - y) % 2 = 1 := by omega
        simp [h, this]
      · have : (2 ^ L * 2 - 1 - y) % 2 = 0 := by omega
        simp [h, this]
    rw [e1, e2]

theorem binary_add_pow : ∀ (L v : ℕ), binary L (v + 2 ^ L) = binary L v
  | 0, _ => rfl
  | L + 1, v => by
    simp only [binary]
    have e1 : (v + 2 ^ (L + 1)) % 2 = v % 2 := by rw [pow_succ]; omega
    have e2 : (v + 2 ^ (L + 1)) / 2 = v / 2 + 2 ^ L := by rw [pow_succ]; omega
    rw [e1, e2, binary_add_pow L (v / 2)]

/-- The difference bit (the sum bit against the complement). -/
def subOut (x y c : Bool) : Bool := addOut x (!y) c

/-- The difference carry. -/
def subNxt (x y c : Bool) : Bool := addNxt x (!y) c

theorem map_notR : ∀ (u v : List Bool) (c : Bool),
    ZipMap.map subOut subNxt u v c = ZipMap.map addOut addNxt u (v.map not) c
  | [], _, _ => by cases ‹List Bool› <;> rfl
  | _ :: _, [], _ => rfl
  | x :: u, y :: v, c => by
    simp only [ZipMap.map, List.map_cons, subOut, subNxt, map_notR u v]

/-- **The borrow transducer is subtraction** of `L`-bit words (`y ≤ x < 2^L`). -/
theorem map_sub (L x y : ℕ) (hx : x < 2 ^ L) (hyx : y ≤ x) :
    ZipMap.map subOut subNxt (binary L x) (binary L y) true = binary L (x - y) := by
  rw [map_notR, binary_not L y (by omega), map_add]
  have hp : 0 < 2 ^ L := Nat.two_pow_pos L
  rw [show x + (2 ^ L - 1 - y) + true.toNat = (x - y) + 2 ^ L by simp; omega, binary_add_pow]

/-! ## Comparison into a cell -/

/-- **The comparison `value u ≤ value v`** of two framed registers, written into the cell `[false]`. -/
theorem cmpStep (u v tu tv : List Bool) (hl : u.length = v.length) :
    Step Compare.machine (2 * u.length + 1) ![0, 0, 0] ![frame u ++ tu, frame v ++ tv, [false]]
      ![2 * u.length, 2 * v.length, 1] ![frame u ++ tu, frame v ++ tv, [decide (value u ≤ value v)]] := by
  have hb := (compareBlock [] [] u v tu tv [] hl).run
  obtain ⟨h1, h2, h3, h4, h5⟩ := compareBlock_out [] [] u v tu tv [] hl
  have hH : (compareBlock [] [] u v tu tv [] hl).entryH = ![0, 0, 0] := rfl
  have hA : (compareBlock [] [] u v tu tv [] hl).entryA = ![frame u ++ tu, frame v ++ tv, []] := by
    funext i; fin_cases i <;> rfl
  have hA' : (compareBlock [] [] u v tu tv [] hl).exitA =
      ![frame u ++ tu, frame v ++ tv, [decide (value u ≤ value v)]] := by
    funext i; fin_cases i
    · simpa using h2
    · simpa using h3
    · simpa using h1
  rw [hH, hA, hA', h4, h5] at hb
  have hp := hb.pad ![0, 0, 1]
  refine (hp.congr_in rfl ?_).congr ?_ ?_
  · funext i; fin_cases i <;> simp [ZeroPadding.pad]
  · funext i; fin_cases i <;> simp
  · funext i; fin_cases i <;> simp [ZeroPadding.pad]

/-! ## A one-step gate -/

/-- Write `f` of the scanned cells onto tape `o`, in one step. -/
def gateM (t : ℕ) (o : Fin t) (f : (Fin t → Bool) → Bool) : Machine t 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 1
  rule := fun q sc => if q.val = 0 then some ⟨1, fun i => if i = o then some (f sc) else none, fun _ => .stay⟩
    else none

/-- **The gate step**: tape `o` gets `f` of the cells under the heads written under its head; nothing moves. -/
theorem gateStep {t : ℕ} (o : Fin t) (f : (Fin t → Bool) → Bool) (H : Fin t → ℕ) (A : Fin t → List Bool) :
    Step (gateM t o f) 1 H A H
      (fun i => if i = o then writeTapeBit (A o) (H o) (f (fun j => readTapeBit (A j) (H j))) else A i) := by
  have hs : step (gateM t o f) ⟨(gateM t o f).start, H, A⟩ = some ⟨1, H,
      fun i => if i = o then writeTapeBit (A o) (H o) (f (fun j => readTapeBit (A j) (H j))) else A i⟩ := by
    simp only [step, gateM]
    simp only [Fin.isValue, Fin.val_zero, ↓reduceIte, Option.map_some, Option.some.injEq]
    apply configuration_ext
    · rfl
    · funext i; simp [applyAction, HeadMove.apply]
    · funext i
      by_cases hi : i = o
      · subst hi; simp [applyAction]; rfl
      · simp [applyAction, hi]
  obtain ⟨r, hr, hf, hs'⟩ := (RecoveryExecution.Timed.single (p := gateM t o f) rfl hs).run rfl
  exact ⟨r, hr, by rw [hf], by rw [hf], by omega⟩

end NearCubicWires.WireExponent3_5.CompilerMachine.Emit
