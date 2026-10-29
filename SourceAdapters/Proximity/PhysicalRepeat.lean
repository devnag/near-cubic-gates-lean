import SourceAdapters.Proximity.PhysicalFields

/-! Q04: paid repeated-word fields, preserving the input unary register and
rewinding the output. Instantiations supply the guard and unary arity tapes. -/
set_option autoImplicit false
namespace NearCubicGates.Adapters.Proximity.PhysicalFields

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.WireExponent3_5.PrimAsm.Emit
open NearCubicWires.WireExponent3_5.PrimAsm.FiltRec

variable {ns nr : ℕ}

def writeRepeatTail (O : Fin (ns + 1)) (R : Fin 4 ↪ Fin nr) (u tail : List Bool) : WM ns nr :=
  .seq (repRegW O (R 3) (R 0) (R 1) (R 2) u)
    (.seq (emitW O (R 3) tail) (WM.rewind O (R 3)))

theorem write_repeat_tail (cap : ℕ) (O : Fin (ns + 1)) (R : Fin 4 ↪ Fin nr) (u tail : List Bool)
    (σ : WState ns nr) (hz : ∀ i : Fin 4, i ≠ 0 → σ.val (R i) = 0)
    (ho : σ.st O = []) (hh : σ.sh O = 0)
    (hcap : σ.val (R 0) + σ.val (R 0) * u.length + tail.length + 2 ≤ cap) :
    WExec cap (writeRepeatTail O R u tail) σ (σ.sets O (reps (σ.val (R 0)) u ++ tail))
      ((22 + 13 * u.length) * σ.val (R 0) + 13 * tail.length + 8) := by
  have hne {i j : Fin 4} (h : i ≠ j) : R i ≠ R j := R.injective.ne h
  have e1 := repRegW_spec cap O (R 3) (R 0) (R 1) (R 2)
    (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)) u σ
    (hz 1 (by decide)) (hz 2 (by decide)) (by rw [ho, hh]; rfl) (by omega)
    (by rw [hz 3 (by decide)]; omega)
  let σ1 := appendO σ O (R 3) (reps (σ.val (R 0)) u)
  have hlen : (reps (σ.val (R 0)) u).length = σ.val (R 0) * u.length := by simp [reps]
  have e2 := emitW_spec cap O (R 3) tail σ1
    (by simp [σ1, ho, hh]) (by simp [σ1, hz, hlen]; omega)
  let σ2 := appendO σ1 O (R 3) tail
  have e3 := wrewind_spec cap O (R 3) (σ.val (R 0) * u.length + tail.length) σ2
    (by simp [σ2, σ1, hz, hlen]) (by simp [σ2, σ1, hz, hlen]; omega)
  have he := WExec.seq e1 (WExec.seq e2 e3)
  have hs : (σ2.setv (R 3) 0).seth O (σ2.sh O - (σ.val (R 0) * u.length + tail.length)) =
      σ.sets O (reps (σ.val (R 0)) u ++ tail) := by
    apply WState.eq
    · funext i
      by_cases hi : i = O
      · subst i; simp [σ2, σ1, hh, hlen]
      · simp [σ2, σ1, hi]
    · funext i
      by_cases hi : i = O
      · subst i; simp [σ2, σ1, ho]
      · simp [σ2, σ1, hi]
    · funext i
      by_cases hi : i = R 3
      · subst i; simp [hz]
      · simp [σ2, σ1, hi]
    · rfl
  rw [hs] at he
  exact he.cast cap rfl (by nlinarith)

theorem reps_ones (n k : ℕ) : reps n (List.replicate k true) = List.replicate (n * k) true := by
  induction n with
  | zero => simp
  | succ n ih => rw [reps_succ, ih, Nat.succ_mul, List.replicate_add]

theorem guard_word (n : ℕ) :
    reps n (List.replicate 32 true) ++ [false] = frame (List.replicate (16 * n) true) := by
  rw [reps_ones, frame_eq, marks_eq, flatMap_replicate]
  change List.replicate (n * 32) true ++ [false] = reps (16 * n) (List.replicate 2 true) ++ [false]
  rw [reps_ones]
  congr 2
  omega

end NearCubicGates.Adapters.Proximity.PhysicalFields
