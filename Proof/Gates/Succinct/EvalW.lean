import Proof.Gates.Succinct.EvalStep
import Proof.Wire_3_5.UnionMachineRoundDiv

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-! ## Clearing the value tape -/

theorem writeTapeBit_set' : ∀ (l : List Bool) (k : ℕ) (v : Bool), k < l.length → writeTapeBit l k v = l.set k v
  | [], k, v, h => by simp at h
  | _ :: l, 0, v, _ => rfl
  | x :: l, k + 1, v, h => by
    simp only [writeTapeBit, List.set_cons_succ]
    rw [writeTapeBit_set' l k v (by simpa using h)]

/-- Write `false` at the first `J` cells (`J` counted down), then rewind. -/
def clearV (V : Fin (ns + 1)) (J Y : Fin nr) : WM ns nr :=
  .seq (.whr J (.seq (.dec J) (.seq (.wr V false) (.seq (.fwd V) (.inc Y))))) (WM.rewind V Y)

theorem clearV_spec (cap : ℕ) (V : Fin (ns + 1)) (J Y : Fin nr) (hJY : J ≠ Y) (σ : WState ns nr) (m : ℕ)
    (vals : List Bool) (hV : σ.st V = vtape m vals) (hVh : σ.sh V = 0) (hJ : σ.val J = vals.length)
    (hY : σ.val Y = 0) (hcap : vals.length + 1 ≤ cap) :
    WExec cap (clearV V J Y) σ ((σ.setv J 0).sets V (List.replicate (max m vals.length) false))
      (vals.length * 16 + 3) := by
  set n := vals.length with hn
  let cl : ℕ → List Bool := fun k => List.replicate k false ++ (vtape m vals).drop k
  have hlen : ∀ k, k ≤ n → (cl k).length = max m n := by
    intro k hk; simp [cl, vtape_length]; omega
  let S : ℕ → WState ns nr := fun k => (((σ.setv J (n - k)).setv Y k).sets V (cl k)).seth V k
  have h0 : S 0 = σ := by
    refine WState.eq ?_ ?_ ?_ rfl
    · funext x; by_cases hx : x = V
      · subst hx; simp [S, hVh]
      · simp [S, Function.update_of_ne hx]
    · funext x; by_cases hx : x = V
      · subst hx; simp [S, cl, hV]
      · simp [S, Function.update_of_ne hx]
    · funext r; simp only [S, WState.seth_val, WState.sets_val, WState.setv_val, Function.update_apply]
      by_cases hrY : r = Y
      · subst hrY; simp [hY]
      · by_cases hrJ : r = J
        · subst hrJ; simp [hrY, hJ]
        · simp [hrY, hrJ]
  have e := UnionMachine.Round.wloop cap J (.seq (.wr V false) (.seq (.fwd V) (.inc Y))) 7 n S
    (fun k _ => by simp [S, Function.update_apply, hJY]) (by omega)
    (fun k hk => by
      set T := (S k).setv J (n - k - 1) with hT
      have e1 := WExec.wr (cap := cap) V false T
      have e2 := WExec.fwd (cap := cap) V (T.sets V (writeTapeBit (T.st V) (T.sh V) false))
      have e3 := WExec.inc (cap := cap) Y ((T.sets V (writeTapeBit (T.st V) (T.sh V) false)).seth V
        ((T.sets V (writeTapeBit (T.st V) (T.sh V) false)).sh V + 1))
        (by
          have : ((S k).setv J (n - k - 1)).val Y = k := by simp [S, Function.update_apply, Ne.symm hJY]
          simp only [WState.seth_val, WState.sets_val, T]; omega)
      refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ (by omega)
      have hw : writeTapeBit (cl k) k false = cl (k + 1) := by
        rw [writeTapeBit_set' _ _ _ (by rw [hlen k hk.le]; omega)]
        simp only [cl]
        apply List.ext_getElem
        · simp [vtape_length]; omega
        · intro i h1 h2
          simp only [List.getElem_set, List.getElem_append, List.length_replicate, List.getElem_replicate,
            List.getElem_drop]
          split_ifs <;> first | rfl | omega | (simp [vtape, List.getElem_append] at *; split_ifs <;> simp_all <;> omega)
      refine WState.eq ?_ ?_ ?_ rfl
      · funext x; by_cases hx : x = V
        · subst hx; simp [T, S]
        · simp [T, S, Function.update_of_ne hx]
      · funext x; by_cases hx : x = V
        · subst hx; simp [T, S, hw]
        · simp [T, S, Function.update_of_ne hx]
      · funext r; simp only [T, S, WState.seth_val, WState.sets_val, WState.setv_val, Function.update_apply]
        by_cases hrY : r = Y
        · subst hrY; simp [Ne.symm hJY]
        · by_cases hrJ : r = J
          · subst hrJ; simp [hrY]; omega
          · simp [hrY, hrJ])
  rw [h0] at e
  have e2 := wrewind_spec cap V Y n (S n) (by simp [S]) (by simp [S]; omega)
  refine WExec.cast cap (WExec.seq e e2) ?_ (by ring_nf; omega)
  have hcl : cl n = List.replicate (max m n) false := by
    simp only [cl, vtape]
    rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega)]
    simp [← List.replicate_add]; omega
  refine WState.eq ?_ ?_ ?_ rfl
  · funext x; by_cases hx : x = V
    · subst hx; simp [S, hVh]
    · simp [S, Function.update_of_ne hx]
  · funext x; by_cases hx : x = V
    · subst hx; simp [S, hcl]
    · simp [S, Function.update_of_ne hx]
  · funext r; simp only [S, WState.seth_val, WState.sets_val, WState.setv_val, Function.update_apply]
    by_cases hrY : r = Y
    · subst hrY; simp [hY, Ne.symm hJY]
    · by_cases hrJ : r = J
      · subst hrJ; simp [hrY]
      · simp [hrY, hrJ]

end NearCubicGates.Close.Succinct
