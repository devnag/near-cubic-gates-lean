import Proof.Gates.Codec.Seek
import Proof.Gates.Codec.PairFrame

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.Interfaces

variable {ns nr : ℕ} (cap : ℕ)

/-- Return the head of `CW` to its start: `T := L`, rewind by `T`. -/
def rewindCW (CW : Fin (ns + 1)) (LC T D : Fin nr) : WM ns nr := .seq (dupR LC T D) (WM.rewind CW T)

theorem rewindCW_spec (CW : Fin (ns + 1)) (LC T D : Fin nr) (hLT : LC ≠ T) (hLD : LC ≠ D) (hTD : T ≠ D)
    (σ : WState ns nr) (hT : σ.val T = 0) (hD : σ.val D = 0) (hL : σ.sh CW ≤ σ.val LC) (hc : σ.val LC ≤ cap) :
    WExec cap (rewindCW CW LC T D) σ (σ.seth CW 0) (18 * σ.val LC + 3 + 1 + (5 * σ.val LC + 1)) := by
  have e1 := dupR_spec cap LC T D hLT hLD hTD σ hD (by omega)
  rw [hT, Nat.zero_add] at e1
  have e2 := wrewind_spec cap CW T (σ.val LC) (σ.setv T (σ.val LC)) (by simp) (by simp; omega)
  refine WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl
  apply WState.eq
  · funext x; by_cases hx : x = CW
    · subst hx; simp; omega
    · simp [Function.update_of_ne hx]
  · rfl
  · funext r; by_cases hr : r = T
    · subst hr; simp [hT]
    · simp [Function.update_of_ne hr]
  · rfl

/-- Append circuit `x` (index in `Rx`) from `CW` (head at its start) to `o`. -/
def fetchCircuit (CW o : Fin (ns + 1)) (RC : Fin 8 ↪ Fin nr) (m I Rx D : Fin nr) (hm : ∀ i : Fin 8, RC i ≠ m) :
    WM ns nr :=
  .seq (dupR Rx I D) (.seq (seekCircuits CW (RC 1) (RC 2) (RC 3) (RC 4) (RC 5) (RC 6) I) (copyCircuit true CW o RC m hm))

/-- The registers of `fetchCircuit`: `RC 0 … RC 6`, `m`, `I`, `D` are scratch (zero), `Rx` holds the index, `RC 7`
counts the output; all distinct. -/
structure FetchRegs (RC : Fin 8 ↪ Fin nr) (m I Rx D : Fin nr) : Prop where
  hm : ∀ i : Fin 8, RC i ≠ m
  hI : ∀ i : Fin 8, RC i ≠ I
  hx : ∀ i : Fin 8, RC i ≠ Rx
  hD : ∀ i : Fin 8, RC i ≠ D
  mI : m ≠ I
  mx : m ≠ Rx
  mD : m ≠ D
  Ix : I ≠ Rx
  ID : I ≠ D
  xD : Rx ≠ D

theorem fetchCircuit_spec (CW o : Fin (ns + 1)) (hCo : CW ≠ o) (RC : Fin 8 ↪ Fin nr) (m I Rx D : Fin nr)
    (hr : FetchRegs RC m I Rx D) {q : ℕ} (Cs : ℕ → NCircuit q) (N x : ℕ) (hx : x < N) (cb V : ℕ)
    (hfit : ∀ j < N, CircuitFits cap (Cs j)) (hcb : ∀ j < N, circuitCost (Cs j) ≤ cb)
    (hcopy : CopyFits cap V (Cs x)) (hxc : 2 * x ≤ cap) (rest : List Bool) (σ : WState ns nr)
    (hst : σ.st CW = cwPrefix Cs N ++ rest) (hsh : σ.sh CW = 0) (ho : σ.sh o = (σ.st o).length)
    (hz : ∀ i : Fin 8, i ≠ 7 → σ.val (RC i) = 0) (hm0 : σ.val m = 0) (hI0 : σ.val I = 0) (hD0 : σ.val D = 0)
    (hX : σ.val Rx = x) (hV : σ.val (RC 7) + (marks (circuitWord (Cs x))).length ≤ V) :
    WExec cap (fetchCircuit CW o RC m I Rx D hr.hm) σ
      (appendO (σ.seth CW (cwPrefix Cs (x + 1)).length) o (RC 7) (marks (circuitWord (Cs x))))
      (18 * x + 3 + 1 + (x * (cb + 4) + 1 + 1 + copyCircuitCost (Cs x))) := by
  -- `I := x`
  have e1 := dupR_spec cap Rx I D hr.Ix.symm hr.xD hr.ID σ hD0 (by rw [hX, hI0]; omega)
  rw [hI0, hX, Nat.zero_add] at e1
  set σ1 := σ.setv I x with hσ1
  -- seek
  have hd6 : [RC 1, RC 2, RC 3, RC 4, RC 5, RC 6].Nodup := by
    have h : ([1, 2, 3, 4, 5, 6] : List (Fin 8)).Nodup := by decide
    have h2 := h.map RC.injective
    simp only [List.map_cons, List.map_nil] at h2
    exact h2
  have hI6 : I ∉ [RC 1, RC 2, RC 3, RC 4, RC 5, RC 6] := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨(hr.hI 1).symm, (hr.hI 2).symm, (hr.hI 3).symm, (hr.hI 4).symm, (hr.hI 5).symm, (hr.hI 6).symm⟩
  have e2 := seekCircuits_spec cap CW (RC 1) (RC 2) (RC 3) (RC 4) (RC 5) (RC 6) I hd6 hI6 Cs N x hx.le cb hfit hcb
    (by omega) rest σ1 (by simp [hσ1, hst]) (by simp [hσ1, hsh])
    (by
      have hz' : ∀ i : Fin 8, i ≠ 7 → σ1.val (RC i) = 0 := fun i hi => by
        simp [hσ1, Function.update_of_ne (hr.hI i), hz i hi]
      intro r hr6
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr6
      rcases hr6 with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hz' 1 (by decide)
      · exact hz' 2 (by decide)
      · exact hz' 3 (by decide)
      · exact hz' 4 (by decide)
      · exact hz' 5 (by decide)
      · exact hz' 6 (by decide))
    (by simp [hσ1])
  set σ2 := (σ1.seth CW (cwPrefix Cs x).length).setv I 0 with hσ2
  -- copy
  have hsplit := cwPrefix_split Cs hx
  have e3 := copyCircuit_spec cap true CW o hCo RC m hr.hm V (Cs x) hcopy (cwPrefix Cs x)
    ((cwPrefix Cs N).drop (cwPrefix Cs (x + 1)).length ++ rest) σ2
    (by
      show σ.st CW = _
      rw [hst]
      conv_lhs => rw [hsplit]
      simp only [WireExponent3_5.PrimAsm.ParseNat.enc, if_true, List.append_assoc])
    (by simp [hσ2])
    (by simp [hσ2, hσ1, Function.update_apply, hCo.symm, ho])
    (by
      intro i hi
      simp only [hσ2, hσ1, WState.setv_val, WState.seth_val]
      rw [Function.update_of_ne (hr.hI i), Function.update_of_ne (hr.hI i)]
      exact hz i hi)
    (by simp only [hσ2, hσ1, WState.setv_val, WState.seth_val]; rw [Function.update_of_ne hr.mI,
      Function.update_of_ne hr.mI]; exact hm0)
    (by simp only [hσ2, hσ1, WState.setv_val, WState.seth_val]; rw [Function.update_of_ne (hr.hI 7),
      Function.update_of_ne (hr.hI 7)]; exact hV)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ le_rfl
  apply WState.eq
  · funext y; by_cases hy : y = CW
    · subst hy; simp [hσ2, hσ1, appendO, Function.update_apply, hCo, cwPrefix_succ, WireExponent3_5.PrimAsm.ParseNat.stp, marks_length]
    · by_cases hyo : y = o
      · subst hyo; simp [hσ2, hσ1, appendO, Function.update_apply, hy]
      · simp [hσ2, hσ1, appendO, Function.update_of_ne hy, Function.update_of_ne hyo]
  · funext y; by_cases hyo : y = o
    · subst hyo; simp [hσ2, hσ1, appendO, Function.update_apply, hCo.symm]
    · simp [hσ2, hσ1, appendO, Function.update_of_ne hyo]
  · funext r
    simp only [hσ2, hσ1, appendO_val, WState.setv_val, WState.seth_val, Function.update_apply]
    by_cases h7 : r = RC 7
    · subst h7; simp [hr.hI 7]
    · by_cases hI : r = I
      · subst hI; simp [h7, hI0]
      · simp [h7, hI]
  · rfl

end NearCubicGates.Close.Codec
