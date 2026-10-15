import Proof.Gates.Codec.FieldCircuitSpec
import Proof.Gates.Codec.Copy
import Proof.Gates.Codec.Circuit

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.Codec

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.RepairOrdinary.Streaming NearCubicGates.Close.Interfaces

variable {ns nr : ℕ} (cap : ℕ)

/-- The marked circuit words of the first `i` circuits. -/
def cwPrefix {q : ℕ} (Cs : ℕ → NCircuit q) (i : ℕ) : List Bool :=
  (List.range i).flatMap fun j => marks (circuitWord (Cs j))

theorem cwPrefix_succ {q : ℕ} (Cs : ℕ → NCircuit q) (i : ℕ) :
    cwPrefix Cs (i + 1) = cwPrefix Cs i ++ marks (circuitWord (Cs i)) := by
  simp [cwPrefix, List.range_succ, List.flatMap_append]

theorem cwPrefix_split {q : ℕ} (Cs : ℕ → NCircuit q) {i N : ℕ} (h : i < N) :
    cwPrefix Cs N = cwPrefix Cs i ++ marks (circuitWord (Cs i)) ++ (cwPrefix Cs N).drop (cwPrefix Cs (i + 1)).length := by
  have hle : i + 1 ≤ N := h
  have hpre : cwPrefix Cs N = cwPrefix Cs (i + 1) ++ (cwPrefix Cs N).drop (cwPrefix Cs (i + 1)).length := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
    have : cwPrefix Cs (i + 1 + d) = cwPrefix Cs (i + 1) ++
        (List.range' (i + 1) d).flatMap (fun j => marks (circuitWord (Cs j))) := by
      simp [cwPrefix, List.range_add, List.flatMap_append, List.range'_eq_map_range]
    rw [this, List.drop_left]
  rw [← cwPrefix_succ]
  exact hpre

/-- Skip `i` circuit words (`I = i` counts down). -/
def seekCircuits (W : Fin (ns + 1)) (f c k K p t I : Fin nr) : WM ns nr := repLoop I (skipCircuit true W f c k K p t)

/-- **Seek.** From the head at the start of `CW = cwPrefix Cs N ++ rest`, `seekCircuits` with `I = i ≤ N` leaves the
head at `|cwPrefix Cs i|` and `I = 0`, everything else as it was. -/
theorem seekCircuits_spec (W : Fin (ns + 1)) (f c k K p t I : Fin nr) (hd : [f, c, k, K, p, t].Nodup)
    (hI : I ∉ [f, c, k, K, p, t]) {q : ℕ} (Cs : ℕ → NCircuit q) (N i : ℕ) (hi : i ≤ N) (cb : ℕ)
    (hfit : ∀ j < N, CircuitFits cap (Cs j)) (hcb : ∀ j < N, circuitCost (Cs j) ≤ cb) (hcap : i ≤ cap)
    (rest : List Bool) (σ : WState ns nr) (hst : σ.st W = cwPrefix Cs N ++ rest) (hsh : σ.sh W = 0)
    (hz : Zeros σ [f, c, k, K, p, t]) (hI0 : σ.val I = i) :
    WExec cap (seekCircuits W f c k K p t I) σ ((σ.seth W (cwPrefix Cs i).length).setv I 0) (i * (cb + 4) + 1) := by
  have hIne : ∀ r ∈ [f, c, k, K, p, t], r ≠ I := fun r hr h => hI (h ▸ hr)
  set g : ℕ → WState ns nr := fun j => (σ.seth W (cwPrefix Cs j).length).setv I (i - j) with hg
  have hg0 : g 0 = σ := by
    apply WState.eq
    · funext x; by_cases hx : x = W
      · subst hx; simp [hg, hsh, cwPrefix]
      · simp [hg, Function.update_of_ne hx]
    · rfl
    · funext r; by_cases hr : r = I
      · subst hr; simp [hg, hI0]
      · simp [hg, Function.update_of_ne hr]
    · rfl
  have hgi : g i = (σ.seth W (cwPrefix Cs i).length).setv I 0 := by simp [hg]
  have hbody : ∀ j < i, WExec cap (skipCircuit true W f c k K p t) ((g j).setv I (i - j - 1)) (g (j + 1)) cb := by
    intro j hj
    have hjN : j < N := lt_of_lt_of_le hj hi
    have hsplit := cwPrefix_split Cs hjN
    have e := skipCircuit_spec cap true W f c k K p t hd (Cs j) (hfit j hjN) (cwPrefix Cs j)
      ((cwPrefix Cs N).drop (cwPrefix Cs (j + 1)).length ++ rest) ((g j).setv I (i - j - 1))
      (by
        show σ.st W = _
        rw [hst]
        conv_lhs => rw [hsplit]
        simp only [WireExponent3_5.PrimAsm.ParseNat.enc, if_true, List.append_assoc])
      (by simp [hg])
      (by
        intro r hr
        simp only [hg, WState.setv_val, WState.seth_val]
        rw [Function.update_of_ne (hIne r hr), Function.update_of_ne (hIne r hr)]
        exact hz r hr)
    refine WExec.cast cap e ?_ (hcb j hjN)
    apply WState.eq
    · funext x; by_cases hx : x = W
      · subst hx; simp [hg, cwPrefix_succ, WireExponent3_5.PrimAsm.ParseNat.stp, marks_length]
      · simp [hg, Function.update_of_ne hx]
    · rfl
    · funext r; by_cases hr : r = I
      · subst hr; simp [hg]; omega
      · simp [hg, Function.update_of_ne hr]
    · rfl
  have e := repLoop_spec cap I (skipCircuit true W f c k K p t) i cb g (fun j _ => by simp [hg]) hcap hbody
  rw [hg0, hgi] at e
  exact e

end NearCubicGates.Close.Codec
