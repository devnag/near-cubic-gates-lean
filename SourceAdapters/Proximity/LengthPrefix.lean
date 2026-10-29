import SourceAdapters.Proximity.CircuitInput
import Proof.Gates.Codec.Unframe
import Proof.Gates.WordPrograms.RegArith
import Proof.Gates.Expand.PolyTabPack

/-! Q04: a paid logarithmic size header for arbitrary words, including trailing
zeros. The result is exactly frame(natWord |w| ++ w). It permits Cells' width
allocation to depend polynomially on the physical input length. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Proximity.LengthPrefix

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Expand.PolyTab
open StablePartition.Workspace (overlay)

abbrev State := WState 1 8
abbrev Script := WMX 1 8

/-- The CODE.ClockSize counter, instantiated with the writer's eight registers. -/
def loadLength : WM 1 8 := .whs 0 (.seq (.fwd 0) (.seq (.fwd 0) (.inc 0)))

theorem load_length (cap : ℕ) (word : List Bool) (σ : State)
    (hIN : σ.st 0 = frame word) (hcap : word.length ≤ cap) :
    ∀ m j, j + m = word.length →
      WExec cap loadLength ((σ.seth 0 (2 * j)).setv 0 j)
        ((σ.seth 0 (2 * word.length)).setv 0 word.length) (9 * m + 1) := by
  intro m
  induction m with
  | zero =>
    intro j hj
    rw [Nat.add_zero] at hj; subst hj
    refine WExec.mono (WExec.whsF ?_) (by omega)
    change readTapeBit (σ.st 0) (2 * word.length) = false
    rw [hIN, readTapeBit, NearCubicGates.Close.Codec.frame_getD_even]
    simp
  | succ m ih =>
    intro j hj
    let τ := (σ.seth 0 (2 * j)).setv 0 j
    have hb : wbit τ 0 = true := by
      change readTapeBit (σ.st 0) (2 * j) = true
      rw [hIN, readTapeBit, NearCubicGates.Close.Codec.frame_getD_even]
      simp; omega
    have e1 := WExec.fwd (cap := cap) (0 : Fin 2) τ
    have e2 := WExec.fwd (cap := cap) (0 : Fin 2) (τ.seth 0 (τ.sh 0 + 1))
    have e3 := WExec.inc (cap := cap) (0 : Fin 8)
      ((τ.seth 0 (τ.sh 0 + 1)).seth 0 ((τ.seth 0 (τ.sh 0 + 1)).sh 0 + 1))
      (by simp [τ]; omega)
    have hi := ih (j + 1) (by omega)
    refine WExec.mono (WExec.whsT hb (WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ le_rfl) hi)
      (by omega)
    apply WState.eq
    · funext i; fin_cases i <;> simp [τ]; omega
    · rfl
    · funext i; fin_cases i <;> simp [τ]
    · rfl

def rewindInput : Script := .seq (addR 0 1 6)
  (.seq (addR 0 1 6) (.wm (WM.rewind 0 1)))

theorem rewind_input (cap : ℕ) (σ : State) (h1 : σ.val 1 = 0) (h6 : σ.val 6 = 0)
    (hH : σ.sh 0 = 2 * σ.val 0) (hcap : 2 * σ.val 0 ≤ cap) :
    WXExec cap rewindInput σ (σ.seth 0 0) (46 * σ.val 0 + 9) := by
  have e1 := addR_spec cap (A := (0 : Fin 8)) (B := 1) (T := 6)
    (by decide) (by decide) (by decide) σ h6 (by rw [h1]; omega)
  rw [h1, Nat.zero_add] at e1
  let σ1 := σ.setv 1 (σ.val 0)
  have e2 := addR_spec cap (A := (0 : Fin 8)) (B := 1) (T := 6)
    (by decide) (by decide) (by decide) σ1 (by simp [σ1, h6]) (by simp [σ1]; omega)
  let σ2 := σ1.setv 1 (σ1.val 1 + σ1.val 0)
  have e3 := wrewind_spec cap (0 : Fin 2) 1 (2 * σ.val 0) σ2
    (by simp [σ2, σ1]; omega) (by simp [σ2, σ1]; omega)
  have he := WXExec.seq e1 (WXExec.seq e2 (WXExec.wm e3))
  have hf : (σ2.setv 1 0).seth 0 (σ2.sh 0 - 2 * σ.val 0) = σ.seth 0 0 := by
    apply WState.eq
    · funext i; fin_cases i <;> simp [σ2, σ1, hH]
    · rfl
    · funext i; fin_cases i <;> simp [σ2, σ1, h1]
    · rfl
  rw [hf] at he
  exact he.cast cap rfl (by simp [σ1]; omega)

def loader : Script := .seq (.wm loadLength)
  (.seq (.wm (writeNatM 1 (Function.Embedding.refl (Fin 8))))
    (.seq rewindInput (.wm (appendRec 0 1 1 7))))

def cost (word : List Bool) : ℕ :=
  (natBitLength word.length + 10) * (100 * word.length + 200) + 95 * word.length + 24

theorem loader_runs (word : List Bool) :
    ∃ τ : State, WXExec (20 * (word.length + 1)) loader
      (idealStart 1 8 word (fun _ => 0)) τ (cost word) ∧
      τ.st 1 = frame (natWord word.length ++ word) := by
  let cap := 20 * (word.length + 1)
  let σ : State := idealStart 1 8 word (fun _ => 0)
  have hbits := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le word.length
  have e1 := load_length cap word σ rfl (by dsimp [cap]; omega) word.length 0 (by omega)
  have hs0 : (σ.seth 0 (2 * 0)).setv 0 0 = σ := by
    apply WState.eq <;> simp [σ, idealStart]
  rw [hs0] at e1
  let σ1 := (σ.seth 0 (2 * word.length)).setv 0 word.length
  have e2 := writeNatM_spec cap (1 : Fin 2) (Function.Embedding.refl (Fin 8)) σ1
    (by simp [σ1, σ, idealStart]) (by simp [σ1, σ, idealStart])
    (by simp [σ1, σ, idealStart]) (by simp [σ1, σ, idealStart])
    (by simp [σ1, σ, idealStart]) (by simp [σ1, σ, idealStart])
    (by simp [σ1, σ, idealStart]) (by simp [σ1, σ, idealStart]; dsimp [cap]; omega)
  let out := Streaming.marks (natWord word.length)
  let σ2 := appendO σ1 1 7 out
  have hoLen : out.length = 4 * natBitLength word.length + 2 := by
    simp [out, Streaming.marks_length]
    omega
  have e3 := rewind_input cap σ2
    (by simp [σ2, σ1, σ, idealStart]) (by simp [σ2, σ1, σ, idealStart])
    (by simp [σ2, σ1]) (by simp [σ2, σ1]; dsimp [cap]; omega)
  let σ3 := σ2.seth 0 0
  have e4 := appendRec_spec cap (Src := (0 : Fin 2)) (O := 1) (CS := (1 : Fin 8)) (CO := 7)
    (by decide) (by decide) σ3 word [] out []
    (by simp [σ3, σ2, σ1, σ, idealStart, frame_eq_frameP])
    (by simp [σ3]) (by simp [σ3, σ2, σ1, σ, idealStart])
    (by simp [OutOn, σ3, σ2, σ1, σ, idealStart, overlay])
    (by rw [hoLen]; dsimp [cap]; omega)
  refine ⟨_, (WXExec.seq (WXExec.wm e1) (WXExec.seq (WXExec.wm e2)
    (WXExec.seq e3 (WXExec.wm e4)))).cast cap rfl ?_, ?_⟩
  · simp [cost, σ2, σ1]
    omega
  · simp only [WState.setv_st, WState.seth_st, WState.sets_st, Function.update_self]
    simpa [overlay, out] using (Streaming.frame_append (natWord word.length) word).symm

/-- Actual ordinary program, with all final head resets included. -/
noncomputable def wordFunction : WordFunction (List Bool) id
    (fun word => frame (natWord word.length ++ word)) (fun word => 2 * cost word + 2) :=
  wordFunction_of_ideal loader 1 (by decide) (fun word => 20 * (word.length + 1))
    (fun _ _ => 0) cost (fun _ => le_rfl) (fun word => ⟨rfl, loader_runs word⟩)

theorem budget_bound (word : List Bool) : 2 * cost word + 2 ≤ 10000 * (word.length + 1) ^ 2 := by
  have hbits := NearCubicGates.Close.CheckedPCPP.NodeEmit.natBitLength_le word.length
  have hh := Nat.mul_le_mul_right (100 * word.length + 200)
    (show natBitLength word.length + 10 ≤ word.length + 11 by omega)
  unfold cost
  nlinarith [Nat.zero_le (word.length ^ 2)]

/-- Uniform quadratic ordinary budget for the exact framed output. -/
noncomputable def polynomialWordFunction : WordFunction (List Bool) id
    (fun word => frame (natWord word.length ++ word))
    (fun word => 10000 * (word.length + 1) ^ 2) :=
  wordFunction.enlargeBudget budget_bound

end NearCubicGates.Adapters.Proximity.LengthPrefix
