import SourceAdapters.Code.CappedInput
import SourceAdapters.Code.PolynomialCosts
import SourceAdapters.Code.Preparation
import Proof.Gates.CounterMachine.CellTablesSet

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid logarithmic-size prefixing which preserves the entire
input word, used by total decoder preprocessing. No target field is discarded. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.LengthPreparation

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Codec NearCubicGates.Close.CounterMachine.CellTablesProg
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open CappedInput

def prepared (word : List Bool) : List Bool := List.replicate word.length.size true ++ false :: word

def outputStage : Script := .seq (emitCopies 2 [true, true])
  (.seq (emitWord [true, false]) (.wm (copyFrameW 0 1 4)))

theorem output_stage (cap : ℕ) (word : List Bool) (σ : State)
    (hIN : σ.st 0 = frame word) (hIH : σ.sh 0 = 0) (hOH : σ.sh 1 = (σ.st 1).length)
    (h2 : σ.val 2 = word.length.size) (h4 : σ.val 4 = 0) (hN : 2 * word.length + 1 ≤ cap) :
    ∃ τ, WXExec cap outputStage σ τ (12 * word.length.size + 22 * word.length + 20) ∧
      τ.st 1 = σ.st 1 ++ frame (prepared word) := by
  have hs : word.length.size ≤ word.length := Nat.size_le.mpr Nat.lt_two_pow_self
  have e1 := emit_copies cap (2 : Fin 6) [true, true] word.length.size σ h2 (by omega) hOH
  let σ1 := appended (σ.setv 2 0) ((List.replicate word.length.size [true, true]).flatten)
  have hO1 : σ1.sh 1 = (σ1.st 1).length := by simp [σ1, appended, hOH]
  have e2 := emit_word cap [true, false] σ1 hO1
  let σ2 := appended σ1 [true, false]
  have e3 := copyFrameW_spec cap (0 : Fin 2) 1 (by decide) (4 : Fin 6) word [] σ2
    (by simp [σ2, σ1, appended, hIN]) (by simp [σ2, σ1, appended, hIH])
    (by simp [σ2, σ1, appended, hOH, Nat.add_assoc]) (by simpa [σ2, σ1, appended, h4] using hN)
  refine ⟨_, (WXExec.seq e1 (WXExec.seq e2 (WXExec.wm e3))).mono (by simp; omega), ?_⟩
  have hun : ∀ k : ℕ, Streaming.marks (List.replicate k true) = (List.replicate k [true, true]).flatten := by
    intro k
    induction k <;> simp_all [Streaming.marks, List.replicate_succ]
  rw [prepared, Streaming.frame_append, hun]
  simp [σ2, σ1, appendO, appended, frame, List.append_assoc]

def loader : Script := .seq (.wm loadLength) (.seq (arithmeticSetup 0 0)
  (.seq (sizeL 0 1 2) outputStage))

def resource (n : ℕ) : ℕ := 10 * n + 20

def loaderCost (n : ℕ) : ℕ := 1000 * (n + 1)

theorem loader_runs (word : List Bool) :
    ∃ τ, WXExec (resource word.length) loader
      (NearCubicGates.Close.Expand.PolyTab.idealStart 1 6 word (fun _ => 0)) τ (loaderCost word.length) ∧
      τ.st 1 = frame (prepared word) := by
  let R := resource word.length
  let σ := NearCubicGates.Close.Expand.PolyTab.idealStart 1 6 word (fun _ => 0)
  have hs : word.length.size ≤ word.length := Nat.size_le.mpr Nat.lt_two_pow_self
  have e1 := load_length R word σ (by simp [σ, NearCubicGates.Close.Expand.PolyTab.idealStart]) (by dsimp [R, resource]; omega)
    word.length 0 (by omega)
  have hstart : (σ.seth 0 (2 * 0)).setv 0 0 = σ := by
    apply WState.eq
    · funext i; fin_cases i <;> simp [σ, NearCubicGates.Close.Expand.PolyTab.idealStart]
    · rfl
    · funext i; fin_cases i <;> simp [σ, NearCubicGates.Close.Expand.PolyTab.idealStart]
    · rfl
  rw [hstart] at e1
  let σ1 := (σ.seth 0 (2 * word.length)).setv 0 word.length
  have e2 := arithmetic_setup R 0 0 σ1
    (by simp [σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by simp [σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by simp [σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by simp [σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart]) (by simp [σ1])
    (by simp [σ1, R, resource]; omega) (by simp [σ1, R, resource]; omega) (by omega)
  let σ2 := setupState σ1 0 0
  have e3 := sizeL_spec R (0 : Fin 6) 1 2 (by decide) (by decide) (by decide) word.length σ2
    (by simp [σ2, setupState, σ1])
    (by simp [σ2, setupState, σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by dsimp [R, resource]; omega) (by simp [σ2, setupState, R, resource]; omega)
  let σ3 := (σ2.setv 0 0).setv 2 (σ2.val 2 + word.length.size)
  obtain ⟨τ, e4, ho⟩ := output_stage R word σ3
    (by simp [σ3, σ2, setupState, σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by simp [σ3, σ2, setupState])
    (by simp [σ3, σ2, setupState, σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by simp [σ3, σ2, setupState])
    (by simp [σ3, σ2, setupState, σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by dsimp [R, resource]; omega)
  refine ⟨τ, (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.seq e3 e4))).mono ?_, ?_⟩
  · simp [loaderCost, σ1]
    omega
  · simpa [σ3, σ2, setupState, σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart] using ho

def budget (word : List Bool) : ℕ := 2 * loaderCost word.length + 2

noncomputable def wordFunction : WordFunction (List Bool) id (fun word => frame (prepared word)) budget :=
  NearCubicGates.Close.Expand.PolyTab.wordFunction_of_ideal loader 1 (by decide)
    (fun word => resource word.length) (fun _ _ => 0) (fun word => loaderCost word.length)
    (fun _ => le_rfl) (fun word => ⟨rfl, loader_runs word⟩)

theorem budget_poly : PolynomialCosts.Bound List.length budget :=
  ⟨2002, 1, fun word => by simp only [budget, loaderCost, pow_one]; omega⟩

theorem leading (word : List Bool) : NearCubicGates.Close.Cells.leadOnes (prepared word) = word.length.size :=
  leadOnes_rep _ _

theorem capacity (word : List Bool) : word.length < 2 ^ NearCubicGates.Close.Cells.leadOnes (prepared word) := by
  rw [leading]
  exact Nat.lt_size_self _

theorem allocation (word : List Bool) :
    2 ^ NearCubicGates.Close.Cells.leadOnes (prepared word) ≤ 2 * (word.length + 1) := by
  rw [leading, ← Nat.size_eq_bits_len]
  exact Parsing.two_pow_bits_length_le _

end NearCubicGates.Adapters.Code.LengthPreparation
