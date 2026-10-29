import SourceAdapters.Code.CappedDock
import Proof.Gates.Codec.Unframe
import Proof.Gates.WordPrograms.RegArith
import Proof.Gates.Cells.Setup
import Proof.Gates.Expand.PolyTabPack

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": paid polynomial-clock request construction. This generic
loader also serves. It starts from an arbitrary raw word, counts
its physical outer frame, and emits the complete extra frame for X8. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.CappedInput

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Codec NearCubicGates.Close.Cells
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

abbrev State := WState 1 6
abbrev Script := WMX 1 6

variable (cap : ℕ)

def emitWord : List Bool → Script
  | [] => .wm .skip
  | b :: bs => .seq (.wr 1 b) (.seq (.fwd 1) (emitWord bs))

def appended (σ : State) (word : List Bool) : State :=
  (σ.sets 1 (σ.st 1 ++ word)).seth 1 (σ.sh 1 + word.length)

theorem emit_word : ∀ (word : List Bool) (σ : State), σ.sh 1 = (σ.st 1).length →
    WXExec cap (emitWord word) σ (appended σ word) (4 * word.length) := by
  intro word
  induction word with
  | nil =>
    intro σ _
    simpa [emitWord, appended, WMX.skip, wsets_same, wseth_same] using WXExec.skip cap σ
  | cons b bs ih =>
    intro σ hO
    have e1 := WXExec.wr cap (1 : Fin 2) b σ
    rw [hO, NearCubicWires.WireExponent3_5.FinalPass.Tm.writeTapeBit_end'] at e1
    let σ1 := σ.sets 1 (σ.st 1 ++ [b])
    have e2 := WXExec.fwd cap (1 : Fin 2) σ1
    let σ2 := σ1.seth 1 (σ1.sh 1 + 1)
    have e3 := ih σ2 (by simp [σ2, σ1, hO])
    have he := WXExec.seq e1 (WXExec.seq e2 e3)
    have hf : appended σ2 bs = appended σ (b :: bs) := by
      apply WState.eq
      · funext i; fin_cases i <;> simp [appended, σ2, σ1]; omega
      · funext i; fin_cases i <;> simp [appended, σ2, σ1, List.append_assoc]
      · rfl
      · rfl
    rw [hf] at he
    convert he using 1 <;> simp [emitWord]
    omega

def loadLength : WM 1 6 := .whs 0 (.seq (.fwd 0) (.seq (.fwd 0) (.inc 0)))

/-- The ClockSize length counter, generalized to arbitrary payload bits. -/
theorem load_length (word : List Bool) (σ : State) (hIN : σ.st 0 = frame word) (hcap : word.length ≤ cap) :
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
    have e3 := WExec.inc (cap := cap) (0 : Fin 6)
      ((τ.seth 0 (τ.sh 0 + 1)).seth 0 ((τ.seth 0 (τ.sh 0 + 1)).sh 0 + 1)) (by simp [τ]; omega)
    have hi := ih (j + 1) (by omega)
    refine WExec.mono (WExec.whsT hb (WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ le_rfl) hi) (by omega)
    apply WState.eq
    · funext i; fin_cases i <;> simp [τ]; omega
    · rfl
    · funext i; fin_cases i <;> simp [τ]
    · rfl

def powerStep : Script := .seq (mulR 0 1 2 3 4) (.seq (.wm (WM.clear 2)) (.wm (WM.move 3 2)))

theorem power_step (σ : State) (h1 : σ.val 1 = 0) (h3 : σ.val 3 = 0) (h4 : σ.val 4 = 0)
    (hA : σ.val 2 ≤ cap) (hN : 2 * σ.val 0 ≤ cap) (hP : σ.val 0 * σ.val 2 ≤ cap) :
    WXExec cap powerStep σ (σ.setv 2 (σ.val 0 * σ.val 2)) (100 * cap + 10) := by
  have e1 := mulR_spec cap (A := (0 : Fin 6)) (A2 := 1) (B := 2) (C := 3) (T := 4)
    (by decide) σ h1 h4 (by simpa [h3] using hP) hN
  rw [h3, Nat.zero_add] at e1
  let σ1 := σ.setv 3 (σ.val 0 * σ.val 2)
  have e2 := wclear_spec cap (2 : Fin 6) (σ.val 2) σ1 (by simp [σ1]) (by simpa [σ1] using hA)
  let σ2 := σ1.setv 2 0
  have e3 := wmove_spec cap (3 : Fin 6) 2 (by decide) (σ.val 0 * σ.val 2) σ2
    (by simp [σ2, σ1]) (by simpa [σ2, σ1] using hP) (by simpa [σ2, σ1] using hP)
  have he := WXExec.seq e1 (WXExec.seq (WXExec.wm e2) (WXExec.wm e3))
  have hf : (σ2.setv 3 0).setv 2 (σ2.val 2 + σ2.val 3) = σ.setv 2 (σ.val 0 * σ.val 2) := by
    apply WState.eq <;> try rfl
    funext i; fin_cases i <;> simp [σ2, σ1, h3]
  rw [hf] at he
  refine he.cast cap rfl ?_
  nlinarith

def power : ℕ → Script
  | 0 => .wm .skip
  | e + 1 => .seq powerStep (power e)

theorem power_spec (N A e : ℕ) (σ : State) (h0 : σ.val 0 = N) (h2 : σ.val 2 = A)
    (h1 : σ.val 1 = 0) (h3 : σ.val 3 = 0) (h4 : σ.val 4 = 0)
    (hN : 2 * N ≤ cap) (hA : ∀ j ≤ e, A * N ^ j ≤ cap) :
    WXExec cap (power e) σ (σ.setv 2 (A * N ^ e)) (e * (100 * cap + 11)) := by
  induction e generalizing A σ with
  | zero =>
    simpa [power, h2, BinW.setv_same, WMX.skip] using WXExec.skip cap σ
  | succ e ih =>
    have ea := power_step cap σ h1 h3 h4 (by simpa [h2] using hA 0 (by omega))
      (by simpa [h0] using hN) (by simpa [h0, h2, Nat.mul_comm] using hA 1 (by omega))
    rw [h0, h2, Nat.mul_comm N A] at ea
    have ei := ih (A * N) (σ.setv 2 (A * N)) (by simp [h0]) (by simp)
      (by simp [h1]) (by simp [h3]) (by simp [h4])
      (by intro j hj; have hh := hA (j + 1) (by omega); simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hh)
    have he := WXExec.seq ea ei
    have hf : (σ.setv 2 (A * N)).setv 2 (A * N * N ^ e) = σ.setv 2 (A * N ^ (e + 1)) := by
      rw [wsetv_setv, pow_succ]
      congr 1
      ring
    rw [hf] at he
    refine he.cast cap rfl ?_
    nlinarith

theorem appended_append (σ : State) (x y : List Bool) :
    appended (appended σ x) y = appended σ (x ++ y) := by
  apply WState.eq
  · funext i; fin_cases i <;> simp [appended]; omega
  · funext i; fin_cases i <;> simp [appended, List.append_assoc]
  · rfl
  · rfl

def emitCopies (reg : Fin 6) (word : List Bool) : Script := .whr reg (.seq (.dec reg) (emitWord word))

theorem emit_copies (reg : Fin 6) (word : List Bool) : ∀ (n : ℕ) (σ : State),
    σ.val reg = n → n ≤ cap → σ.sh 1 = (σ.st 1).length →
      WXExec cap (emitCopies reg word) σ (appended (σ.setv reg 0) ((List.replicate n word).flatten))
        ((4 * word.length + 4) * n + 1) := by
  intro n
  induction n with
  | zero =>
    intro σ hc _ _
    have he : σ.setv reg 0 = σ := by rw [← hc, wsetv_same]
    simpa [emitCopies, appended, he, wsets_same, wseth_same] using
      (WXExec.whrF (cap := cap) (r := reg) (P := .seq (.dec reg) (emitWord word)) hc)
  | succ n ih =>
    intro σ hc hn hO
    have e1 := WXExec.dec cap reg σ (by omega)
    rw [hc, Nat.add_sub_cancel] at e1
    have e2 := emit_word cap word (σ.setv reg n) (by simpa using hO)
    have ei := ih (appended (σ.setv reg n) word) (by simp [appended]) (by omega)
      (by simp [appended, hO])
    have he := WXExec.whrT (r := reg) (by omega) (WXExec.seq e1 e2) ei
    have hf : appended ((appended (σ.setv reg n) word).setv reg 0) ((List.replicate n word).flatten) =
        appended (σ.setv reg 0) ((List.replicate (n + 1) word).flatten) := by
      have hs : (appended (σ.setv reg n) word).setv reg 0 = appended (σ.setv reg 0) word := by
        apply WState.eq <;> try rfl
        funext i; simp [appended, WState.setv, Function.update_apply]
      rw [hs, appended_append]
      simp [List.replicate_succ]
    rw [hf] at he
    exact he.cast cap rfl (by nlinarith)

def arithmeticSetup (K offset : ℕ) : Script :=
  .seq (addR 0 1 4) (.seq (addR 0 1 4) (.seq (.wm (WM.rewind 0 1))
    (.seq (addR 0 5 4) (.seq (addR 0 5 4) (.seq (incN 5 1)
      (.seq (incN 0 offset) (incN 2 K)))))))

def setupState (σ : State) (K offset : ℕ) : State :=
  (((σ.seth 0 0).setv 0 (σ.val 0 + offset)).setv 2 K).setv 5 (2 * σ.val 0 + 1)

theorem arithmetic_setup (K offset : ℕ) (σ : State)
    (h1 : σ.val 1 = 0) (h2 : σ.val 2 = 0) (h4 : σ.val 4 = 0) (h5 : σ.val 5 = 0)
    (hH : σ.sh 0 = 2 * σ.val 0) (hn : 2 * σ.val 0 + 1 ≤ cap)
    (hb : σ.val 0 + offset ≤ cap) (hK : K ≤ cap) :
    WXExec cap (arithmeticSetup K offset) σ (setupState σ K offset)
      (82 * σ.val 0 + 4 * offset + 4 * K + 24) := by
  have e1 := addR_spec cap (A := (0 : Fin 6)) (B := 1) (T := 4) (by decide) (by decide) (by decide) σ h4
    (by rw [h1]; omega)
  rw [h1, Nat.zero_add] at e1
  let σ1 := σ.setv 1 (σ.val 0)
  have e2 := addR_spec cap (A := (0 : Fin 6)) (B := 1) (T := 4) (by decide) (by decide) (by decide) σ1
    (by simp [σ1, h4]) (by simp [σ1]; omega)
  let σ2 := σ1.setv 1 (σ1.val 1 + σ1.val 0)
  have e3 := wrewind_spec cap (0 : Fin 2) 1 (2 * σ.val 0) σ2
    (by simp [σ2, σ1]; omega) (by simp [σ2, σ1]; omega)
  let σ3 := (σ2.setv 1 0).seth 0 (σ2.sh 0 - 2 * σ.val 0)
  have e4 := addR_spec cap (A := (0 : Fin 6)) (B := 5) (T := 4) (by decide) (by decide) (by decide) σ3
    (by simp [σ3, σ2, σ1, h4]) (by simp [σ3, σ2, σ1, h5]; omega)
  let σ4 := σ3.setv 5 (σ3.val 5 + σ3.val 0)
  have e5 := addR_spec cap (A := (0 : Fin 6)) (B := 5) (T := 4) (by decide) (by decide) (by decide) σ4
    (by simp [σ4, σ3, σ2, σ1, h4]) (by simp [σ4, σ3, σ2, σ1, h5]; omega)
  let σ5 := σ4.setv 5 (σ4.val 5 + σ4.val 0)
  have e6 := incN_spec cap (5 : Fin 6) 1 σ5 (by simp [σ5, σ4, σ3, σ2, σ1, h5]; omega)
  let σ6 := σ5.setv 5 (σ5.val 5 + 1)
  have e7 := incN_spec cap (0 : Fin 6) offset σ6 (by simpa [σ6, σ5, σ4, σ3, σ2, σ1] using hb)
  let σ7 := σ6.setv 0 (σ6.val 0 + offset)
  have e8 := incN_spec cap (2 : Fin 6) K σ7 (by simpa [σ7, σ6, σ5, σ4, σ3, σ2, σ1, h2] using hK)
  have he := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq (WXExec.wm e3)
    (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6 (WXExec.seq e7 e8))))))
  have hf : σ7.setv 2 (σ7.val 2 + K) = setupState σ K offset := by
    apply WState.eq
    · funext i; fin_cases i <;> simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, setupState, hH]
    · rfl
    · funext i; fin_cases i <;> simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1, setupState, h1, h2, h5]; omega
    · rfl
  rw [hf] at he
  refine he.cast cap rfl ?_
  simp [σ1, σ3, σ2, σ4]
  omega

def outputStage : Script := .seq (emitCopies 2 [true, true, true, true])
  (.seq (emitWord [true, false]) (.seq (.wm (frameStream 0 1 4 5)) (emitWord [false])))

theorem request_frame (fuel : ℕ) (word : List Bool) :
    frame (NearCubicGates.Adapters.Joins.cappedRequestWord (fuel, word)) =
      (List.replicate fuel [true, true, true, true]).flatten ++ [true, false] ++
        Streaming.marks (frame word) ++ [false] := by
  have hu : ∀ n : ℕ, Streaming.marks (frame (List.replicate n true)) =
      (List.replicate n [true, true, true, true]).flatten ++ [true, false] := by
    intro n
    induction n <;> simp_all [frame, Streaming.marks, List.replicate_succ]
  rw [NearCubicGates.Adapters.Joins.cappedRequestWord, frame_eq_marks]
  simp only [Streaming.marks, List.flatMap_append] at hu ⊢
  rw [hu]

theorem output_stage (word : List Bool) (fuel : ℕ) (σ : State)
    (hIN : σ.st 0 = frame word) (hIH : σ.sh 0 = 0)
    (hOH : σ.sh 1 = (σ.st 1).length) (h2 : σ.val 2 = fuel) (h4 : σ.val 4 = 0)
    (h5 : σ.val 5 = 2 * word.length + 1) (hF : fuel ≤ cap) (hN : 4 * word.length + 2 ≤ cap) :
    ∃ τ, WXExec cap outputStage σ τ (20 * fuel + 44 * word.length + 40) ∧
      τ.st 1 = σ.st 1 ++ frame (NearCubicGates.Adapters.Joins.cappedRequestWord (fuel, word)) := by
  have e1 := emit_copies cap (2 : Fin 6) [true, true, true, true] fuel σ h2 hF hOH
  let σ1 := appended (σ.setv 2 0) ((List.replicate fuel [true, true, true, true]).flatten)
  have hO1 : σ1.sh 1 = (σ1.st 1).length := by simp [σ1, appended, hOH]
  have e2 := emit_word cap [true, false] σ1 hO1
  let σ2 := appended σ1 [true, false]
  have hO2 : σ2.sh 1 = (σ2.st 1).length := by simp [σ2, appended, hO1]
  have e3 := frameStream_spec cap (0 : Fin 2) 1 (by decide) (4 : Fin 6) 5 (by decide)
    (frame word) [] [] σ2 (by simp [σ2, σ1, appended, hIN]) (by simp [σ2, σ1, appended, hIH]) hO2
    (by simp [σ2, σ1, appended, h5, frame_length]) (by rw [frame_length]; omega)
    (by simp [σ2, σ1, appended, h4, frame_length]; omega)
  let σ3 := ((appendO σ2 1 4 (Streaming.marks (frame word))).setv 5 0).seth 0 (0 + (frame word).length)
  have hO3 : σ3.sh 1 = (σ3.st 1).length := by simp [σ3, appendO, hO2]
  have e4 := emit_word cap [false] σ3 hO3
  refine ⟨_, (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq (WXExec.wm e3) e4))).mono ?_, ?_⟩
  · simp [frame_length]
    omega
  · rw [request_frame]
    simp [σ3, σ2, σ1, appended, appendO, List.append_assoc]

def resource (K offset e n : ℕ) : ℕ := 10 * (K + 1) * (n + offset + 1) ^ (e + 1) + 10

theorem resource_bounds (K offset e n : ℕ) :
    1 ≤ resource K offset e n ∧ 4 * n + 2 ≤ resource K offset e n ∧
    n + offset ≤ resource K offset e n ∧ K ≤ resource K offset e n ∧
    2 * (n + offset) ≤ resource K offset e n ∧
    (∀ j ≤ e, K * (n + offset) ^ j ≤ resource K offset e n) := by
  have hp : n + offset + 1 ≤ (n + offset + 1) ^ (e + 1) := Nat.le_self_pow (by omega) _
  have hp1 : 1 ≤ (n + offset + 1) ^ (e + 1) := by omega
  have hprod : (n + offset + 1) ^ (e + 1) ≤ (K + 1) * (n + offset + 1) ^ (e + 1) := by nlinarith
  refine ⟨by dsimp [resource]; omega, by dsimp [resource]; nlinarith,
    by dsimp [resource]; nlinarith, by dsimp [resource]; nlinarith,
    by dsimp [resource]; nlinarith, ?_⟩
  intro j hj
  have hpow := (Nat.pow_le_pow_left (show n + offset ≤ n + offset + 1 by omega) j).trans
    (Nat.pow_le_pow_right (show 1 ≤ n + offset + 1 by omega) (show j ≤ e + 1 by omega))
  have hm := Nat.mul_le_mul_left K hpow
  dsimp [resource]
  nlinarith

def loader (K offset e : ℕ) : Script := .seq (.wm loadLength)
  (.seq (arithmeticSetup K offset) (.seq (power e) outputStage))

def loaderCost (K offset e n : ℕ) : ℕ :=
  (9 * n + 1) + (82 * n + 4 * offset + 4 * K + 24) +
    e * (100 * resource K offset e n + 11) + (20 * (K * (n + offset) ^ e) + 44 * n + 40) + 3

theorem loader_runs (K offset e : ℕ) (word : List Bool) :
    ∃ τ, WXExec (resource K offset e word.length) (loader K offset e)
      (NearCubicGates.Close.Expand.PolyTab.idealStart 1 6 word (fun _ => 0)) τ (loaderCost K offset e word.length) ∧
      τ.st 1 = frame (NearCubicGates.Adapters.Joins.cappedRequestWord (K * (word.length + offset) ^ e, word)) := by
  let R := resource K offset e word.length
  obtain ⟨hR, hN, hB, hK, h2B, hpow⟩ := resource_bounds K offset e word.length
  let σ := NearCubicGates.Close.Expand.PolyTab.idealStart 1 6 word (fun _ => 0)
  have e1 := load_length R word σ (by simp [σ, NearCubicGates.Close.Expand.PolyTab.idealStart]) (by dsimp [R]; omega)
    word.length 0 (by omega)
  have hs : (σ.seth 0 (2 * 0)).setv 0 0 = σ := by
    apply WState.eq
    · funext i; fin_cases i <;> simp [σ, NearCubicGates.Close.Expand.PolyTab.idealStart]
    · rfl
    · funext i; fin_cases i <;> simp [σ, NearCubicGates.Close.Expand.PolyTab.idealStart]
    · rfl
  rw [hs] at e1
  let σ1 := (σ.seth 0 (2 * word.length)).setv 0 word.length
  have e2 := arithmetic_setup R K offset σ1
    (by simp [σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by simp [σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by simp [σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by simp [σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart]) (by simp [σ1])
    (by simp [σ1, R]; omega) (by simpa [σ1, R] using hB) hK
  let σ2 := setupState σ1 K offset
  have e3 := power_spec R (word.length + offset) K e σ2
    (by simp [σ2, setupState, σ1]) (by simp [σ2, setupState])
    (by simp [σ2, setupState, σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by simp [σ2, setupState, σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by simp [σ2, setupState, σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart]) h2B hpow
  let σ3 := σ2.setv 2 (K * (word.length + offset) ^ e)
  obtain ⟨τ, e4, ho⟩ := output_stage R word (K * (word.length + offset) ^ e) σ3
    (by simp [σ3, σ2, setupState, σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by simp [σ3, σ2, setupState])
    (by simp [σ3, σ2, setupState, σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart]) (by simp [σ3])
    (by simp [σ3, σ2, setupState, σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart])
    (by simp [σ3, σ2, setupState, σ1]) (hpow e le_rfl) hN
  refine ⟨τ, (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.seq e3 e4))).mono ?_, ?_⟩
  · simp [loaderCost, σ1, R]
    omega
  · simpa [σ3, σ2, setupState, σ1, σ, NearCubicGates.Close.Expand.PolyTab.idealStart] using ho

def budget (K offset e : ℕ) (word : List Bool) : ℕ := 2 * loaderCost K offset e word.length + 2

/-- The complete ordinary loader, including the final paid head reset. -/
noncomputable def wordFunction (K offset e : ℕ) :
    WordFunction (List Bool) id
      (fun word => frame (NearCubicGates.Adapters.Joins.cappedRequestWord
        (K * (word.length + offset) ^ e, word))) (budget K offset e) :=
  NearCubicGates.Close.Expand.PolyTab.wordFunction_of_ideal (loader K offset e) 1 (by decide)
    (fun word => resource K offset e word.length) (fun _ _ => 0)
    (fun word => loaderCost K offset e word.length) (fun _ => le_rfl)
    (fun word => ⟨rfl, loader_runs K offset e word⟩)

theorem resource_poly (K offset e n : ℕ) :
    resource K offset e n ≤ (10 * (K + 1) * (offset + 1) ^ (e + 1) + 10) * (n + 1) ^ (e + 1) := by
  have hb : n + offset + 1 ≤ (offset + 1) * (n + 1) := by nlinarith
  have hp := Nat.pow_le_pow_left hb (e + 1)
  rw [mul_pow] at hp
  have hm := Nat.mul_le_mul_left (10 * (K + 1)) hp
  have hH : 1 ≤ (n + 1) ^ (e + 1) := by
    have := Nat.le_self_pow (by omega : e + 1 ≠ 0) (n + 1)
    omega
  dsimp [resource]
  nlinarith

def budgetCoefficient (K offset e : ℕ) : ℕ :=
  (200 * e + 40) * (10 * (K + 1) * (offset + 1) ^ (e + 1) + 10) +
    270 + 8 * offset + 8 * K + 22 * e + 138

theorem budget_bound (K offset e : ℕ) (word : List Bool) :
    budget K offset e word ≤ budgetCoefficient K offset e * (word.length + 1) ^ (e + 1) := by
  let n := word.length
  let R := resource K offset e n
  let H := (n + 1) ^ (e + 1)
  let D := 10 * (K + 1) * (offset + 1) ^ (e + 1) + 10
  let C := 8 * offset + 8 * K + 22 * e + 138
  have hF : K * (n + offset) ^ e ≤ R := (resource_bounds K offset e n).2.2.2.2.2 e le_rfl
  have hR : R ≤ D * H := resource_poly K offset e n
  have hn : n + 1 ≤ H := Nat.le_self_pow (by omega) _
  have h1 := Nat.mul_le_mul_left (200 * e + 40) hR
  have h2 := Nat.mul_le_mul_left 270 (show n ≤ H by omega)
  have h3 := Nat.mul_le_mul_left C (show 1 ≤ H by omega)
  have hcost : budget K offset e word ≤ (200 * e + 40) * R + 270 * n + C := by
    dsimp [budget, loaderCost, C, n, R] at *
    nlinarith
  calc
    budget K offset e word ≤ (200 * e + 40) * R + 270 * n + C := hcost
    _ ≤ (200 * e + 40) * (D * H) + 270 * H + C * H := by nlinarith
    _ = budgetCoefficient K offset e * (word.length + 1) ^ (e + 1) := by
      dsimp [budgetCoefficient, D, H, C, n]
      ring

theorem budget_poly (K offset e : ℕ) : ∃ C d : ℕ, ∀ word : List Bool,
    budget K offset e word ≤ C * (word.length + 1) ^ d :=
  ⟨budgetCoefficient K offset e, e + 1, budget_bound K offset e⟩

/-- Shared code/PCPP specialization requested for a clock in `(|w|+1)^e`. -/
noncomputable def cappedInputWordFunction (K e : ℕ) :
    WordFunction (List Bool) id
      (fun word => frame (NearCubicGates.Adapters.Joins.cappedRequestWord
        (K * (word.length + 1) ^ e, word))) (budget K 1 e) := wordFunction K 1 e

theorem cappedInputBudget_poly (K e : ℕ) : ∃ C d : ℕ, ∀ word : List Bool,
    budget K 1 e word ≤ C * (word.length + 1) ^ d := budget_poly K 1 e

end NearCubicGates.Adapters.Code.CappedInput
