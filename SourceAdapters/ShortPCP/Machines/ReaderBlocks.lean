import SourceAdapters.ShortPCP.Machines.ReaderWords
import SourceAdapters.ShortPCP.Machines.Coroutine
import Proof.Gates.WordPrograms.OutX

/-!
# Single-run time, stage 3 (reader): the blocks of one call

The reader (`Time.ReaderStage`; proof of `thm:short-pcp-ours`, Step 4: "its proof bits are read at addresses below L_π … replace each read
of a proof bit by an oracle gate on the ℓ address bits") is a re-entrant WMX program on the coroutine seam
`Machines/Coroutine.lean`. Streams: `S = 0` (the framed reader word), `OUT = 1`, `Qs = 2` (query), `AN = 3` (answer
cell), `FL = 4` (ask flag); registers `P = 0` (the `S` head), `CQ = 1` (the `Qs` head), `G = 2` (loop flag),
`CO = 3` (the `OUT` head).

During a call the word on `S` is `frame (A ++ B)` with the head on the odd cell `2|A| + 1`, i.e. on bit `|A|` of the
word (`at'`): reading tests the first bit of `B` (`frame_odd`), writing replaces it (`frame_write_odd`), and `stepU`
moves one bit of the word forward. This module proves the blocks: `stepU`, the bit writes, the unary skip, the
frame skip `skipF` and the frame copy `copyF` (to `Qs`).
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Machines.ReaderRun

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.ShortPCP.Machines.Reader
open StablePartition.Workspace (overlay)

abbrev St := WState 4 4

/-- The state during a call: `S = frame u` (head `h`, `P = h`), `OUT` empty, `Qs = qs` (head `hq`, `CQ = hq`),
`AN = an`, `FL = fl`, `G = g`. -/
def sc (u : List Bool) (h : ℕ) (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ) : St :=
  ⟨![h, 0, hq, 0, 0], ![frame u, [], qs, an, fl], ![h, hq, g, 0], false⟩

/-- The head on bit `|A|` of the word `A ++ B`. -/
def at' (A B : List Bool) (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ) : St :=
  sc (A ++ B) (2 * A.length + 1) qs hq an fl g

variable (cap : ℕ)

/-! ## Reading and writing a bit of the word -/

theorem frame_odd_app (A B : List Bool) (b : Bool) :
    readTapeBit (frame (A ++ b :: B)) (2 * A.length + 1) = b := by
  rw [frame_odd _ _ (by simp)]
  simp

theorem frame_write_app (A B : List Bool) (b c : Bool) :
    writeTapeBit (frame (A ++ b :: B)) (2 * A.length + 1) c = frame (A ++ c :: B) := by
  rw [frame_write_odd _ _ (by simp)]
  congr 1
  rw [List.set_append_right _ _ (le_refl _)]
  simp

theorem wbit_S (A B : List Bool) (b : Bool) (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ) :
    wbit (at' A (b :: B) qs hq an fl g) 0 = b := by
  simp only [wbit, at', sc]
  exact frame_odd_app A B b

theorem wbit_AN (u : List Bool) (h : ℕ) (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ) :
    wbit (sc u h qs hq an fl g) 3 = readTapeBit an 0 := rfl

theorem wbit_FL (u : List Bool) (h : ℕ) (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ) :
    wbit (sc u h qs hq an fl g) 4 = readTapeBit fl 0 := rfl

theorem read_write_zero (l : List Bool) (b : Bool) : readTapeBit (writeTapeBit l 0 b) 0 = b := by
  cases l <;> rfl

/-! ## One bit forward -/

/-- One bit of the word forward: two cells of `S`, counted in `P`. -/
def stepU : WMX 4 4 := .wm (.seq (.fwd 0) (.seq (.fwd 0) (.seq (.inc 0) (.inc 0))))

theorem stepU_sc (u : List Bool) (h : ℕ) (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ)
    (hc : h + 2 ≤ cap) : WXExec cap stepU (sc u h qs hq an fl g) (sc u (h + 2) qs hq an fl g) 11 := by
  set σ := sc u h qs hq an fl g
  have e1 := WExec.fwd (cap := cap) (0 : Fin 5) σ
  set σ1 := σ.seth 0 (σ.sh 0 + 1)
  have e2 := WExec.fwd (cap := cap) (0 : Fin 5) σ1
  set σ2 := σ1.seth 0 (σ1.sh 0 + 1)
  have e3 := WExec.inc (cap := cap) (0 : Fin 4) σ2 (by simp [σ2, σ1, σ, sc]; omega)
  set σ3 := σ2.setv 0 (σ2.val 0 + 1)
  have e4 := WExec.inc (cap := cap) (0 : Fin 4) σ3 (by simp [σ3, σ2, σ1, σ, sc]; omega)
  refine WXExec.wm (WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ le_rfl)
  apply WState.eq
  · funext i; fin_cases i <;> simp [σ3, σ2, σ1, σ, sc]
  · rfl
  · funext i; fin_cases i <;> simp [σ3, σ2, σ1, σ, sc]
  · rfl

theorem stepU_at (A B : List Bool) (b : Bool) (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ)
    (hc : 2 * (A.length + B.length) + 4 ≤ cap) :
    WXExec cap stepU (at' A (b :: B) qs hq an fl g) (at' (A ++ [b]) B qs hq an fl g) 11 := by
  refine WXExec.cast cap (stepU_sc cap _ _ qs hq an fl g (by omega)) ?_ le_rfl
  simp only [at', List.append_assoc, List.singleton_append, List.length_append, List.length_singleton]
  congr 1

/-! ## Writing a bit of the word -/

theorem wrS_at (A B : List Bool) (b c : Bool) (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ) :
    WXExec cap (WMX.wr 0 c) (at' A (b :: B) qs hq an fl g) (at' A (c :: B) qs hq an fl g) 1 := by
  refine WXExec.cast cap (WXExec.wr cap 0 c _) ?_ le_rfl
  apply WState.eq
  · rfl
  · funext i; fin_cases i <;> simp [at', sc, frame_write_app]
  · rfl
  · rfl

/-- `V := AN[0]`: copy the answer cell into the scanned bit of the word. -/
def recV : WMX 4 4 := .ifs 3 (WMX.wr 0 true) (WMX.wr 0 false)

theorem recV_at (A B : List Bool) (b : Bool) (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ) :
    WXExec cap recV (at' A (b :: B) qs hq an fl g) (at' A (readTapeBit an 0 :: B) qs hq an fl g) 2 := by
  cases h : readTapeBit an 0
  · exact WXExec.ifsF (by rw [at', wbit_AN, h]) (wrS_at cap A B b false qs hq an fl g)
  · exact WXExec.ifsT (by rw [at', wbit_AN, h]) (wrS_at cap A B b true qs hq an fl g)

/-- The flag cell. -/
theorem wrFL_sc (u : List Bool) (h : ℕ) (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ) (c : Bool) :
    WXExec cap (WMX.wr 4 c) (sc u h qs hq an fl g) (sc u h qs hq an (writeTapeBit fl 0 c) g) 1 := by
  refine WXExec.cast cap (WXExec.wr cap 4 c _) ?_ le_rfl
  apply WState.eq
  · rfl
  · funext i; fin_cases i <;> simp [sc]
  · rfl
  · rfl

theorem incG_sc (u : List Bool) (h : ℕ) (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ) (hc : g < cap) :
    WXExec cap (WMX.inc 2) (sc u h qs hq an fl g) (sc u h qs hq an fl (g + 1)) 3 := by
  refine WXExec.cast cap (WXExec.inc cap 2 _ (by simpa [sc] using hc)) ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext i; fin_cases i <;> simp [sc]
  · rfl

theorem decG_sc (u : List Bool) (h : ℕ) (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ) (hc : g ≤ cap) :
    WXExec cap (WMX.dec 2) (sc u h qs hq an fl g) (sc u h qs hq an fl (g - 1)) 1 := by
  refine WXExec.cast cap (WXExec.dec cap 2 _ (by simpa [sc] using hc)) ?_ le_rfl
  apply WState.eq
  · rfl
  · rfl
  · funext i; fin_cases i <;> simp [sc]
  · rfl

/-! ## The query stream as an output stream -/

theorem outOn_sc (u : List Bool) (h : ℕ) (out L0 : List Bool) (an fl : List Bool) (g : ℕ) :
    OutOn (sc u h (overlay out L0) out.length an fl g) 2 1 out L0 := ⟨rfl, rfl, rfl⟩

theorem outSt_sc (u : List Bool) (h : ℕ) (out out' L0 : List Bool) (an fl : List Bool) (g : ℕ) :
    outSt (sc u h (overlay out L0) out.length an fl g) 2 1 out' L0 =
      sc u h (overlay out' L0) out'.length an fl g := by
  apply WState.eq
  · funext i; fin_cases i <;> simp [outSt, sc]
  · funext i; fin_cases i <;> simp [outSt, sc]
  · funext i; fin_cases i <;> simp [outSt, sc]
  · rfl

theorem emitQ_sc (u : List Bool) (h : ℕ) (out L0 : List Bool) (an fl : List Bool) (g : ℕ) (b : Bool)
    (hc : out.length < cap) :
    WXExec cap (emitO 2 1 b) (sc u h (overlay out L0) out.length an fl g)
      (sc u h (overlay (out ++ [b]) L0) (out ++ [b]).length an fl g) 7 := by
  have e := emitO_spec cap _ out L0 b (outOn_sc u h out L0 an fl g) hc
  rwa [outSt_sc] at e

/-- Return the query head (and `CQ`) to `0`. -/
def rewindQ : WMX 4 4 := .wm (WM.rewind 2 1)

theorem rewindQ_sc (u : List Bool) (h : ℕ) (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ)
    (hc : hq ≤ cap) : WXExec cap rewindQ (sc u h qs hq an fl g) (sc u h qs 0 an fl g) (5 * hq + 1) := by
  refine WXExec.wm (WExec.cast cap (wrewind_spec cap 2 1 hq _ rfl hc) ?_ le_rfl)
  apply WState.eq
  · funext i; fin_cases i <;> simp [sc]
  · rfl
  · funext i; fin_cases i <;> simp [sc]
  · rfl

/-! ## Skipping ones, skipping and copying a framed word -/

/-- Skip the unary prefix: `whs S stepU`. -/
theorem skipOnes_at (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ) (B : List Bool) :
    ∀ (k : ℕ) (A : List Bool), 2 * (A.length + k + 1 + B.length) + 4 ≤ cap →
      WXExec cap (.whs 0 stepU) (at' A (List.replicate k true ++ false :: B) qs hq an fl g)
        (at' (A ++ List.replicate k true) (false :: B) qs hq an fl g) (13 * k + 1)
  | 0, A, _ => by
    simp only [List.replicate_zero, List.nil_append, List.append_nil]
    exact WXExec.mono (WXExec.whsF (wbit_S A B false qs hq an fl g)) (by omega)
  | k + 1, A, hc => by
    have e1 := stepU_at cap A (List.replicate k true ++ false :: B) true qs hq an fl g (by simp; omega)
    have e2 := skipOnes_at qs hq an fl g B k (A ++ [true]) (by simp; omega)
    rw [List.append_assoc, List.singleton_append, ← List.replicate_succ] at e2
    rw [List.replicate_succ, List.cons_append]
    exact WXExec.mono (WXExec.whsT (wbit_S A _ true qs hq an fl g) e1 e2) (by omega)

/-- Skip a framed word: its pairs, then its end marker. -/
def skipF : WMX 4 4 := .seq (.whs 0 (.seq stepU stepU)) stepU

theorem skipPairs_at (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ) (B : List Bool) :
    ∀ (w A : List Bool), 2 * (A.length + 2 * w.length + 1 + B.length) + 4 ≤ cap →
      WXExec cap (.whs 0 (.seq stepU stepU)) (at' A (frameP w ++ false :: B) qs hq an fl g)
        (at' (A ++ frameP w) (false :: B) qs hq an fl g) (25 * w.length + 1)
  | [], A, _ => by
    simp only [frameP, List.flatMap_nil, List.nil_append, List.append_nil, List.length_nil]
    exact WXExec.whsF (wbit_S A B false qs hq an fl g)
  | b :: w, A, hc => by
    simp only [List.length_cons] at hc
    have e1 := stepU_at cap A (b :: (frameP w ++ false :: B)) true qs hq an fl g (by simp; omega)
    have e2 := stepU_at cap (A ++ [true]) (frameP w ++ false :: B) b qs hq an fl g (by simp; omega)
    have e3 := skipPairs_at qs hq an fl g B w (A ++ [true] ++ [b]) (by simp at hc ⊢; omega)
    have hw : frameP (b :: w) = true :: b :: frameP w := rfl
    rw [hw, List.cons_append, List.cons_append]
    have ha : A ++ [true] ++ [b] ++ frameP w = A ++ true :: b :: frameP w := by simp
    rw [ha] at e3
    refine WXExec.mono (WXExec.whsT (wbit_S A _ true qs hq an fl g) (WXExec.seq e1 e2) e3) ?_
    simp; omega

theorem skipF_at (qs : List Bool) (hq : ℕ) (an fl : List Bool) (g : ℕ) (w A B : List Bool)
    (hc : 2 * (A.length + 2 * w.length + 1 + B.length) + 4 ≤ cap) :
    WXExec cap skipF (at' A (frame w ++ B) qs hq an fl g) (at' (A ++ frame w) B qs hq an fl g)
      (25 * w.length + 13) := by
  have e1 := skipPairs_at cap qs hq an fl g B w A (by omega)
  have e2 := stepU_at cap (A ++ frameP w) B false qs hq an fl g (by simp; omega)
  rw [frame_eq_frameP, List.append_assoc, List.singleton_append]
  have ha : A ++ frameP w ++ [false] = A ++ (frameP w ++ [false]) := by simp
  rw [ha] at e2
  exact WXExec.mono (WXExec.seq e1 e2) (by omega)

/-- Copy one pair of a framed word to `Qs`. -/
def copyBody : WMX 4 4 :=
  .seq (emitO 2 1 true) (.seq stepU (.seq (.ifs 0 (emitO 2 1 true) (emitO 2 1 false)) stepU))

/-- Copy a framed word of the word to `Qs` (written as an output stream from its head). -/
def copyF : WMX 4 4 := .seq (.whs 0 copyBody) (.seq (emitO 2 1 false) stepU)

theorem emitQ_at (A B out L0 an fl : List Bool) (g : ℕ) (b : Bool) (hc : out.length < cap) :
    WXExec cap (emitO 2 1 b) (at' A B (overlay out L0) out.length an fl g)
      (at' A B (overlay (out ++ [b]) L0) (out ++ [b]).length an fl g) 7 :=
  emitQ_sc cap _ _ out L0 an fl g b hc

theorem copyPairs_at (an fl : List Bool) (g : ℕ) (L0 B : List Bool) :
    ∀ (w A out : List Bool), 2 * (A.length + 2 * w.length + 1 + B.length) + 4 ≤ cap →
      out.length + 2 * w.length < cap →
      WXExec cap (.whs 0 copyBody) (at' A (frameP w ++ false :: B) (overlay out L0) out.length an fl g)
        (at' (A ++ frameP w) (false :: B) (overlay (out ++ frameP w) L0) (out ++ frameP w).length an fl g)
        (42 * w.length + 1)
  | [], A, out, _, _ => by
    simp only [frameP, List.flatMap_nil, List.nil_append, List.append_nil, List.length_nil]
    exact WXExec.whsF (wbit_S A B false _ _ an fl g)
  | b :: w, A, out, hc, ho => by
    simp only [List.length_cons] at hc ho
    have e1 := emitQ_at cap A (true :: b :: (frameP w ++ false :: B)) out L0 an fl g true (by omega)
    have e2 := stepU_at cap A (b :: (frameP w ++ false :: B)) true (overlay (out ++ [true]) L0)
      (out ++ [true]).length an fl g (by simp; omega)
    have e3 : WXExec cap (.ifs 0 (emitO 2 1 true) (emitO 2 1 false))
        (at' (A ++ [true]) (b :: (frameP w ++ false :: B)) (overlay (out ++ [true]) L0) (out ++ [true]).length an fl g)
        (at' (A ++ [true]) (b :: (frameP w ++ false :: B)) (overlay (out ++ [true] ++ [b]) L0)
          (out ++ [true] ++ [b]).length an fl g) 8 := by
      cases b
      · exact WXExec.ifsF (wbit_S _ _ false _ _ an fl g) (emitQ_at cap _ _ _ L0 an fl g false (by simp; omega))
      · exact WXExec.ifsT (wbit_S _ _ true _ _ an fl g) (emitQ_at cap _ _ _ L0 an fl g true (by simp; omega))
    have e4 := stepU_at cap (A ++ [true]) (frameP w ++ false :: B) b (overlay (out ++ [true] ++ [b]) L0)
      (out ++ [true] ++ [b]).length an fl g (by simp; omega)
    have e5 := copyPairs_at an fl g L0 B w (A ++ [true] ++ [b]) (out ++ [true] ++ [b]) (by simp; omega)
      (by simp; omega)
    have hw : frameP (b :: w) = true :: b :: frameP w := rfl
    have ha : A ++ [true] ++ [b] ++ frameP w = A ++ frameP (b :: w) := by simp [hw]
    have ho' : out ++ [true] ++ [b] ++ frameP w = out ++ frameP (b :: w) := by simp [hw]
    rw [ha, ho'] at e5
    rw [show frameP (b :: w) ++ false :: B = true :: b :: (frameP w ++ false :: B) from rfl]
    refine WXExec.mono (WXExec.whsT (wbit_S A _ true _ _ an fl g)
      (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 e4))) e5) ?_
    simp; omega

theorem copyF_at (an fl : List Bool) (g : ℕ) (L0 w A B out : List Bool)
    (hc : 2 * (A.length + 2 * w.length + 1 + B.length) + 4 ≤ cap) (ho : out.length + 2 * w.length + 1 < cap) :
    WXExec cap copyF (at' A (frame w ++ B) (overlay out L0) out.length an fl g)
      (at' (A ++ frame w) B (overlay (out ++ frame w) L0) (out ++ frame w).length an fl g)
      (42 * w.length + 21) := by
  have e1 := copyPairs_at cap an fl g L0 B w A out (by omega) (by omega)
  have e2 := emitQ_at cap (A ++ frameP w) (false :: B) (out ++ frameP w) L0 an fl g false (by simp; omega)
  have e3 := stepU_at cap (A ++ frameP w) B false (overlay (out ++ frameP w ++ [false]) L0)
    (out ++ frameP w ++ [false]).length an fl g (by simp; omega)
  rw [frame_eq_frameP, List.append_assoc, List.singleton_append]
  have ha : A ++ frameP w ++ [false] = A ++ (frameP w ++ [false]) := by simp
  have hb : out ++ frameP w ++ [false] = out ++ (frameP w ++ [false]) := by simp
  rw [ha, hb] at e3
  rw [hb] at e2
  exact WXExec.mono (WXExec.seq e1 (WXExec.seq e2 e3)) (by omega)

end NearCubicGates.Adapters.ShortPCP.Machines.ReaderRun
