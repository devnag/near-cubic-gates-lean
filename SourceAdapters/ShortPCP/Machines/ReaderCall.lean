import SourceAdapters.ShortPCP.Machines.ReaderBlocks

/-!
# Single-run time, stage 3 (reader): one call of the coroutine

One call of the reader `readerW` (proof of `thm:short-pcp-ours`: the proof bits of the computation are read at the listed
addresses, one oracle gate per read) on the word `1^s 0 ++ entries ++ 0 ++ rest` (`Time.readerWord`, entries
`1 U P V ++ frame (binary L a)`, `Reader.entry`): skip `1^s 0`, then for each entry by its marker bit:
* `U = 0` (asked before): `P := 0`, and if `P` was `1` (the pending entry) `V := AN[0]`; skip to the next entry;
* `U = 1` (not yet asked): `U P := 0 1`, copy its address frame to `Qs`, set the flag cell `FL[0] := 1` (ask);
* the end marker `0`: `FL[0] := 0` (stop), and copy the word to `OUT` (`fieldO`, `closeOut`).
Heads and registers are `0` at entry and exit. `call_ask` and `call_fin` are the two outcomes, each within
`200·(|u| + 1)` steps.
-/

set_option autoImplicit false

namespace NearCubicGates.Adapters.ShortPCP.Machines.ReaderRun

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.ShortPCP.Machines.Reader
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open StablePartition.Workspace (overlay)

variable (cap : ℕ)

/-! ## The entry bodies -/

/-- `P = 1` (pending): `P := 0`, then `V := AN[0]`; `P = 0`: step to `V`. -/
def pendV : WMX 4 4 := .ifs 0 (.seq (WMX.wr 0 false) (.seq stepU recV)) stepU

/-- An entry asked before (`U = 0`). -/
def oldE : WMX 4 4 := .seq stepU (.seq pendV (.seq stepU skipF))

/-- An entry not yet asked (`U = 1`). -/
def askE : WMX 4 4 :=
  .seq (WMX.wr 0 false) (.seq stepU (.seq (WMX.wr 0 true) (.seq stepU (.seq stepU
    (.seq copyF (.seq rewindQ (.seq (WMX.wr 4 true) (WMX.dec 2))))))))

/-- The end marker. -/
def finE : WMX 4 4 := .seq (WMX.wr 4 false) (WMX.dec 2)

/-- One entry (or the end marker). -/
def body : WMX 4 4 := .ifs 0 (.seq stepU (.ifs 0 askE oldE)) finE

theorem pendV_at (A R qs an fl : List Bool) (g : ℕ) (p v : Bool)
    (hc : 2 * (A.length + R.length + 2) + 4 ≤ cap) :
    WXExec cap pendV (at' A (p :: v :: R) qs 0 an fl g)
      (at' (A ++ [false]) ((if p then readTapeBit an 0 else v) :: R) qs 0 an fl g) 17 := by
  cases p
  · exact WXExec.mono (WXExec.ifsF (wbit_S A _ false qs 0 an fl g) (stepU_at cap A (v :: R) false qs 0 an fl g
      (by simp; omega))) (by omega)
  · have e1 := wrS_at cap A (v :: R) true false qs 0 an fl g
    have e2 := stepU_at cap A (v :: R) false qs 0 an fl g (by simp; omega)
    have e3 := recV_at cap (A ++ [false]) R v qs 0 an fl g
    exact WXExec.ifsT (wbit_S A _ true qs 0 an fl g) (WXExec.seq e1 (WXExec.seq e2 e3))

theorem entry_app (L a : ℕ) (U P V : Bool) (B : List Bool) :
    entry L a U P V ++ B = true :: U :: P :: V :: (frame (binary L a) ++ B) := by
  simp [entry]

theorem frame_binary_length (L a : ℕ) : (binary L a).length = L := binary_length L a

/-- **An old entry**: `P := 0`, `V := AN[0]` if it was pending; the head moves past the entry. -/
theorem body_old (L a : ℕ) (p v : Bool) (A B qs an fl : List Bool)
    (hc : 2 * (A.length + (2 * L + 5) + B.length) + 4 ≤ cap) :
    WXExec cap body (at' A (entry L a false p v ++ B) qs 0 an fl 1)
      (at' (A ++ entry L a false false (if p then readTapeBit an 0 else v)) B qs 0 an fl 1) (25 * L + 69) := by
  rw [entry_app]
  set v' := if p then readTapeBit an 0 else v
  have e1 := stepU_at cap A (false :: p :: v :: (frame (binary L a) ++ B)) true qs 0 an fl 1 (by simp; omega)
  have e2 := stepU_at cap (A ++ [true]) (p :: v :: (frame (binary L a) ++ B)) false qs 0 an fl 1 (by simp; omega)
  have e3 := pendV_at cap (A ++ [true] ++ [false]) (frame (binary L a) ++ B) qs an fl 1 p v (by simp; omega)
  have e4 := stepU_at cap (A ++ [true] ++ [false] ++ [false]) (frame (binary L a) ++ B) v' qs 0 an fl 1
    (by simp; omega)
  have e5 := skipF_at cap qs 0 an fl 1 (binary L a) (A ++ [true] ++ [false] ++ [false] ++ [v']) B (by simp; omega)
  have hA : A ++ [true] ++ [false] ++ [false] ++ [v'] ++ frame (binary L a) = A ++ entry L a false false v' := by
    simp [entry]
  rw [hA] at e5
  have hold : WXExec cap oldE (at' (A ++ [true]) (false :: p :: v :: (frame (binary L a) ++ B)) qs 0 an fl 1)
      (at' (A ++ entry L a false false v') B qs 0 an fl 1) (25 * L + 55) := by
    refine WXExec.mono (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 e5))) ?_
    simp; omega
  exact WXExec.mono (WXExec.ifsT (wbit_S A _ true qs 0 an fl 1)
    (WXExec.seq e1 (WXExec.ifsF (wbit_S (A ++ [true]) _ false qs 0 an fl 1) hold))) (by omega)

/-- **An unasked entry**: `U P := 0 1`, its address frame on `Qs` (head back at `0`), `FL[0] := 1`, `G := 0`. -/
theorem body_ask (L a : ℕ) (A B qs an fl : List Bool) (hc : 2 * (A.length + (2 * L + 5) + B.length) + 4 ≤ cap) :
    WXExec cap body (at' A (entry L a true false false ++ B) qs 0 an fl 1)
      (at' (A ++ entry L a false true false) B (overlay (frame (binary L a)) qs) 0 an (writeTapeBit fl 0 true) 0)
      (52 * L + 86) := by
  rw [entry_app]
  set F := frame (binary L a)
  have hF : F.length = 2 * L + 1 := by simp [F, RepairOrdinary.frame_length]
  have e1 := stepU_at cap A (true :: false :: false :: (F ++ B)) true qs 0 an fl 1 (by simp; omega)
  have a1 := wrS_at cap (A ++ [true]) (false :: false :: (F ++ B)) true false qs 0 an fl 1
  have a2 := stepU_at cap (A ++ [true]) (false :: false :: (F ++ B)) false qs 0 an fl 1 (by simp; omega)
  have a3 := wrS_at cap (A ++ [true] ++ [false]) (false :: (F ++ B)) false true qs 0 an fl 1
  have a4 := stepU_at cap (A ++ [true] ++ [false]) (false :: (F ++ B)) true qs 0 an fl 1 (by simp; omega)
  have a5 := stepU_at cap (A ++ [true] ++ [false] ++ [true]) (F ++ B) false qs 0 an fl 1 (by simp; omega)
  have a6 := copyF_at cap an fl 1 qs (binary L a) (A ++ [true] ++ [false] ++ [true] ++ [false]) B []
    (by simp; omega) (by simp; omega)
  have hq0 : overlay [] qs = qs := by simp [overlay]
  simp only [hq0, List.nil_append, List.length_nil] at a6
  have hA : A ++ [true] ++ [false] ++ [true] ++ [false] ++ F = A ++ entry L a false true false := by
    simp [entry, F]
  rw [hA] at a6
  have a7 := rewindQ_sc cap (A ++ entry L a false true false ++ B) (2 * (A ++ entry L a false true false).length + 1)
    (overlay F qs) F.length an fl 1 (by rw [hF]; omega)
  have a8 := wrFL_sc cap (A ++ entry L a false true false ++ B) (2 * (A ++ entry L a false true false).length + 1)
    (overlay F qs) 0 an fl 1 true
  have a9 := decG_sc cap (A ++ entry L a false true false ++ B) (2 * (A ++ entry L a false true false).length + 1)
    (overlay F qs) 0 an (writeTapeBit fl 0 true) 1 (by omega)
  have hask : WXExec cap askE (at' (A ++ [true]) (true :: false :: false :: (F ++ B)) qs 0 an fl 1)
      (at' (A ++ entry L a false true false) B (overlay F qs) 0 an (writeTapeBit fl 0 true) 0) (52 * L + 72) := by
    refine WXExec.mono (WXExec.seq a1 (WXExec.seq a2 (WXExec.seq a3 (WXExec.seq a4 (WXExec.seq a5
      (WXExec.seq a6 (WXExec.seq a7 (WXExec.seq a8 a9)))))))) ?_
    simp only [hF, binary_length]; omega
  exact WXExec.mono (WXExec.ifsT (wbit_S A _ true qs 0 an fl 1)
    (WXExec.seq e1 (WXExec.ifsT (wbit_S (A ++ [true]) _ true qs 0 an fl 1) hask))) (by omega)

/-- **The end marker**: `FL[0] := 0`, `G := 0`. -/
theorem body_fin (A R qs an fl : List Bool) (hc : 1 ≤ cap) :
    WXExec cap body (at' A (false :: R) qs 0 an fl 1) (at' A (false :: R) qs 0 an (writeTapeBit fl 0 false) 0) 4 :=
  WXExec.ifsF (wbit_S A R false qs 0 an fl 1)
    (WXExec.seq (wrFL_sc cap _ _ qs 0 an fl 1 false) (decG_sc cap _ _ qs 0 an _ 1 (by omega)))

/-! ## The entry loop -/

/-- An entry asked before, as data: address, `P`, `V`. -/
def oldW (L : ℕ) (olds : List (ℕ × Bool × Bool)) : List Bool :=
  (olds.map fun x => entry L x.1 false x.2.1 x.2.2).flatten

/-- The same entries after the pass: `P = 0`, the pending one answered by `AN[0]`. -/
def procW (L : ℕ) (an : List Bool) (olds : List (ℕ × Bool × Bool)) : List Bool :=
  (olds.map fun x => entry L x.1 false false (if x.2.1 then readTapeBit an 0 else x.2.2)).flatten

theorem oldW_length (L : ℕ) (olds : List (ℕ × Bool × Bool)) :
    (oldW L olds).length = olds.length * (2 * L + 5) := by
  induction olds with
  | nil => simp [oldW]
  | cons x olds ih => simp [oldW] at ih ⊢; rw [ih, entry_length]; ring

theorem procW_length (L : ℕ) (an : List Bool) (olds : List (ℕ × Bool × Bool)) :
    (procW L an olds).length = olds.length * (2 * L + 5) := by
  induction olds with
  | nil => simp [procW]
  | cons x olds ih => simp [procW] at ih ⊢; rw [ih, entry_length]; ring

theorem loop_olds (L : ℕ) (qs an fl T : List Bool) (ρ : St) (c : ℕ) :
    ∀ (olds : List (ℕ × Bool × Bool)) (A : List Bool),
      2 * (A.length + olds.length * (2 * L + 5) + T.length) + 4 ≤ cap →
      WXExec cap (.whr 2 body) (at' (A ++ procW L an olds) T qs 0 an fl 1) ρ c →
      WXExec cap (.whr 2 body) (at' A (oldW L olds ++ T) qs 0 an fl 1) ρ (c + olds.length * (25 * L + 71))
  | [], A, _, h => by simpa [procW, oldW] using h
  | x :: olds, A, hc, h => by
    have e1 := body_old cap L x.1 x.2.1 x.2.2 A (oldW L olds ++ T) qs an fl (by
      simp [oldW_length]; simp at hc; nlinarith)
    have e2 := loop_olds L qs an fl T ρ c olds (A ++ entry L x.1 false false
      (if x.2.1 then readTapeBit an 0 else x.2.2)) (by simp [entry_length]; simp at hc; nlinarith)
      (by simpa [procW, List.append_assoc] using h)
    have hw : oldW L (x :: olds) ++ T = entry L x.1 false x.2.1 x.2.2 ++ (oldW L olds ++ T) := by
      simp [oldW]
    rw [hw]
    refine WXExec.mono (WXExec.whrT (by simp [at', sc]) e1 e2) ?_
    simp; nlinarith

theorem loop_fin (A R qs an fl : List Bool) (hc : 1 ≤ cap) :
    WXExec cap (.whr 2 body) (at' A (false :: R) qs 0 an fl 1)
      (at' A (false :: R) qs 0 an (writeTapeBit fl 0 false) 0) 7 :=
  WXExec.whrT (by simp [at', sc]) (body_fin cap A R qs an fl hc) (WXExec.whrF rfl)

theorem loop_ask (L a : ℕ) (A B qs an fl : List Bool) (hc : 2 * (A.length + (2 * L + 5) + B.length) + 4 ≤ cap) :
    WXExec cap (.whr 2 body) (at' A (entry L a true false false ++ B) qs 0 an fl 1)
      (at' (A ++ entry L a false true false) B (overlay (frame (binary L a)) qs) 0 an (writeTapeBit fl 0 true) 0)
      (52 * L + 89) :=
  WXExec.whrT (by simp [at', sc]) (body_ask cap L a A B qs an fl hc) (WXExec.whrF rfl)

/-! ## One call -/

/-- From cell `0` to cell `1` (bit `0` of the word). -/
def startS : WMX 4 4 := .wm (.seq (.fwd 0) (.inc 0))

theorem startS_sc (u qs an fl : List Bool) (g : ℕ) (hc : 2 ≤ cap) :
    WXExec cap startS (sc u 0 qs 0 an fl g) (at' [] u qs 0 an fl g) 5 := by
  set σ := sc u 0 qs 0 an fl g
  have e1 := WExec.fwd (cap := cap) (0 : Fin 5) σ
  have e2 := WExec.inc (cap := cap) (0 : Fin 4) (σ.seth 0 (σ.sh 0 + 1)) (by simp [σ, sc]; omega)
  refine WXExec.wm (WExec.cast cap (WExec.seq e1 e2) ?_ le_rfl)
  apply WState.eq
  · funext i; fin_cases i <;> simp [σ, at', sc]
  · funext i; fin_cases i <;> simp [σ, at', sc]
  · funext i; fin_cases i <;> simp [σ, at', sc]
  · rfl

/-- Rewind `S` by `P`. -/
def rewindS : WMX 4 4 := .wm (WM.rewind 0 0)

theorem rewindS_sc (u qs an fl : List Bool) (h : ℕ) (hc : h ≤ cap) :
    WXExec cap rewindS (sc u h qs 0 an fl 0) (sc u 0 qs 0 an fl 0) (5 * h + 1) := by
  refine WXExec.wm (WExec.cast cap (wrewind_spec cap 0 0 h _ rfl hc) ?_ le_rfl)
  apply WState.eq
  · funext i; fin_cases i <;> simp [sc]
  · rfl
  · funext i; fin_cases i <;> simp [sc]
  · rfl

/-- The state after the last call: `OUT = frame u`, all heads and registers `0`. -/
def finSt (u qs an fl : List Bool) : St :=
  ⟨![0, 0, 0, 0, 0], ![frame u, frame u, qs, an, fl], ![0, 0, 0, 0], false⟩

/-- The final copy of the word to `OUT`. -/
def outW : WMX 4 4 := .seq (fieldO 0 1 0 3) (closeOutX 1 3)

theorem outW_sc (u qs an fl : List Bool) (hc : 2 * u.length + 1 ≤ cap) :
    WXExec cap outW (sc u 0 qs 0 an fl 0) (finSt u qs an fl) (50 * u.length + 7) := by
  have e1 := fieldO_spec cap (Src := (0 : Fin 5)) (O := (1 : Fin 5)) (CS := (0 : Fin 4)) (CO := (3 : Fin 4))
    (by decide) (by decide) (sc u 0 qs 0 an fl 0) u [] [] [] (by simp [sc, frame_eq_frameP]) rfl rfl
    ⟨rfl, rfl, rfl⟩ (by simp; omega)
  have e2 := closeOut_spec cap (O := (1 : Fin 5)) (CO := (3 : Fin 4)) (outSt (sc u 0 qs 0 an fl 0) 1 3
    ([] ++ frameP u) []) ([] ++ frameP u) [] (outOn_outSt _ 1 3 _ []) (by simp; omega)
  refine WXExec.seq' cap e1 (WXExec.cast cap (WXExec.wm e2) ?_ le_rfl) (by simp; omega)
  apply WState.eq
  · funext i; fin_cases i <;> simp [outSt, sc, finSt]
  · funext i; fin_cases i <;> simp [outSt, sc, finSt, overlay, frame_eq_frameP]
  · funext i; fin_cases i <;> simp [outSt, sc, finSt]
  · rfl

/-- **The reader coroutine** (one call). -/
def readerW : WMX 4 4 :=
  .seq startS (.seq (.whs 0 stepU) (.seq stepU (.seq (WMX.inc 2) (.seq (.whr 2 body) (.seq rewindS
    (.ifs 4 WMX.skip outW))))))

/-- The unary prefix `1^s 0`. -/
def pre (s : ℕ) : List Bool := List.replicate s true ++ [false]

theorem cost_olds (n L : ℕ) : n * (25 * L + 71) ≤ 15 * (n * (2 * L + 5)) := by
  calc n * (25 * L + 71) ≤ n * (15 * (2 * L + 5)) := Nat.mul_le_mul_left _ (by omega)
    _ = 15 * (n * (2 * L + 5)) := by ring

/-- **A call that asks**: the entries before the first unasked one are passed (the pending one answered by
`AN[0]`), the first unasked entry becomes pending and its address frame is the query on `Qs`, `FL[0] = 1`. -/
theorem call_ask (s L a : ℕ) (olds : List (ℕ × Bool × Bool)) (B qs an fl : List Bool)
    (hc : 2 * (s + 1 + olds.length * (2 * L + 5) + (2 * L + 5) + B.length) + 4 ≤ cap) :
    WXExec cap readerW (sc (pre s ++ oldW L olds ++ entry L a true false false ++ B) 0 qs 0 an fl 0)
      (sc (pre s ++ procW L an olds ++ entry L a false true false ++ B) 0 (overlay (frame (binary L a)) qs) 0 an
        (writeTapeBit fl 0 true) 0)
      (200 * (s + 1 + olds.length * (2 * L + 5) + (2 * L + 5) + B.length + 1)) := by
  set E := entry L a true false false
  set E' := entry L a false true false
  set fl' := writeTapeBit fl 0 true
  set X := olds.length * (2 * L + 5) with hX
  have hXY := cost_olds olds.length L
  have hE : E.length = 2 * L + 5 := entry_length _ _ _ _ _
  have hE' : E'.length = 2 * L + 5 := entry_length _ _ _ _ _
  have hu : pre s ++ oldW L olds ++ E ++ B = List.replicate s true ++ false :: (oldW L olds ++ (E ++ B)) := by
    simp [pre]
  rw [hu]
  set A0 := [] ++ List.replicate s true ++ [false]
  have hA0 : A0.length = s + 1 := by simp [A0]
  have e1 := startS_sc cap (List.replicate s true ++ false :: (oldW L olds ++ (E ++ B))) qs an fl 0 (by omega)
  have e2 := skipOnes_at cap qs 0 an fl 0 (oldW L olds ++ (E ++ B)) s [] (by simp [oldW_length, hE]; omega)
  have e3 := stepU_at cap ([] ++ List.replicate s true) (oldW L olds ++ (E ++ B)) false qs 0 an fl 0
    (by simp [oldW_length, hE]; omega)
  have e4 : WXExec cap (WMX.inc 2) (at' A0 (oldW L olds ++ (E ++ B)) qs 0 an fl 0)
      (at' A0 (oldW L olds ++ (E ++ B)) qs 0 an fl 1) 3 := incG_sc cap _ _ qs 0 an fl 0 (by omega)
  have e5i := loop_ask cap L a (A0 ++ procW L an olds) B qs an fl (by simp [procW_length, hA0]; omega)
  have e5 := loop_olds cap L qs an fl (E ++ B) _ _ olds A0 (by simp [hE, hA0]; omega) e5i
  have e6 := rewindS_sc cap (A0 ++ procW L an olds ++ E' ++ B) (overlay (frame (binary L a)) qs) an fl'
    (2 * (A0 ++ procW L an olds ++ E').length + 1) (by simp [procW_length, hA0, hE']; omega)
  have e7 : WXExec cap (.ifs 4 WMX.skip outW) (sc (A0 ++ procW L an olds ++ E' ++ B) 0
      (overlay (frame (binary L a)) qs) 0 an fl' 0) (sc (A0 ++ procW L an olds ++ E' ++ B) 0
      (overlay (frame (binary L a)) qs) 0 an fl' 0) 1 :=
    WXExec.ifsT (by rw [wbit_FL]; exact read_write_zero _ _) (WXExec.skip cap _)
  have whole := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6 e7)))))
  refine WXExec.cast cap whole ?_ ?_
  · simp [A0, pre, E']
  · simp only [List.length_append, hA0, procW_length, hE']
    omega

/-- **The last call**: the entries are passed (the pending one answered by `AN[0]`), the end marker reached,
`FL[0] = 0`, and the word is copied to `OUT`. -/
theorem call_fin (s L : ℕ) (olds : List (ℕ × Bool × Bool)) (rest qs an fl : List Bool)
    (hc : 2 * (s + 1 + olds.length * (2 * L + 5) + 1 + rest.length) + 4 ≤ cap) :
    WXExec cap readerW (sc (pre s ++ oldW L olds ++ false :: rest) 0 qs 0 an fl 0)
      (finSt (pre s ++ procW L an olds ++ false :: rest) qs an (writeTapeBit fl 0 false))
      (200 * (s + 1 + olds.length * (2 * L + 5) + 1 + rest.length + 1)) := by
  set fl' := writeTapeBit fl 0 false
  set X := olds.length * (2 * L + 5) with hX
  have hXY := cost_olds olds.length L
  have hu : pre s ++ oldW L olds ++ false :: rest = List.replicate s true ++ false :: (oldW L olds ++ false :: rest) := by
    simp [pre]
  have hv : pre s ++ procW L an olds ++ false :: rest = [] ++ List.replicate s true ++ [false] ++ procW L an olds ++
      false :: rest := by
    simp [pre]
  rw [hu, hv]
  set A0 := [] ++ List.replicate s true ++ [false]
  have hA0 : A0.length = s + 1 := by simp [A0]
  have e1 := startS_sc cap (List.replicate s true ++ false :: (oldW L olds ++ false :: rest)) qs an fl 0 (by omega)
  have e2 := skipOnes_at cap qs 0 an fl 0 (oldW L olds ++ false :: rest) s [] (by simp [oldW_length]; omega)
  have e3 := stepU_at cap ([] ++ List.replicate s true) (oldW L olds ++ false :: rest) false qs 0 an fl 0
    (by simp [oldW_length]; omega)
  have e4 : WXExec cap (WMX.inc 2) (at' A0 (oldW L olds ++ false :: rest) qs 0 an fl 0)
      (at' A0 (oldW L olds ++ false :: rest) qs 0 an fl 1) 3 := incG_sc cap _ _ qs 0 an fl 0 (by omega)
  have e5i := loop_fin cap (A0 ++ procW L an olds) rest qs an fl (by omega)
  have e5 := loop_olds cap L qs an fl (false :: rest) _ _ olds A0 (by simp [hA0]; omega) e5i
  have e6 := rewindS_sc cap (A0 ++ procW L an olds ++ false :: rest) qs an fl'
    (2 * (A0 ++ procW L an olds).length + 1) (by simp [procW_length, hA0]; omega)
  have e7 : WXExec cap (.ifs 4 WMX.skip outW) (sc (A0 ++ procW L an olds ++ false :: rest) 0 qs 0 an fl' 0)
      (finSt (A0 ++ procW L an olds ++ false :: rest) qs an fl')
      (50 * (A0 ++ procW L an olds ++ false :: rest).length + 8) :=
    WXExec.ifsF (by rw [wbit_FL]; exact read_write_zero _ _)
      (outW_sc cap _ qs an fl' (by simp [procW_length, hA0]; omega))
  have whole := WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4 (WXExec.seq e5 (WXExec.seq e6 e7)))))
  refine WXExec.mono whole ?_
  simp only [List.length_append, hA0, procW_length, List.length_cons]
  omega

end NearCubicGates.Adapters.ShortPCP.Machines.ReaderRun
