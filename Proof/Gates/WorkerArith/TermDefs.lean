import Proof.Gates.WorkerArith.CallTailMain
import Proof.Gates.WorkerArith.RowTest
import Proof.Gates.WorkerArith.SuppEq
import Proof.Gates.Worker.TermModel
import Proof.Gates.Worker.Classify
import Proof.Gates.Codec.ParityW

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT.ReadEq
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.RepairOrdinary.Streaming
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicGates.Close.Interfaces (Counter Call callWord outputWord bitWord ratWord NCircuit)
open NearCubicGates.Close.Worker (Opd model1 model2)
open NearCubicGates.Close.Codec (oneCallOf pairCallOf cwPrefix rowPrefix)

variable {ns nr : ℕ}

/-! ## Register layout -/

/-- The call writers' file (`Codec.callOneW`/`callPairW`/`parRow`/`rowNonemptyW`): `Rw 7 = R 17` the call stream's
counter, `Rw 12 = R 7` (circuit-stream bound), `Rw 13 = R 23`, `Rw 14 = R 24` (indices), `Rw 15 = R 6` (`q`). -/
def cIdx : Fin 16 → Fin 40 := ![10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 7, 23, 24, 6]
/-- `suppEqW`'s word file: `R 10 … R 25`. -/
def sIdx : Fin 16 → Fin 40 := ![10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]
/-- `suppEqW`'s file: `Q 0 = R 2`, `Q 1 = R 5`, `Q 2 = R 6`, `Q 3 = R 8`, `Q 4 … Q 11 = R 26 … R 33`. -/
def qIdx : Fin 12 → Fin 40 := ![2, 5, 6, 8, 26, 27, 28, 29, 30, 31, 32, 33]
/-- `callTailP`'s `P`: `P 0 = R f` (the flip), `P 1 = R 17`, `P 2 … P 7 = R 26 … R 31`. -/
def pIdx (f : Fin 40) : Fin 8 → Fin 40 := ![f, 17, 26, 27, 28, 29, 30, 31]
/-- `ctrCallP`'s `Rg`: `Rg 0 … Rg 6 = R 10 … R 16`, `Rg 7 = R 9`. -/
def gIdx : Fin 8 → Fin 40 := ![10, 11, 12, 13, 14, 15, 16, 9]

theorem cIdx_inj : Function.Injective cIdx := by decide
theorem sIdx_inj : Function.Injective sIdx := by decide
theorem qIdx_inj : Function.Injective qIdx := by decide
theorem gIdx_inj : Function.Injective gIdx := by decide
theorem pIdx_inj (f : Fin 40) (hf : f = 0 ∨ f = 39) : Function.Injective (pIdx f) := by
  rcases hf with rfl | rfl <;> decide

/-- A sub-file of `R`. -/
def subR {k : ℕ} (R : Fin 40 ↪ Fin nr) (f : Fin k → Fin 40) (hf : Function.Injective f) : Fin k ↪ Fin nr :=
  ⟨fun i => R (f i), R.injective.comp hf⟩

def rwC (R : Fin 40 ↪ Fin nr) : Fin 16 ↪ Fin nr := subR R cIdx cIdx_inj
def rwS (R : Fin 40 ↪ Fin nr) : Fin 16 ↪ Fin nr := subR R sIdx sIdx_inj
def qS (R : Fin 40 ↪ Fin nr) : Fin 12 ↪ Fin nr := subR R qIdx qIdx_inj
def gT (R : Fin 40 ↪ Fin nr) : Fin 8 ↪ Fin nr := subR R gIdx gIdx_inj
/-- `P` with the flip `R 0` (one-operand terms) or `R 39` (two-operand terms). -/
def pT (R : Fin 40 ↪ Fin nr) (f : Fin 40) (hf : f = 0 ∨ f = 39) : Fin 8 ↪ Fin nr := subR R (pIdx f) (pIdx_inj f hf)

/-! ## The streams -/

structure TermEnv (ns nr : ℕ) where
  CW : Fin (ns + 1)
  SUP : Fin (ns + 1)
  S1 : Fin (ns + 1)
  S2 : Fin (ns + 1)
  TL : Fin (ns + 1)
  G : Fin (ns + 1)
  L : Fin (ns + 1)
  VI : Fin (ns + 1)
  WT : Fin (ns + 1)
  R : Fin 40 ↪ Fin nr

/-! ## Programs -/

section Programs
variable (E : TermEnv ns nr)

def skipFieldW : WMX ns nr :=
  .seq (.wm (.seq (Codec.fieldFrameW E.WT E.S2 (E.R 26) (E.R 27)) (WM.rewind E.S2 (E.R 26))))
    (clearFrameP E.S2 E.G (E.R 28) (E.R 29) (E.R 30) (E.R 31))

/-- `R 37 := [sysList q rows u ≠ []]` for `u` in register `X` (`u < q`, else row `u − q` nonempty). -/
def sysFlagW (X : Fin nr) : WM ns nr :=
  .seq (Worker.ltSubW X (E.R 6) (E.R 24) (E.R 34) (E.R 35) (E.R 36))
  (.seq (.ifr (E.R 34) (.inc (E.R 37)) (rowNonemptyW E.SUP (rwC E.R) (E.R 8) (E.R 37)))
  (.seq (WM.clear (E.R 34)) (WM.clear (E.R 24))))

/-- The exact entry with the inverted test: `(F ≠ 0, (1/2 if H = 0 else 0, 0))`. -/
def exactEntryNW (o : Fin (ns + 1)) (OP F H : Fin nr) : WMX ns nr :=
  .seq (.ifr F (.wm (Codec.emitMarks o OP (bitWord true))) (.wm (Codec.emitMarks o OP (bitWord false))))
    (.ifr H (.wm (Codec.emitMarks o OP (outputWord (0, 0)))) (.wm (Codec.emitMarks o OP (outputWord (1 / 2, 0)))))

/-- `F := [A ≠ 0] xor [B ≠ 0]` (`F = 0` before). -/
def xorW (A B F : Fin nr) : WM ns nr := .ifr A (.ifr B .skip (.inc F)) (.ifr B (.inc F) .skip)

/-- The single call on circuit `X` with no parity (`Rw 13 := X`). -/
def oneAuxW (X : Fin nr) (ω : ℚ) : WM ns nr :=
  .seq (Codec.dupR X (E.R 23) (E.R 38)) (Codec.callOneW E.CW E.S1 (rwC E.R) 0 (Codec.parNone E.S1 (E.R 17)) ω)

/-- The call on circuit `Xa` with the parity list `sysList q rows u`, `u` in `Xs`. -/
def sysAuxW (Xs Xa : Fin nr) (ω : ℚ) : WM ns nr :=
  .seq (Codec.dupR Xa (E.R 23) (E.R 38))
  (.seq (Worker.ltSubW Xs (E.R 6) (E.R 24) (E.R 34) (E.R 35) (E.R 36))
  (.ifr (E.R 34)
    (.seq (WM.clear (E.R 34)) (.seq (Codec.dupR Xs (E.R 24) (E.R 38))
      (Codec.callOneW E.CW E.S1 (rwC E.R) 2 (Codec.parSys E.S1 (rwC E.R)) ω)))
    (.seq (rowNonemptyW E.SUP (rwC E.R) (E.R 8) (E.R 37))
      (.ifr (E.R 37)
        (.seq (WM.clear (E.R 37)) (Codec.callOneW E.CW E.S1 (rwC E.R) 2 (Codec.parRow E.SUP E.S1 (rwC E.R) (E.R 8)) ω))
        (Codec.callOneW E.CW E.S1 (rwC E.R) 0 (Codec.parRow E.SUP E.S1 (rwC E.R) (E.R 8)) ω)))))

/-- The pair call on circuits `R 2`, `R 5`. -/
def pairW (ω : ℚ) : WM ns nr :=
  .seq (Codec.dupR (E.R 2) (E.R 23) (E.R 38)) (.seq (Codec.dupR (E.R 5) (E.R 24) (E.R 38))
    (Codec.callPairW E.CW E.S1 (rwC E.R) ω))

/-- Restore the scratch after a call: clear the index copies, rewind `CW` and `SUP`. -/
def cleanW : WM ns nr :=
  .seq (WM.clear (E.R 23)) (.seq (WM.clear (E.R 24))
  (.seq (Codec.rewindCW E.CW (E.R 7) (E.R 21) (E.R 20)) (Codec.rewindCW E.SUP (E.R 8) (E.R 21) (E.R 20))))

/-- After a call writer: rewind the call stream, the call tail (flip `R f`), restore. -/
noncomputable def callFinW {B1 B2 : ℕ} (ctr : Counter B1 B2) (tmap : Fin ctr.program.program.tapeCount → Fin (ns + 1))
    (f : Fin 40) (hf : f = 0 ∨ f = 39) : WMX ns nr :=
  .seq (.wm (.seq (Codec.dupR (E.R 17) (E.R 38) (E.R 35)) (WM.rewind E.S1 (E.R 38))))
  (.seq (callTailP ctr tmap E.S1 E.S2 E.TL E.G E.L E.VI E.WT (gT E.R) (pT E.R f hf)) (.wm (cleanW E)))

/-- **The one-operand term program** (operand in `R 0, R 1, R 2`). -/
noncomputable def termW1 {B1 B2 : ℕ} (ctr : Counter B1 B2) (tmap : Fin ctr.program.program.tapeCount → Fin (ns + 1))
    (ω : ℚ) : WMX ns nr :=
  .ifr (E.R 1)
    (.seq (skipFieldW E) (.seq (.wm (sysFlagW E (E.R 2)))
      (.seq (exactEntryW E.VI (E.R 9) (E.R 0) (E.R 37)) (.wm (WM.clear (E.R 37))))))
    (.seq (.wm (oneAuxW E (E.R 2) ω)) (callFinW E ctr tmap 0 (Or.inl rfl)))

/-- **The two-operand term program** (operands in `R 0 … R 5`; the flip `R 39 := xor`). -/
noncomputable def termW2 {B1 B2 : ℕ} (ctr : Counter B1 B2) (tmap : Fin ctr.program.program.tapeCount → Fin (ns + 1))
    (ω : ℚ) : WMX ns nr :=
  .seq (.wm (xorW (E.R 0) (E.R 3) (E.R 39)))
  (.seq (.ifr (E.R 1)
    (.ifr (E.R 4)
      (.seq (skipFieldW E) (.seq (.wm (suppEqW E.SUP E.S1 E.S2 (rwS E.R) (qS E.R)))
        (.seq (exactEntryNW E.VI (E.R 9) (E.R 39) (E.R 26)) (.wm (WM.clear (E.R 26))))))
      (.seq (.wm (sysAuxW E (E.R 2) (E.R 5) ω)) (callFinW E ctr tmap 39 (Or.inr rfl))))
    (.ifr (E.R 4)
      (.seq (.wm (sysAuxW E (E.R 5) (E.R 2) ω)) (callFinW E ctr tmap 39 (Or.inr rfl)))
      (.seq (.wm (Worker.ltSubW (E.R 2) (E.R 5) (E.R 34) (E.R 35) (E.R 36) (E.R 38)))
        (.ifr (E.R 34)
          (.seq (.wm (.seq (WM.clear (E.R 34)) (WM.clear (E.R 35))))
            (.seq (.wm (pairW E ω)) (callFinW E ctr tmap 39 (Or.inr rfl))))
          (.ifr (E.R 35)
            (.seq (.wm (.seq (WM.clear (E.R 34)) (WM.clear (E.R 35))))
              (.seq (.wm (pairW E ω)) (callFinW E ctr tmap 39 (Or.inr rfl))))
            (.seq (skipFieldW E) (exactEntryW E.VI (E.R 9) (E.R 39) (E.R 37))))))))
  (.wm (WM.clear (E.R 39))))

end Programs

/-! ## The ideal end state, the cost class, the hypotheses -/

/-- The operand in registers `N Y X`. -/
def opdAt (σ : WState ns nr) (N Y X : Fin nr) : Opd := ⟨decide (σ.val N ≠ 0), decide (σ.val Y ≠ 0), σ.val X⟩

open Classical in

noncomputable def termIdeal {t : ℕ} (σ : WState ns nr) (tmap : Fin t → Fin (ns + 1)) (E : TermEnv ns nr) (hWT : ℕ)
    (entry : List Bool) : WState ns nr :=
  appendO ⟨fun i => if (∃ j, tmap j = i) ∨ i = E.TL ∨ i = E.G ∨ i = E.S1 ∨ i = E.S2 then 0 else
      if i = E.WT then hWT else σ.sh i,
    fun i => if (∃ j, tmap j = i) ∨ i = E.TL ∨ i = E.G ∨ i = E.S1 ∨ i = E.S2 then [] else σ.st i, σ.val, σ.cell⟩
    E.VI (E.R 9) (marks entry)

/-- The entry word of a term. -/
def entryWord (e : Bool × (ℚ × ℚ)) : List Bool := bitWord e.1 ++ outputWord e.2

section Budgets
variable {B1 B2 : ℕ} (ctr : Counter B1 B2) {q : ℕ} (Cs : ℕ → NCircuit q) (rows : ℕ → List ℕ) (ω : ℚ)
  (w : List Bool)

/-- The counter budget a one-operand term spends (`0` for exact terms). -/
noncomputable def bud1 (o : Opd) : ℕ := if o.sys then 0 else ctr.budget (oneCallOf Cs o.idx [] ω) w

/-- The counter budget a two-operand term spends (`0` for exact terms). -/
noncomputable def bud2 (o1 o2 : Opd) : ℕ :=
  match o1.sys, o2.sys with
  | true, true => 0
  | true, false => ctr.budget (oneCallOf Cs o2.idx (sysList q rows o1.idx) ω) w
  | false, true => ctr.budget (oneCallOf Cs o1.idx (sysList q rows o2.idx) ω) w
  | false, false => if o1.idx = o2.idx then 0 else ctr.budget (pairCallOf Cs o1.idx o2.idx ω) w

end Budgets

/-- The cost class of one term (`t` counter tapes, `Z` the sizes, `B` the per-item costs, `bud` the counter budget). -/
def termCost (t Z B bud : ℕ) : ℕ := 10000000000000 * (t + 1) * (Z + 1) ^ 4 * (B + 1) + (300 * t + 6000) * bud

/-- The streams and registers before a term (scratch `R 10 … R 38` zero; `R 39` free). -/
structure TermBase (E : TermEnv ns nr) {t : ℕ} (tmap : Fin t → Fin (ns + 1)) {q : ℕ} (Cs : ℕ → NCircuit q) (N : ℕ)
    (rows : ℕ → List ℕ) (Rn : ℕ) (w pre rest : List Bool) (σ : WState ns nr) : Prop where
  inj : Function.Injective tmap
  tdis : ∀ j, tmap j ∉ [E.CW, E.SUP, E.S1, E.S2, E.TL, E.G, E.L, E.VI, E.WT]
  nd : [E.CW, E.SUP, E.S1, E.S2, E.TL, E.G, E.L, E.VI, E.WT].Nodup
  cw : ∃ r, σ.st E.CW = cwPrefix Cs N ++ r
  cwh : σ.sh E.CW = 0
  cwL : (cwPrefix Cs N).length ≤ σ.val (E.R 7)
  sup : ∃ r, σ.st E.SUP = rowPrefix rows Rn ++ r
  suph : σ.sh E.SUP = 0
  supL : (rowPrefix rows Rn).length ≤ σ.val (E.R 8)
  b1 : Worker.Blank (σ.st E.S1)
  h1 : σ.sh E.S1 = 0
  b2 : Worker.Blank (σ.st E.S2)
  h2 : σ.sh E.S2 = 0
  bt : ∀ j, Worker.Blank (σ.st (tmap j))
  ht : ∀ j, σ.sh (tmap j) = 0
  bTL : Worker.Blank (σ.st E.TL)
  hTL : σ.sh E.TL = 0
  bG : Worker.Blank (σ.st E.G)
  hG : σ.sh E.G = 0
  bL : Worker.Blank (σ.st E.L)
  hL : σ.sh E.L = 0
  wt : σ.st E.WT = pre ++ (Worker.Format.countWord w.length ++ w) ++ rest
  wth : σ.sh E.WT = pre.length
  vi : σ.sh E.VI = (σ.st E.VI).length
  hq : σ.val (E.R 6) = q
  z : ∀ i : Fin 40, 10 ≤ i.val → i.val < 39 → σ.val (E.R i) = 0

/-- The streams and registers before a term (all scratch `R 10 … R 39` zero). -/
structure TermPre (E : TermEnv ns nr) {t : ℕ} (tmap : Fin t → Fin (ns + 1)) {q : ℕ} (Cs : ℕ → NCircuit q) (N : ℕ)
    (rows : ℕ → List ℕ) (Rn : ℕ) (w pre rest : List Bool) (σ : WState ns nr) : Prop
    extends TermBase E tmap Cs N rows Rn w pre rest σ where
  z39 : σ.val (E.R 39) = 0

/-- The sizes and the fits (`Z` bounds every size the term reads, `B` every per-item cost, `V` the call frames). -/
structure TermFit (cap : ℕ) {q : ℕ} (Cs : ℕ → NCircuit q) (N : ℕ) (rows : ℕ → List ℕ) (Rn : ℕ) (ω : ℚ)
    (w : List Bool) (Z B V : ℕ) : Prop where
  fit : ∀ k < N, Codec.CircuitFits cap (Cs k)
  cb : ∀ k < N, Codec.circuitCost (Cs k) ≤ B
  copy : ∀ k < N, Codec.CopyFits cap V (Cs k)
  ccB : ∀ k < N, Codec.copyCircuitCost (Cs k) ≤ B
  cwZ : ∀ k < N, (Interfaces.circuitWord (Cs k)).length ≤ Z
  rowB : ∀ j < Rn, Codec.rowCost (rows j) ≤ B
  rowfit : ∀ j < Rn, 2 ^ (natBitLength (rows j).length + 1) ≤ cap ∧ (rows j).length ≤ cap ∧
    ∀ x ∈ rows j, natBitLength x + 1 ≤ cap
  rowZ : ∀ j < Rn, (Interfaces.listWord natWord (rows j)).length ≤ Z
  qZ : q ≤ Z
  NZ : N ≤ Z
  RZ : Rn ≤ Z
  wZ : w.length ≤ Z
  ωZ : (ratWord ω).length ≤ Z
  VZ : 30 * Z + 100 ≤ V
  capV : V + 1000 * (Z + 1) ≤ cap

def TermW1Ideal {B1 B2 : ℕ} (ctr : Counter B1 B2) (E : TermEnv ns nr)
    (tmap : Fin ctr.program.program.tapeCount → Fin (ns + 1)) {q : ℕ} (Cs : ℕ → NCircuit q) (N : ℕ)
    (rows : ℕ → List ℕ) (Rn : ℕ) (ω : ℚ) (w pre rest : List Bool) (cap Z B V : ℕ) (σ : WState ns nr) : Prop :=
  TermPre E tmap Cs N rows Rn w pre rest σ → TermFit cap Cs N rows Rn ω w Z B V →
  (σ.val (E.R 1) ≠ 0 → σ.val (E.R 2) < q + Rn) → (σ.val (E.R 1) = 0 → σ.val (E.R 2) < N) →
  σ.val (E.R 7) ≤ Z → σ.val (E.R 8) ≤ Z → σ.val (E.R 2) ≤ Z →
  σ.val (E.R 9) + 1000 * (Z + 1) + 8 * bud1 ctr Cs ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) ≤ cap →
  ∃ τ, WXExec cap (termW1 E ctr tmap ω) σ τ
      (termCost ctr.program.program.tapeCount Z B (bud1 ctr Cs ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)))) ∧
    SimW (termIdeal σ tmap E (pre.length + w.length + 1 + w.length)
      (entryWord (model1 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2))))) τ

def TermW2Ideal {B1 B2 : ℕ} (ctr : Counter B1 B2) (E : TermEnv ns nr)
    (tmap : Fin ctr.program.program.tapeCount → Fin (ns + 1)) {q : ℕ} (Cs : ℕ → NCircuit q) (N : ℕ)
    (rows : ℕ → List ℕ) (Rn : ℕ) (ω : ℚ) (w pre rest : List Bool) (cap Z B V : ℕ) (σ : WState ns nr) : Prop :=
  TermPre E tmap Cs N rows Rn w pre rest σ → TermFit cap Cs N rows Rn ω w Z B V →
  (σ.val (E.R 1) ≠ 0 → σ.val (E.R 2) < q + Rn) → (σ.val (E.R 1) = 0 → σ.val (E.R 2) < N) →
  (σ.val (E.R 4) ≠ 0 → σ.val (E.R 5) < q + Rn) → (σ.val (E.R 4) = 0 → σ.val (E.R 5) < N) →
  σ.val (E.R 7) ≤ Z → σ.val (E.R 8) ≤ Z → σ.val (E.R 2) ≤ Z → σ.val (E.R 5) ≤ Z →
  σ.val (E.R 9) + 1000 * (Z + 1) +
    8 * bud2 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) (opdAt σ (E.R 3) (E.R 4) (E.R 5)) ≤ cap →
  ∃ τ, WXExec cap (termW2 E ctr tmap ω) σ τ
      (termCost ctr.program.program.tapeCount Z B
        (bud2 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) (opdAt σ (E.R 3) (E.R 4) (E.R 5)))) ∧
    SimW (termIdeal σ tmap E (pre.length + w.length + 1 + w.length)
      (entryWord (model2 ctr Cs rows ω w (opdAt σ (E.R 0) (E.R 1) (E.R 2)) (opdAt σ (E.R 3) (E.R 4) (E.R 5))))) τ

end NearCubicGates.Close.WorkerArith
