import Proof.CaseAnalysis.FinalRowAnswerWord
import Proof.CaseAnalysis.FinalBandClearDock
import Proof.CaseAnalysis.FinalRoundCursor
import Proof.CaseAnalysis.FinalWordFunctionDock

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10RoundBudget

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10AnswerShift
  (answerShiftFuel answerShiftFuel_eq)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10RowAnswerWord (rowAnswerFuel)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10BandClearDock (clear_budget)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10RoundCursor
  (unaryCursorCost unaryCursorCost_eq)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10CallCountCap
  (siteCap site_le length_flatMap_le scale_length)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
  (siteRecords callRecords siteCalls)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (addressRecords)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage (Rounds)
open NearCubicWires.RepairSource.CloseoutFinal.C10LedgerBounds (countRecordAppend_le)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
  (widthAt widthPower one_le_widthPower widthPower_le_logScale widthConst thresholdFloor
    entryWidthSchedule)
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin
  (polyFuel poly_polylog_le_polyFuel repinOnset)
open NearCubicWires.RepairSource.CloseoutFinal.C10CostAtTable (hotFuel polyFuel_le_hotFuel)
open NearCubicWires.RepairSource.CloseoutFinal.C10WordFunctionDock
  (rewound inSlot clause_dock)
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable section

/-- **The paper's `q^{O(1)}` (`paper.tex:1382-1385`), as a predicate on budget
families.** -/
def WidthPoly (sources : RepairSource.EightSources) (k : ℕ) (f : ℕ → ℕ) : Prop :=
  ∃ A c : ℕ, ∀ N, f N ≤ A * widthPower sources k c N

/-- A pointwise-smaller family is still `q^{O(1)}`. -/
theorem WidthPoly.mono {sources : RepairSource.EightSources} {k : ℕ} {f g : ℕ → ℕ}
    (h : ∀ N, g N ≤ f N) (hf : WidthPoly sources k f) : WidthPoly sources k g := by
  obtain ⟨A, c, hA⟩ := hf
  exact ⟨A, c, fun N => le_trans (h N) (hA N)⟩

/-- A constant is `q^{O(1)}` at exponent `0`. -/
theorem WidthPoly.const (sources : RepairSource.EightSources) (k a : ℕ) :
    WidthPoly sources k (fun _ => a) := by
  refine ⟨a, 0, fun N => ?_⟩
  unfold widthPower
  simp

/-- **Closure under `+` -- the lemma that makes a per-round SUM legal.**  The
exponents add rather than max, which costs nothing and avoids a case split. -/
theorem WidthPoly.add {sources : RepairSource.EightSources} {k : ℕ} {f g : ℕ → ℕ}
    (hf : WidthPoly sources k f) (hg : WidthPoly sources k g) :
    WidthPoly sources k (fun N => f N + g N) := by
  obtain ⟨A, c, hA⟩ := hf
  obtain ⟨B, d, hB⟩ := hg
  refine ⟨A + B, c + d, fun N => ?_⟩
  have hc : widthPower sources k c N ≤ widthPower sources k (c + d) N := by
    unfold widthPower
    exact Nat.pow_le_pow_right (by omega) (Nat.le_add_right c d)
  have hd : widthPower sources k d N ≤ widthPower sources k (c + d) N := by
    unfold widthPower
    exact Nat.pow_le_pow_right (by omega) (Nat.le_add_left d c)
  show f N + g N ≤ (A + B) * widthPower sources k (c + d) N
  calc f N + g N ≤ A * widthPower sources k c N + B * widthPower sources k d N :=
        Nat.add_le_add (hA N) (hB N)
    _ ≤ A * widthPower sources k (c + d) N + B * widthPower sources k (c + d) N :=
        Nat.add_le_add (Nat.mul_le_mul_left A hc) (Nat.mul_le_mul_left B hd)
    _ = (A + B) * widthPower sources k (c + d) N := by ring

/-- **Closure under `*`** -- one round runs `terms` copies of the per-monomial
work, and `terms` is itself `q^{O(1)}` (`addressRecords_length_le`). -/
theorem WidthPoly.mul {sources : RepairSource.EightSources} {k : ℕ} {f g : ℕ → ℕ}
    (hf : WidthPoly sources k f) (hg : WidthPoly sources k g) :
    WidthPoly sources k (fun N => f N * g N) := by
  obtain ⟨A, c, hA⟩ := hf
  obtain ⟨B, d, hB⟩ := hg
  refine ⟨A * B, c + d, fun N => ?_⟩
  have hsplit : widthPower sources k (c + d) N
      = widthPower sources k c N * widthPower sources k d N := by
    unfold widthPower
    rw [← pow_add]
  calc f N * g N ≤ A * widthPower sources k c N * (B * widthPower sources k d N) :=
        Nat.mul_le_mul (hA N) (hB N)
    _ = A * B * (widthPower sources k c N * widthPower sources k d N) := by ring
    _ = A * B * widthPower sources k (c + d) N := by rw [hsplit]

theorem WidthPoly.le_hotFuel {sources : RepairSource.EightSources} {k : ℕ} {f : ℕ → ℕ}
    (hf : WidthPoly sources k f) (r degree : ℕ) :
    ∃ onset : ℕ, ∀ N, onset ≤ N → f N ≤ hotFuel sources k r degree N := by
  obtain ⟨A, c, hA⟩ := hf
  obtain ⟨onset0, honset0⟩ :=
    poly_polylog_le_polyFuel 0 (A * widthConst sources k ^ c) c 1 1 (le_refl 1) (by omega)
  refine ⟨max onset0 (repinOnset sources k r degree 1), fun N hN => ?_⟩
  have hN0 : onset0 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : repinOnset sources k r degree 1 ≤ N := le_trans (le_max_right _ _) hN
  have h1 := hA N
  have h2 : A * widthPower sources k c N ≤ A * (widthConst sources k ^ c * logScale N ^ c) :=
    Nat.mul_le_mul_left _ (widthPower_le_logScale sources k c N)
  have h3 := honset0 N hN0
  have h4 := polyFuel_le_hotFuel sources k r degree 1 1 N (by omega) hN1
  have hre : (N + 1) ^ 0 * (A * widthConst sources k ^ c * logScale N ^ c)
      = A * (widthConst sources k ^ c * logScale N ^ c) := by ring
  rw [hre] at h3
  omega

/-! ## §2  The record width, and the three compiled stage charges -/

/-- The scheduled record width is `q^{O(1)}`: `thresholdFloor`
(`Proof/CaseAnalysis/FinalPartsSchedule.lean`) is a constant of the source and
`widthPower` is at least `1`. -/
theorem widthPoly_entryWidthSchedule (sources : RepairSource.EightSources) (k r : ℕ) :
    WidthPoly sources k (entryWidthSchedule sources k r) := by
  refine ⟨thresholdFloor sources + 1, r, fun N => ?_⟩
  have h := one_le_widthPower sources k r N
  have h2 : thresholdFloor sources ≤ thresholdFloor sources * widthPower sources k r N := by
    calc thresholdFloor sources = thresholdFloor sources * 1 := (Nat.mul_one _).symm
      _ ≤ thresholdFloor sources * widthPower sources k r N := Nat.mul_le_mul_left _ h
  have h3 : (thresholdFloor sources + 1) * widthPower sources k r N
      = thresholdFloor sources * widthPower sources k r N + widthPower sources k r N := by ring
  show thresholdFloor sources + widthPower sources k r N
      ≤ (thresholdFloor sources + 1) * widthPower sources k r N
  omega

/-- **Stage 2a, the summation half of the answer channel.**  `rowAnswerFuel w rows
= 2*(rows*(16*w+20)+5)+2` (`Proof/CaseAnalysis/FinalRowAnswerWord.lean`) is
bilinear in the record width and the external-row count. -/
theorem widthPoly_rowAnswerFuel (sources : RepairSource.EightSources) (k : ℕ)
    {w rows : ℕ → ℕ} (hw : WidthPoly sources k w) (hrows : WidthPoly sources k rows) :
    WidthPoly sources k (fun N => rowAnswerFuel (w N) (rows N)) := by
  refine WidthPoly.mono (f := fun N => 32 * (rows N * w N) + (40 * rows N + 12))
    (fun N => le_of_eq (by unfold rowAnswerFuel; ring)) ?_
  exact ((WidthPoly.const sources k 32).mul (hrows.mul hw)).add
    (((WidthPoly.const sources k 40).mul hrows).add (WidthPoly.const sources k 12))

/-- **Stage 2b, the shift half of the answer channel.**  `answerShiftFuel_eq`
(`Proof/CaseAnalysis/FinalAnswerShift.lean`) is `128*(w+1)*(shift+2)`. -/
theorem widthPoly_answerShiftFuel (sources : RepairSource.EightSources) (k : ℕ)
    {w shift : ℕ → ℕ} (hw : WidthPoly sources k w) (hshift : WidthPoly sources k shift) :
    WidthPoly sources k (fun N => answerShiftFuel (w N) (shift N)) := by
  refine WidthPoly.mono (f := fun N => 128 * ((w N + 1) * (shift N + 2)))
    (fun N => le_of_eq (by rw [answerShiftFuel_eq]; ring)) ?_
  exact (WidthPoly.const sources k 128).mul
    ((hw.add (WidthPoly.const sources k 1)).mul (hshift.add (WidthPoly.const sources k 2)))

theorem widthPoly_recordAppend (sources : RepairSource.EightSources) (k : ℕ)
    {w : ℕ → ℕ} (hw : WidthPoly sources k w) :
    WidthPoly sources k (fun N => CompetitorCountRecordAppend.budget (w N)) := by
  refine WidthPoly.mono (f := fun N => 25120 * ((w N + 1) * (w N + 1))) (fun N => ?_) ?_
  · have h := countRecordAppend_le (w N)
    have hsq : (w N + 1) ^ 2 = (w N + 1) * (w N + 1) := by ring
    omega
  · exact (WidthPoly.const sources k 25120).mul
      ((hw.add (WidthPoly.const sources k 1)).mul (hw.add (WidthPoly.const sources k 1)))

/-! ## §3  The composed per-round fuel -/

def termFuel (w rows shift : ℕ) : ℕ :=
  rowAnswerFuel w rows + 1 + answerShiftFuel w shift + 1
    + CompetitorCountRecordAppend.budget w

/-- **A docked segment, then the clear that puts its slots back to `[]`.**
`round_clear_seq` (`Proof/CaseAnalysis/FinalBandClearDock.lean`) delivers a
single `Step` at `cost + 1 + (2*total + 4)` with `total := cost + 1`, which
`clear_budget` (`:385`) computes as `3*cost + 7`.

Use `round_clear_seq`, NOT `zeroBand_round_then_clear`: `round_step_of_dock`'s
`hframe` freezes tape `81`, so the latter cannot produce the port change
`Rounds` needs. -/
def clearedFuel (f : ℕ) : ℕ := 3 * f + 7

/-- `clearedFuel` IS segment-then-clear, at `clear_budget`'s own arithmetic. -/
theorem clearedFuel_eq (f : ℕ) : clearedFuel f = f + 1 + (2 * (f + 1) + 4) :=
  (clear_budget f).symm

/-- **THE WHOLE ROUND.**  Decode the clause address (cleared), run the `terms`
monomials that address emits (each cleared, because the slots are reused), bump
the round cursor (cleared) -- every join a `Step.seq` bridge step. -/
def roundFuel (w rows shift decode cursor terms : ℕ) : ℕ :=
  clearedFuel decode + 1 + terms * (clearedFuel (termFuel w rows shift) + 1) + 1
    + clearedFuel cursor

/-- The per-monomial charge is `q^{O(1)}`. -/
theorem widthPoly_termFuel (sources : RepairSource.EightSources) (k : ℕ)
    {w rows shift : ℕ → ℕ} (hw : WidthPoly sources k w) (hrows : WidthPoly sources k rows)
    (hshift : WidthPoly sources k shift) :
    WidthPoly sources k (fun N => termFuel (w N) (rows N) (shift N)) := by
  refine WidthPoly.mono
    (f := fun N => rowAnswerFuel (w N) (rows N) + 1 + answerShiftFuel (w N) (shift N) + 1
      + CompetitorCountRecordAppend.budget (w N)) (fun N => le_of_eq rfl) ?_
  exact ((((widthPoly_rowAnswerFuel sources k hw hrows).add (WidthPoly.const sources k 1)).add
    (widthPoly_answerShiftFuel sources k hw hshift)).add (WidthPoly.const sources k 1)).add
    (widthPoly_recordAppend sources k hw)

/-- A cleared segment is `q^{O(1)}` whenever the segment is. -/
theorem widthPoly_clearedFuel (sources : RepairSource.EightSources) (k : ℕ) {f : ℕ → ℕ}
    (hf : WidthPoly sources k f) : WidthPoly sources k (fun N => clearedFuel (f N)) := by
  refine WidthPoly.mono (f := fun N => 3 * f N + 7) (fun N => le_of_eq rfl) ?_
  exact ((WidthPoly.const sources k 3).mul hf).add (WidthPoly.const sources k 7)

/-- **The whole round -- every stage and every clear -- is `q^{O(1)}`.** -/
theorem widthPoly_roundFuel (sources : RepairSource.EightSources) (k : ℕ)
    {w rows shift decode cursor terms : ℕ → ℕ} (hw : WidthPoly sources k w)
    (hrows : WidthPoly sources k rows) (hshift : WidthPoly sources k shift)
    (hdecode : WidthPoly sources k decode) (hcursor : WidthPoly sources k cursor)
    (hterms : WidthPoly sources k terms) :
    WidthPoly sources k
      (fun N => roundFuel (w N) (rows N) (shift N) (decode N) (cursor N) (terms N)) := by
  refine WidthPoly.mono
    (f := fun N => clearedFuel (decode N) + 1
      + terms N * (clearedFuel (termFuel (w N) (rows N) (shift N)) + 1) + 1
      + clearedFuel (cursor N)) (fun N => le_of_eq rfl) ?_
  exact ((((widthPoly_clearedFuel sources k hdecode).add (WidthPoly.const sources k 1)).add
    (hterms.mul ((widthPoly_clearedFuel sources k
      (widthPoly_termFuel sources k hw hrows hshift)).add
      (WidthPoly.const sources k 1)))).add (WidthPoly.const sources k 1)).add
    (widthPoly_clearedFuel sources k hcursor)

theorem roundFuel_le_hotFuel (sources : RepairSource.EightSources) (k r degree : ℕ)
    (rows shift decode cursor terms : ℕ → ℕ)
    (hrows : WidthPoly sources k rows) (hshift : WidthPoly sources k shift)
    (hdecode : WidthPoly sources k decode) (hcursor : WidthPoly sources k cursor)
    (hterms : WidthPoly sources k terms) :
    ∃ onset : ℕ, ∀ N, onset ≤ N →
      roundFuel (entryWidthSchedule sources k r N) (rows N) (shift N) (decode N)
          (cursor N) (terms N)
        ≤ hotFuel sources k r degree N :=
  (widthPoly_roundFuel sources k (widthPoly_entryWidthSchedule sources k r) hrows hshift
    hdecode hcursor hterms).le_hotFuel r degree

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

theorem rounds_enlarge (extra : ℕ) (bs : ℕ) (body : Machine (218 + (60 + extra)) bs)
    (cost cost' entryWidth : ℕ) (hle : cost ≤ cost')
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (Inv : ℕ → (ℕ → List Bool) → Prop)
    (h : Rounds extra body cost entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness Inv) :
    Rounds extra body cost' entryWidth answer denominator phase pcpp coordinate
      systematicAtom input witness Inv := by
  intro k s hk
  obtain ⟨s', hinv, hstep⟩ := h k s hk
  exact ⟨s', hinv, hstep.enlarge hle⟩

theorem rounds_at_cell (sources : RepairSource.EightSources) (k r degree N : ℕ)
    (rows shift decode cursor terms : ℕ → ℕ)
    (hfit : roundFuel (entryWidthSchedule sources k r N) (rows N) (shift N) (decode N)
        (cursor N) (terms N)
      ≤ hotFuel sources k r degree N)
    (extra : ℕ) (bs : ℕ) (body : Machine (218 + (60 + extra)) bs)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (Inv : ℕ → (ℕ → List Bool) → Prop)
    (h : Rounds extra body
      (roundFuel (entryWidthSchedule sources k r N) (rows N) (shift N) (decode N)
        (cursor N) (terms N))
      (entryWidthSchedule sources k r N) answer denominator phase pcpp coordinate
      systematicAtom input witness Inv) :
    Rounds extra body (hotFuel sources k r degree N) (entryWidthSchedule sources k r N)
      answer denominator phase pcpp coordinate systematicAtom input witness Inv :=
  rounds_enlarge extra bs body _ _ _ hfit answer denominator phase pcpp coordinate
    systematicAtom input witness Inv h

/-- **The two halves fused.**  From the five stage magnitudes alone: past an
onset, every round loop that fits the composed stage total fits the paper's
per-call cell. -/
theorem rounds_at_cell_eventually (sources : RepairSource.EightSources) (k r degree : ℕ)
    (rows shift decode cursor terms : ℕ → ℕ)
    (hrows : WidthPoly sources k rows) (hshift : WidthPoly sources k shift)
    (hdecode : WidthPoly sources k decode) (hcursor : WidthPoly sources k cursor)
    (hterms : WidthPoly sources k terms) :
    ∃ onset : ℕ, ∀ N, onset ≤ N →
      ∀ (extra bs : ℕ) (body : Machine (218 + (60 + extra)) bs)
        (answer : List Atom → ℕ) (denominator : ℕ)
        (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
        (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
          CircuitPolynomial Atom 1)
        (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
        (Inv : ℕ → (ℕ → List Bool) → Prop),
        Rounds extra body
            (roundFuel (entryWidthSchedule sources k r N) (rows N) (shift N) (decode N)
              (cursor N) (terms N))
            (entryWidthSchedule sources k r N) answer denominator phase pcpp coordinate
            systematicAtom input witness Inv →
          Rounds extra body (hotFuel sources k r degree N) (entryWidthSchedule sources k r N)
            answer denominator phase pcpp coordinate systematicAtom input witness Inv := by
  obtain ⟨onset, honset⟩ :=
    roundFuel_le_hotFuel sources k r degree rows shift decode cursor terms hrows hshift
      hdecode hcursor hterms
  refine ⟨onset, fun N hN extra bs body answer denominator phase pcpp coordinate
    systematicAtom input witness Inv h => ?_⟩
  exact rounds_at_cell sources k r degree N rows shift decode cursor terms (honset N hN)
    extra bs body answer denominator phase pcpp coordinate systematicAtom input witness Inv h

/-! ## §5  `k`-FREENESS -- the check that decides whether this is one factor or two -/

/-- **The number of records ONE round emits does not grow with the round.**
`addressRecords` (`Proof/CaseAnalysis/FinalSupplierCall.lean`) is `siteRecords`
at a single clause address, and `site_le`
(`Proof/CaseAnalysis/FinalCallCountCap.lean`) caps that address's monomial
count by `siteCap L = 16*(L+1)^4` UNIFORMLY in the address.  So the round's
`terms` is `k`-free -- compiled, not read. -/
theorem addressRecords_length_le (L n : ℕ) {circ : BooleanCircuit n}
    (pcpp : PointwisePCPP circ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hL : ∀ i, (coordinate i).monomials.length ≤ L) (k : ℕ) :
    (addressRecords answer denominator phase pcpp coordinate systematicAtom k).length
      ≤ siteCap L := by
  unfold addressRecords
  have hsite : ∀ address ∈ (((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.drop k).take 1),
      (siteRecords answer denominator phase pcpp coordinate systematicAtom address).length
        ≤ siteCap L := by
    intro address _
    unfold siteRecords callRecords siteCalls
    simp only [List.length_map, scale_length]
    exact site_le L n pcpp phase coordinate systematicAtom hL address
  have hflat := length_flatMap_le
    (((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.drop k).take 1)
    (siteRecords answer denominator phase pcpp coordinate systematicAtom) (siteCap L) hsite
  have hlen : (((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.drop k).take 1).length
      ≤ 1 := by
    rw [List.length_take]
    omega
  calc ((((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.drop k).take 1).flatMap
          (siteRecords answer denominator phase pcpp coordinate systematicAtom)).length
      ≤ (((univ : Finset (Fin (2 ^ pcpp.clauseBits))).toList.drop k).take 1).length
        * siteCap L := hflat
    _ ≤ 1 * siteCap L := Nat.mul_le_mul_right _ hlen
    _ = siteCap L := one_mul _

/-- **The clause decode's charge, named.**  `clause_dock`
(`Proof/CaseAnalysis/FinalWordFunctionDock.lean`) pays
`2*(Q.coefficient*(rq.circuit.size + rq.arity + 1)^Q.degree) + 2`. -/
def decodeFuel (a : PointwisePCPPAlgorithm) (Q : PCPPQueryRealization a)
    (rq : PCPPRequest a.minimumArity) : ℕ :=
  2 * (Q.coefficient * (rq.circuit.size + rq.arity + 1) ^ Q.degree) + 2

/-- **The clause decode's charge does not see the round index.**  This is
`clause_dock` restated with its fuel written as `decodeFuel a Q rq`, an
expression in the PCPP REQUEST alone: the clause index `i` -- which IS the round
index -- does not occur in it.  The proof is `clause_dock` itself, so the
statement is a machine-checked certificate that the decode is `k`-free. -/
theorem clause_dock_at_decodeFuel (a : PointwisePCPPAlgorithm) (Q : PCPPQueryRealization a)
    {M : ℕ} (slots : Fin (rewound Q.clause).tapeCount → Fin M)
    (hinj : Function.Injective slots) (A : Fin M → List Bool)
    (rq : PCPPRequest a.minimumArity) (i : Fin (2 ^ (a.output rq).clauseBits))
    (hin : A (slots (inSlot (rewound Q.clause))) = frame (pcppInput rq ++ natWord i.val))
    (hblank : ∀ j, j ≠ inSlot (rewound Q.clause) → A (slots j) = []) :
    ∃ tout : Fin (rewound Q.clause).tapeCount → List Bool,
      tout (rewound Q.clause).outputTape =
        natListWord [literalIndex ((a.output rq).clauses i).left,
          literalIndex ((a.output rq).clauses i).right] ∧
      Step (RecoveryFocus.machine slots (rewound Q.clause).machine) (decodeFuel a Q rq)
        (fun _ => 0) A (fun _ => 0) (install slots A tout) :=
  clause_dock a Q slots hinj A rq i hin hblank

theorem unaryCursor_no_uniform_bound (C : ℕ) :
    ∃ k : ℕ, unaryCursorCost k + C < unaryCursorCost (k + 1) := by
  refine ⟨C, ?_⟩
  rw [unaryCursorCost_eq, unaryCursorCost_eq]
  nlinarith

end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10RoundBudget
