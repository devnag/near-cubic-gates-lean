import Proof.Gates.Expand.PolyTabLay
import Proof.Gates.TabMachine.Back
import Proof.Gates.TabMachine.CutM

set_option autoImplicit false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.Tabulator NearCubicGates.Close.TabMachine NearCubicGates.Close.Interfaces.Formats
open NearCubicWires.RepairOrdinary.CompetitorCrossScheduler (producer)
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-- The printer's tape count of the back end. -/
noncomputable def Qa (a : WilliamsAlgorithm) : ℕ := CompetitorCountBanks.tapes (producer a) + 124

/-- The cap requirement `hcapS` of `cutM_spec` (the source printer) for `tabT E r` at the stacked width. -/
noncomputable def capSk (E : ExpandMachine) (r : TabReq) : ℕ :=
  2 * (EquationRowCuts.stream (Wdk E r) (tabT E r).exactCuts).length +
    10 * ((r.s + 1) / 2 + Wdk E r + (tabT E r).exactCuts.length) +
    2 * (marks (srcHdr ((r.s + 1) / 2) (Wdk E r) (tabT E r).exactCuts.length (decide (r.s % 2 = 1)))).length + 40

/-- **The head's deliverable** (the tail's precondition). -/
structure TailPre (E : ExpandMachine) (a : WilliamsAlgorithm) (r : TabReq) (cap : ℕ)
    (σ : WState (NSx E.wf.program.tapeCount (Qa a)) NRk) : Prop where
  cut : CutRest sZ rY cap (Wk E r) r.s r.k (codeRecs (tsK E r)) [] [] 0 0 σ
  c56 : σ.st (sZ 56) = recStream (coefRecs r.s (Wk E r) (tsK E r))
  c56h : σ.sh (sZ 56) = 0
  c57 : σ.st (sZ 57) = recStream ((hsK E r).map (binary (Wk E r + 1)))
  c57h : σ.sh (sZ 57) = 0
  y100 : σ.val (rY 100) = 0
  y101 : σ.val (rY 101) = 0
  y102 : σ.val (rY 102) = 0
  y103 : σ.val (rY 103) = 0
  y104 : σ.val (rY 104) = 0
  y108 : σ.val (rY 108) = 0
  y109 : σ.val (rY 109) = 0
  y105 : σ.val (rY 105) = (r.s + 1) / 2
  y106 : σ.val (rY 106) = Wdk E r
  y107 : σ.val (rY 107) = (decide (r.s % 2 = 1)).toNat
  pBlank : ∀ i : Fin 130, σ.st (sP i) = [] ∧ σ.sh (sP i) = 0
  qBlank : ∀ j : Fin (Qa a), σ.st (sQ j) = [] ∧ σ.sh (sQ j) = 0
  outBlank : σ.st sOUT = [] ∧ σ.sh sOUT = 0
  bRegs : ∀ j : Fin 10, σ.val (rB j) = 0
  capK : capk E r ≤ cap
  capBig : 2 ^ (2 * (r.s + Wdk E r + 10)) ≤ cap
  capS : capSk E r ≤ cap

end NearCubicGates.Close.Expand.PolyTab
