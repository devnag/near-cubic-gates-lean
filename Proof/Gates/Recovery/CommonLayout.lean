import Proof.Gates.Recovery.GateWidth
import Proof.Gates.Recovery.CommonSem
import Proof.Gates.GateRecovery.Proof.CaseAnalysis.CommonPrefixSelected
import Proof.Hierarchy.HierarchyFixedWord
import Proof.CaseAnalysis.CommonPortBank

/-!
# The common SAT-oracle program of the recovery: layout

Paper §11.6: "The fixed-machine refuter runs in poly(T_clk(N_ν)) = 2^{O(q)} time with SAT access. The choices of
sec:gadget-transfer are recovered in three stages …; Since q = O(n), the final functions belong to E^NP." One ordinary
SAT-oracle program on every final length `n`, three pieces on one tape bank:
* piece 0, the refuter prefix (GR's `CloseoutCommonPrefix.program` at `toEight s g`): the schedule selects `ν`, the
  live flag is `onset ≤ N_ν`, the hierarchy slot holds `frame z ++ post` for the refuter's output `z`, tape 0 the
  framed final address, the query tape a run of zeros;
* piece 1, the after-prefix program `AfterRun` (`Recovery.AfterSpec`), its ports `zPort`, `pointPort`, query and output
  banked onto the hierarchy slot, the address, the query tape and the output tape, every other tape fresh;
* piece 2, the fixed word `false` on the output tape (no live source index).
-/

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.Common

open NearCubicWires NearCubicWires.RepairSource NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairSource.OrdinaryOracleCompose NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicGates.Close.Transfer NearCubicGates.Close.Gadget

/-- The constants of the common program: the prefix's (chosen by `CloseoutCommonPrefix.exists_selected`) and the
after-prefix program. -/
structure Params (s : GateSources) (P : ThreeQueryPCPP) (g : GateParams) where
  As : ℕ
  Bs : ℕ
  onset : ℕ
  Aw : ℕ
  Bw : ℕ
  refuter : OrdinaryOracleProgram
  ar : AfterRun s P g

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

noncomputable section

/-- The schedule's work tapes. -/
noncomputable def work (s : GateSources) (g : GateParams) : ℕ :=
  GR.NearCubicWires.RepairSource.CloseoutSchedule.Step.workTapes (toEight s g) g.k g.clauseDegree

/-- Piece 0's program. -/
noncomputable def prefixProgram (p : Params s P g) : OrdinaryOracleProgram :=
  GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.program (toEight s g) g.k g.clauseDegree g.ampFactor
    (g.positionLog - 1) p.As p.Bs p.onset p.Aw p.Bw g.clock p.refuter

/-- The prefix's tape count. -/
noncomputable abbrev pt (p : Params s P g) : ℕ := (prefixProgram p).base.tapeCount

theorem pt_eq (p : Params s P g) :
    pt p = GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.tapes (work s g) p.refuter g.k := rfl

/-- The prefix bank and the output tape. -/
noncomputable abbrev n0 (p : Params s P g) : ℕ := pt p + 1
noncomputable abbrev ta (p : Params s P g) : ℕ := p.ar.prog.base.tapeCount
noncomputable abbrev tapes (p : Params s P g) : ℕ := n0 p + ta p + 2

/-! ## The prefix's ports, in its own bank -/

/-- The framed final address (tape 0). -/
noncomputable def addressP (p : Params s P g) : Fin (pt p) :=
  GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.firstSlots (work s g) p.refuter g.k
    (GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.address (work s g) p.refuter)

/-- The hierarchy slot `frame z ++ post`. -/
noncomputable def wordP (p : Params s P g) : Fin (pt p) :=
  GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.prepareSlots (work s g) p.refuter g.k
    (CloseoutCommonPrepare.hierarchySlot g.k)

/-- The live flag `[decide (onset ≤ N)]`. -/
noncomputable def flagP (p : Params s P g) : Fin (pt p) :=
  GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.firstSlots (work s g) p.refuter g.k
    (CloseoutRetainedRefuter.old p.refuter
      (GR.NearCubicWires.RepairSource.CloseoutSchedule.RefuterPrefix.flagPort (work s g)))

theorem addressP_val (p : Params s P g) : (addressP p).val = 0 := by
  unfold addressP
  rw [GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.first_address]
  rfl

theorem queryP_pos (p : Params s P g) : (prefixProgram p).queryTape.val ≠ 0 := (prefixProgram p).queryFresh

theorem queryP_lt (p : Params s P g) :
    (prefixProgram p).queryTape.val < 1 + GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.base (work s g) p.refuter :=
  GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.first_bound (work s g) p.refuter g.k
    (GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.query (work s g) p.refuter)

theorem wordP_ge (p : Params s P g) :
    1 + GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.base (work s g) p.refuter ≤ (wordP p).val := by
  have hb := HierarchyFromInput.tapes_lower (g.k + 2)
  have hf : (CloseoutHierarchyRequest.fresh g.k 0).val ≠ 2 := by
    change CloseoutHierarchyClock.Input.tapes (g.k + 2) + 0 ≠ 2
    unfold CloseoutHierarchyClock.Input.tapes
    omega
  have hw : (CloseoutCommonPrepare.hierarchySlot g.k).val = 27 + (CloseoutHierarchyRequest.fresh g.k 0).val := by
    simp only [CloseoutCommonPrepare.hierarchySlot, CloseoutCommonPrepare.requestSlots,
      CloseoutHierarchyRequest.Shared.bank, if_neg hf, Fin.val_natAdd]
  have h0 : (CloseoutCommonPrepare.hierarchySlot g.k).val ≠ 0 := by omega
  have h1 : (CloseoutCommonPrepare.hierarchySlot g.k).val ≠ 1 := by omega
  unfold wordP
  simp only [GR.NearCubicWires.RepairSource.CloseoutCommonPrefix.prepareSlots, if_neg h0, if_neg h1]
  omega

/-! ## The common bank -/

def lift0 (p : Params s P g) (i : Fin (n0 p)) : Fin (tapes p) := (i.castAdd (ta p)).castAdd 2
def prefixSlot (p : Params s P g) (i : Fin (pt p)) : Fin (tapes p) := lift0 p (i.castAdd 1)
def output0 (p : Params s P g) : Fin (n0 p) := (0 : Fin 1).natAdd (pt p)

/-- The after-prefix program's four shared ports. -/
def afterLocal (p : Params s P g) : Fin 4 → Fin (ta p) :=
  ![p.ar.zPort, p.ar.pointPort, p.ar.prog.queryTape, p.ar.prog.base.outputTape]
def afterShared (p : Params s P g) : Fin 4 → Fin (n0 p) :=
  ![(wordP p).castAdd 1, (addressP p).castAdd 1, (prefixProgram p).queryTape.castAdd 1, output0 p]
def afterSlot (p : Params s P g) (i : Fin (ta p)) : Fin (tapes p) :=
  (CloseoutCommonPortBank.slot (afterLocal p) (afterShared p) i).castAdd 2

def falseLocal : Fin 1 → Fin 2 := fun _ => 0
def falseShared (p : Params s P g) : Fin 1 → Fin (n0 p + ta p) := fun _ => (output0 p).castAdd (ta p)
def falseSlot (p : Params s P g) : Fin 2 → Fin (tapes p) := CloseoutCommonPortBank.slot falseLocal (falseShared p)

def liveFlag (p : Params s P g) : Fin (tapes p) := prefixSlot p (flagP p)

/-- The three pieces. -/
noncomputable def pieces (p : Params s P g) : Fin 3 → Piece (tapes p) :=
  ![focused (prefixProgram p) (prefixSlot p),
    focused p.ar.prog (afterSlot p),
    ordinary (RecoveryFocus.machine (falseSlot p) (HierarchyFixedWord.machine [false]))]

/-- After the prefix: the after-prefix program on a live flag, else `false`; then stop. -/
def next (p : Params s P g) (j : Fin 3) (_ : Fin (pieces p j).states) (read : Fin (tapes p) → Bool) : Option (Fin 3) :=
  if j.val = 0 then some (if read (liveFlag p) then 1 else 2) else none

theorem output0_ne_zero (p : Params s P g) : (lift0 p (output0 p)).val ≠ 0 := by
  have h := (prefixProgram p).base.twoTapes
  change pt p + 0 ≠ 0
  unfold pt
  omega

noncomputable def ports (p : Params s P g) : Ports (tapes p) where
  twoTapes := by unfold tapes; omega
  outputTape := lift0 p (output0 p)
  outputFresh := output0_ne_zero p
  queryTape := lift0 p ((prefixProgram p).queryTape.castAdd 1)
  queryFresh := (prefixProgram p).queryFresh

/-- **The common program.** -/
noncomputable def program (p : Params s P g) : OrdinaryOracleProgram := (ports p).program (graph (pieces p) 0 (next p))

/-- The initial bank: the framed final address on tape 0. -/
def input (p : Params s P g) (bits : List Bool) (i : Fin (tapes p)) : List Bool := if i.val = 0 then RepairOrdinary.frame bits else []

theorem ordinary_input (p : Params s P g) (bits : List Bool) : (program p).base.inputTapes bits = input p bits := rfl

/-! ## Injectivity -/

theorem lift0_injective (p : Params s P g) : Function.Injective (lift0 p) := by
  intro i j h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa [lift0] using this

theorem prefix_injective (p : Params s P g) : Function.Injective (prefixSlot p) :=
  (lift0_injective p).comp (Fin.castAdd_injective _ _)

theorem afterLocal_injective (p : Params s P g) : Function.Injective (afterLocal p) := by
  have h1 := p.ar.zPoint
  have h2 := p.ar.zQuery
  have h3 := p.ar.zOutput
  have h4 := p.ar.pointQuery
  have h5 := p.ar.pointOutput
  have h6 := p.ar.queryOutput
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [afterLocal]

theorem afterShared_injective (p : Params s P g) : Function.Injective (afterShared p) := by
  have ha := addressP_val p
  have hq0 := queryP_pos p
  have hq1 := queryP_lt p
  have hw := wordP_ge p
  have hwb := (wordP p).isLt
  have hqb := (prefixProgram p).queryTape.isLt
  intro i j h
  have hv := congrArg Fin.val h
  fin_cases i <;> fin_cases j <;> simp [afterShared, output0] at hv ⊢ <;> unfold pt at * <;> omega

theorem after_injective (p : Params s P g) : Function.Injective (afterSlot p) :=
  (Fin.castAdd_injective _ _).comp (CloseoutCommonPortBank.injective _ _ (afterShared_injective p))

theorem false_injective (p : Params s P g) : Function.Injective (falseSlot p) :=
  CloseoutCommonPortBank.injective _ _ (fun i j _ => Subsingleton.elim i j)

end

end NearCubicGates.Close.Recovery.Common
