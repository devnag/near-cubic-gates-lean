import Proof.Gates.ENP.ListedStage
import Proof.MachineModel.ClockJoin

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.After

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RecoveryScheduleEnvelope NearCubicWires.RepairOrdinary.CloseoutRecoveryWorkspace
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicGates.Close.ENP

/-- A one-port input bank: `w` on tape `i`, every other tape blank. -/
def oneBank {t : ℕ} (i : Fin t) (w : List Bool) : Fin t → List Bool := fun j => if j = i then w else []

/-- **Stage cost** (`sec:all-lengths`, "SAT formulas of size `2^{O(q)}`"): a listed-pairs stage costs at most `K (W+1)^e`
whenever `W` satisfies the workspace hypotheses of `ENP.UStage.stage_run`. -/
def UCostPoly (d : ℕ) : Prop :=
  ∃ K e : ℕ, ∀ (w R W : ℕ) (vals : List Bool) (hw : w ≤ R) {n : ℕ} (x : BitInput n),
    vals.length = 2 ^ w → 0 < oracleSizeBound d R →
    originalWorkspace R (oracleSizeBound d R) vals.length vals.length ≤ W →
    (DedupBytes.fields (unitPCP w vals)).length ≤ W → 2 ^ R ≤ W →
    UStage.cost d w R W vals hw x ≤ K * (W + 1) ^ e

/-- **Stage workspace** (`sec:all-lengths`): the workspace a listed-pairs stage needs is polynomial in `2^R`. -/
def UNeedPoly (d : ℕ) : Prop :=
  ∃ K e : ℕ, ∀ (w R : ℕ) (vals : List Bool), w ≤ R → vals.length = 2 ^ w →
    originalWorkspace R (oracleSizeBound d R) vals.length vals.length +
      (DedupBytes.fields (unitPCP w vals)).length + 2 ^ R ≤ K * (2 ^ R + 1) ^ e

/-- **`1^ν`** (`sec:gadget-machine`, `N = 2^ν`): one machine from `frame x` to `1^{⌊log₂ |x|⌋}` within `K (|x| + 1)`
steps. -/
structure NuDonor where
  t : ℕ
  st : ℕ
  M : Machine t st
  inp : Fin t
  outp : Fin t
  ne : inp ≠ outp
  K : ℕ
  run : ∀ x : List Bool, ∃ out, ClockJoin.ReadyRun M (K * (x.length + 1)) (oneBank inp (RepairOrdinary.frame x)) out ∧
    out outp = List.replicate (Nat.log 2 x.length) true

/-- **Unframe** (`sec:all-lengths`, the raw descriptor of `B*_src` for the imported constructor): one machine from
`frame d` to `d` within `K (|d| + 1)` steps. -/
structure Unframe where
  t : ℕ
  st : ℕ
  M : Machine t st
  src : Fin t
  dst : Fin t
  ne : src ≠ dst
  K : ℕ
  run : ∀ d : List Bool, ∃ out, ClockJoin.ReadyRun M (K * (d.length + 1)) (oneBank src (RepairOrdinary.frame d)) out ∧
    out dst = d

end NearCubicGates.Close.Recovery.After
