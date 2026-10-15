import Proof.PCP.ProjectionNormalizationDedupLoop

/-! The concrete workspace bounds for the enclosing raw-clause caller. All
zero padding is removed by the later cold run; these numbers are not supplied
unary inputs or externally assumed runtime addresses. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Dedup
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def pairCap (rows : List SuffixScan.Clause) := 2*(SuffixScan.stream rows).length+3
def scanCapacity (rows : List SuffixScan.Clause) := 2*(rows.length*(2*pairCap rows+6)+1)+2
def copyCapacity (rows : List SuffixScan.Clause) := (SuffixScan.stream rows).length+2

theorem clause_min (row : SuffixScan.Clause) : 3 ≤ (ClauseEquality.stream row).length := by
  simp [ClauseEquality.stream,frame_length]
  omega

theorem count_le_bytes (rows : List SuffixScan.Clause) : rows.length ≤ (SuffixScan.stream rows).length := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have h := clause_min row
    simp only [SuffixScan.stream_cons,List.length_append,List.length_cons]
    omega

theorem member_bytes (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) (hr : row∈rows) :
    (ClauseEquality.stream row).length ≤ (SuffixScan.stream rows).length := by
  induction rows with
  | nil => simp at hr
  | cons head rows ih =>
    rcases List.mem_cons.mp hr with h|h
    · subst head; simp
    · have ht := ih h
      simp only [SuffixScan.stream_cons,List.length_append]
      omega

theorem pair_budget (left right : SuffixScan.Clause) :
    ClauseProbe.budget left right ≤ (ClauseEquality.stream left).length+(ClauseEquality.stream right).length+3 := by
  have h0 : max (left 0).length (right 0).length ≤ (left 0).length+(right 0).length := by omega
  have h1 : max (left 1).length (right 1).length ≤ (left 1).length+(right 1).length := by omega
  have h2 : max (left 2).length (right 2).length ≤ (left 2).length+(right 2).length := by omega
  simp only [ClauseProbe.budget,ClauseEquality.budget,ClauseEquality.stream,List.length_append,frame_length]
  omega

theorem pair_fits (rows : List SuffixScan.Clause) (a : SuffixScan.Clause) (ha : a∈rows)
    (b : SuffixScan.Clause) (hb : b∈rows) : ClauseProbe.budget a b ≤ pairCap rows := by
  have h := pair_budget a b
  have h1 := member_bytes a rows ha
  have h2 := member_bytes b rows hb
  dsimp only [pairCap]
  omega

theorem copy_fits (rows : List SuffixScan.Clause) (a : SuffixScan.Clause) (ha : a∈rows) :
    (ClauseEquality.stream a).length+2 ≤ copyCapacity rows := by
  exact Nat.add_le_add_right (member_bytes a rows ha) 2

def initialStore (source : List Bool) (sourcePos : ℕ) (rows : List SuffixScan.Clause) : Store where
  source := source
  sourcePos := sourcePos
  candidate := []
  candidatePos := 0
  out := []
  discard := []
  driverPos := 1
  eq := false
  found := false
  kept := 0
  count := rows.length
  cap := pairCap rows
  scanCap := scanCapacity rows
  copyCap := copyCapacity rows

theorem initial_run (pre suffix : List Bool) (rows : List SuffixScan.Clause) :
    ∃ r,runFrom machine (loopBudget (initialStore (pre++SuffixScan.stream rows++suffix) pre.length rows) rows)
      (loopCfg 0 (initialStore (pre++SuffixScan.stream rows++suffix) pre.length rows))=some r ∧
      r.steps ≤ loopBudget (initialStore (pre++SuffixScan.stream rows++suffix) pre.length rows) rows ∧
      r.final=loopCfg 1 (process rows (initialStore (pre++SuffixScan.stream rows++suffix) pre.length rows)) := by
  exact loop_run rows _ pre suffix 0 rfl rfl rfl rfl (by simp [initialStore])
    (copy_fits rows) (pair_fits rows) (by rfl)

theorem cubic_budget (source : List Bool) (pos : ℕ) (rows : List SuffixScan.Clause) :
    2*loopBudget (initialStore source pos rows) rows+8 ≤ 128*((SuffixScan.stream rows).length+1)^3 := by
  have h := count_le_bytes rows
  have hsq : rows.length^2 ≤ (SuffixScan.stream rows).length^2 := Nat.pow_le_pow_left h 2
  have hcube : rows.length^2*(SuffixScan.stream rows).length ≤ (SuffixScan.stream rows).length^3 := by
    calc
      _ ≤ (SuffixScan.stream rows).length^2*(SuffixScan.stream rows).length := Nat.mul_le_mul_right _ hsq
      _ = _ := by ring
  simp only [loopBudget,initialStore,pairCap]
  nlinarith

end NearCubicWires.RepairSource.ProjectionNormalization.Dedup
