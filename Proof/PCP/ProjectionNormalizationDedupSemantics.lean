import Proof.PCP.ProjectionNormalizationDedupBody

/-! The exact store transformation computed by the keep-last call graph.
In particular, its output is the target's ordered List.dedup stream and its
physical kept counter has precisely that list length. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.Dedup
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

@[simp] theorem result_source (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) :
    (result d row rows).source=d.source := by
  classical
  unfold result
  split <;> rfl

@[simp] theorem result_sourcePos (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) :
    (result d row rows).sourcePos=d.sourcePos+(ClauseEquality.stream row).length := by
  classical
  unfold result
  split <;> rfl

@[simp] theorem result_candidate (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) :
    (result d row rows).candidate=d.candidate++ClauseEquality.stream row := by
  classical
  unfold result
  split <;> rfl

@[simp] theorem result_candidatePos (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) :
    (result d row rows).candidatePos=d.candidate.length+(ClauseEquality.stream row).length := by
  classical
  unfold result
  split <;> rfl

@[simp] theorem result_driverPos (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) :
    (result d row rows).driverPos=d.driverPos+1 := by
  classical
  unfold result
  split <;> rfl

@[simp] theorem result_count (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) :
    (result d row rows).count=d.count := by
  classical
  unfold result
  split <;> rfl

@[simp] theorem result_cap (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) :
    (result d row rows).cap=d.cap := by
  classical
  unfold result
  split <;> rfl

@[simp] theorem result_scanCap (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) :
    (result d row rows).scanCap=d.scanCap := by
  classical
  unfold result
  split <;> rfl

@[simp] theorem result_copyCap (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) :
    (result d row rows).copyCap=d.copyCap := by
  classical
  unfold result
  split <;> rfl

theorem result_out (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) :
    (result d row rows).out=if row∈rows then d.out else d.out++ClauseEquality.stream row := by
  classical
  unfold result
  split <;> rfl

theorem result_kept (d : Store) (row : SuffixScan.Clause) (rows : List SuffixScan.Clause) :
    (result d row rows).kept=if row∈rows then d.kept else d.kept+1 := by
  classical
  unfold result
  split <;> rfl

noncomputable def process : List SuffixScan.Clause → Store → Store
  | [],d => d
  | row::rows,d => process rows (result d row rows)

@[simp] theorem process_source (rows : List SuffixScan.Clause) (d : Store) :
    (process rows d).source=d.source := by
  induction rows generalizing d with
  | nil => rfl
  | cons row rows ih => rw [process,ih,result_source]

@[simp] theorem process_sourcePos (rows : List SuffixScan.Clause) (d : Store) :
    (process rows d).sourcePos=d.sourcePos+(SuffixScan.stream rows).length := by
  induction rows generalizing d with
  | nil => simp [process]
  | cons row rows ih =>
    rw [process,ih,result_sourcePos]
    simp only [SuffixScan.stream_cons,List.length_append,Nat.add_assoc]

@[simp] theorem process_candidate (rows : List SuffixScan.Clause) (d : Store) :
    (process rows d).candidate=d.candidate++SuffixScan.stream rows := by
  induction rows generalizing d with
  | nil => simp [process]
  | cons row rows ih =>
    rw [process,ih,result_candidate]
    simp only [SuffixScan.stream_cons,List.append_assoc]

@[simp] theorem process_driverPos (rows : List SuffixScan.Clause) (d : Store) :
    (process rows d).driverPos=d.driverPos+rows.length := by
  induction rows generalizing d with
  | nil => simp [process]
  | cons row rows ih =>
    rw [process,ih,result_driverPos]
    simp only [List.length_cons,Nat.add_assoc,Nat.add_comm 1 rows.length]

@[simp] theorem process_count (rows : List SuffixScan.Clause) (d : Store) :
    (process rows d).count=d.count := by
  induction rows generalizing d with
  | nil => rfl
  | cons row rows ih => rw [process,ih,result_count]

@[simp] theorem process_cap (rows : List SuffixScan.Clause) (d : Store) :
    (process rows d).cap=d.cap := by
  induction rows generalizing d with
  | nil => rfl
  | cons row rows ih => rw [process,ih,result_cap]

@[simp] theorem process_scanCap (rows : List SuffixScan.Clause) (d : Store) :
    (process rows d).scanCap=d.scanCap := by
  induction rows generalizing d with
  | nil => rfl
  | cons row rows ih => rw [process,ih,result_scanCap]

@[simp] theorem process_copyCap (rows : List SuffixScan.Clause) (d : Store) :
    (process rows d).copyCap=d.copyCap := by
  induction rows generalizing d with
  | nil => rfl
  | cons row rows ih => rw [process,ih,result_copyCap]

theorem process_append (rows : List SuffixScan.Clause) (d : Store) (hc : d.candidatePos=d.candidate.length) :
    (process rows d).candidatePos=(process rows d).candidate.length := by
  induction rows generalizing d with
  | nil => exact hc
  | cons row rows ih =>
    exact ih (result d row rows) (by simp only [result_candidatePos,result_candidate,List.length_append])

theorem process_out (rows : List SuffixScan.Clause) (d : Store) :
    (process rows d).out=d.out++SuffixScan.stream rows.dedup := by
  classical
  induction rows generalizing d with
  | nil => simp [process]
  | cons row rows ih =>
    rw [process,ih,result_out]
    by_cases h : row∈rows <;> simp [h,List.append_assoc]

theorem process_kept (rows : List SuffixScan.Clause) (d : Store) :
    (process rows d).kept=d.kept+rows.dedup.length := by
  classical
  induction rows generalizing d with
  | nil => simp [process]
  | cons row rows ih =>
    rw [process,ih,result_kept]
    by_cases h : row∈rows <;> simp [h,Nat.add_assoc,Nat.add_comm ]

end NearCubicWires.RepairSource.ProjectionNormalization.Dedup
