import SourceAdapters.Compile.OraclePrintTrans

/-!
proof of `thm:short-pcp-ours`, Step 4: constant register resources for the runtime transition template.
Fixed program tables change syntax size, never the binder or term workspace.
-/
namespace NearCubicGates.Adapters.Compile.OraclePrint
open NearCubicWires NearCubicWires.RepairSource NearCubicWires.FinitePredicateCircuit
  NearCubicWires.LocalBitMultitape OracleExecution
set_option autoImplicit false

theorem orList_depth_le (us : List U) (d : ℕ) : (U.orList us).depth ≤ d ↔ ∀ u ∈ us, u.depth ≤ d := by
  induction us with
  | nil => simp [U.orList,U.depth,U.ofBool]
  | cons u us ih => simp [U.orList,U.depth,ih]

theorem andList_depth_le (us : List U) (d : ℕ) : (U.andList us).depth ≤ d ↔ ∀ u ∈ us, u.depth ≤ d := by
  induction us with
  | nil => simp [U.andList,U.depth,U.ofBool]
  | cons u us ih => simp [U.andList,U.depth,ih]

theorem orList_tneed_le (us : List U) (d : ℕ) (hd : 1≤d) :
    (U.orList us).tneed ≤ d ↔ ∀ u ∈ us, u.tneed ≤ d := by
  induction us with
  | nil => simp [U.orList,U.tneed,U.ofBool,Tm.ofBool,Tm.need,hd]
  | cons u us ih => simp [U.orList,U.tneed,ih]

theorem andList_tneed_le (us : List U) (d : ℕ) (hd : 1≤d) :
    (U.andList us).tneed ≤ d ↔ ∀ u ∈ us, u.tneed ≤ d := by
  induction us with
  | nil => simp [U.andList,U.tneed,U.ofBool,Tm.ofBool,Tm.need,hd]
  | cons u us ih => simp [U.andList,U.tneed,ih]

theorem pickU_depth_le (us : List U) (index : Tm) (d : ℕ)
    (h : ∀ u ∈ us, u.depth ≤ d) : (pickU us index).depth ≤ d := by
  induction us generalizing index with
  | nil => simp [pickU,U.depth,U.ofBool]
  | cons u us ih =>
    simp only [pickU,U.depth,max_le_iff]
    exact ⟨h u (by simp),ih _ (fun v hv => h v (by simp [hv]))⟩

theorem pickU_tneed_le (us : List U) (index : Tm) (d : ℕ) (hd : 2≤d)
    (hi : index.need≤d) (h : ∀ u ∈ us, u.tneed≤d) : (pickU us index).tneed≤d := by
  induction us generalizing index with
  | nil => simp [pickU,U.tneed,U.ofBool,Tm.ofBool,Tm.need];omega
  | cons u us ih =>
    simp only [pickU,U.tneed,Tm.need,max_le_iff]
    exact ⟨⟨hi,hd⟩,h u (by simp),ih _ (by simp [Tm.need,hi,hd]) (fun v hv => h v (by simp [hv]))⟩

theorem rowU_depth {t s : ℕ} (q : Fin s) (scans : Fin t → Bool) (ℓ : ℕ) :
    (rowU q scans ℓ).depth≤1 := by
  simp only [rowU,U.depth,max_le_iff,andList_depth_le]
  constructor
  · omega
  · intro u hu
    obtain ⟨tape,rfl⟩ := List.mem_ofFn.mp hu
    split <;> simp [scannedU,headSelectionU,U.depth,U.ofBool]

theorem rowU_tneed {t s : ℕ} (q : Fin s) (scans : Fin t → Bool) (ℓ : ℕ) :
    (rowU q scans ℓ).tneed≤16 := by
  simp only [rowU,U.tneed,max_le_iff,andList_tneed_le _ 16 (by omega)]
  constructor
  · simp [Tm.need]
  · intro u hu
    obtain ⟨tape,rfl⟩ := List.mem_ofFn.mp hu
    split <;> simp [scannedU,headSelectionU,U.tneed,U.ofBool,Tm.ofBool,headT,cellT,Tm.need]

theorem fitsU_depth {t s : ℕ} (action : Action t s) (ℓ : ℕ) : (fitsU action ℓ).depth≤1 := by
  apply (andList_depth_le _ _).2
  intro u hu
  obtain ⟨tape,rfl⟩ := List.mem_ofFn.mp hu
  simp [headSelectionU,U.depth,U.ofBool]

theorem fitsU_tneed {t s : ℕ} (action : Action t s) (ℓ : ℕ) : (fitsU action ℓ).tneed≤16 := by
  apply (andList_tneed_le _ 16 (by omega)).2
  intro u hu
  obtain ⟨tape,rfl⟩ := List.mem_ofFn.mp hu
  cases action.move tape <;> simp [headSelectionU,moveT,U.tneed,U.ofBool,Tm.ofBool,headT,Tm.need]

theorem localGuardU_depth (p : OrdinaryOracleProgram) (action : Action p.base.tapeCount p.base.stateCount) :
    (localGuardU p action 5).depth≤1 := by
  simp only [localGuardU,U.depth,max_le_iff]
  exact ⟨by simp [positiveU,U.depth,U.ofBool],fitsU_depth action 5⟩

theorem localGuardU_tneed (p : OrdinaryOracleProgram) (action : Action p.base.tapeCount p.base.stateCount) :
    (localGuardU p action 5).tneed≤16 := by
  simp only [localGuardU,U.tneed,max_le_iff]
  exact ⟨by simp [positiveU,U.tneed,U.ofBool,Tm.ofBool,Tm.need,budgetT,initLengthEndT,initWindowT],fitsU_tneed action 5⟩

theorem queryGuardU_depth (p : OrdinaryOracleProgram) : (queryGuardU p 5).depth≤4 := by
  simp [queryGuardU,affordableU,remainingU,prefixU,allocU,cellU,U.depth,U.ofBool]

theorem queryGuardU_tneed (p : OrdinaryOracleProgram) : (queryGuardU p 5).tneed≤16 := by
  simp [queryGuardU,affordableU,remainingU,prefixU,allocU,cellU,U.tneed,U.ofBool,Tm.ofBool,
    headT,cellT,lenT,budgetT,initLengthEndT,initWindowT,Tm.need]

theorem queryActionU_depth (p : OrdinaryOracleProgram) (rule : OracleReturn p.base.stateCount) :
    (queryActionU p rule).depth≤3 := by
  simp [queryActionU,remainingU,prefixU,allocU,cellU,U.depth,U.ofBool]

theorem queryActionU_tneed (p : OrdinaryOracleProgram) (rule : OracleReturn p.base.stateCount) :
    (queryActionU p rule).tneed≤16 := by
  simp [queryActionU,remainingU,prefixU,allocU,cellU,U.tneed,U.ofBool,Tm.ofBool,
    clockSizeT,cellT,lenT,budgetT,initLengthEndT,initWindowT,Tm.need]

end NearCubicGates.Adapters.Compile.OraclePrint
