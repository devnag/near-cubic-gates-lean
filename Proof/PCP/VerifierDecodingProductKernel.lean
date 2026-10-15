import Proof.PCP.VerifierDecodingCapReset

/-! The finite capped-product controller for the exact CountsFit guard.
It adds one operand per unary driver mark and executes a source rewind after
each successful addition. Overflow is a terminal rejecting control. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.ProductMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def addCode : Fin 3 → Fin 6 := ![1,2,5]
def resetCode : Fin 3 → Fin 6 := ![2,3,0]
def mapAction {t s : ℕ} (f : Fin s → Fin 6) (a : Action t s) : Action t 6 :=
  ⟨f a.nextControl, a.write, a.move⟩
def jump (next : Fin 6) (advance : Bool) : Action 4 6 :=
  ⟨next, fun _ => none, fun tape => if tape.val = 3 ∧ advance then .right else .stay⟩
def machine : Machine 4 6 where
  descriptionBits := 0
  start := 0
  halted := fun state => 4 ≤ state.val
  rule := fun state scanned =>
    if state.val = 0 then some (jump (if scanned 3 then 1 else 4) (scanned 3))
    else if state.val = 1 then
      ((TapeEmbedding.machine 1 CapMachine.machine).rule 0 scanned).map (mapAction addCode)
    else if state.val = 2 then
      ((TapeEmbedding.machine 3 UnaryTemplate.machine).rule 0 scanned).map (mapAction resetCode)
    else if state.val = 3 then
      ((TapeEmbedding.machine 3 UnaryTemplate.machine).rule 1 scanned).map (mapAction resetCode)
    else none

def boundary (cap operand total pos value : ℕ) : Configuration 4 6 :=
  ⟨0, ![1,value+1,value+1,pos+1],
    ![CapMachine.counter cap operand, CapMachine.counter cap value,
      CapMachine.counter cap cap, CapMachine.counter cap total]⟩

theorem boundary_cells (cap operand total pos value : ℕ)
    (ha : operand ≤ cap) (ht : total ≤ cap) (hv : value ≤ cap) :
    (boundary cap operand total pos value).tapeCells = 4*(cap+2) := by
  simp [boundary, Configuration.tapeCells, Fin.sum_univ_succ,
    CapMachine.counter_length _ _ ha, CapMachine.counter_length _ _ ht,
    CapMachine.counter_length _ _ hv, CapMachine.counter_length cap cap (Nat.le_refl _)]
  omega

theorem add_prefix {space steps : ℕ} {c d : Configuration 4 3}
    (h : Prefix (TapeEmbedding.machine 1 CapMachine.machine) space steps c d) :
    Prefix machine space steps (controlConfig addCode c) (controlConfig addCode d) := by
  apply h.mapControl addCode
  · intro c hn
    have hz : c.control = 0 := Fin.ext (by simpa [TapeEmbedding.machine, CapMachine.machine] using hn)
    simp [machine, hz, addCode]
  · intro c d hn hs
    have hz : c.control = 0 := Fin.ext (by simpa [TapeEmbedding.machine, CapMachine.machine] using hn)
    have he : step machine (controlConfig addCode c) =
        (step (TapeEmbedding.machine 1 CapMachine.machine) c).map (controlConfig addCode) := by
      unfold step
      change ((machine.rule (addCode c.control) c.scanned).map _) = _
      rw [hz]
      change ((((TapeEmbedding.machine 1 CapMachine.machine).rule 0 c.scanned).map
        (mapAction addCode)).map (applyAction (controlConfig addCode c))) = _
      simp only [Option.map_map, Function.comp_def]
      rfl
    rw [he, hs]
    rfl

theorem reset_prefix {space steps : ℕ} {c d : Configuration 4 3}
    (h : Prefix (TapeEmbedding.machine 3 UnaryTemplate.machine) space steps c d) :
    Prefix machine space steps (controlConfig resetCode c) (controlConfig resetCode d) := by
  apply h.mapControl resetCode
  · intro c hn
    rcases c with ⟨state,heads,tapes⟩
    fin_cases state <;> simp_all [TapeEmbedding.machine, UnaryTemplate.machine, machine, resetCode]
  · intro c d hn hs
    have he : step machine (controlConfig resetCode c) =
        (step (TapeEmbedding.machine 3 UnaryTemplate.machine) c).map (controlConfig resetCode) := by
      rcases c with ⟨state,heads,tapes⟩
      fin_cases state <;> simp only [TapeEmbedding.machine, UnaryTemplate.machine] at hn
      all_goals first | contradiction | skip
      all_goals
        simp only [step, controlConfig, resetCode, machine, Configuration.scanned,
          Option.map_map, Function.comp_def]
        rfl
    rw [he, hs]
    rfl

theorem enter_step (cap operand total pos value : ℕ) (hp : pos < total) :
    step machine (boundary cap operand total pos value) =
      some (controlConfig addCode (TapeEmbedding.config (fun _ : Fin 1 => pos+2)
        (fun _ => CapMachine.counter cap total) (CapMachine.cfg 0 cap operand value 0))) := by
  simp [step, machine, boundary, Configuration.scanned, CapMachine.counter_read, hp]
  apply configuration_ext
  · rfl
  · funext i
    fin_cases i <;> simp [applyAction, jump, controlConfig, TapeEmbedding.config, CapMachine.cfg,
      HeadMove.apply, Fin.addCases]
  · funext i
    fin_cases i <;> simp [applyAction, jump, controlConfig, TapeEmbedding.config, CapMachine.cfg, Fin.addCases]

theorem stop_step (cap operand total value : ℕ) :
    step machine (boundary cap operand total total value) =
      some { boundary cap operand total total value with control := 4 } := by
  simp [step, machine, boundary, Configuration.scanned, CapMachine.counter_read]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, jump, HeadMove.apply]
  · rfl

theorem success_iteration (cap operand total pos value : ℕ)
    (ha : operand ≤ cap) (ht : total ≤ cap) (hp : pos < total) (hv : value+operand ≤ cap) :
    Prefix machine (4*(cap+2)) (2*operand+4)
      (boundary cap operand total pos value)
      (boundary cap operand total (pos+1) (value+operand)) := by
  obtain ⟨r,hr,hf,hs,hpeak⟩ := CapMachine.capped_add_run cap value operand (by omega) ha
  have hc : min operand (cap-value) = operand := Nat.min_eq_left (by omega)
  simp only [hc, if_pos hv, min_eq_right hv] at hr hf hs
  have hrun := TapeEmbedding.run_embed CapMachine.machine (fun _ : Fin 1 => pos+2)
    (fun _ => CapMachine.counter cap total) _ _ r hr
  have hbody := add_prefix (prefix_of_run _ _ _ _ hrun).1
  simp only [TapeEmbedding.receipt, TapeEmbedding.extraCells, Fin.sum_univ_one,
    CapMachine.counter_length _ _ ht, hs, hf] at hbody
  have hbody' := hbody.enlarge (large := 4*(cap+2)) (by omega)
  obtain ⟨rr,hrr,hfr,hsr,hpr⟩ := CapMachine.reset_run cap operand operand ha (Nat.le_refl _)
  let heads : Fin 3 → ℕ := ![value+operand+1,value+operand+1,pos+2]
  let tapes : Fin 3 → List Bool := ![CapMachine.counter cap (value+operand),
    CapMachine.counter cap cap, CapMachine.counter cap total]
  have hreset := TapeEmbedding.run_embed UnaryTemplate.machine heads tapes _ _ rr hrr
  have hreset' := reset_prefix (prefix_of_run _ _ _ _ hreset).1
  simp only [TapeEmbedding.receipt, hfr, hsr] at hreset'
  have hreset'' := hreset'.enlarge (large := 4*(cap+2)) (by
    simp [TapeEmbedding.extraCells, tapes, Fin.sum_univ_succ, CapMachine.counter_length _ _ hv,
      CapMachine.counter_length _ _ ht, CapMachine.counter_length cap cap (Nat.le_refl _)]
    omega)
  have hmid : controlConfig addCode (TapeEmbedding.config (fun _ : Fin 1 => pos+2)
      (fun _ => CapMachine.counter cap total) (CapMachine.cfg 1 cap operand (value+operand) operand)) =
      controlConfig resetCode (TapeEmbedding.config heads tapes
        (UnaryTemplate.config 0 (CapMachine.counter cap operand) (operand+1))) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [controlConfig, TapeEmbedding.config, CapMachine.cfg, UnaryTemplate.config,
        heads, Fin.addCases]
    · funext i; fin_cases i <;> simp [controlConfig, TapeEmbedding.config, CapMachine.cfg, UnaryTemplate.config,
        tapes, Fin.addCases]
  have hend : controlConfig resetCode (TapeEmbedding.config heads tapes
      (UnaryTemplate.config 2 (CapMachine.counter cap operand) 1)) =
      boundary cap operand total (pos+1) (value+operand) := by
    apply configuration_ext
    · rfl
    · funext i; fin_cases i <;> simp [controlConfig, TapeEmbedding.config, UnaryTemplate.config,
        heads, boundary, Fin.addCases]
    · funext i; fin_cases i <;> simp [controlConfig, TapeEmbedding.config, UnaryTemplate.config,
        tapes, boundary, Fin.addCases]
  rw [hmid] at hbody'
  rw [hend] at hreset''
  have hpref := Prefix.step (by rw [boundary_cells _ _ _ _ _ ha ht (by omega)]) (by rfl)
    (enter_step cap operand total pos value hp) (hbody'.trans hreset'')
  convert hpref using 1
  omega

end NearCubicWires.RepairSource.VerifierDecoding.ProductMachine
