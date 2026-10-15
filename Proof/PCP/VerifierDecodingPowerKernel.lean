import Proof.PCP.VerifierDecodingCopy

/-! Finite controller for the cap-c dimension power. Two synchronized unary
copies permit a guarded doubling, with every copy and rewind paid. -/
namespace NearCubicWires.RepairSource.VerifierDecoding.PowerMachine
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def swap : Fin 4 ≃ Fin 4 where
  toFun := ![1,0,2,3]
  invFun := ![1,0,2,3]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def add : Machine 4 3 := TapeEmbedding.machine 1 CapMachine.machine
def resetA : Machine 4 3 := TapeEmbedding.machine 3 UnaryTemplate.machine
def resetB : Machine 4 3 := TapeRenaming.machine swap resetA
def copy : Machine 4 2 := TapeRenaming.machine swap (TapeEmbedding.machine 2 CopyMachine.machine)
def addCode : Fin 3 → Fin 11 := ![1,2,10]
def firstResetCode : Fin 3 → Fin 11 := ![2,3,4]
def secondResetCode : Fin 3 → Fin 11 := ![4,5,6]
def copyCode : Fin 2 → Fin 11 := ![6,7]
def finalResetCode : Fin 3 → Fin 11 := ![7,8,0]
def mapAction {s : ℕ} (f : Fin s → Fin 11) (a : Action 4 s) : Action 4 11 :=
  ⟨f a.nextControl,a.write,a.move⟩
def driverAction (next : Fin 11) (advance : Bool) : Action 4 11 :=
  ⟨next,fun _ => none,fun i => if i.val = 3 ∧ advance then .right else .stay⟩
def machine : Machine 4 11 where
  descriptionBits := 0
  start := 0
  halted := fun state => 9 ≤ state.val
  rule := fun state scanned =>
    ![some (driverAction (if scanned 3 then 1 else 9) (scanned 3)),
      (add.rule 0 scanned).map (mapAction addCode),
      (resetA.rule 0 scanned).map (mapAction firstResetCode),
      (resetA.rule 1 scanned).map (mapAction firstResetCode),
      (resetB.rule 0 scanned).map (mapAction secondResetCode),
      (resetB.rule 1 scanned).map (mapAction secondResetCode),
      (copy.rule 0 scanned).map (mapAction copyCode),
      (resetA.rule 0 scanned).map (mapAction finalResetCode),
      (resetA.rule 1 scanned).map (mapAction finalResetCode),none,none] state

def boundary (cap total pos value : ℕ) : Configuration 4 11 :=
  ⟨0,![1,value+1,value+1,pos+1],
    ![CapMachine.counter cap value,CapMachine.counter cap value,
      CapMachine.counter cap cap,CapMachine.counter cap total]⟩

theorem boundary_cells (cap total pos value : ℕ) (ht : total ≤ cap) (hv : value ≤ cap) :
    (boundary cap total pos value).tapeCells = 4*(cap+2) := by
  simp [boundary, Configuration.tapeCells, Fin.sum_univ_succ,
    CapMachine.counter_length _ _ ht, CapMachine.counter_length _ _ hv,
    CapMachine.counter_length cap cap (Nat.le_refl _)]
  omega

private theorem transport {s space steps : ℕ} (p : Machine 4 s) (f : Fin s → Fin 11)
    (hh : ∀ state, p.halted state = false → machine.halted (f state) = false)
    (hm : ∀ state bits, p.halted state = false →
      machine.rule (f state) bits = (p.rule state bits).map (mapAction f))
    {c d : Configuration 4 s} (h : Prefix p space steps c d) :
    Prefix machine space steps (controlConfig f c) (controlConfig f d) := by
  apply h.mapControl f
  · intro c hn; exact hh c.control hn
  · intro c d hn hs
    have he : step machine (controlConfig f c) = (step p c).map (controlConfig f) := by
      unfold step
      change ((machine.rule (f c.control) c.scanned).map _) = _
      rw [hm c.control c.scanned hn]
      simp only [Option.map_map, Function.comp_def]
      rfl
    rw [he,hs]
    rfl

theorem add_prefix {space steps : ℕ} {c d : Configuration 4 3} (h : Prefix add space steps c d) :
    Prefix machine space steps (controlConfig addCode c) (controlConfig addCode d) := by
  apply transport add addCode ?_ ?_ h
  · intro state hn; fin_cases state <;> first | rfl | cases hn
  · intro state bits hn; fin_cases state <;> first | rfl | cases hn

theorem first_reset_prefix {space steps : ℕ} {c d : Configuration 4 3}
    (h : Prefix resetA space steps c d) :
    Prefix machine space steps (controlConfig firstResetCode c) (controlConfig firstResetCode d) := by
  apply transport resetA firstResetCode ?_ ?_ h
  · intro state _; fin_cases state <;> rfl
  · intro state bits hn; fin_cases state <;> first | rfl | cases hn

theorem second_reset_prefix {space steps : ℕ} {c d : Configuration 4 3}
    (h : Prefix resetB space steps c d) :
    Prefix machine space steps (controlConfig secondResetCode c) (controlConfig secondResetCode d) := by
  apply transport resetB secondResetCode ?_ ?_ h
  · intro state _; fin_cases state <;> rfl
  · intro state bits hn; fin_cases state <;> first | rfl | cases hn

theorem copy_prefix {space steps : ℕ} {c d : Configuration 4 2}
    (h : Prefix copy space steps c d) :
    Prefix machine space steps (controlConfig copyCode c) (controlConfig copyCode d) := by
  apply transport copy copyCode ?_ ?_ h
  · intro state _; fin_cases state <;> rfl
  · intro state bits hn; fin_cases state <;> first | rfl | cases hn

theorem final_reset_prefix {space steps : ℕ} {c d : Configuration 4 3}
    (h : Prefix resetA space steps c d) :
    Prefix machine space steps (controlConfig finalResetCode c) (controlConfig finalResetCode d) := by
  apply transport resetA finalResetCode ?_ ?_ h
  · intro state _; fin_cases state <;> rfl
  · intro state bits hn; fin_cases state <;> first | rfl | cases hn

theorem enter_step (cap total pos value : ℕ) (hp : pos < total) :
    step machine (boundary cap total pos value) =
      some (controlConfig addCode (TapeEmbedding.config (fun _ : Fin 1 => pos+2)
        (fun _ => CapMachine.counter cap total) (CapMachine.cfg 0 cap value value 0))) := by
  simp [step, machine, boundary, Configuration.scanned, CapMachine.counter_read, hp]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, driverAction, controlConfig, TapeEmbedding.config,
      CapMachine.cfg, HeadMove.apply, Fin.addCases]
  · funext i; fin_cases i <;> simp [applyAction, driverAction, controlConfig, TapeEmbedding.config,
      CapMachine.cfg, Fin.addCases]

theorem stop_step (cap total value : ℕ) :
    step machine (boundary cap total total value) =
      some { boundary cap total total value with control := 9 } := by
  simp [step, machine, boundary, Configuration.scanned, CapMachine.counter_read]
  apply configuration_ext
  · rfl
  · funext i; fin_cases i <;> simp [applyAction, driverAction, HeadMove.apply]
  · rfl

end NearCubicWires.RepairSource.VerifierDecoding.PowerMachine
