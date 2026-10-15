import Proof.Wire_3_5.CertWidth
import Proof.Wire_3_5.FoldBody
import Proof.CaseAnalysis.ScheduleCompare
import Proof.Amplification.RecoveryTapeSupport
import Proof.CaseAnalysis.CapacityPower
import Proof.PCP.ProjectionDimensionTemplate

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

/-- **A ready run grows no tape beyond its cost.** -/
theorem ready_lengths {t s : ℕ} {p : Machine t s} {cost : ℕ} {input output : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p cost input output) (cap : ℕ) (hin : ∀ i, (input i).length ≤ cap) :
    ∀ i, (output i).length ≤ max cap (cost + 1) := by
  obtain ⟨r, hr, ht, _, hs⟩ := h
  have hsup := RecoveryTapeSupport.run_support p cost (initialConfiguration p input) r hr cap 0
    (fun _ => le_refl 0) (fun i => (hin i).trans (le_max_left _ _))
  intro i
  rw [← ht]
  exact (hsup i).trans (max_le_max le_rfl (by omega))

/-! ## The flag `[a > b]` -/

section Flag

def slotsFlagOne : Fin 2 → Fin 10 := ![2, 3]
def slotsFlagSum : Fin 4 → Fin 10 := ![1, 2, 4, 5]
def slotsFlagCmp : Fin 6 → Fin 10 := ![4, 0, 6, 7, 8, 9]

/-- **The flag machine**: `1^1`, then `b + 1` by the unary sum, then base's comparison of `b + 1` with `a`. -/
noncomputable def flagMachine :=
  Composition.machine (RecoveryFocus.machine slotsFlagOne (HierarchyFixedWord.machine [true]))
  (Composition.machine (RecoveryFocus.machine slotsFlagSum ClockUnarySum.machine)
    (RecoveryFocus.machine slotsFlagCmp RepairSource.CloseoutSchedule.RawCompare.machine))

/-- The input: `1^a` padded to `cA` on tape 0, `1^b` padded to `cB` on tape 1. -/
def flagInput (a b cA cB : ℕ) : Fin 10 → List Bool := fun i =>
  if i.val = 0 then ZeroPadding.pad cA (List.replicate a true)
  else if i.val = 1 then ZeroPadding.pad cB (List.replicate b true) else []

/-- The flag machine's cost. -/
def flagCost (a b : ℕ) : ℕ := 4 + 1 + ((2 * (b + 1) + 6) + 1 + RepairSource.CloseoutSchedule.RawCompare.budget (b + 1) a)

/-- **The flag machine is ready**: tapes 0, 1 are kept and tape 8 holds `[b + 1 ≤ a]`. -/
theorem flagMachine_ready (a b cA cB : ℕ) : ∃ out : Fin 10 → List Bool,
    ClockJoin.ReadyRun flagMachine (flagCost a b) (flagInput a b cA cB) out ∧
      out 0 = ZeroPadding.pad cA (List.replicate a true) ∧ out 1 = ZeroPadding.pad cB (List.replicate b true) ∧
      out 8 = [decide (b + 1 ≤ a)] := by
  have h1 := (UWalkNumbers.fixed_ready [true]).focus slotsFlagOne (by decide) (flagInput a b cA cB) (by
    intro j; fin_cases j <;> rfl)
  set a1 := install slotsFlagOne (flagInput a b cA cB) ![[true], List.replicate [true].length false] with ha1
  -- the sum `b + 1`, with `1^b` padded
  have hs := ready_pad _ _ _ _ ![cB, 0, 0, 0] (ClockUnarySum.sum_ready b 1)
  have h2 := hs.focus slotsFlagSum (by decide) a1 (by
    intro j; fin_cases j
    · show a1 1 = _; rw [ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a1 2 = _; rw [ha1, show (2 : Fin 10) = slotsFlagOne 0 from rfl, install_slot _ (by decide)]; rfl
    · show a1 4 = _; rw [ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a1 5 = _; rw [ha1, install_other _ _ _ _ (by decide)]; rfl)
  set a2 := install slotsFlagSum a1 (fun i => ZeroPadding.pad (![cB, 0, 0, 0] i)
    (![List.replicate b true, List.replicate 1 true, List.replicate (b + 1) true,
      List.replicate (b + 1 + 2) false] i)) with ha2
  -- the comparison of `b + 1` with `a`, with `1^a` padded
  have hc := ready_pad _ _ _ _ ![0, cA, 0, 0, 0, 0] (RepairSource.CloseoutSchedule.RawCompare.compare_run (b + 1) a)
  have h3 := hc.focus slotsFlagCmp (by decide) a2 (by
    intro j; fin_cases j
    · show a2 4 = _; rw [ha2, show (4 : Fin 10) = slotsFlagSum 2 from rfl, install_slot _ (by decide)]; rfl
    · show a2 0 = _
      rw [ha2, install_other _ _ _ _ (by decide), ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a2 6 = _
      rw [ha2, install_other _ _ _ _ (by decide), ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a2 7 = _
      rw [ha2, install_other _ _ _ _ (by decide), ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a2 8 = _
      rw [ha2, install_other _ _ _ _ (by decide), ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a2 9 = _
      rw [ha2, install_other _ _ _ _ (by decide), ha1, install_other _ _ _ _ (by decide)]; rfl)
  refine ⟨_, ClockJoin.join _ _ _ _ _ _ _ h1 (ClockJoin.join _ _ _ _ _ _ _ h2 h3), ?_, ?_, ?_⟩
  · rw [show (0 : Fin 10) = slotsFlagCmp 1 from rfl, install_slot _ (by decide)]; rfl
  · rw [install_other _ _ _ _ (by decide), ha2, show (1 : Fin 10) = slotsFlagSum 0 from rfl,
      install_slot _ (by decide)]; rfl
  · rw [show (8 : Fin 10) = slotsFlagCmp 4 from rfl, install_slot _ (by decide)]; rfl

end Flag

/-! ## The update: the counter, `a·p`, `b·w` -/

section Update

theorem pad_one_flag (f : Bool) : ZeroPadding.pad 1 (List.replicate f.toNat true) = [f] := by
  cases f <;> rfl

def slotsUpdSum : Fin 4 → Fin 12 := ![2, 5, 6, 7]
def slotsUpdPA : Fin 4 → Fin 12 := ![0, 3, 8, 9]
def slotsUpdPB : Fin 4 → Fin 12 := ![1, 4, 10, 11]

/-- **The update machine**: the counter plus the flag, `a·p` and `b·w` (on fresh tapes 6, 8, 10). -/
noncomputable def updateMachine :=
  Composition.machine (RecoveryFocus.machine slotsUpdSum ClockUnarySum.machine)
  (Composition.machine (RecoveryFocus.machine slotsUpdPA ClockUnaryProduct.machine)
    (RecoveryFocus.machine slotsUpdPB ClockUnaryProduct.machine))

/-- The input: the padded `1^a`, `1^b`, `1^e`, the words `0 1^p`, `0 1^w`, and the flag `[f]`. -/
def updateInput (a b e p w cA cB cE : ℕ) (f : Bool) : Fin 12 → List Bool :=
  ![ZeroPadding.pad cA (List.replicate a true), ZeroPadding.pad cB (List.replicate b true),
    ZeroPadding.pad cE (List.replicate e true), CompareMachine.word p, CompareMachine.word w, [f], [], [], [], [], [], []]

def updateCost (a b e p w : ℕ) (f : Bool) : ℕ :=
  (2 * (e + f.toNat) + 6) + 1 + (UWalkNumbers.productCost a p + 1 + UWalkNumbers.productCost b w)

/-- **The update machine is ready**: the ports are kept, tape 6 holds `1^{e + [f]}`, tape 8 `1^{a·p}`, tape 10
`1^{b·w}`. -/
theorem updateMachine_ready (a b e p w cA cB cE : ℕ) (f : Bool) : ∃ out : Fin 12 → List Bool,
    ClockJoin.ReadyRun updateMachine (updateCost a b e p w f) (updateInput a b e p w cA cB cE f) out ∧
      (∀ i : Fin 12, i.val < 6 → out i = updateInput a b e p w cA cB cE f i) ∧
      out 6 = List.replicate (e + f.toNat) true ∧ out 8 = List.replicate (a * p) true ∧
      out 10 = List.replicate (b * w) true := by
  set x := updateInput a b e p w cA cB cE f with hx
  have hs := ready_pad _ _ _ _ ![cE, 1, 0, 0] (ClockUnarySum.sum_ready e f.toNat)
  have h1 := hs.focus slotsUpdSum (by decide) x (by
    intro j; fin_cases j
    · rfl
    · show [f] = _; simp [pad_one_flag]
    · rfl
    · rfl)
  set a1 := install slotsUpdSum x (fun i => ZeroPadding.pad (![cE, 1, 0, 0] i)
    (![List.replicate e true, List.replicate f.toNat true, List.replicate (e + f.toNat) true,
      List.replicate (e + f.toNat + 2) false] i)) with ha1
  have hp := ready_pad _ _ _ _ ![cA, 0, 0, 0] (UWalkNumbers.product_ready a p)
  have h2 := hp.focus slotsUpdPA (by decide) a1 (by
    intro j; fin_cases j
    · show a1 0 = _; rw [ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a1 3 = _; rw [ha1, install_other _ _ _ _ (by decide)]; simp [hx, updateInput, UWalkNumbers.productInput, CompareMachine.word]
    · show a1 8 = _; rw [ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a1 9 = _; rw [ha1, install_other _ _ _ _ (by decide)]; rfl)
  set a2 := install slotsUpdPA a1 (fun i => ZeroPadding.pad (![cA, 0, 0, 0] i)
    (UWalkNumbers.productOutput a p i)) with ha2
  have hq := ready_pad _ _ _ _ ![cB, 0, 0, 0] (UWalkNumbers.product_ready b w)
  have h3 := hq.focus slotsUpdPB (by decide) a2 (by
    intro j; fin_cases j
    · show a2 1 = _; rw [ha2, install_other _ _ _ _ (by decide), ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a2 4 = _
      rw [ha2, install_other _ _ _ _ (by decide), ha1, install_other _ _ _ _ (by decide)]
      simp [hx, updateInput, UWalkNumbers.productInput, CompareMachine.word]
    · show a2 10 = _; rw [ha2, install_other _ _ _ _ (by decide), ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a2 11 = _; rw [ha2, install_other _ _ _ _ (by decide), ha1, install_other _ _ _ _ (by decide)]; rfl)
  refine ⟨_, ClockJoin.join _ _ _ _ _ _ _ h1 (ClockJoin.join _ _ _ _ _ _ _ h2 h3), ?_, ?_, ?_, ?_⟩
  · intro i hi
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by
      rcases i with ⟨v, hv⟩; interval_cases v <;> simp_all
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [install_other _ _ _ _ (by decide), ha2, show (0 : Fin 12) = slotsUpdPA 0 from rfl,
        install_slot _ (by decide)]; rfl
    · rw [show (1 : Fin 12) = slotsUpdPB 0 from rfl, install_slot _ (by decide)]; rfl
    · rw [install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), ha1,
        show (2 : Fin 12) = slotsUpdSum 0 from rfl, install_slot _ (by decide)]; rfl
    · rw [install_other _ _ _ _ (by decide), ha2, show (3 : Fin 12) = slotsUpdPA 1 from rfl,
        install_slot _ (by decide)]
      simp [hx, updateInput, UWalkNumbers.productOutput, CompareMachine.word, slotsUpdPA]
    · rw [show (4 : Fin 12) = slotsUpdPB 1 from rfl, install_slot _ (by decide)]
      simp [hx, updateInput, UWalkNumbers.productOutput, CompareMachine.word, slotsUpdPB]
    · rw [install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), ha1,
        show (5 : Fin 12) = slotsUpdSum 1 from rfl, install_slot _ (by decide)]
      simp [hx, updateInput, pad_one_flag, slotsUpdSum]
  · rw [install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), ha1,
      show (6 : Fin 12) = slotsUpdSum 2 from rfl, install_slot _ (by decide)]; simp
  · rw [install_other _ _ _ _ (by decide), ha2, show (8 : Fin 12) = slotsUpdPA 2 from rfl,
      install_slot _ (by decide)]; simp [UWalkNumbers.productOutput]
  · rw [show (10 : Fin 12) = slotsUpdPB 2 from rfl, install_slot _ (by decide)]; simp [UWalkNumbers.productOutput]

end Update

/-! ## The write-back: erase the three ports and copy the new values onto them -/

section WriteBack

def slotsWE : Fin 5 → Fin 17 := ![0, 1, 2, 3, 4]
def slotsWTA : Fin 3 → Fin 17 := ![5, 8, 9]
def slotsWCA : Fin 3 → Fin 17 := ![8, 0, 10]
def slotsWTB : Fin 3 → Fin 17 := ![6, 11, 12]
def slotsWCB : Fin 3 → Fin 17 := ![11, 1, 13]
def slotsWTE : Fin 3 → Fin 17 := ![7, 14, 15]
def slotsWCE : Fin 3 → Fin 17 := ![14, 2, 16]

/-- **The write-back machine**: erase tapes 0–2, then copy `1^{a'}`, `1^{b'}`, `1^{e'}` (tapes 5–7) onto them. -/
noncomputable def writeBackMachine :=
  Composition.machine (RecoveryFocus.machine slotsWE (RecoveryScratchErase.resetMachine 3))
  (Composition.machine (RecoveryFocus.machine slotsWTA (RepairSource.ProjectionNormalization.DimensionTemplate.machine false))
  (Composition.machine (RecoveryFocus.machine slotsWCA (UWalkUnary.machine false false))
  (Composition.machine (RecoveryFocus.machine slotsWTB (RepairSource.ProjectionNormalization.DimensionTemplate.machine false))
  (Composition.machine (RecoveryFocus.machine slotsWCB (UWalkUnary.machine false false))
  (Composition.machine (RecoveryFocus.machine slotsWTE (RepairSource.ProjectionNormalization.DimensionTemplate.machine false))
    (RecoveryFocus.machine slotsWCE (UWalkUnary.machine false false)))))))

def writeBackInput (A B E : List Bool) (total capT a' b' e' : ℕ) : Fin 17 → List Bool :=
  ![A, B, E, List.replicate total true, List.replicate capT false, List.replicate a' true, List.replicate b' true,
    List.replicate e' true, [], [], [], [], [], [], [], [], []]

def writeBackCost (total a' b' e' : ℕ) : ℕ :=
  (2 * total + 4) + 1 + ((2 * a' + 8) + 1 + ((2 * a' + 6) + 1 + ((2 * b' + 8) + 1 + ((2 * b' + 6) + 1 +
    ((2 * e' + 8) + 1 + (2 * e' + 6))))))

/-- **The write-back is ready**: tapes 0–2 end as `1^{a'}`, `1^{b'}`, `1^{e'}` padded to `total`, the driver and a
capacity tape of length `≥ total + 1` are kept. -/
theorem writeBackMachine_ready (A B E : List Bool) (total capT a' b' e' : ℕ) (hcap : total + 1 ≤ capT)
    (hA : A.length ≤ total) (hB : B.length ≤ total) (hE : E.length ≤ total) :
    ∃ out : Fin 17 → List Bool,
      ClockJoin.ReadyRun writeBackMachine (writeBackCost total a' b' e') (writeBackInput A B E total capT a' b' e') out ∧
      out 0 = ZeroPadding.pad total (List.replicate a' true) ∧ out 1 = ZeroPadding.pad total (List.replicate b' true) ∧
      out 2 = ZeroPadding.pad total (List.replicate e' true) ∧ out 3 = List.replicate total true ∧
      out 4 = List.replicate capT false := by
  set x := writeBackInput A B E total capT a' b' e' with hx
  have hmax : max capT (total + 1) = capT := max_eq_left hcap
  have he := ready_of_root (RecoveryScratchErase.erase_ready total capT ![A, B, E] (by
    intro i; fin_cases i <;> simpa))
  rw [hmax] at he
  have h1 := he.focus slotsWE (by decide) x (by
    intro j; fin_cases j <;> rfl)
  set a1 := install slotsWE x (Fin.addCases (motive := fun _ => List Bool)
    (Fin.addCases (motive := fun _ => List Bool) (fun _ : Fin 3 => List.replicate total false)
    (fun _ : Fin 1 => List.replicate total true)) (fun _ : Fin 1 => List.replicate capT false)) with ha1
  have hlow : ∀ i : Fin 17, 5 ≤ i.val → a1 i = x i := by
    intro i hi
    rw [ha1, install_other _ _ _ _ (by
      intro j; fin_cases j <;> (intro h; have := congrArg Fin.val h; simp [slotsWE] at this; omega))]
  -- `a'`
  have h2 := (RepairSource.ProjectionNormalization.DimensionTemplate.ready false a').focus slotsWTA (by decide) a1 (by
    intro j; fin_cases j
    · show a1 5 = _; rw [hlow _ (by decide)]; rfl
    · show a1 8 = _; rw [hlow _ (by decide)]; rfl
    · show a1 9 = _; rw [hlow _ (by decide)]; rfl)
  set a2 := install slotsWTA a1 (RepairSource.ProjectionNormalization.DimensionTemplate.output false a') with ha2
  have hc := ready_pad _ _ _ _ ![0, total, 0] (UWalkUnary.ready false false (a' + 2) a')
  have h3 := hc.focus slotsWCA (by decide) a2 (by
    intro j; fin_cases j
    · show a2 8 = _
      rw [ha2, show (8 : Fin 17) = slotsWTA 1 from rfl, install_slot _ (by decide)]
      simp [RepairSource.ProjectionNormalization.DimensionTemplate.output, UWalkUnary.input,
        RepairSource.CloseoutCapacity.Power.template_source]
    · show a2 0 = _
      rw [ha2, install_other _ _ _ _ (by decide), ha1, show (0 : Fin 17) = slotsWE 0 from rfl,
        install_slot _ (by decide)]
      rfl
    · show a2 10 = _; rw [ha2, install_other _ _ _ _ (by decide), hlow _ (by decide)]; rfl)
  set a3 := install slotsWCA a2 (fun i => ZeroPadding.pad (![0, total, 0] i) (UWalkUnary.result false false (a' + 2) a' i))
    with ha3
  -- `b'`
  have h4 := (RepairSource.ProjectionNormalization.DimensionTemplate.ready false b').focus slotsWTB (by decide) a3 (by
    intro j; fin_cases j
    · show a3 6 = _
      rw [ha3, install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), hlow _ (by decide)]; rfl
    · show a3 11 = _
      rw [ha3, install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), hlow _ (by decide)]; rfl
    · show a3 12 = _
      rw [ha3, install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), hlow _ (by decide)]; rfl)
  set a4 := install slotsWTB a3 (RepairSource.ProjectionNormalization.DimensionTemplate.output false b') with ha4
  have hc' := ready_pad _ _ _ _ ![0, total, 0] (UWalkUnary.ready false false (b' + 2) b')
  have h5 := hc'.focus slotsWCB (by decide) a4 (by
    intro j; fin_cases j
    · show a4 11 = _
      rw [ha4, show (11 : Fin 17) = slotsWTB 1 from rfl, install_slot _ (by decide)]
      simp [RepairSource.ProjectionNormalization.DimensionTemplate.output, UWalkUnary.input,
        RepairSource.CloseoutCapacity.Power.template_source]
    · show a4 1 = _
      rw [ha4, install_other _ _ _ _ (by decide), ha3, install_other _ _ _ _ (by decide), ha2,
        install_other _ _ _ _ (by decide), ha1, show (1 : Fin 17) = slotsWE 1 from rfl, install_slot _ (by decide)]
      rfl
    · show a4 13 = _
      rw [ha4, install_other _ _ _ _ (by decide), ha3, install_other _ _ _ _ (by decide), ha2,
        install_other _ _ _ _ (by decide), hlow _ (by decide)]; rfl)
  set a5 := install slotsWCB a4 (fun i => ZeroPadding.pad (![0, total, 0] i) (UWalkUnary.result false false (b' + 2) b' i))
    with ha5
  -- `e'`
  have h6 := (RepairSource.ProjectionNormalization.DimensionTemplate.ready false e').focus slotsWTE (by decide) a5 (by
    intro j; fin_cases j
    · show a5 7 = _
      rw [ha5, install_other _ _ _ _ (by decide), ha4, install_other _ _ _ _ (by decide), ha3,
        install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), hlow _ (by decide)]; rfl
    · show a5 14 = _
      rw [ha5, install_other _ _ _ _ (by decide), ha4, install_other _ _ _ _ (by decide), ha3,
        install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), hlow _ (by decide)]; rfl
    · show a5 15 = _
      rw [ha5, install_other _ _ _ _ (by decide), ha4, install_other _ _ _ _ (by decide), ha3,
        install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), hlow _ (by decide)]; rfl)
  set a6 := install slotsWTE a5 (RepairSource.ProjectionNormalization.DimensionTemplate.output false e') with ha6
  have hc'' := ready_pad _ _ _ _ ![0, total, 0] (UWalkUnary.ready false false (e' + 2) e')
  have h7 := hc''.focus slotsWCE (by decide) a6 (by
    intro j; fin_cases j
    · show a6 14 = _
      rw [ha6, show (14 : Fin 17) = slotsWTE 1 from rfl, install_slot _ (by decide)]
      simp [RepairSource.ProjectionNormalization.DimensionTemplate.output, UWalkUnary.input,
        RepairSource.CloseoutCapacity.Power.template_source]
    · show a6 2 = _
      rw [ha6, install_other _ _ _ _ (by decide), ha5, install_other _ _ _ _ (by decide), ha4,
        install_other _ _ _ _ (by decide), ha3, install_other _ _ _ _ (by decide), ha2,
        install_other _ _ _ _ (by decide), ha1, show (2 : Fin 17) = slotsWE 2 from rfl, install_slot _ (by decide)]
      rfl
    · show a6 16 = _
      rw [ha6, install_other _ _ _ _ (by decide), ha5, install_other _ _ _ _ (by decide), ha4,
        install_other _ _ _ _ (by decide), ha3, install_other _ _ _ _ (by decide), ha2,
        install_other _ _ _ _ (by decide), hlow _ (by decide)]; rfl)
  refine ⟨_, ClockJoin.join _ _ _ _ _ _ _ h1 (ClockJoin.join _ _ _ _ _ _ _ h2 (ClockJoin.join _ _ _ _ _ _ _ h3
    (ClockJoin.join _ _ _ _ _ _ _ h4 (ClockJoin.join _ _ _ _ _ _ _ h5 (ClockJoin.join _ _ _ _ _ _ _ h6 h7))))),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [install_other _ _ _ _ (by decide), ha6, install_other _ _ _ _ (by decide), ha5,
      install_other _ _ _ _ (by decide), ha4, install_other _ _ _ _ (by decide), ha3,
      show (0 : Fin 17) = slotsWCA 1 from rfl, install_slot _ (by decide)]
    simp [UWalkUnary.result, UWalkUnary.output, UWalkUnary.lead]
  · rw [install_other _ _ _ _ (by decide), ha6, install_other _ _ _ _ (by decide), ha5,
      show (1 : Fin 17) = slotsWCB 1 from rfl, install_slot _ (by decide)]
    simp [UWalkUnary.result, UWalkUnary.output, UWalkUnary.lead]
  · rw [show (2 : Fin 17) = slotsWCE 1 from rfl, install_slot _ (by decide)]
    simp [UWalkUnary.result, UWalkUnary.output, UWalkUnary.lead]
  · rw [install_other _ _ _ _ (by decide), ha6, install_other _ _ _ _ (by decide), ha5,
      install_other _ _ _ _ (by decide), ha4, install_other _ _ _ _ (by decide), ha3,
      install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), ha1,
      show (3 : Fin 17) = slotsWE 3 from rfl, install_slot _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by decide), ha6, install_other _ _ _ _ (by decide), ha5,
      install_other _ _ _ _ (by decide), ha4, install_other _ _ _ _ (by decide), ha3,
      install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), ha1,
      show (4 : Fin 17) = slotsWE 4 from rfl, install_slot _ (by decide)]
    rfl

end WriteBack

/-! ## One round: flag, update, write-back -/

section Round

def slotsRF : Fin 10 → Fin 30 := ![0, 1, 7, 8, 9, 10, 11, 12, 13, 14]
def slotsRU : Fin 12 → Fin 30 := ![0, 1, 2, 3, 4, 13, 15, 16, 17, 18, 19, 20]
def slotsRW : Fin 17 → Fin 30 := ![0, 1, 2, 5, 6, 17, 19, 15, 21, 22, 23, 24, 25, 26, 27, 28, 29]

/-- **One round of the schedule loop**. -/
noncomputable def roundMachine :=
  Composition.machine (RecoveryFocus.machine slotsRF flagMachine)
  (Composition.machine (RecoveryFocus.machine slotsRU updateMachine) (RecoveryFocus.machine slotsRW writeBackMachine))

/-- The round's tapes: the ports `1^a`, `1^b`, `1^e` (padded to `total`), the words `0 1^p`, `0 1^w`, the erase driver
and capacity tape; the 23 scratch tapes are empty. -/
def roundInput (a b e p w total capT : ℕ) : Fin 30 → List Bool := fun i =>
  if i.val = 0 then ZeroPadding.pad total (List.replicate a true)
  else if i.val = 1 then ZeroPadding.pad total (List.replicate b true)
  else if i.val = 2 then ZeroPadding.pad total (List.replicate e true)
  else if i.val = 3 then CompareMachine.word p
  else if i.val = 4 then CompareMachine.word w
  else if i.val = 5 then List.replicate total true
  else if i.val = 6 then List.replicate capT false else []

def roundCost (a b e p w total : ℕ) : ℕ :=
  flagCost a b + 1 + (updateCost a b e p w (decide (b + 1 ≤ a)) + 1 +
    writeBackCost total (a * p) (b * w) (e + (decide (b + 1 ≤ a)).toNat))

theorem pad_length_total (total n : ℕ) (hn : n ≤ total) :
    (ZeroPadding.pad total (List.replicate n true)).length = total := by
  simp [ZeroPadding.pad]; omega

/-- **One round is ready**: the ports become `1^{a·p}`, `1^{b·w}`, `1^{e + [a > b]}` (padded to `total`); the words,
the driver and the capacity tape are kept. -/
theorem roundMachine_ready (a b e p w total capT : ℕ) (hcap : total + 1 ≤ capT) (ha : a ≤ total) (hb : b ≤ total)
    (he : e ≤ total) :
    ∃ out : Fin 30 → List Bool, ClockJoin.ReadyRun roundMachine (roundCost a b e p w total)
      (roundInput a b e p w total capT) out ∧
      ∀ i : Fin 30, i.val < 7 →
        out i = roundInput (a * p) (b * w) (e + (decide (b + 1 ≤ a)).toNat) p w total capT i := by
  set x := roundInput a b e p w total capT with hx
  set f := decide (b + 1 ≤ a) with hf
  have hscr : ∀ i : Fin 30, 7 ≤ i.val → x i = [] := by
    intro i hi; simp only [hx, roundInput]; split_ifs <;> first | rfl | omega
  -- the flag
  obtain ⟨o1, h1, o10, o11, o18⟩ := flagMachine_ready a b total total
  have g1 := h1.focus slotsRF (by decide) x (by
    intro j; fin_cases j <;> simp [flagInput, hx, roundInput, slotsRF])
  set a1 := install slotsRF x o1 with ha1
  -- the update
  obtain ⟨o2, h2, o2p, o26, o28, o210⟩ := updateMachine_ready a b e p w total total total f
  have g2 := h2.focus slotsRU (by decide) a1 (by
    intro j; fin_cases j
    · show a1 0 = _; rw [ha1, show (0 : Fin 30) = slotsRF 0 from rfl, install_slot _ (by decide), o10]; rfl
    · show a1 1 = _; rw [ha1, show (1 : Fin 30) = slotsRF 1 from rfl, install_slot _ (by decide), o11]; rfl
    · show a1 2 = _; rw [ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a1 3 = _; rw [ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a1 4 = _; rw [ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a1 13 = _; rw [ha1, show (13 : Fin 30) = slotsRF 8 from rfl, install_slot _ (by decide), o18]; rfl
    all_goals (show a1 _ = _; rw [ha1, install_other _ _ _ _ (by decide), hscr _ (by decide)]; rfl))
  set a2 := install slotsRU a1 o2 with ha2
  have a20 : a2 0 = ZeroPadding.pad total (List.replicate a true) := by
    rw [ha2, show (0 : Fin 30) = slotsRU 0 from rfl, install_slot _ (by decide), o2p 0 (by decide)]; rfl
  have a21 : a2 1 = ZeroPadding.pad total (List.replicate b true) := by
    rw [ha2, show (1 : Fin 30) = slotsRU 1 from rfl, install_slot _ (by decide), o2p 1 (by decide)]; rfl
  have a22 : a2 2 = ZeroPadding.pad total (List.replicate e true) := by
    rw [ha2, show (2 : Fin 30) = slotsRU 2 from rfl, install_slot _ (by decide), o2p 2 (by decide)]; rfl
  -- the write-back
  obtain ⟨o3, h3, o30, o31, o32, o33, o34⟩ := writeBackMachine_ready (a2 0) (a2 1) (a2 2) total capT (a * p) (b * w)
    (e + f.toNat) hcap (by rw [a20, pad_length_total _ _ ha]) (by rw [a21, pad_length_total _ _ hb])
    (by rw [a22, pad_length_total _ _ he])
  have g3 := h3.focus slotsRW (by decide) a2 (by
    intro j; fin_cases j
    · rfl
    · rfl
    · rfl
    · show a2 5 = _
      rw [ha2, install_other _ _ _ _ (by decide), ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a2 6 = _
      rw [ha2, install_other _ _ _ _ (by decide), ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a2 17 = _; rw [ha2, show (17 : Fin 30) = slotsRU 8 from rfl, install_slot _ (by decide), o28]; rfl
    · show a2 19 = _; rw [ha2, show (19 : Fin 30) = slotsRU 10 from rfl, install_slot _ (by decide), o210]; rfl
    · show a2 15 = _; rw [ha2, show (15 : Fin 30) = slotsRU 6 from rfl, install_slot _ (by decide), o26]; rfl
    all_goals (show a2 _ = _; rw [ha2, install_other _ _ _ _ (by decide), ha1, install_other _ _ _ _ (by decide),
      hscr _ (by decide)]; rfl))
  refine ⟨_, ClockJoin.join _ _ _ _ _ _ _ g1 (ClockJoin.join _ _ _ _ _ _ _ g2 g3), ?_⟩
  intro i hi
  have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by
    rcases i with ⟨v, hv⟩; interval_cases v <;> simp_all
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show (0 : Fin 30) = slotsRW 0 from rfl, install_slot _ (by decide), o30]; rfl
  · rw [show (1 : Fin 30) = slotsRW 1 from rfl, install_slot _ (by decide), o31]; rfl
  · rw [show (2 : Fin 30) = slotsRW 2 from rfl, install_slot _ (by decide), o32]; rfl
  · rw [install_other _ _ _ _ (by decide), ha2, show (3 : Fin 30) = slotsRU 3 from rfl, install_slot _ (by decide),
      o2p 3 (by decide)]; rfl
  · rw [install_other _ _ _ _ (by decide), ha2, show (4 : Fin 30) = slotsRU 4 from rfl, install_slot _ (by decide),
      o2p 4 (by decide)]; rfl
  · rw [show (5 : Fin 30) = slotsRW 3 from rfl, install_slot _ (by decide), o33]; rfl
  · rw [show (6 : Fin 30) = slotsRW 4 from rfl, install_slot _ (by decide), o34]; rfl

end Round

/-! ## The loop -/

section Loop

/-- A machine that halts at once. -/
def idleMachine (t : ℕ) : Machine t 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none

theorem idle_ready (t : ℕ) (X : Fin t → List Bool) : ClockJoin.ReadyRun (idleMachine t) 0 X X :=
  ⟨⟨initialConfiguration (idleMachine t) X, 0, (initialConfiguration (idleMachine t) X).tapeCells⟩,
    runFrom_zero_of_halted _ _ rfl, rfl, fun _ => rfl, le_refl 0⟩

/-- The round's scratch slots `7, …, 29`. -/
def roundScratch : Fin 23 → Fin 30 := fun j => ⟨j.val + 7, by omega⟩

theorem roundScratch_injective : Function.Injective roundScratch := by
  intro a b h; have := congrArg Fin.val h; simp [roundScratch] at this; exact Fin.ext this

/-- **The schedule loop**: `c` rounds on one reused bank. -/
noncomputable def schedLoop := foldLoop (foldBody roundMachine roundScratch (idleMachine (30 + 2)))

/-- The counter after `i` rounds: `e₀` plus the number of rounds `j < i` with `b₀w^j < a₀p^j`. -/
def roundCount (a0 b0 e0 p w : ℕ) : ℕ → ℕ
  | 0 => e0
  | i + 1 => roundCount a0 b0 e0 p w i + (decide (b0 * w ^ i + 1 ≤ a0 * p ^ i)).toNat

/-- The ports before round `i`. -/
def roundState (a0 b0 e0 p w total capT i : ℕ) : Fin 30 → List Bool :=
  roundInput (a0 * p ^ i) (b0 * w ^ i) (roundCount a0 b0 e0 p w i) p w total capT

theorem roundCount_le (a0 b0 e0 p w i : ℕ) : roundCount a0 b0 e0 p w i ≤ e0 + i := by
  induction i with
  | zero => simp [roundCount]
  | succ i ih => simp only [roundCount]; have := Bool.toNat_le (decide (b0 * w ^ i + 1 ≤ a0 * p ^ i)); omega

/-- The round's cost at the largest values. -/
def roundCostBound (p w total : ℕ) : ℕ :=
  flagCost total total + 1 + (updateCost total total total p w true + 1 +
    writeBackCost total (total * p) (total * w) (total + 1))

theorem roundCost_le (a b e p w total : ℕ) (ha : a ≤ total) (hb : b ≤ total) (he : e ≤ total) :
    roundCost a b e p w total ≤ roundCostBound p w total := by
  unfold roundCostBound roundCost flagCost updateCost writeBackCost UWalkNumbers.productCost
    RepairSource.CloseoutSchedule.RawCompare.budget
  have h1 : a * p ≤ total * p := Nat.mul_le_mul_right _ ha
  have h2 : b * w ≤ total * w := Nat.mul_le_mul_right _ hb
  have h3 : a * (2 * p + 3) ≤ total * (2 * p + 3) := Nat.mul_le_mul_right _ ha
  have h4 : b * (2 * w + 3) ≤ total * (2 * w + 3) := Nat.mul_le_mul_right _ hb
  have h5 := Bool.toNat_le (decide (b + 1 ≤ a))
  have h7 : min (b + 1) a ≤ min (total + 1) total := min_le_min (by omega) ha
  simp only [Bool.toNat_true]
  omega

end Loop

section Loop2

theorem roundState_length (a0 b0 e0 p w total capT i : ℕ) (ha : a0 * p ^ i ≤ total) (hb : b0 * w ^ i ≤ total)
    (he : roundCount a0 b0 e0 p w i ≤ total) (hcap : total ≤ capT) (k : Fin 30) :
    (roundState a0 b0 e0 p w total capT i k).length ≤ max capT (max (p + 1) (w + 1)) := by
  unfold roundState roundInput
  split_ifs <;> simp [ZeroPadding.pad, CompareMachine.word] <;> omega

/-- **The schedule loop is ready**: after `c` rounds from `(a₀, b₀, e₀)` the ports hold `a₀p^c`, `b₀w^c` and the
counter `roundCount … c`, given the values stay within `total`. -/
theorem schedLoop_ready (a0 b0 e0 p w total capT T capF c : ℕ) (hcap : total + 1 ≤ capT)
    (hbound : ∀ i, i ≤ c → a0 * p ^ i ≤ total ∧ b0 * w ^ i ≤ total ∧ e0 + i ≤ total)
    (hT : max capT (max (p + 1) (w + 1)) ≤ T) (hTc : roundCostBound p w total + 1 ≤ T) (hcapF : T + 1 ≤ capF) :
    ClockJoin.ReadyRun schedLoop
      (1 + 1 + (c * (roundCostBound p w total + 1 + (2 * T + 4 + 1 + 0) + 2) + c + 3 + 1 + 1))
      (Fin.addCases (roundTapes (padScratch roundScratch T (roundState a0 b0 e0 p w total capT 0)) T capF)
        (fun _ => CompareMachine.word c))
      (Fin.addCases (roundTapes (padScratch roundScratch T (roundState a0 b0 e0 p w total capT c)) T capF)
        (fun _ => CompareMachine.word c)) := by
  have hr : ∀ i, i < c → ∃ out : Fin 30 → List Bool,
      ClockJoin.ReadyRun roundMachine (roundCost (a0 * p ^ i) (b0 * w ^ i) (roundCount a0 b0 e0 p w i) p w total)
        (roundState a0 b0 e0 p w total capT i) out ∧
      ∀ k : Fin 30, k.val < 7 → out k = roundState a0 b0 e0 p w total capT (i + 1) k := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hbound i hi.le
    obtain ⟨out, hout, hports⟩ := roundMachine_ready (a0 * p ^ i) (b0 * w ^ i) (roundCount a0 b0 e0 p w i) p w total
      capT hcap h1 h2 ((roundCount_le a0 b0 e0 p w i).trans h3)
    refine ⟨out, hout, fun k hk => ?_⟩
    rw [hports k hk]
    unfold roundState
    simp only [roundCount]
    rw [show a0 * p ^ i * p = a0 * p ^ (i + 1) by ring, show b0 * w ^ i * w = b0 * w ^ (i + 1) by ring]
  classical
  let Q' : ℕ → Fin 30 → List Bool := fun i => if h : i < c then Classical.choose (hr i h)
    else roundState a0 b0 e0 p w total capT i
  have hQ' : ∀ i (h : i < c), Q' i = Classical.choose (hr i h) := fun i h => by simp only [Q', dif_pos h]
  apply uniformFold_ready roundMachine roundScratch roundScratch_injective (idleMachine (30 + 2)) T capF
    (roundCostBound p w total) 0 c hcapF (fun i => roundState a0 b0 e0 p w total capT i) Q'
  · intro i hi
    rw [hQ' i hi]
    obtain ⟨h1, h2, h3⟩ := hbound i hi.le
    exact ClockJoin.enlarge _ _ _ _ _ (Classical.choose_spec (hr i hi)).1
      (roundCost_le _ _ _ p w total h1 h2 ((roundCount_le a0 b0 e0 p w i).trans h3))
  · intro i hi j
    rw [hQ' i hi]
    obtain ⟨h1, h2, h3⟩ := hbound i hi.le
    have hl := ready_lengths (Classical.choose_spec (hr i hi)).1 _
      (roundState_length a0 b0 e0 p w total capT i h1 h2 ((roundCount_le a0 b0 e0 p w i).trans h3) (by omega))
    have hc := roundCost_le _ _ _ p w total h1 h2 ((roundCount_le a0 b0 e0 p w i).trans h3)
    exact (hl _).trans (max_le hT (by omega))
  · intro i hi
    have he : padScratch roundScratch T (blankScratch roundScratch (Q' i)) =
        padScratch roundScratch T (roundState a0 b0 e0 p w total capT (i + 1)) := by
      funext k
      unfold padScratch blankScratch
      by_cases hk : ∃ j, roundScratch j = k
      · rw [if_pos hk]
        obtain ⟨j, rfl⟩ := hk
        congr 1
      · rw [if_neg hk, hQ' i hi]
        congr 1
        have hk7 : k.val < 7 := by
          by_contra h
          exact hk ⟨⟨k.val - 7, by omega⟩, Fin.ext (by simp [roundScratch]; omega)⟩
        exact (Classical.choose_spec (hr i hi)).2 k hk7
    rw [he]
    exact idle_ready _ _

end Loop2

/-! ## The loop computes the schedule -/

section Correct
open NearCubicWires.WireExponent3_5.Schedule

/-- The numerator and denominator of `ζ`. -/
def zu (ζ : ℚ) : ℕ := ζ.num.toNat
def zv (ζ : ℚ) : ℕ := ζ.den

variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

include h0 in
theorem zeta_eq : ζ = (zu ζ : ℚ) / zv ζ := by
  have hn : 0 ≤ ζ.num := Rat.num_nonneg.mpr h0.le
  have e : ((ζ.num.toNat : ℕ) : ℚ) = (ζ.num : ℚ) := by rw [← Int.cast_natCast, Int.toNat_of_nonneg hn]
  unfold zu zv
  rw [e]
  exact (Rat.num_div_den ζ).symm

include h0 h1 in
theorem two_u_lt_v : 2 * zu ζ < zv ζ := by
  have hv : (0 : ℚ) < zv ζ := by unfold zv; exact_mod_cast ζ.den_pos
  have h := h1
  rw [zeta_eq h0, div_lt_iff₀ hv] at h
  have : (2 * zu ζ : ℚ) < zv ζ := by linarith
  exact_mod_cast this

/-- `a_j = ((v−u)^j (v−2u))^{16} L³` and `b_j = (v^j·2v)^{16}`. -/
def schedA (ζ : ℚ) (L j : ℕ) : ℕ := (zv ζ - 2 * zu ζ) ^ 16 * L ^ 3 * ((zv ζ - zu ζ) ^ 16) ^ j
def schedB (ζ : ℚ) (j : ℕ) : ℕ := (2 * zv ζ) ^ 16 * (zv ζ ^ 16) ^ j

include h0 h1 in
/-- **Round `j+1` is good iff `a_j ≤ b_j`.** -/
theorem good_iff (L j : ℕ) : Good ζ L (j + 1) ↔ schedA ζ L j ≤ schedB ζ j := by
  have hlt := two_u_lt_v h0 h1
  have hz := zeta_eq h0
  have hvpos : 0 < zv ζ := ζ.den_pos
  unfold Good schedA schedB
  generalize zu ζ = u at hlt hz ⊢
  generalize zv ζ = v at hlt hz hvpos ⊢
  have hv0 : (v : ℚ) ≠ 0 := by exact_mod_cast hvpos.ne'
  have e1 : 1 - ζ = ((v - u : ℕ) : ℚ) / v := by
    rw [hz, Nat.cast_sub (by omega)]; field_simp
  have e2 : 1 / 2 - ζ = ((v - 2 * u : ℕ) : ℚ) / (2 * v) := by
    rw [hz, Nat.cast_sub (by omega)]; push_cast; field_simp
  have hB : (0 : ℚ) < (((2 * v) ^ 16 * (v ^ 16) ^ j : ℕ) : ℚ) := by
    have : 0 < (2 * v) ^ 16 * (v ^ 16) ^ j := by positivity
    exact_mod_cast this
  have key : eps ζ (j + 1) ^ 16 * (L : ℚ) ^ 3 =
      (((v - 2 * u) ^ 16 * L ^ 3 * ((v - u) ^ 16) ^ j : ℕ) : ℚ) / (((2 * v) ^ 16 * (v ^ 16) ^ j : ℕ) : ℚ) := by
    unfold eps
    rw [Nat.add_sub_cancel, e1, e2, div_pow, div_mul_div_comm, div_pow, div_mul_eq_mul_div]
    congr 1
    · push_cast; ring
    · push_cast; ring
  rw [key, div_le_one hB]
  constructor
  · rintro ⟨-, h⟩; exact_mod_cast h
  · intro h; exact ⟨by omega, by exact_mod_cast h⟩

include h0 h1 in
theorem good_mono (L t t' : ℕ) (ht : Good ζ L t) (htt : t ≤ t') : Good ζ L t' := by
  obtain ⟨ht1, hle⟩ := ht
  refine ⟨by omega, le_trans ?_ hle⟩
  have hb : (0 : ℚ) ≤ 1 - ζ := by linarith
  have hb1 : 1 - ζ ≤ 1 := by linarith
  have he : eps ζ t' ≤ eps ζ t := by
    unfold eps
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact pow_le_pow_of_le_one hb hb1 (by omega)
  have he0 : 0 ≤ eps ζ t' := eps_nonneg h0 h1 t'
  have hL : (0 : ℚ) ≤ (L : ℚ) ^ 3 := by positivity
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ he0 he 16) hL

include h0 h1 in
/-- **The loop's counter is the schedule**: after `c ≥ t − 1` rounds from `(a₀, b₀, 1)` it is `t = sched(L)`. -/
theorem roundCount_sched (L c : ℕ) (hc : sched ζ h0 h1 L ≤ c + 1) :
    roundCount (schedA ζ L 0) (schedB ζ 0) 1 ((zv ζ - zu ζ) ^ 16) (zv ζ ^ 16) c = sched ζ h0 h1 L := by
  have hs1 : 1 ≤ sched ζ h0 h1 L := (sched_spec h0 h1 L).1
  -- the flag of round `j` is `j + 1 < sched`
  have hflag : ∀ j, decide (schedB ζ 0 * (zv ζ ^ 16) ^ j + 1 ≤ schedA ζ L 0 * ((zv ζ - zu ζ) ^ 16) ^ j) =
      decide (j + 1 < sched ζ h0 h1 L) := by
    intro j
    have ea : schedA ζ L 0 * ((zv ζ - zu ζ) ^ 16) ^ j = schedA ζ L j := by unfold schedA; ring
    have eb : schedB ζ 0 * (zv ζ ^ 16) ^ j = schedB ζ j := by unfold schedB; ring
    rw [ea, eb]
    apply decide_eq_decide.mpr
    constructor
    · intro h
      by_contra hge
      have hg := good_mono h0 h1 L _ (j + 1) (sched_spec h0 h1 L) (by omega)
      have := (good_iff h0 h1 L j).1 hg
      omega
    · intro h
      have hng : ¬ Good ζ L (j + 1) := Nat.find_min (exists_good h0 h1 L) h
      rw [good_iff h0 h1 L j] at hng
      omega
  have key : ∀ c', roundCount (schedA ζ L 0) (schedB ζ 0) 1 ((zv ζ - zu ζ) ^ 16) (zv ζ ^ 16) c' =
      1 + min c' (sched ζ h0 h1 L - 1) := by
    intro c'
    induction c' with
    | zero => simp [roundCount]
    | succ c' ih =>
      simp only [roundCount, hflag, ih]
      by_cases h : c' + 1 < sched ζ h0 h1 L
      · simp [h]; omega
      · simp [h]; omega
  rw [key]
  omega

end Correct

end NearCubicWires.WireExponent3_5.Transfer
