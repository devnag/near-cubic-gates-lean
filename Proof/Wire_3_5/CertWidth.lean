import Proof.Wire_3_5.CertSchedule
import Proof.MachineModel.UWalkArithmetic
import Proof.MachineModel.ClockUnarySum
import Proof.CaseAnalysis.ScheduleClog
import Proof.Hierarchy.HierarchyBinaryPower

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

theorem install_at {t u : ℕ} (slot : Fin t → Fin u) (hi : Function.Injective slot) (amb out : Fin u → List Bool)
    (j : Fin t) (k : Fin u) (hk : slot j = k) : install slot amb (fun j => out (slot j)) k = out k := by
  rw [← hk, install_slot _ hi]

theorem install_off' {t u : ℕ} (slot : Fin t → Fin u) (amb : Fin u → List Bool) (out : Fin t → List Bool) (k : Fin u)
    (hk : ∀ j, slot j ≠ k) : install slot amb out k = amb k := install_other _ _ _ _ hk

theorem ready_of_root {t s : ℕ} {p : Machine t s} {n : ℕ} {input output : Fin t → List Bool}
    (h : RecoveryRootRound.ReadyRun p n input output) : ClockJoin.ReadyRun p n input output := by
  obtain ⟨r, hr, ht, hh, hs⟩ := h
  exact ⟨r, hr, ht, hh, hs.le⟩

section Width
variable (k A : ℕ)

/-- The fixed word `0 1^{k+2}` (the multiplier of `a`). -/
def wordK : List Bool := false :: List.replicate (k + 2) true
/-- The fixed word `1^2`. -/
def wordTwo : List Bool := [true, true]
/-- The fixed word `0 1^{A}` (the multiplier `A_pad`). -/
def wordA : List Bool := false :: List.replicate A true

def slotsF1 : Fin 2 → Fin 28 := ![1, 2]
def slotsP1 : Fin 4 → Fin 28 := ![0, 1, 3, 4]
def slotsF2 : Fin 2 → Fin 28 := ![5, 6]
def slotsS1 : Fin 4 → Fin 28 := ![3, 5, 7, 8]
def slotsC : Fin 12 → Fin 28 := ![7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19]
def slotsU : Fin 3 → Fin 28 := ![18, 20, 21]
def slotsF3 : Fin 2 → Fin 28 := ![22, 23]
def slotsP2 : Fin 4 → Fin 28 := ![20, 22, 24, 25]
def slotsS2 : Fin 4 → Fin 28 := ![3, 24, 26, 27]

/-- **The width machine**: nine focused steps computing `1^{q(2^a)}` on tape 26 from `1^a` on tape 0. -/
noncomputable def widthMachine :=
  Composition.machine (RecoveryFocus.machine slotsF1 (HierarchyFixedWord.machine (wordK k)))
  (Composition.machine (RecoveryFocus.machine slotsP1 ClockUnaryProduct.machine)
  (Composition.machine (RecoveryFocus.machine slotsF2 (HierarchyFixedWord.machine wordTwo))
  (Composition.machine (RecoveryFocus.machine slotsS1 ClockUnarySum.machine)
  (Composition.machine (RecoveryFocus.machine slotsC RepairSource.CloseoutSchedule.Clog.machine)
  (Composition.machine (RecoveryFocus.machine slotsU (UWalkUnary.machine false true))
  (Composition.machine (RecoveryFocus.machine slotsF3 (HierarchyFixedWord.machine (wordA A)))
  (Composition.machine (RecoveryFocus.machine slotsP2 ClockUnaryProduct.machine)
    (RecoveryFocus.machine slotsS2 ClockUnarySum.machine))))))))

/-- The input: `1^a` on tape 0. -/
def widthInput (a : ℕ) : Fin 28 → List Bool := fun i => if i.val = 0 then List.replicate a true else []

/-- The width's intermediate quantities. -/
def xOf (a : ℕ) : ℕ := a * (k + 2)
def yOf (a : ℕ) : ℕ := Nat.clog 2 (xOf k a + 2)

theorem widthAt_split (a : ℕ) : widthAt k A a = xOf k a + (yOf k a + 1) * A := by
  simp only [widthAt, xOf, yOf]; ring

/-- **The width machine is ready**: from `1^a` it halts at restored heads with `1^{q(2^a)}` on tape 26. -/
theorem widthMachine_ready (a : ℕ) : ∃ (cost : ℕ) (out : Fin 28 → List Bool),
    ClockJoin.ReadyRun (widthMachine k A) cost (widthInput a) out ∧ out 0 = List.replicate a true ∧
      out 26 = List.replicate (widthAt k A a) true := by
  -- step 1: the fixed word `0 1^{k+2}` on tapes 1, 2
  have h1 := (UWalkNumbers.fixed_ready (wordK k)).focus slotsF1 (by decide) (widthInput a) (by
    intro j; fin_cases j <;> rfl)
  set a1 := install slotsF1 (widthInput a) ![wordK k, List.replicate (wordK k).length false] with ha1
  -- step 2: the product `a·(k+2)` on tapes 0, 1, 3, 4
  have h2 := (UWalkNumbers.product_ready a (k + 2)).focus slotsP1 (by decide) a1 (by
    intro j; fin_cases j
    · show a1 0 = _; rw [ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a1 1 = _; rw [ha1, show (1 : Fin 28) = slotsF1 0 from rfl, install_slot _ (by decide)]; rfl
    · show a1 3 = _; rw [ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a1 4 = _; rw [ha1, install_other _ _ _ _ (by decide)]; rfl)
  set a2 := install slotsP1 a1 (UWalkNumbers.productOutput a (k + 2)) with ha2
  -- step 3: the fixed word `1^2` on tapes 5, 6
  have h3 := (UWalkNumbers.fixed_ready wordTwo).focus slotsF2 (by decide) a2 (by
    intro j; fin_cases j
    · show a2 5 = _; rw [ha2, install_other _ _ _ _ (by decide), ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a2 6 = _; rw [ha2, install_other _ _ _ _ (by decide), ha1, install_other _ _ _ _ (by decide)]; rfl)
  set a3 := install slotsF2 a2 ![wordTwo, List.replicate wordTwo.length false] with ha3
  -- step 4: the sum `x + 2` on tapes 3, 5, 7, 8
  have h4 := (ClockUnarySum.sum_ready (xOf k a) 2).focus slotsS1 (by decide) a3 (by
    intro j; fin_cases j
    · show a3 3 = _
      rw [ha3, install_other _ _ _ _ (by decide), ha2, show (3 : Fin 28) = slotsP1 2 from rfl,
        install_slot _ (by decide)]
      rfl
    · show a3 5 = _; rw [ha3, show (5 : Fin 28) = slotsF2 0 from rfl, install_slot _ (by decide)]; rfl
    · show a3 7 = _
      rw [ha3, install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), ha1,
        install_other _ _ _ _ (by decide)]; rfl
    · show a3 8 = _
      rw [ha3, install_other _ _ _ _ (by decide), ha2, install_other _ _ _ _ (by decide), ha1,
        install_other _ _ _ _ (by decide)]; rfl)
  set a4 := install slotsS1 a3 ![List.replicate (xOf k a) true, List.replicate 2 true,
    List.replicate (xOf k a + 2) true, List.replicate (xOf k a + 2 + 2) false] with ha4
  -- step 5: `⌈log₂(x+2)⌉` on the clog slots; its output word is on tape 18
  have hbelow : ∀ i : Fin 28, 9 ≤ i.val → i.val ≤ 25 → a4 i = [] := by
    intro i h9 h25
    have e0 : ∀ j, slotsS1 j ≠ i := by
      intro j; fin_cases j <;> (intro h; have := congrArg Fin.val h; simp [slotsS1] at this; omega)
    have e1 : ∀ j, slotsF2 j ≠ i := by
      intro j; fin_cases j <;> (intro h; have := congrArg Fin.val h; simp [slotsF2] at this; omega)
    have e2 : ∀ j, slotsP1 j ≠ i := by
      intro j; fin_cases j <;> (intro h; have := congrArg Fin.val h; simp [slotsP1] at this; omega)
    have e3 : ∀ j, slotsF1 j ≠ i := by
      intro j; fin_cases j <;> (intro h; have := congrArg Fin.val h; simp [slotsF1] at this; omega)
    rw [ha4, install_other _ _ _ _ e0, ha3, install_other _ _ _ _ e1, ha2, install_other _ _ _ _ e2, ha1,
      install_other _ _ _ _ e3]
    simp [widthInput]; omega
  obtain ⟨outC, hC, hC10⟩ := RepairSource.CloseoutSchedule.Clog.clog_run (xOf k a + 2) (by omega)
  have h5 := hC.focus slotsC (by decide) a4 (by
    intro j
    by_cases hj : j = 0
    · subst hj
      show a4 7 = _
      rw [ha4, show (7 : Fin 28) = slotsS1 2 from rfl, install_slot _ (by decide)]
      simp [RepairSource.CloseoutSchedule.Clog.input]
    · have hv : 9 ≤ (slotsC j).val ∧ (slotsC j).val ≤ 25 := by fin_cases j <;> simp_all [slotsC]
      rw [hbelow _ hv.1 hv.2]
      simp [RepairSource.CloseoutSchedule.Clog.input, hj])
  set a5 := install slotsC a4 outC with ha5
  -- step 6: `1^{y+1}` on tape 20 from the word `0 1^y` on tape 18
  have h6 := (UWalkUnary.ready false true 0 (yOf k a)).focus slotsU (by decide) a5 (by
    intro j; fin_cases j
    · show a5 18 = _
      rw [ha5, show (18 : Fin 28) = slotsC 10 from rfl, install_slot _ (by decide), hC10]
      simp [UWalkUnary.input, UWalkUnary.source, yOf]
    · show a5 20 = _; rw [ha5, install_other _ _ _ _ (by decide), hbelow _ (by decide) (by decide)]; rfl
    · show a5 21 = _; rw [ha5, install_other _ _ _ _ (by decide), hbelow _ (by decide) (by decide)]; rfl)
  set a6 := install slotsU a5 (UWalkUnary.result false true 0 (yOf k a)) with ha6
  -- step 7: the fixed word `0 1^A` on tapes 22, 23
  have h7 := (UWalkNumbers.fixed_ready (wordA A)).focus slotsF3 (by decide) a6 (by
    intro j; fin_cases j
    · show a6 22 = _
      rw [ha6, install_other _ _ _ _ (by decide), ha5, install_other _ _ _ _ (by decide),
        hbelow _ (by decide) (by decide)]
    · show a6 23 = _
      rw [ha6, install_other _ _ _ _ (by decide), ha5, install_other _ _ _ _ (by decide),
        hbelow _ (by decide) (by decide)])
  set a7 := install slotsF3 a6 ![wordA A, List.replicate (wordA A).length false] with ha7
  -- step 8: the product `(y+1)·A` on tapes 20, 22, 24, 25
  have h8 := (UWalkNumbers.product_ready (yOf k a + 1) A).focus slotsP2 (by decide) a7 (by
    intro j; fin_cases j
    · show a7 20 = _
      rw [ha7, install_other _ _ _ _ (by decide), ha6, show (20 : Fin 28) = slotsU 1 from rfl,
        install_slot _ (by decide)]
      simp [UWalkUnary.result, UWalkUnary.output, UWalkUnary.lead, UWalkNumbers.productInput]
    · show a7 22 = _; rw [ha7, show (22 : Fin 28) = slotsF3 0 from rfl, install_slot _ (by decide)]; rfl
    · show a7 24 = _
      rw [ha7, install_other _ _ _ _ (by decide), ha6, install_other _ _ _ _ (by decide), ha5,
        install_other _ _ _ _ (by decide), hbelow _ (by decide) (by decide)]; rfl
    · show a7 25 = _
      rw [ha7, install_other _ _ _ _ (by decide), ha6, install_other _ _ _ _ (by decide), ha5,
        install_other _ _ _ _ (by decide), hbelow _ (by decide) (by decide)]; rfl)
  set a8 := install slotsP2 a7 (UWalkNumbers.productOutput (yOf k a + 1) A) with ha8
  -- step 9: the sum `x + (y+1)·A` on tapes 3, 24, 26, 27
  have hx3 : a8 3 = List.replicate (xOf k a) true := by
    rw [ha8, install_other _ _ _ _ (by decide), ha7, install_other _ _ _ _ (by decide), ha6,
      install_other _ _ _ _ (by decide), ha5, install_other _ _ _ _ (by decide), ha4,
      show (3 : Fin 28) = slotsS1 0 from rfl, install_slot _ (by decide)]
    rfl
  have h26 : ∀ i : Fin 28, 26 ≤ i.val → a8 i = [] := by
    intro i h
    have e : ∀ {m : ℕ} (s : Fin m → Fin 28), (∀ j, (s j).val < 26) → ∀ j, s j ≠ i := by
      intro m s hs j hj; have := hs j; rw [hj] at this; omega
    rw [ha8, install_other _ _ _ _ (e _ (by decide)), ha7, install_other _ _ _ _ (e _ (by decide)), ha6,
      install_other _ _ _ _ (e _ (by decide)), ha5, install_other _ _ _ _ (e _ (by decide)), ha4,
      install_other _ _ _ _ (e _ (by decide)), ha3, install_other _ _ _ _ (e _ (by decide)), ha2,
      install_other _ _ _ _ (e _ (by decide)), ha1, install_other _ _ _ _ (e _ (by decide))]
    simp [widthInput]; omega
  have h9 := (ClockUnarySum.sum_ready (xOf k a) ((yOf k a + 1) * A)).focus slotsS2 (by decide) a8 (by
    intro j; fin_cases j
    · exact hx3
    · show a8 24 = _; rw [ha8, show (24 : Fin 28) = slotsP2 2 from rfl, install_slot _ (by decide)]; rfl
    · exact h26 26 (by decide)
    · exact h26 27 (by decide))
  refine ⟨_, _, ClockJoin.join _ _ _ _ _ _ _ h1 (ClockJoin.join _ _ _ _ _ _ _ h2 (ClockJoin.join _ _ _ _ _ _ _ h3
    (ClockJoin.join _ _ _ _ _ _ _ h4 (ClockJoin.join _ _ _ _ _ _ _ h5 (ClockJoin.join _ _ _ _ _ _ _ h6
    (ClockJoin.join _ _ _ _ _ _ _ h7 (ClockJoin.join _ _ _ _ _ _ _ h8 h9))))))), ?_, ?_⟩
  · rw [install_other _ _ _ _ (by decide), ha8, install_other _ _ _ _ (by decide), ha7,
      install_other _ _ _ _ (by decide), ha6, install_other _ _ _ _ (by decide), ha5,
      install_other _ _ _ _ (by decide), ha4, install_other _ _ _ _ (by decide), ha3,
      install_other _ _ _ _ (by decide), ha2, show (0 : Fin 28) = slotsP1 0 from rfl, install_slot _ (by decide)]
    rfl
  · rw [show (26 : Fin 28) = slotsS2 2 from rfl, install_slot _ (by decide), widthAt_split]
    rfl

end Width

/-! ## `L(q) = ⌈log₂(q+2)⌉` -/

section Lq

def slotsLF : Fin 2 → Fin 20 := ![1, 2]
def slotsLS : Fin 4 → Fin 20 := ![0, 1, 3, 4]
def slotsLC : Fin 12 → Fin 20 := ![3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
def slotsLU : Fin 3 → Fin 20 := ![14, 16, 17]

/-- **The `L` machine**: from `1^q` on tape 0, `1^{⌈log₂(q+2)⌉}` on tape 16. -/
noncomputable def lqMachine :=
  Composition.machine (RecoveryFocus.machine slotsLF (HierarchyFixedWord.machine wordTwo))
  (Composition.machine (RecoveryFocus.machine slotsLS ClockUnarySum.machine)
  (Composition.machine (RecoveryFocus.machine slotsLC RepairSource.CloseoutSchedule.Clog.machine)
    (RecoveryFocus.machine slotsLU (UWalkUnary.machine false false))))

def lqInput (q : ℕ) : Fin 20 → List Bool := fun i => if i.val = 0 then List.replicate q true else []

theorem lqMachine_ready (q : ℕ) : ∃ (cost : ℕ) (out : Fin 20 → List Bool),
    ClockJoin.ReadyRun lqMachine cost (lqInput q) out ∧ out 0 = List.replicate q true ∧
      out 16 = List.replicate (Ledger.Lq q) true := by
  have h1 := (UWalkNumbers.fixed_ready wordTwo).focus slotsLF (by decide) (lqInput q) (by
    intro j; fin_cases j <;> rfl)
  set a1 := install slotsLF (lqInput q) ![wordTwo, List.replicate wordTwo.length false] with ha1
  have h2 := (ClockUnarySum.sum_ready q 2).focus slotsLS (by decide) a1 (by
    intro j; fin_cases j
    · show a1 0 = _; rw [ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a1 1 = _; rw [ha1, show (1 : Fin 20) = slotsLF 0 from rfl, install_slot _ (by decide)]; rfl
    · show a1 3 = _; rw [ha1, install_other _ _ _ _ (by decide)]; rfl
    · show a1 4 = _; rw [ha1, install_other _ _ _ _ (by decide)]; rfl)
  set a2 := install slotsLS a1 ![List.replicate q true, List.replicate 2 true,
    List.replicate (q + 2) true, List.replicate (q + 2 + 2) false] with ha2
  have hbelow : ∀ i : Fin 20, 5 ≤ i.val → a2 i = [] := by
    intro i h5
    have e0 : ∀ j, slotsLS j ≠ i := by
      intro j; fin_cases j <;> (intro h; have := congrArg Fin.val h; simp [slotsLS] at this; omega)
    have e1 : ∀ j, slotsLF j ≠ i := by
      intro j; fin_cases j <;> (intro h; have := congrArg Fin.val h; simp [slotsLF] at this; omega)
    rw [ha2, install_other _ _ _ _ e0, ha1, install_other _ _ _ _ e1]
    simp [lqInput]; omega
  obtain ⟨outC, hC, hC10⟩ := RepairSource.CloseoutSchedule.Clog.clog_run (q + 2) (by omega)
  have h3 := hC.focus slotsLC (by decide) a2 (by
    intro j
    by_cases hj : j = 0
    · subst hj
      show a2 3 = _
      rw [ha2, show (3 : Fin 20) = slotsLS 2 from rfl, install_slot _ (by decide)]
      simp [RepairSource.CloseoutSchedule.Clog.input]
    · have hv : 5 ≤ (slotsLC j).val := by fin_cases j <;> simp_all [slotsLC]
      rw [hbelow _ hv]
      simp [RepairSource.CloseoutSchedule.Clog.input, hj])
  set a3 := install slotsLC a2 outC with ha3
  have h4 := (UWalkUnary.ready false false 0 (Nat.clog 2 (q + 2))).focus slotsLU (by decide) a3 (by
    intro j; fin_cases j
    · show a3 14 = _
      rw [ha3, show (14 : Fin 20) = slotsLC 10 from rfl, install_slot _ (by decide), hC10]
      simp [UWalkUnary.input, UWalkUnary.source]
    · show a3 16 = _; rw [ha3, install_other _ _ _ _ (by decide), hbelow _ (by decide)]; rfl
    · show a3 17 = _; rw [ha3, install_other _ _ _ _ (by decide), hbelow _ (by decide)]; rfl)
  refine ⟨_, _, ClockJoin.join _ _ _ _ _ _ _ h1 (ClockJoin.join _ _ _ _ _ _ _ h2
    (ClockJoin.join _ _ _ _ _ _ _ h3 h4)), ?_, ?_⟩
  · rw [install_other _ _ _ _ (by decide), ha3, install_other _ _ _ _ (by decide), ha2,
      show (0 : Fin 20) = slotsLS 0 from rfl, install_slot _ (by decide)]
    rfl
  · rw [show (16 : Fin 20) = slotsLU 1 from rfl, install_slot _ (by decide)]
    simp [UWalkUnary.result, UWalkUnary.output, UWalkUnary.lead, Ledger.Lq]

end Lq

end NearCubicWires.WireExponent3_5.Transfer
