import Proof.Gates.Interfaces.Transfer

set_option autoImplicit false

namespace NearCubicGates.Close.Transfer

open NearCubicWires NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairOrdinary
open NearCubicGates.Close.Gadget NearCubicGates.HeadlineAssembly NearCubicGates.Target

variable {s : GateSources} {P : ThreeQueryPCPP} {ε : ℝ}

namespace GateClosure
variable (c : GateClosure s P ε)

/-- The refuter's output at the source length selected for final length `n`. -/
noncomputable def input (n : ℕ) : BitInput (2 ^ c.g.selected s n) :=
  (s.hierarchy (fun n => n ^ (c.g.k + 2)) c.g.clock).output c.M (2 ^ c.g.selected s n)

/-- Case 2 at the selected source length (paper v2 §11.5: the first honest oracle of the first CHECK-passing source
circuit has a `q^G`-gate circuit). -/
def Small (n : ℕ) : Prop := c.g.IsCaseTwo s (c.g.selected s n) (c.input n)

noncomputable def nativeFn (n : ℕ) : BoolFunction (c.g.nativeLength s n) := c.g.native s P c.M n

end GateClosure

/-- Selection facts shared by the case parts: the selected source index tends to infinity, and at large `n` it is a
genuine index (`1 ≤ ν`, past the source onset) whose core arity is the native length (v2 lines 2499–2512). -/
def SelectionFacts (c : GateClosure s P ε) : Prop :=
  (∀ N0 : ℕ, ∃ n0 : ℕ, ∀ n, n0 ≤ n → N0 ≤ c.g.selected s n) ∧
    ∃ o : ℕ, ∀ n, o ≤ n → 1 ≤ c.g.selected s n ∧ c.g.sourceOnset ≤ 2 ^ c.g.selected s n ∧
      c.g.nativeLength s n = c.g.coreArity s (c.g.selected s n)

def SchedulePart (c : GateClosure s P ε) : Prop :=
  SelectionFacts c ∧ ∃ K : ℕ, 0 < K ∧ ∃ B : ℕ, 0 < B ∧ ∃ onset : ℕ,
    (∀ n, onset ≤ n → n ≤ B * c.g.nativeLength s n) ∧
    (∀ n, onset ≤ n → ∀ w : ℕ, MainBudget K (c.g.nativeLength s n) w →
      w ≤ c.budget (c.g.width s (c.g.selected s n)))

def CaseOnePart (c : GateClosure s P ε) : Prop :=
  SelectionFacts c → ∃ onset : ℕ, ∀ n, onset ≤ n → ¬ c.Small n →
    ∀ C : WeightedSymmetricCircuit (c.g.nativeLength s n),
      C.topWeight ≤ c.budget (c.g.width s (c.g.selected s n)) →
      NearCubicGates.FiniteAverages.agreement C.eval (c.nativeFn n) < 1 - (P.gamma : ℝ) / 5 + ε

def CaseTwoPart (c : GateClosure s P ε) : Prop :=
  SelectionFacts c → ∃ onset : ℕ, ∀ n, onset ≤ n → c.Small n →
    ∀ C : WeightedSymmetricCircuit (c.g.nativeLength s n),
      C.topWeight ≤ c.budget (c.g.width s (c.g.selected s n)) →
      NearCubicGates.FiniteAverages.agreement C.eval (c.nativeFn n) < 1 - (P.gamma : ℝ) / 5 + ε

def RecoveryPart (c : GateClosure s P ε) : Prop :=
  NearCubicGates.Target.InENP (padded (c.g.nativeLength s) (c.g.nativeLength_le s) c.nativeFn)

theorem frontier_of_parts (c : GateClosure s P ε) (hs : SchedulePart c) (h1 : CaseOnePart c)
    (h2 : CaseTwoPart c) (hr : RecoveryPart c) : Nonempty (NativeFrontier (P.gamma : ℝ) ε) := by
  classical
  obtain ⟨hsel, K, hK, B, hB, o0, hlen, hbud⟩ := hs
  obtain ⟨o1, hone⟩ := h1 hsel
  obtain ⟨o2, htwo⟩ := h2 hsel
  refine ⟨{ q := c.g.nativeLength s, q_le := c.g.nativeLength_le s, native := c.nativeFn,
            budgetConstant := K, budgetPositive := hK, dilation := B, dilationPositive := hB,
            onset := max o0 (max o1 o2),
            lengthBound := fun n hn => hlen n (le_trans (le_max_left _ _) hn),
            hard := ?_, ordinaryRecovery := hr }⟩
  intro n hn C hC
  have h0 : o0 ≤ n := le_trans (le_max_left _ _) hn
  have h1n : o1 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have h2n : o2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hw := hbud n h0 C.topWeight hC
  by_cases hsmall : c.Small n
  · exact htwo n h2n hsmall C hw
  · exact hone n h1n hsmall C hw

/-- The transfer side follows from the four parts at every closure. -/
theorem frontierOfClosure_of_parts
    (h : ∀ (s : GateSources) (P : ThreeQueryPCPP) (ε : ℝ), 0 < ε → ε < (P.gamma : ℝ) / 5 →
      ∀ c : GateClosure s P ε, SchedulePart c ∧ CaseOnePart c ∧ CaseTwoPart c ∧ RecoveryPart c) :
    FrontierOfClosure := by
  intro s P ε hε hεγ c
  obtain ⟨hs, h1, h2, hr⟩ := h s P ε hε hεγ c
  exact frontier_of_parts c hs h1 h2 hr

end NearCubicGates.Close.Transfer
