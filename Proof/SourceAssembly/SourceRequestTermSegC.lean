import Proof.SourceAssembly.SourceRequestTermSegB
import Proof.MachineModel.ClockNormalize

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.TermSegC
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceRequest.TermSeg

theorem resize_binary_eq (k W n : Nat) (hn : n < 2 ^ W) :
    ClockNormalize.resize k (SignedSortKey.binary W n) = SignedSortKey.binary k n := by
  induction k generalizing W n with
  | zero => rfl
  | succ k ih =>
    cases W with
    | zero =>
      have h0 : n = 0 := by simpa using hn
      subst h0
      have := ih 0 0 (by norm_num)
      simp only [SignedSortKey.binary] at this ⊢
      simp only [ClockNormalize.resize, this]
      rfl
    | succ W =>
      simp only [SignedSortKey.binary, ClockNormalize.resize]
      rw [ih W (n / 2) (by rw [pow_succ] at hn; omega)]

def pS (i : Fin 149) : Fin 155 := ⟨1 + i.val, by omega⟩
def c1S : Fin 3 → Fin 155 := ![0, 2, 150]
def nS : Fin 5 → Fin 155 := ![151, 79, 152, 153, 154]

theorem pS_inj : Function.Injective pS := by
  intro i j h; exact Fin.ext (by have := congrArg Fin.val h; simp only [pS] at this; omega)
theorem c1S_inj : Function.Injective c1S := by decide
theorem nS_inj : Function.Injective nS := by decide

/-- Entry: the term-code frame on `0`, `[false]` on `1`, the resident width `1^cwid` on `151`, blank elsewhere. -/
def entry (t : List Bool) (cwid : Nat) : Fin 155 → List Bool := fun x =>
  if x.val = 0 then frame t else if x.val = 1 then [false] else if x.val = 151 then List.replicate cwid true else []

noncomputable def machine :=
  Composition.machine
    (Composition.machine (RecoveryFocus.machine c1S copyMachine)
      (RecoveryFocus.machine pS CloseoutWitness.PairHeader.machine))
    (RecoveryFocus.machine nS ClockNormalize.machine)

def cost (n cwid : Nat) : Nat := ((2 * (2 * n + 1) + 2) + 1 + 28000 * (n + 1) ^ 2) + 1 + (4 * cwid + 4)

theorem circuit_run (t : List Bool) (cwid : Nat) : ∃ X : Fin 155 → List Bool,
    Step machine (cost t.length cwid) (fun _ => 0) (entry t cwid) (fun _ => 0) X ∧
    X 0 = frame t ∧ X 151 = List.replicate cwid true ∧
    X 152 = frame (ClockNormalize.resize cwid (CloseoutWitness.PairHeader.codeWord t 1)) ∧
    X 39 = frame (CloseoutWitness.PairHeader.codeWord t 0) := by
  obtain ⟨l1, s1⟩ := copy_run t
  have d1 := dock s1 c1S c1S_inj (fun _ => 0) (entry t cwid) (fun _ => rfl) (by intro i; fin_cases i <;> rfl)
  have gh := stepOfReady (CloseoutWitness.PairHeader.header_run t).1
  have hA2 : ∀ i, install c1S (entry t cwid) (copyOut t l1) (pS i) = CloseoutWitness.PairHeader.input t i := by
    intro i
    rw [TermSegB.pairInput_eq]
    by_cases h1 : i.val = 1
    · have e : pS i = c1S 1 := Fin.ext (by simp [pS, c1S]; omega)
      rw [e, install_slot _ c1S_inj, if_neg (by omega), if_pos h1]
      rfl
    · rw [install_other _ _ _ _ (by
        intro j h; have := congrArg Fin.val h; fin_cases j <;> simp [c1S, pS] at this <;> omega)]
      unfold entry
      simp only [pS]
      by_cases h0 : i.val = 0
      · rw [if_neg (by omega), if_pos (by omega), if_pos h0]; rfl
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg h0, if_neg h1]
  have d2 := dock gh pS pS_inj (fun _ => 0) _ (fun _ => rfl) hA2
  obtain ⟨r, hr, h0, h1, h2, _, _, hh, hs⟩ := ClockNormalize.normalize_run cwid (CloseoutWitness.PairHeader.codeWord t 1)
  have nm : Step ClockNormalize.machine (4 * cwid + 4) (fun _ => 0)
      (ClockNormalize.input cwid (CloseoutWitness.PairHeader.codeWord t 1)) (fun _ => 0) r.final.tapes :=
    Step.of_run hr (funext hh) rfl
  have h78 : CloseoutWitness.PairHeader.output t 78 = frame (CloseoutWitness.PairHeader.codeWord t 1) :=
    (CloseoutWitness.PairHeader.header_run t).2.2.2
  have h38 : CloseoutWitness.PairHeader.output t 38 = frame (CloseoutWitness.PairHeader.codeWord t 0) :=
    (CloseoutWitness.PairHeader.header_run t).2.2.1
  have hA3 : ∀ i, install pS (install c1S (entry t cwid) (copyOut t l1)) (CloseoutWitness.PairHeader.output t) (nS i) =
      ClockNormalize.input cwid (CloseoutWitness.PairHeader.codeWord t 1) i := by
    intro i
    fin_cases i
    · rw [install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; simp [pS, nS] at this; omega),
        install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; fin_cases j <;> simp [c1S, nS] at this)]
      rfl
    · show install pS _ _ (pS 78) = _
      rw [install_slot _ pS_inj, h78]; rfl
    all_goals
      rw [install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; simp [pS, nS] at this; omega),
        install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; fin_cases j <;> simp [c1S, nS] at this)]
      rfl
  have d3 := dock nm nS nS_inj (fun _ => 0) _ (fun _ => rfl) hA3
  have hlen : (CloseoutWitness.PairHeader.codeWord t 1).length = t.length := by
    simp [CloseoutWitness.PairHeader.codeWord, RecoveryFixedUnpair.leftWord, CompetitorWitnessTriple.word_length]
  refine ⟨_, ((d1.seq d2).seq d3).enlarge ?_, ?_, ?_, ?_, ?_⟩
  · unfold cost CloseoutWitness.PairHeader.budget; omega
  · rw [install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; fin_cases j <;> simp [nS] at this),
      install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; simp [pS] at this)]
    show install c1S _ _ (c1S 0) = _
    rw [install_slot _ c1S_inj]
    rfl
  · show install nS _ _ (nS 0) = _
    rw [install_slot _ nS_inj, h0]
  · show install nS _ _ (nS 2) = _
    rw [install_slot _ nS_inj, h2]
  · rw [install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; fin_cases j <;> simp [nS] at this)]
    show install pS _ _ (pS 38) = _
    rw [install_slot _ pS_inj, h38]

end NearCubicWires.SourceRequest.TermSegC

