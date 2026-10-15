import Proof.SourceAssembly.SourceRequestTermSegA
import Proof.CaseAnalysis.WitnessPairHeader

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.TermSegB
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceRequest.TermSeg

theorem pairInput_eq (c : List Bool) (i : Fin 149) : CloseoutWitness.PairHeader.input c i =
    if i.val = 0 then frame [] else if i.val = 1 then frame c else [] := by
  by_cases h : i.val < 148
  · have e : i = Fin.castAdd 1 (⟨i.val, h⟩ : Fin 148) := Fin.ext rfl
    rw [e, CloseoutWitness.PairHeader.input, Fin.addCases_left, CompetitorWitnessHeader.input_eq]
    rfl
  · have e : i = Fin.natAdd 148 (0 : Fin 1) := Fin.ext (by simp; omega)
    rw [e, CloseoutWitness.PairHeader.input, Fin.addCases_right]
    simp

/-! ## Segment B core: layout on `Fin 189` -/

/-- `0` sum code; `1 + i` the pair parser (149); `150` log; `151 + i` the rewound traversal (37); `188` log. -/
def pS (i : Fin 149) : Fin 189 := ⟨1 + i.val, by omega⟩
def tS (i : Fin 37) : Fin 189 := ⟨151 + i.val, by omega⟩
def c1S : Fin 3 → Fin 189 := ![0, 2, 150]
def c2S : Fin 3 → Fin 189 := ![79, 151, 188]

theorem pS_inj : Function.Injective pS := by
  intro i j h; exact Fin.ext (by have := congrArg Fin.val h; simp only [pS] at this; omega)
theorem tS_inj : Function.Injective tS := by
  intro i j h; exact Fin.ext (by have := congrArg Fin.val h; simp only [tS] at this; omega)
theorem c1S_inj : Function.Injective c1S := by decide
theorem c2S_inj : Function.Injective c2S := by decide

/-- Entry: the sum-code frame on `0`, the parser's (empty) first field `frame [] = [false]` on `1`, blank elsewhere. -/
def entry (bits : List Bool) : Fin 189 → List Bool := fun x =>
  if x.val = 0 then frame bits else if x.val = 1 then [false] else []

noncomputable def machine :=
  Composition.machine
    (Composition.machine
      (Composition.machine (RecoveryFocus.machine c1S copyMachine)
        (RecoveryFocus.machine pS CloseoutWitness.PairHeader.machine))
      (RecoveryFocus.machine c2S copyMachine))
    (RecoveryFocus.machine tS (Rewind.machine CloseoutWitness.TraversalCold.machine))

def cost (n : Nat) : Nat :=
  (((2 * (2 * n + 1) + 2) + 1 + 28000 * (n + 1) ^ 2) + 1 + (2 * (2 * n + 1) + 2)) + 1 +
    (2 * (1048576 * (n + 1) ^ 3) + 2)

/-- The terms-list field of a sum code. -/
noncomputable def termsCode (c : List Bool) : List Bool := CloseoutWitness.PairHeader.codeWord c 1

theorem termsCode_length (c : List Bool) : (termsCode c).length = c.length := by
  simp [termsCode, CloseoutWitness.PairHeader.codeWord, RecoveryFixedUnpair.leftWord,
    CompetitorWitnessTriple.word_length]

/-- The term codes of a sum code, in order. -/
noncomputable def terms (c : List Bool) : List Nat :=
  (PCPPNativeCanonicalTree.tree (RadixSemantics.value (termsCode c))).atoms

theorem core_run (bits : List Bool) : ∃ X : Fin 189 → List Bool,
    Step machine (cost bits.length) (fun _ => 0) (entry bits) (fun _ => 0) X ∧
    X 0 = frame bits ∧
    X (tS 27) = PCPPNativeCanonicalWalk.atomStream bits.length (terms bits) ∧
    X (tS 28) = List.replicate (terms bits).length true := by
  obtain ⟨l1, s1⟩ := copy_run bits
  have d1 := dock s1 c1S c1S_inj (fun _ => 0) (entry bits) (fun _ => rfl) (by intro i; fin_cases i <;> rfl)
  have gh := stepOfReady (CloseoutWitness.PairHeader.header_run bits).1
  have hA2 : ∀ i, install c1S (entry bits) (copyOut bits l1) (pS i) = CloseoutWitness.PairHeader.input bits i := by
    intro i
    rw [pairInput_eq]
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
      · rw [if_neg (by omega), if_neg (by omega), if_neg h0, if_neg h1]
  have d2 := dock gh pS pS_inj (fun _ => 0) _ (fun _ => rfl) hA2
  obtain ⟨l2, s3⟩ := copy_run (termsCode bits)
  have h78 : CloseoutWitness.PairHeader.output bits 78 = frame (termsCode bits) :=
    (CloseoutWitness.PairHeader.header_run bits).2.2.2
  have hA3 : ∀ i, install pS (install c1S (entry bits) (copyOut bits l1))
      (CloseoutWitness.PairHeader.output bits) (c2S i) = copyIn (termsCode bits) i := by
    intro i
    fin_cases i
    · show install pS _ _ (pS 78) = _
      rw [install_slot _ pS_inj, h78]; rfl
    · rw [install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; simp [pS, c2S] at this; omega),
        install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; fin_cases j <;> simp [c1S, c2S] at this)]
      rfl
    · rw [install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; simp [pS, c2S] at this; omega),
        install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; fin_cases j <;> simp [c1S, c2S] at this)]
      rfl
  have d3 := dock s3 c2S c2S_inj (fun _ => 0) _ (fun _ => rfl) hA3
  obtain ⟨r, hr, hs, h27, h28, _⟩ := CloseoutWitness.TraversalCold.cold_run (termsCode bits)
  have st : Step CloseoutWitness.TraversalCold.machine
      (CloseoutWitness.TraversalCold.budget (termsCode bits)) (fun _ => 0)
      (CloseoutWitness.TraversalCold.input (termsCode bits)) r.final.heads r.final.tapes :=
    ⟨r, hr, rfl, rfl, hs⟩
  obtain ⟨l4, s4⟩ := rewound st
  have hA4 : ∀ i, install c2S (install pS (install c1S (entry bits) (copyOut bits l1))
      (CloseoutWitness.PairHeader.output bits)) (copyOut (termsCode bits) l2) (tS i) =
      Fin.addCases (m := 36) (n := 1) (motive := fun _ => List Bool)
        (CloseoutWitness.TraversalCold.input (termsCode bits)) (fun _ => []) i := by
    intro i
    by_cases h0 : i.val = 0
    · have e : tS i = c2S 1 := Fin.ext (by simp [tS, c2S]; omega)
      have ei : i = Fin.castAdd 1 (0 : Fin 36) := Fin.ext (by simp; omega)
      rw [e, install_slot _ c2S_inj, ei, Fin.addCases_left]
      rfl
    · rw [install_other _ _ _ _ (by
          intro j h; have := congrArg Fin.val h; fin_cases j <;> simp [tS, c2S] at this <;> omega),
        install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; simp [pS, tS] at this; omega),
        install_other _ _ _ _ (by
          intro j h; have := congrArg Fin.val h; fin_cases j <;> simp [tS, c1S] at this <;> omega)]
      have ee : entry bits (tS i) = [] := by
        unfold entry; simp only [tS]; rw [if_neg (by omega), if_neg (by omega)]
      rw [ee]
      by_cases h36 : i.val < 36
      · have ei : i = Fin.castAdd 1 (⟨i.val, h36⟩ : Fin 36) := Fin.ext rfl
        rw [ei, Fin.addCases_left]
        unfold CloseoutWitness.TraversalCold.input
        rw [if_neg h0]
      · have ei : i = Fin.natAdd 36 (0 : Fin 1) := Fin.ext (by simp; omega)
        rw [ei, Fin.addCases_right]
  have d4 := dock s4 tS tS_inj (fun _ => 0) _ (fun _ => rfl) hA4
  have whole := ((d1.seq d2).seq d3).seq d4
  have hlen := termsCode_length bits
  refine ⟨_, whole.enlarge ?_, ?_, ?_, ?_⟩
  · unfold cost CloseoutWitness.PairHeader.budget CloseoutWitness.TraversalCold.budget
    rw [hlen]
  · rw [install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; simp [tS] at this),
      install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; fin_cases j <;> simp [c2S] at this),
      install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; simp [pS] at this)]
    have e : (0 : Fin 189) = c1S 0 := rfl
    rw [e, install_slot _ c1S_inj]
    rfl
  · rw [install_slot _ tS_inj]
    show r.final.tapes 27 = _
    rw [h27, hlen]
    rfl
  · rw [install_slot _ tS_inj]
    show r.final.tapes 28 = _
    rw [h28]
    rfl

/-! ## Segment B: the `i`-th term code of a sum code, on `Fin 192` -/

def coreS (i : Fin 189) : Fin 192 := ⟨i.val, by omega⟩
def seekS : Fin 4 → Fin 192 := ![178, 189, 190, 191]
theorem coreS_inj : Function.Injective coreS := by
  intro i j h; exact Fin.ext (by have := congrArg Fin.val h; simpa [coreS] using this)
theorem seekS_inj : Function.Injective seekS := by decide

noncomputable def machineB :=
  Composition.machine (RecoveryFocus.machine coreS machine) (RecoveryFocus.machine seekS (Rewind.machine seekCore))

def costB (n i : Nat) : Nat := cost n + 1 + (2 * seekCost n i n + 2)

open RepairSource.VerifierDecoding in
/-- Segment B's entry: the sum-code frame on `0`, `[false]` on `1`, the counter `word i` on `189`, blank elsewhere. -/
def entryB (c : List Bool) (i : Nat) : Fin 192 → List Bool := fun x =>
  if x.val = 0 then frame c else if x.val = 1 then [false] else if x.val = 189 then CompareMachine.word i else []

open RepairSource.VerifierDecoding in

theorem segB_run (c : List Bool) (i : Nat) (hi : i < (terms c).length) : ∃ X : Fin 192 → List Bool,
    Step machineB (costB c.length i) (fun _ => 0) (entryB c i) (fun _ => 0) X ∧
    X 0 = frame c ∧ X 189 = CompareMachine.word i ∧
    X 190 = frame (SignedSortKey.binary c.length (terms c)[i]) ∧
    X 179 = List.replicate (terms c).length true := by
  obtain ⟨X0, s0, x0, x27, x28⟩ := core_run c
  have hE : ∀ k, entryB c i (coreS k) = entry c k := by
    intro k
    have hk := k.isLt
    unfold entryB entry
    simp only [coreS]
    split_ifs <;> first | rfl | omega
  have d0 := dock s0 coreS coreS_inj (fun _ => 0) (entryB c i) (fun _ => rfl) hE
  let words := ((terms c).take i).map (SignedSortKey.binary c.length)
  have hw : ∀ b ∈ words, b.length ≤ c.length := by
    intro b hb
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
    rw [SignedSortKey.binary_length]
  have hwl : words.length = i := by
    simp only [words, List.length_map, List.length_take]; omega
  obtain ⟨hout, sk⟩ := seekCore_run words (SignedSortKey.binary c.length (terms c)[i])
    (PCPPNativeCanonicalWalk.atomStream c.length ((terms c).drop (i + 1))) c.length hw
  obtain ⟨log, sr⟩ := rewound sk
  have hsplit := stream_split c.length (terms c) i hi
  have hA : ∀ k, install coreS (entryB c i) X0 (seekS k) =
      Fin.addCases (m := 3) (n := 1) (motive := fun _ => List Bool)
        (seekIn (words.flatMap frame ++ frame (SignedSortKey.binary c.length (terms c)[i]) ++
          PCPPNativeCanonicalWalk.atomStream c.length ((terms c).drop (i + 1))) words.length)
        (fun _ => []) k := by
    intro k
    fin_cases k
    · show install coreS _ _ (coreS (tS 27)) = _
      rw [install_slot _ coreS_inj, x27, hsplit]
      rfl
    · rw [install_other _ _ _ _ (by intro m h; have := congrArg Fin.val h; simp [coreS, seekS] at this; omega)]
      show entryB c i 189 = RepairSource.VerifierDecoding.CompareMachine.word words.length
      rw [hwl]; rfl
    · rw [install_other _ _ _ _ (by intro m h; have := congrArg Fin.val h; simp [coreS, seekS] at this; omega)]
      rfl
    · rw [install_other _ _ _ _ (by intro m h; have := congrArg Fin.val h; simp [coreS, seekS] at this; omega)]
      rfl
  have d1 := dock sr seekS seekS_inj (fun _ => 0) _ (fun _ => rfl) hA
  refine ⟨_, (d0.seq d1).enlarge ?_, ?_, ?_, ?_, ?_⟩
  · unfold costB; rw [hwl, SignedSortKey.binary_length]
  · rw [install_other _ _ _ _ (by intro k h; have := congrArg Fin.val h; fin_cases k <;> simp [seekS] at this)]
    show install coreS _ _ (coreS 0) = _
    rw [install_slot _ coreS_inj, x0]
  · show install seekS _ _ (seekS 1) = _
    rw [install_slot _ seekS_inj]
    show RepairSource.VerifierDecoding.CompareMachine.word words.length = _
    rw [hwl]
  · show install seekS _ _ (seekS 2) = _
    rw [install_slot _ seekS_inj]
    rfl
  · rw [install_other _ _ _ _ (by intro k h; have := congrArg Fin.val h; fin_cases k <;> simp [seekS] at this)]
    show install coreS _ _ (coreS (tS 28)) = _
    rw [install_slot _ coreS_inj, x28]

end NearCubicWires.SourceRequest.TermSegB

