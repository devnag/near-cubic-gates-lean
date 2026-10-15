import Proof.SourceAssembly.SourceRequestTermReader
import Proof.CaseAnalysis.RowsGateHeader
import Proof.CaseAnalysis.CloseoutWitnessTraversalCold
import Proof.CaseAnalysis.RowsTupleSeekFrame
import Proof.Foundations.OrdinaryRewind
import Proof.CaseAnalysis.RowsTouchingFrameSeek
import Proof.Circuits.DecompositionCountPosition

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.TermSeg
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound

/-! ## Generic seams -/

theorem stepOfReady {t s : Nat} {p : Machine t s} {b : Nat} {inp out : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p b inp out) : Step p b (fun _ => 0) inp (fun _ => 0) out := by
  obtain ⟨r, hr, ht, hh, _⟩ := h
  exact Step.of_run hr (funext hh) ht

/-- A zero-entry-head run, rewound: every head back at `0`, original tapes as the run left them, the rewind log is
some word. -/
theorem rewound {t s : Nat} {p : Machine t s} {n : Nat} {tin tout : Fin t → List Bool} {hout : Fin t → Nat}
    (h : Step p n (fun _ => 0) tin hout tout) :
    ∃ log : List Bool, Step (Rewind.machine p) (2 * n + 2) (fun _ => 0) (Fin.addCases tin (fun _ => []))
      (fun _ => 0) (Fin.addCases tout (fun _ => log)) := by
  obtain ⟨r, hr, _, ht, hs⟩ := h
  obtain ⟨r', hr', hkeep, hh, hsteps, _⟩ := Rewind.reset_run p n tin r hr
  refine ⟨r'.final.tapes (Fin.last t), ?_⟩
  have st : Step (Rewind.machine p) (2 * r.steps + 2) (fun _ => 0) (Fin.addCases tin (fun _ => []))
      (fun _ => 0) (Fin.addCases tout (fun _ => r'.final.tapes (Fin.last t))) := by
    refine Step.of_run hr' (funext hh) ?_
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.addCases_left, hkeep j, ht]
    · rw [Fin.addCases_right]
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      rfl
  exact st.enlarge (by omega)

/-- Dock a zero-head run onto slots whose ambient values ARE its input; ambient heads stay. -/
theorem dock {t u s : Nat} {p : Machine t s} {n : Nat} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (H : Fin u → Nat) (A : Fin u → List Bool) (hH : ∀ i, H (slots i) = 0) (hA : ∀ i, A (slots i) = tin i) :
    Step (RecoveryFocus.machine slots p) n H A H (install slots A tout) := by
  have hf := h.focus slots hi H A
  have e1 : install slots A tin = A := install_existing slots A tin hA
  have e2 : dockH slots H (fun _ => 0) = H := by
    funext x
    by_cases hx : ∃ j, slots j = x
    · obtain ⟨j, rfl⟩ := hx
      rw [dockH_slot _ hi, hH]
    · simp only [not_exists] at hx
      exact dockH_other _ _ _ _ hx
  rw [e1, e2] at hf
  exact hf

/-- The framed-word copy, rewound: `[frame w, [], []] ↦ [frame w, frame w, log]`, heads `0`. -/
noncomputable def copyMachine := Rewind.machine (CloseoutRowsTupleSeek.frameMachine true)

def copyIn (w : List Bool) : Fin 3 → List Bool :=
  Fin.addCases (m := 2) (n := 1) (motive := fun _ => List Bool) (CloseoutRowsTupleSeek.fieldData (frame w) [])
    (fun _ => [])

def copyOut (w log : List Bool) : Fin 3 → List Bool :=
  Fin.addCases (m := 2) (n := 1) (motive := fun _ => List Bool) (CloseoutRowsTupleSeek.fieldData (frame w) (frame w))
    (fun _ => log)

theorem copy_run (w : List Bool) : ∃ log : List Bool,
    Step copyMachine (2 * (2 * w.length + 1) + 2) (fun _ => 0) (copyIn w) (fun _ => 0) (copyOut w log) := by
  have h := CloseoutRowsTupleSeek.frame_run true [] w [] []
  simp only [List.nil_append, List.append_nil, List.length_nil, CloseoutRowsTupleSeek.selected, if_true] at h
  have h0 : CloseoutRowsTupleSeek.fieldHeads 0 ([] : List Bool) = fun _ => 0 := by
    funext i; fin_cases i <;> rfl
  rw [h0] at h
  exact rewound h

/-! ## Segment A, part 1: layout on `Fin 188` -/

/-- `0` witness; `1 + i` the header parser (148); `149` log; `150 + i` the rewound traversal (37); `187` log. -/
def gS (i : Fin 148) : Fin 188 := ⟨1 + i.val, by omega⟩
def tS (i : Fin 37) : Fin 188 := ⟨150 + i.val, by omega⟩
def c1S : Fin 3 → Fin 188 := ![0, 2, 149]
def c2S : Fin 3 → Fin 188 := ![119, 150, 187]

theorem gS_inj : Function.Injective gS := by
  intro i j h; exact Fin.ext (by have := congrArg Fin.val h; simp only [gS] at this; omega)
theorem tS_inj : Function.Injective tS := by
  intro i j h; exact Fin.ext (by have := congrArg Fin.val h; simp only [tS] at this; omega)
theorem c1S_inj : Function.Injective c1S := by decide
theorem c2S_inj : Function.Injective c2S := by decide

/-- Entry: the witness frame on `0`, the parser's (empty) first field `frame [] = [false]` on `1`, blank elsewhere. -/
def entry (bits : List Bool) : Fin 188 → List Bool := fun x =>
  if x.val = 0 then frame bits else if x.val = 1 then [false] else []

noncomputable def machine :=
  Composition.machine
    (Composition.machine
      (Composition.machine (RecoveryFocus.machine c1S copyMachine)
        (RecoveryFocus.machine gS CloseoutRowsGateHeader.machine))
      (RecoveryFocus.machine c2S copyMachine))
    (RecoveryFocus.machine tS (Rewind.machine CloseoutWitness.TraversalCold.machine))

def cost (n : Nat) : Nat :=
  (((2 * (2 * n + 1) + 2) + 1 + 27000 * (n + 1) ^ 2) + 1 + (2 * (2 * n + 1) + 2)) + 1 +
    (2 * (1048576 * (n + 1) ^ 3) + 2)

/-- The family field is the header parser's third code word. -/
theorem family_eq (bits : List Bool) :
    CloseoutWitness.BoundedFields.family bits = CloseoutRowsGateHeader.codeWord bits 2 := rfl

theorem family_length (bits : List Bool) :
    (CloseoutWitness.BoundedFields.family bits).length = bits.length := by
  simp [CloseoutWitness.BoundedFields.family, RecoveryFixedUnpair.leftWord,
    CompetitorWitnessTriple.word_length]

/-- The sum codes of the witness family, in order (`tree` = the canonical balanced-list view). -/
noncomputable def sums (bits : List Bool) : List Nat :=
  (PCPPNativeCanonicalTree.tree (RadixSemantics.value (CloseoutWitness.BoundedFields.family bits))).atoms

theorem core_run (bits : List Bool) : ∃ X : Fin 188 → List Bool,
    Step machine (cost bits.length) (fun _ => 0) (entry bits) (fun _ => 0) X ∧
    X 0 = frame bits ∧
    X (tS 27) = PCPPNativeCanonicalWalk.atomStream bits.length (sums bits) ∧
    X (tS 28) = List.replicate (sums bits).length true := by
  -- 1. copy the witness onto the parser's witness tape
  obtain ⟨l1, s1⟩ := copy_run bits
  have d1 := dock s1 c1S c1S_inj (fun _ => 0) (entry bits) (fun _ => rfl) (by intro i; fin_cases i <;> rfl)
  -- 2. the header parser
  have gh := stepOfReady (CloseoutRowsGateHeader.header_run bits).1
  have hA2 : ∀ i, install c1S (entry bits)
      (copyOut bits l1) (gS i) =
      CompetitorWitnessHeader.input [] bits i := by
    intro i
    rw [CompetitorWitnessHeader.input_eq]
    by_cases h1 : i.val = 1
    · have e : gS i = c1S 1 := Fin.ext (by simp [gS, c1S]; omega)
      rw [e, install_slot _ c1S_inj, if_neg (by omega), if_pos h1]
      rfl
    · rw [install_other _ _ _ _ (by
        intro j h; have := congrArg Fin.val h; fin_cases j <;> simp [c1S, gS] at this <;> omega)]
      unfold entry
      simp only [gS]
      by_cases h0 : i.val = 0
      · rw [if_neg (by omega), if_pos (by omega), if_pos h0]; rfl
      · rw [if_neg (by omega), if_neg (by omega), if_neg h0, if_neg h1]
  have d2 := dock gh gS gS_inj (fun _ => 0) _ (fun _ => rfl) hA2
  -- 3. copy the family frame onto the traversal's input tape
  obtain ⟨l2, s3⟩ := copy_run (CloseoutRowsGateHeader.codeWord bits 2)
  have h118 : CloseoutRowsGateHeader.output bits 118 = frame (CloseoutRowsGateHeader.codeWord bits 2) :=
    (CloseoutRowsGateHeader.header_run bits).2.2 2
  have hA3 : ∀ i, install gS (install c1S (entry bits)
      (copyOut bits l1))
      (CloseoutRowsGateHeader.output bits) (c2S i) = copyIn (CloseoutRowsGateHeader.codeWord bits 2) i := by
    intro i
    fin_cases i
    · show install gS _ _ (gS 118) = _
      rw [install_slot _ gS_inj, h118]; rfl
    · rw [install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; simp [gS, c2S] at this; omega),
        install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; fin_cases j <;> simp [c1S, c2S] at this)]
      rfl
    · rw [install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; simp [gS, c2S] at this; omega),
        install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; fin_cases j <;> simp [c1S, c2S] at this)]
      rfl
  have d3 := dock s3 c2S c2S_inj (fun _ => 0) _ (fun _ => rfl) hA3
  -- 4. the traversal of the family code
  obtain ⟨r, hr, hs, h27, h28, _⟩ := CloseoutWitness.TraversalCold.cold_run (CloseoutRowsGateHeader.codeWord bits 2)
  have st : Step CloseoutWitness.TraversalCold.machine
      (CloseoutWitness.TraversalCold.budget (CloseoutRowsGateHeader.codeWord bits 2)) (fun _ => 0)
      (CloseoutWitness.TraversalCold.input (CloseoutRowsGateHeader.codeWord bits 2)) r.final.heads r.final.tapes :=
    ⟨r, hr, rfl, rfl, hs⟩
  obtain ⟨l4, s4⟩ := rewound st
  have hA4 : ∀ i, install c2S (install gS (install c1S (entry bits)
      (copyOut bits l1))
      (CloseoutRowsGateHeader.output bits))
      (copyOut (CloseoutRowsGateHeader.codeWord bits 2) l2) (tS i) =
      Fin.addCases (m := 36) (n := 1) (motive := fun _ => List Bool)
        (CloseoutWitness.TraversalCold.input (CloseoutRowsGateHeader.codeWord bits 2)) (fun _ => []) i := by
    intro i
    by_cases h0 : i.val = 0
    · have e : tS i = c2S 1 := Fin.ext (by simp [tS, c2S]; omega)
      have ei : i = Fin.castAdd 1 (0 : Fin 36) := Fin.ext (by simp; omega)
      rw [e, install_slot _ c2S_inj, ei, Fin.addCases_left]
      rfl
    · rw [install_other _ _ _ _ (by
          intro j h; have := congrArg Fin.val h; fin_cases j <;> simp [tS, c2S] at this <;> omega),
        install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; simp [gS, tS] at this; omega),
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
  have hlen := family_length bits
  rw [family_eq] at hlen
  refine ⟨_, whole.enlarge ?_, ?_, ?_, ?_⟩
  · unfold cost CloseoutRowsGateHeader.budget CloseoutWitness.TraversalCold.budget
    rw [hlen]
  · rw [install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; simp [tS] at this),
      install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; fin_cases j <;> simp [c2S] at this),
      install_other _ _ _ _ (by intro j h; have := congrArg Fin.val h; simp [gS] at this)]
    have e : (0 : Fin 188) = c1S 0 := rfl
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

/-! ## Segment A, part 2: the `j`-th frame of a framed stream (`[stream, word j, out]`, rewound) -/

open RepairSource.VerifierDecoding in

theorem skip_step (words : List (List Bool)) (tail : List Bool) (w : Nat) (hw : ∀ b ∈ words, b.length ≤ w) :
    Step CloseoutRowsTouching.FrameSeek.machine (CloseoutRowsTouching.FrameSeek.budget w words.length)
      (Fin.addCases (m := 1) (n := 1) (motive := fun _ => Nat) (fun _ => 0) (fun _ => 1))
      (Fin.addCases (m := 1) (n := 1) (motive := fun _ => List Bool) (fun _ => words.flatMap frame ++ tail)
        (fun _ => CompareMachine.word words.length))
      (Fin.addCases (m := 1) (n := 1) (motive := fun _ => Nat) (fun _ => (words.flatMap frame).length)
        (fun _ => 1))
      (Fin.addCases (m := 1) (n := 1) (motive := fun _ => List Bool) (fun _ => words.flatMap frame ++ tail)
        (fun _ => CompareMachine.word words.length)) := by
  obtain ⟨r, hr, hf, _⟩ := CloseoutRowsTouching.FrameSeek.seek_run words [] tail w hw
  refine Step.of_run (r := r) hr ?_ ?_
  · rw [hf]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [RepeatMachine.cfg, TapeEmbedding.config, NearCubicWires.RepairOrdinary.controlConfig,
        CloseoutRowsTouching.FrameSeek.entry, FrameSkip.cfg]
    · simp only [RepeatMachine.cfg, TapeEmbedding.config, NearCubicWires.RepairOrdinary.controlConfig,
        Fin.addCases_right]
  · rw [hf]
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [RepeatMachine.cfg, TapeEmbedding.config, NearCubicWires.RepairOrdinary.controlConfig,
        CloseoutRowsTouching.FrameSeek.entry, FrameSkip.cfg]
    · simp only [RepeatMachine.cfg, TapeEmbedding.config, NearCubicWires.RepairOrdinary.controlConfig,
        Fin.addCases_right]

/-- `dock` with arbitrary entry/exit heads. -/
theorem dockG {t u s : Nat} {p : Machine t s} {n : Nat} {hin hout : Fin t → Nat} {tin tout : Fin t → List Bool}
    (h : Step p n hin tin hout tout) (slots : Fin t → Fin u) (hi : Function.Injective slots)
    (H : Fin u → Nat) (A : Fin u → List Bool) (hH : ∀ i, H (slots i) = hin i) (hA : ∀ i, A (slots i) = tin i) :
    Step (RecoveryFocus.machine slots p) n H A (dockH slots H hout) (install slots A tout) := by
  have hf := h.focus slots hi H A
  have e1 : install slots A tin = A := install_existing slots A tin hA
  have e2 : dockH slots H hin = H := by
    funext x
    by_cases hx : ∃ j, slots j = x
    · obtain ⟨j, rfl⟩ := hx
      rw [dockH_slot _ hi, hH]
    · simp only [not_exists] at hx
      exact dockH_other _ _ _ _ hx
  rw [e1, e2] at hf
  exact hf

open RepairSource.VerifierDecoding in
def seekIn (src : List Bool) (j : Nat) : Fin 3 → List Bool := ![src, CompareMachine.word j, []]
open RepairSource.VerifierDecoding in
def seekOut (src : List Bool) (j : Nat) (o : List Bool) : Fin 3 → List Bool := ![src, CompareMachine.word j, o]

def sk01 : Fin 2 → Fin 3 := ![0, 1]
def sk02 : Fin 2 → Fin 3 := ![0, 2]

noncomputable def seekCore :=
  Composition.machine (DecompositionCountPosition.move ![HeadMove.stay, HeadMove.right, HeadMove.stay])
    (Composition.machine (RecoveryFocus.machine sk01 CloseoutRowsTouching.FrameSeek.machine)
      (RecoveryFocus.machine sk02 (CloseoutRowsTupleSeek.frameMachine true)))

def seekCost (w j b : Nat) : Nat := 1 + 1 + (CloseoutRowsTouching.FrameSeek.budget w j + 1 + (2 * b + 1))

/-- **Seek, one call:** from the stream `(words.flatMap frame) ++ frame bits ++ rest` and the counter `word |words|`, the
frame `frame bits` lands on the fresh output tape; stream and counter kept. -/
theorem seekCore_run (words : List (List Bool)) (bits rest : List Bool) (w : Nat) (hw : ∀ b ∈ words, b.length ≤ w) :
    ∃ hout : Fin 3 → Nat, Step seekCore (seekCost w words.length bits.length) (fun _ => 0)
      (seekIn (words.flatMap frame ++ frame bits ++ rest) words.length) hout
      (seekOut (words.flatMap frame ++ frame bits ++ rest) words.length (frame bits)) := by
  obtain ⟨r0, hr0, hf0, hs0⟩ := DecompositionCountPosition.move_run ![HeadMove.stay, HeadMove.right, HeadMove.stay]
    (fun _ => 0) (seekIn (words.flatMap frame ++ frame bits ++ rest) words.length)
  have m : Step (DecompositionCountPosition.move ![HeadMove.stay, HeadMove.right, HeadMove.stay]) 1 (fun _ => 0)
      (seekIn (words.flatMap frame ++ frame bits ++ rest) words.length) ![0, 1, 0]
      (seekIn (words.flatMap frame ++ frame bits ++ rest) words.length) := by
    refine ⟨r0, hr0, ?_, ?_, by omega⟩
    · rw [hf0]; funext i; fin_cases i <;> rfl
    · rw [hf0]
  have sk := skip_step words (frame bits ++ rest) w hw
  rw [← List.append_assoc] at sk
  have d1 := dockG sk sk01 (by decide) ![0, 1, 0] (seekIn (words.flatMap frame ++ frame bits ++ rest) words.length)
    (by intro i; fin_cases i <;> rfl) (by intro i; fin_cases i <;> rfl)
  have cp := CloseoutRowsTupleSeek.frame_run true (words.flatMap frame) bits rest []
  simp only [CloseoutRowsTupleSeek.selected, if_true, List.nil_append] at cp
  have hH2 : ∀ i, dockH sk01 ![0, 1, 0]
      (Fin.addCases (m := 1) (n := 1) (motive := fun _ => Nat) (fun _ => (words.flatMap frame).length)
        (fun _ => 1)) (sk02 i) = CloseoutRowsTupleSeek.fieldHeads (words.flatMap frame).length [] i := by
    intro i
    fin_cases i
    · show dockH sk01 _ _ (sk01 0) = _
      rw [dockH_slot _ (by decide)]
      rfl
    · rw [dockH_other _ _ _ _ (by intro j h; fin_cases j <;> simp [sk01, sk02] at h)]
      rfl
  have hA2 : ∀ i, install sk01 (seekIn (words.flatMap frame ++ frame bits ++ rest) words.length)
      (Fin.addCases (m := 1) (n := 1) (motive := fun _ => List Bool)
        (fun _ => words.flatMap frame ++ frame bits ++ rest)
        (fun _ => RepairSource.VerifierDecoding.CompareMachine.word words.length)) (sk02 i) =
      CloseoutRowsTupleSeek.fieldData (words.flatMap frame ++ frame bits ++ rest) [] i := by
    intro i
    fin_cases i
    · show install sk01 _ _ (sk01 0) = _
      rw [install_slot _ (by decide)]
      rfl
    · rw [install_other _ _ _ _ (by intro j h; fin_cases j <;> simp [sk01, sk02] at h)]
      rfl
  have d2 := dockG cp sk02 (by decide) _ _ hH2 hA2
  refine ⟨_, ((m.seq (d1.seq d2)).enlarge (by unfold seekCost; omega)).congr rfl ?_⟩
  funext i
  fin_cases i
  · show install sk02 _ _ (sk02 0) = _
    rw [install_slot _ (by decide)]
    rfl
  · rw [install_other _ _ _ _ (by intro j h; fin_cases j <;> simp [sk02] at h)]
    show install sk01 _ _ (sk01 1) = _
    rw [install_slot _ (by decide)]
    rfl
  · show install sk02 _ _ (sk02 1) = _
    rw [install_slot _ (by decide)]
    rfl

/-! ## Segment A: the `j`-th sum code of the witness family, on `Fin 191` -/

theorem stream_split (w : Nat) (xs : List Nat) (j : Nat) (hj : j < xs.length) :
    PCPPNativeCanonicalWalk.atomStream w xs =
      ((xs.take j).map (SignedSortKey.binary w)).flatMap frame ++ frame (SignedSortKey.binary w xs[j]) ++
        PCPPNativeCanonicalWalk.atomStream w (xs.drop (j + 1)) := by
  have hs : xs = xs.take j ++ xs[j] :: xs.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j xs]
    rw [List.drop_eq_getElem_cons hj]
  unfold PCPPNativeCanonicalWalk.atomStream
  conv_lhs => rw [hs]
  rw [List.flatMap_append, List.flatMap_cons, List.flatMap_map]
  simp only [List.append_assoc]

def coreS (i : Fin 188) : Fin 191 := ⟨i.val, by omega⟩
def seekS : Fin 4 → Fin 191 := ![177, 188, 189, 190]
theorem coreS_inj : Function.Injective coreS := by
  intro i j h; exact Fin.ext (by have := congrArg Fin.val h; simpa [coreS] using this)
theorem seekS_inj : Function.Injective seekS := by decide

noncomputable def machineA :=
  Composition.machine (RecoveryFocus.machine coreS machine) (RecoveryFocus.machine seekS (Rewind.machine seekCore))

def costA (n j : Nat) : Nat := cost n + 1 + (2 * seekCost n j n + 2)

open RepairSource.VerifierDecoding in
/-- Segment A's entry: the witness frame on `0`, `[false]` on `1`, the counter `word j` on `188`, blank elsewhere. -/
def entryA (bits : List Bool) (j : Nat) : Fin 191 → List Bool := fun x =>
  if x.val = 0 then frame bits else if x.val = 1 then [false] else if x.val = 188 then CompareMachine.word j else []

open RepairSource.VerifierDecoding in

theorem segA_run (bits : List Bool) (j : Nat) (hj : j < (sums bits).length) : ∃ X : Fin 191 → List Bool,
    Step machineA (costA bits.length j) (fun _ => 0) (entryA bits j) (fun _ => 0) X ∧
    X 0 = frame bits ∧ X 188 = CompareMachine.word j ∧
    X 189 = frame (SignedSortKey.binary bits.length (sums bits)[j]) ∧
    X 178 = List.replicate (sums bits).length true := by
  obtain ⟨X0, s0, x0, x27, x28⟩ := core_run bits
  have hE : ∀ i, entryA bits j (coreS i) = entry bits i := by
    intro i
    have hi := i.isLt
    unfold entryA entry
    simp only [coreS]
    split_ifs <;> first | rfl | omega
  have d0 := dock s0 coreS coreS_inj (fun _ => 0) (entryA bits j) (fun _ => rfl) hE
  let words := ((sums bits).take j).map (SignedSortKey.binary bits.length)
  have hw : ∀ b ∈ words, b.length ≤ bits.length := by
    intro b hb
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
    rw [SignedSortKey.binary_length]
  have hwl : words.length = j := by
    simp only [words, List.length_map, List.length_take]; omega
  obtain ⟨hout, sk⟩ := seekCore_run words (SignedSortKey.binary bits.length (sums bits)[j])
    (PCPPNativeCanonicalWalk.atomStream bits.length ((sums bits).drop (j + 1))) bits.length hw
  obtain ⟨log, sr⟩ := rewound sk
  have hsplit := stream_split bits.length (sums bits) j hj
  have hA : ∀ i, install coreS (entryA bits j) X0 (seekS i) =
      Fin.addCases (m := 3) (n := 1) (motive := fun _ => List Bool)
        (seekIn (words.flatMap frame ++ frame (SignedSortKey.binary bits.length (sums bits)[j]) ++
          PCPPNativeCanonicalWalk.atomStream bits.length ((sums bits).drop (j + 1))) words.length)
        (fun _ => []) i := by
    intro i
    fin_cases i
    · show install coreS _ _ (coreS (tS 27)) = _
      rw [install_slot _ coreS_inj, x27, hsplit]
      rfl
    · rw [install_other _ _ _ _ (by intro k h; have := congrArg Fin.val h; simp [coreS, seekS] at this; omega)]
      show entryA bits j 188 = RepairSource.VerifierDecoding.CompareMachine.word words.length
      rw [hwl]; rfl
    · rw [install_other _ _ _ _ (by intro k h; have := congrArg Fin.val h; simp [coreS, seekS] at this; omega)]
      rfl
    · rw [install_other _ _ _ _ (by intro k h; have := congrArg Fin.val h; simp [coreS, seekS] at this; omega)]
      rfl
  have d1 := dock sr seekS seekS_inj (fun _ => 0) _ (fun _ => rfl) hA
  refine ⟨_, (d0.seq d1).enlarge ?_, ?_, ?_, ?_, ?_⟩
  · unfold costA; rw [hwl, SignedSortKey.binary_length]
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

end NearCubicWires.SourceRequest.TermSeg

