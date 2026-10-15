import Proof.CaseAnalysis.FinalEnvelopeCounter
import Proof.CaseAnalysis.FinalUnaryExpDock

namespace NearCubicWires.RepairSource.CloseoutFinal.C10PrologueUniform

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerDockSeam (phaseRecords)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall
open NearCubicWires.RepairSource.CloseoutLanguage (clauseWidth)
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

variable {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}

/-! ## §1 The prologue's target bank is branch-free -/

theorem loopBank_zero (extra entryWidth : ℕ) (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (input witness : List Bool)
    (scratch : ℕ → ℕ → List Bool) :
    loopBank extra entryWidth answer denominator phase pcpp coordinate systematicAtom
        input witness scratch 0
      = bank [] (CompareMachine.word 0) (List.replicate entryWidth true) input witness
          (scratch 0) := rfl

/-! ## §2 The obligation, with the length INSIDE the machine binder -/

def Prologue (extra : ℕ) (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ) (preFuel : ℕ → ℕ)
    {ps : ℕ} (pre : Machine (218 + (60 + extra) + 1) ps) : Prop :=
  ∀ (len : ℕ) (x : BitInput len) (bits : List Bool),
    ∃ w : ℕ → List Bool,
      Step pre (preFuel len) (fun _ => 0)
        (bank [] [] [] (List.ofFn x) bits (fun _ => []))
        (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
        (Fin.addCases (motive := fun _ => List Bool)
          (bank [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
            (List.ofFn x) bits w)
          (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree (q len))))

/-! ## §3 One run of the prologue is `hpre` at EVERY branch -/

theorem hpre_of_step (extra : ℕ) (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ) (preFuel : ℕ → ℕ)
    {ps : ℕ} (pre : Machine (218 + (60 + extra) + 1) ps)
    (len : ℕ) (x : BitInput len) (bits : List Bool) (w : ℕ → List Bool)
    (hstep : Step pre (preFuel len) (fun _ => 0)
      (bank [] [] [] (List.ofFn x) bits (fun _ => []))
      (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
      (Fin.addCases (motive := fun _ => List Bool)
        (bank [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
          (List.ofFn x) bits w)
        (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree (q len)))))
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (heads : ℕ → Fin (218 + (60 + extra)) → ℕ) (scratch : ℕ → ℕ → List Bool)
    (hheads : heads 0 = fun _ => 0) (hscratch : scratch 0 = w) :
    Step pre (preFuel len) (fun _ => 0)
      (bank [] [] [] (List.ofFn x) bits (fun _ => []))
      (Fin.addCases (heads 0) (fun _ : Fin 1 => 1))
      (Fin.addCases
        (loopBank extra (entryWidth len) answer denominator phase pcpp coordinate systematicAtom
          (List.ofFn x) bits scratch 0)
        (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree (q len)))) := by
  rw [hheads, loopBank_zero, hscratch]
  exact hstep

/-! ## §4 The consumer: `CallsReady`, from `Prologue` and the emitter -/

/-- **S0's `CallsReady` from a length-uniform prologue.**  The emitter side
enters as `hbody`, and it is quantified over the prologue's OWN leftover
workspace `w`: whoever builds the per-address emitter must be able to start from
whatever the prologue left above tape `278`, which is the only coupling between
the two halves of `call_run`. -/
theorem callsReady_of_prologue (extra : ℕ) (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ)
    (preFuel : ℕ → ℕ) {ps bs : ℕ} (pre : Machine (218 + (60 + extra) + 1) ps)
    (body : Machine (218 + (60 + extra)) bs) (cost : ℕ)
    (hpro : Prologue extra entryWidth q clauseDegree preFuel pre)
    (len : ℕ) (x : BitInput len) (bits : List Bool)
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) (callCount : ℕ)
    (hlen : (phaseRecords answer denominator phase pcpp coordinate systematicAtom).length
      = callCount)
    (hfit : pcpp.clauseBits ≤ clauseWidth clauseDegree (q len))
    (hbody : ∀ w : ℕ → List Bool,
      ∃ (heads : ℕ → Fin (218 + (60 + extra)) → ℕ) (scratch : ℕ → ℕ → List Bool),
        heads 0 = (fun _ => 0) ∧ scratch 0 = w ∧
        (∀ address, address < 2 ^ pcpp.clauseBits →
          Step body cost (heads address)
            (loopBank extra (entryWidth len) answer denominator phase pcpp coordinate
              systematicAtom (List.ofFn x) bits scratch address)
            (heads (address + 1))
            (loopBank extra (entryWidth len) answer denominator phase pcpp coordinate
              systematicAtom (List.ofFn x) bits scratch (address + 1))) ∧
        (∀ address, 2 ^ pcpp.clauseBits ≤ address →
            address < 2 ^ clauseWidth clauseDegree (q len) →
          Step body cost (heads address)
            (loopBank extra (entryWidth len) answer denominator phase pcpp coordinate
              systematicAtom (List.ofFn x) bits scratch address)
            (heads (address + 1))
            (loopBank extra (entryWidth len) answer denominator phase pcpp coordinate
              systematicAtom (List.ofFn x) bits scratch (address + 1)))) :
    C10SupplierStage.CallsReady (extra + 2) (callMachine extra pre body)
      (callFuel (preFuel len) (clauseWidth clauseDegree (q len)) cost) (entryWidth len) callCount
      (CloseoutRowsEstimatorCoefficients.Stream.words (entryWidth len)
        (phaseRecords answer denominator phase pcpp coordinate systematicAtom))
      (List.ofFn x) bits := by
  obtain ⟨w, hstep⟩ := hpro len x bits
  obtain ⟨heads, scratch, hheads, hscratch, hsite, hidle⟩ := hbody w
  exact C10EnvelopeCounter.callsReady_at_clauseWidth extra pre body answer denominator phase
    pcpp coordinate systematicAtom (entryWidth len) callCount (preFuel len) cost clauseDegree
    (q len) (List.ofFn x) bits heads scratch hlen hfit
    (hpre_of_step extra entryWidth q clauseDegree preFuel pre len x bits w hstep answer
      denominator phase pcpp coordinate systematicAtom heads scratch hheads hscratch)
    hsite hidle

/-! ## §6 Two readings of the bank, and the count word built -/

theorem bank_apply {t : ℕ} (stream count driver input witness : List Bool)
    (scratch : ℕ → List Bool) (i : Fin t) :
    bank stream count driver input witness scratch i
      = bankAt stream count driver input witness scratch i.val := rfl

/-- Above `278` the bank IS the scratch: `bankAt`
(`Proof/CaseAnalysis/FinalSupplierCall.lean`) leaves that whole region to
whoever supplies `hpre`. -/
theorem bankAt_scratch (stream count driver input witness : List Bool)
    (scratch : ℕ → List Bool) (v : ℕ) (hv : 278 ≤ v) :
    bankAt stream count driver input witness scratch v = scratch v := by
  unfold bankAt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega), if_pos hv]

/-- Bank tape `90` and one private scratch tape. -/
def zeroSlots (e : ℕ) : Fin 2 → Fin (218 + (60 + (e + 23)) + 1) :=
  fun j => ⟨if j.val = 0 then 90 else 300, by split_ifs <;> omega⟩

theorem zeroSlots_injective (e : ℕ) : Function.Injective (zeroSlots e) := by
  intro i j h
  have hi := i.isLt
  have hj := j.isLt
  have hv := congrArg Fin.val h
  simp only [zeroSlots] at hv
  exact Fin.ext (by split_ifs at hv <;> omega)

/-- The fixed machine that writes the empty call count. -/
noncomputable def zeroCount (e : ℕ) :=
  RecoveryFocus.machine (zeroSlots e) (HierarchyFixedWord.machine [false])

/-- **The count word, laid down by one fixed machine.**  `CompareMachine.word 0`
(`Proof/PCP/VerifierDecodingCompare.lean`) is `[false]`, so `fixedWord_dock`
(`Proof/CaseAnalysis/FinalWordEngines.lean`) writes it in four steps; nothing
in the machine, the fuel or the conclusion mentions the length or the branch.
This is the dock into the `218 + (60 + extra) + 1` bank at a concrete injective
slot map, which is the step every further prologue word repeats. -/
theorem zeroCount_run (e : ℕ) (driver input witness : List Bool) (s : ℕ → List Bool)
    (hs : s 300 = []) :
    ∃ w : ℕ → List Bool,
      Step (zeroCount e) 4 (fun _ => 0)
        (bank [] [] driver input witness s)
        (fun _ => 0)
        (bank [] (CompareMachine.word 0) driver input witness w) ∧
      ∀ v, v ≠ 300 → w v = s v := by
  obtain ⟨H', A', hstep, hzero, hword, hrest⟩ :=
    CloseoutFinalC10WordEngines.fixedWord_dock (m := 218 + (60 + (e + 23)) + 1) [false]
      (zeroSlots e) (zeroSlots_injective e) (fun _ => 0)
      (bank [] [] driver input witness s) (fun _ => rfl)
      (by rw [bank_apply]; simp [zeroSlots, bankAt])
      (by rw [bank_apply]; rw [show ((zeroSlots e 1).val) = 300 from rfl,
        bankAt_scratch _ _ _ _ _ _ _ (by omega)]; exact hs)
  have hH : H' = fun _ => 0 := funext hzero
  have hA : A' = bank [] (CompareMachine.word 0) driver input witness
      (fun v => if v = 300 then A' ⟨300, by omega⟩ else s v) := by
    funext i
    rw [bank_apply]
    by_cases h90 : i.val = 90
    · have hi : zeroSlots e 0 = i := Fin.ext (by simp [zeroSlots, h90])
      have hval : A' i = [false] := by rw [← hi]; exact hword
      rw [hval]
      unfold bankAt
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos h90]
      rfl
    · by_cases h300 : i.val = 300
      · rw [bankAt_scratch _ _ _ _ _ _ _ (by omega)]
        show A' i = (if i.val = 300 then A' ⟨300, by omega⟩ else s i.val)
        rw [if_pos h300]
        congr 1
        exact Fin.ext h300
      · have hne : ∀ j, zeroSlots e j ≠ i := by
          intro j hj
          have hv := congrArg Fin.val hj
          simp only [zeroSlots] at hv
          split_ifs at hv <;> omega
        rw [hrest i hne, bank_apply]
        unfold bankAt
        split_ifs <;> first | rfl | simp [h300]
  refine ⟨fun v => if v = 300 then A' ⟨300, by omega⟩ else s v, ?_, fun v hv => by simp [hv]⟩
  rw [hH, hA] at hstep
  exact hstep

/-! ## §7 The head bump on the loop's counter tape -/

def bump : Machine 1 2 where
  descriptionBits := 0
  start := 0
  halted := fun state => 1 ≤ state.val
  rule := fun state _ =>
    if state.val = 0 then some ⟨1, fun _ => none, fun _ => HeadMove.right⟩ else none

theorem bump_run (A : Fin 1 → List Bool) : Step bump 1 (fun _ => 0) A (fun _ => 1) A := by
  refine ⟨{ final := ⟨1, fun _ => 1, A⟩, steps := 1,
            peakTapeCells := max (Configuration.tapeCells
                (⟨bump.start, fun _ => 0, A⟩ : Configuration 1 2))
              (Configuration.tapeCells (⟨1, fun _ => 1, A⟩ : Configuration 1 2)) },
    rfl, rfl, rfl, le_refl 1⟩

/-- The loop's counter tape: the single tape `call_run` adds above the bank. -/
def counterTape (e : ℕ) : Fin (218 + (60 + (e + 23)) + 1) := ⟨301 + e, by omega⟩

def bumpSlots (e : ℕ) : Fin 1 → Fin (218 + (60 + (e + 23)) + 1) := fun _ => counterTape e

theorem bumpSlots_injective (e : ℕ) : Function.Injective (bumpSlots e) :=
  fun _ _ _ => Subsingleton.elim _ _

theorem counterTape_natAdd (e : ℕ) :
    counterTape e = Fin.natAdd (218 + (60 + (e + 23))) (0 : Fin 1) := by
  apply Fin.ext
  show 301 + e = 218 + (60 + (e + 23)) + 0
  omega

noncomputable def bumpCounter (e : ℕ) := RecoveryFocus.machine (bumpSlots e) bump

theorem bumpCounter_run (e : ℕ) (A : Fin (218 + (60 + (e + 23)) + 1) → List Bool) :
    Step (bumpCounter e) 1 (fun _ => 0) A
      (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1)) A := by
  have hdock := (bump_run (fun _ => A (counterTape e))).dock (bumpSlots e) (bumpSlots_injective e)
    (fun _ => 0) A (fun _ => rfl) (fun _ => rfl)
  have hT : RecoveryRootRound.install (bumpSlots e) A (fun _ => A (counterTape e)) = A :=
    RecoveryRootRound.install_existing (bumpSlots e) A _ (fun _ => rfl)
  have hH : dockH (bumpSlots e) (fun _ => 0) (fun _ : Fin 1 => 1)
      = Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1) := by
    funext i
    by_cases h : i.val = 301 + e
    · have hi : bumpSlots e 0 = i := Fin.ext h.symm
      have hr : i = Fin.natAdd (218 + (60 + (e + 23))) (0 : Fin 1) := by
        rw [← hi]; exact counterTape_natAdd e
      rw [← hi, dockH_slot _ (bumpSlots_injective e), hi, hr, Fin.addCases_right]
    · have hne : ∀ j, bumpSlots e j ≠ i := by
        intro j hj
        exact h (by rw [← hj]; rfl)
      have hlt : i.val < 218 + (60 + (e + 23)) := by have := i.isLt; omega
      have hl : i = Fin.castAdd 1 (⟨i.val, hlt⟩ : Fin (218 + (60 + (e + 23)))) := Fin.ext rfl
      rw [dockH_other _ _ _ i hne, hl, Fin.addCases_left]
  rw [hT, hH] at hdock
  exact hdock

/-! ## §8 The residual, named: two length-driven unary words -/

/-- The prologue's scratch after the seed: the paper's envelope exponent
`r(N)` (`paper.tex:4508-4517`) in unary on tape `278`, the prologue's own
working window `279 .. 300` and the loop's counter tape blank, and the seed's
private workspace -- whatever it is -- free above `300`. -/
def seedTapes (exponent : ℕ) (junk : ℕ → List Bool) (v : ℕ) : List Bool :=
  if v = 278 then List.replicate exponent true else junk v

/-- **`Seed` -- the whole of what `hpre` still owes.**  ONE machine, uniform in
the length, that reads `frame (List.ofFn x)` off tape `0` and lays two UNARY
words: the supplier's driver `List.replicate (entryWidth len) true` on bank tape
`218`, and the branch-independent envelope exponent
`clauseWidth clauseDegree (q len)` (`Proof/CaseAnalysis/Language.lean`, the
`r(N)=\lceil d_G\log_2(q(N)+2)\rceil` of `paper.tex:4508-4517`) on scratch tape
`278`.  No decoded quantity appears: `pcpp` is not a binder of this definition,
and this is the Lean form of C.12's "Compute `q(N_s)` from the displayed padding
formula and the branch-independent clause-address width" (`paper.tex:1636-1642`).

The seed keeps a private workspace: `junk` is existential and is required blank
only on `279 .. 300`, which is where §9 docks the count word and the unary
exponentiator, and on the loop's counter tape, which `hpre` writes.  Every tape
of `301 .. 300 + e` is the seed's own, so a docked engine need not clean up --
`extra = e + 23` with `e` free is what buys that, and `StageBlock.he`
(`Proof/CaseAnalysis/FinalStageContracts.lean`) already forces `extra ≥ 56`. -/
def Seed (e : ℕ) (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ) (seedFuel : ℕ → ℕ)
    {ss : ℕ} (seed : Machine (218 + (60 + (e + 23)) + 1) ss) : Prop :=
  ∀ (len : ℕ) (x : BitInput len) (bits : List Bool),
    ∃ junk : ℕ → List Bool,
      (∀ v, 279 ≤ v → v ≤ 300 → junk v = []) ∧ junk (301 + e) = [] ∧
      Step seed (seedFuel len) (fun _ => 0)
        (bank [] [] [] (List.ofFn x) bits (fun _ => []))
        (fun _ => 0)
        (bank [] [] (List.replicate (entryWidth len) true) (List.ofFn x) bits
          (seedTapes (clauseWidth clauseDegree (q len)) junk))

/-! ## §8b `Seed` needs no new machine in the bank's ABI: the dock bridge -/

/-- **From an engine on its OWN layout to `Seed`.**  Any machine whose single
non-blank entry tape is `frame (List.ofFn x)` and whose exit carries the two
unary widths becomes a `Seed` once its input slot is mapped to bank tape `0`,
its driver slot to `218`, its exponent slot to `278`, and every private tape
above `300`.  Nothing about the bank's `218 + (60 + extra) + 1` layout survives
into the hypothesis: `hengine` is stated entirely in `Fin t`.  So what `hpre`
still owes is a LENGTH READER in any layout, not a machine written against the
C10 bank. -/
theorem seed_run_of_engine (e : ℕ) {t s : ℕ} (engine : Machine t s)
    (slots : Fin t → Fin (218 + (60 + (e + 23)) + 1)) (hinj : Function.Injective slots)
    (inSlot driverSlot expSlot : Fin t)
    (hin : (slots inSlot).val = 0) (hdriver : (slots driverSlot).val = 218)
    (hexp : (slots expSlot).val = 278)
    (hprivate : ∀ j, j ≠ inSlot → j ≠ driverSlot → j ≠ expSlot →
      301 ≤ (slots j).val ∧ (slots j).val < 301 + e)
    (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ) (seedFuel : ℕ → ℕ)
    (len : ℕ) (x : BitInput len) (bits : List Bool) (out : Fin t → List Bool)
    (hout0 : out inSlot = frame (List.ofFn x))
    (houtd : out driverSlot = List.replicate (entryWidth len) true)
    (houte : out expSlot = List.replicate (clauseWidth clauseDegree (q len)) true)
    (hstep : Step engine (seedFuel len) (fun _ => 0)
      (fun j => if j = inSlot then frame (List.ofFn x) else []) (fun _ => 0) out) :
    ∃ junk : ℕ → List Bool,
      (∀ v, 279 ≤ v → v ≤ 300 → junk v = []) ∧ junk (301 + e) = [] ∧
      Step (RecoveryFocus.machine slots engine) (seedFuel len) (fun _ => 0)
        (bank [] [] [] (List.ofFn x) bits (fun _ => [])) (fun _ => 0)
        (bank [] [] (List.replicate (entryWidth len) true) (List.ofFn x) bits
          (seedTapes (clauseWidth clauseDegree (q len)) junk)) ∧
      (∀ j : Fin t, junk (slots j).val = out j) := by
  have hentry : ∀ j, bank (t := 218 + (60 + (e + 23)) + 1) [] [] [] (List.ofFn x) bits
      (fun _ => []) (slots j) = (if j = inSlot then frame (List.ofFn x) else []) := by
    intro j
    rw [bank_apply]
    by_cases hj : j = inSlot
    · rw [hj, if_pos rfl]
      unfold bankAt
      rw [if_pos (by rw [hin])]
    · rw [if_neg hj]
      by_cases hd : j = driverSlot
      · rw [hd]
        unfold bankAt
        rw [if_neg (by rw [hdriver]; omega), if_neg (by rw [hdriver]; omega),
          if_neg (by rw [hdriver]; omega), if_neg (by rw [hdriver]; omega),
          if_neg (by rw [hdriver]; omega), if_pos (by rw [hdriver])]
      · by_cases he : j = expSlot
        · rw [he, bankAt_scratch _ _ _ _ _ _ _ (by rw [hexp])]
        · obtain ⟨hlow, _⟩ := hprivate j hj hd he
          rw [bankAt_scratch _ _ _ _ _ _ _ (by omega)]
  have hdock := hstep.dock slots hinj (fun _ => 0)
    (bank [] [] [] (List.ofFn x) bits (fun _ => [])) (fun _ => rfl) hentry
  have himage : ∀ j : Fin t, (slots j).val = 0 ∨ (slots j).val = 218 ∨ (slots j).val = 278 ∨
      (301 ≤ (slots j).val ∧ (slots j).val < 301 + e) := by
    intro j
    by_cases hji : j = inSlot
    · exact Or.inl (by rw [hji]; exact hin)
    · by_cases hjd : j = driverSlot
      · exact Or.inr (Or.inl (by rw [hjd]; exact hdriver))
      · by_cases hje : j = expSlot
        · exact Or.inr (Or.inr (Or.inl (by rw [hje]; exact hexp)))
        · exact Or.inr (Or.inr (Or.inr (hprivate j hji hjd hje)))
  set A := RecoveryRootRound.install slots
    (bank (t := 218 + (60 + (e + 23)) + 1) [] [] [] (List.ofFn x) bits (fun _ => [])) out with hA
  refine ⟨fun v => if h : v < 218 + (60 + (e + 23)) + 1 then A ⟨v, h⟩ else [], ?_, ?_, ?_, ?_⟩
  · intro v h1 h2
    have hne : ∀ j, slots j ≠ (⟨v, by omega⟩ : Fin (218 + (60 + (e + 23)) + 1)) := by
      intro j hj
      have hv : (slots j).val = v := by rw [hj]
      rcases himage j with h | h | h | ⟨ha, hb⟩ <;> omega
    show (if h : v < 218 + (60 + (e + 23)) + 1 then A ⟨v, h⟩ else []) = []
    rw [dif_pos (by omega), hA, RecoveryRootRound.install_other _ _ _ _ hne,
      bank_apply, bankAt_scratch _ _ _ _ _ _ _ (by show (278 : ℕ) ≤ v; omega)]
  · have hne : ∀ j, slots j ≠ (⟨301 + e, by omega⟩ : Fin (218 + (60 + (e + 23)) + 1)) := by
      intro j hj
      have hv : (slots j).val = 301 + e := by rw [hj]
      rcases himage j with h | h | h | ⟨ha, hb⟩ <;> omega
    show (if h : 301 + e < 218 + (60 + (e + 23)) + 1 then A ⟨301 + e, h⟩ else []) = []
    rw [dif_pos (by omega), hA, RecoveryRootRound.install_other _ _ _ _ hne,
      bank_apply, bankAt_scratch _ _ _ _ _ _ _ (by show (278 : ℕ) ≤ 301 + e; omega)]
  · have hfinal : A = bank [] [] (List.replicate (entryWidth len) true) (List.ofFn x) bits
        (seedTapes (clauseWidth clauseDegree (q len))
          (fun v => if h : v < 218 + (60 + (e + 23)) + 1 then A ⟨v, h⟩ else [])) := by
      funext i
      rw [bank_apply]
      by_cases h0 : i.val = 0
      · have hi : slots inSlot = i := Fin.ext (by rw [hin, h0])
        rw [← hi, hA, RecoveryRootRound.install_slot _ hinj, hout0]
        unfold bankAt
        rw [if_pos (show (slots inSlot).val = 0 from hin)]
      · by_cases h218 : i.val = 218
        · have hi : slots driverSlot = i := Fin.ext (by rw [hdriver, h218])
          rw [← hi, hA, RecoveryRootRound.install_slot _ hinj, houtd]
          unfold bankAt
          rw [if_neg (by rw [hdriver]; omega), if_neg (by rw [hdriver]; omega),
            if_neg (by rw [hdriver]; omega), if_neg (by rw [hdriver]; omega),
            if_neg (by rw [hdriver]; omega), if_pos (show (slots driverSlot).val = 218 from hdriver)]
        · by_cases h278 : i.val = 278
          · have hi : slots expSlot = i := Fin.ext (by rw [hexp, h278])
            rw [← hi, hA, RecoveryRootRound.install_slot _ hinj, houte,
              bankAt_scratch _ _ _ _ _ _ _ (by rw [hexp])]
            rw [hexp, seedTapes, if_pos rfl]
          · by_cases hs : 278 ≤ i.val
            · rw [bankAt_scratch _ _ _ _ _ _ _ hs]
              show A i = seedTapes (clauseWidth clauseDegree (q len))
                (fun v => if h : v < 218 + (60 + (e + 23)) + 1 then A ⟨v, h⟩ else []) i.val
              rw [seedTapes, if_neg h278]
              show A i = (if h : i.val < 218 + (60 + (e + 23)) + 1 then A ⟨i.val, h⟩ else [])
              rw [dif_pos i.isLt]
            · have hne : ∀ j, slots j ≠ i := by
                intro j hj
                have hv : (slots j).val = i.val := by rw [hj]
                rcases himage j with h | h | h | ⟨ha, hb⟩ <;> omega
              rw [hA, RecoveryRootRound.install_other _ _ _ _ hne, bank_apply]
              unfold bankAt
              split_ifs <;> rfl
    rw [← hfinal]
    rw [dockH_existing slots (fun _ => 0) (fun _ => 0) (fun _ => rfl)] at hdock
    exact hdock
  · intro j
    change (if h : (slots j).val < 218 + (60 + (e + 23)) + 1
      then A ⟨(slots j).val, h⟩ else []) = out j
    rw [dif_pos (slots j).isLt]
    change A (slots j) = out j
    rw [hA, RecoveryRootRound.install_slot slots hinj]

/-- Original seed interface, forgetting only the retained output relation. -/
theorem seed_of_engine (e : ℕ) {t s : ℕ} (engine : Machine t s)
    (slots : Fin t → Fin (218 + (60 + (e + 23)) + 1)) (hinj : Function.Injective slots)
    (inSlot driverSlot expSlot : Fin t)
    (hin : (slots inSlot).val = 0) (hdriver : (slots driverSlot).val = 218)
    (hexp : (slots expSlot).val = 278)
    (hprivate : ∀ j, j ≠ inSlot → j ≠ driverSlot → j ≠ expSlot →
      301 ≤ (slots j).val ∧ (slots j).val < 301 + e)
    (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ) (seedFuel : ℕ → ℕ)
    (hengine : ∀ (len : ℕ) (x : BitInput len), ∃ out : Fin t → List Bool,
      out inSlot = frame (List.ofFn x) ∧
      out driverSlot = List.replicate (entryWidth len) true ∧
      out expSlot = List.replicate (clauseWidth clauseDegree (q len)) true ∧
      Step engine (seedFuel len) (fun _ => 0)
        (fun j => if j = inSlot then frame (List.ofFn x) else []) (fun _ => 0) out) :
    Seed e entryWidth q clauseDegree seedFuel (RecoveryFocus.machine slots engine) := by
  intro len x bits
  obtain ⟨out, h0, hd, he, hs⟩ := hengine len x
  obtain ⟨junk, hb, hc, hrun, _⟩ := seed_run_of_engine e engine slots hinj
    inSlot driverSlot expSlot hin hdriver hexp hprivate entryWidth q clauseDegree seedFuel
    len x bits out h0 hd he hs
  exact ⟨junk, hb, hc, hrun⟩

/-! ## §9 `Seed` is the ONLY residual: the prologue, assembled -/

/-- The exponentiator's twenty-tape window inside the bank: the exponent on
`278`, the counter word on the loop's own counter tape, the engine's eighteen
private tapes on `279 .. 297`. -/
def envSlots (e : ℕ) (j : Fin 20) : Fin (218 + (60 + (e + 23)) + 1) :=
  ⟨if j.val = 0 then 278 else if j.val = 18 then 301 + e else 278 + j.val, by
    have := j.isLt; split_ifs <;> omega⟩

theorem envSlots_injective (e : ℕ) : Function.Injective (envSlots e) := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  have hv := congrArg Fin.val h
  simp only [envSlots] at hv
  exact Fin.ext (by split_ifs at hv <;> omega)

theorem envSlots_zero (e : ℕ) : (envSlots e 0).val = 278 := rfl

theorem envSlots_eighteen (e : ℕ) : envSlots e 18 = counterTape e := rfl

theorem envSlots_bounds (e : ℕ) (j : Fin 20) (hj : j ≠ 0) :
    278 < (envSlots e j).val ∧ (envSlots e j).val ≠ 300 := by
  have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
  have := j.isLt
  simp only [envSlots]
  split_ifs <;> omega

/-- Every slot of the exponentiator's window other than the exponent lies in the
prologue's own band `279 .. 297`, or IS the loop's counter tape. -/
theorem envSlots_window (e : ℕ) (j : Fin 20) (hj : j ≠ 0) :
    (279 ≤ (envSlots e j).val ∧ (envSlots e j).val ≤ 300) ∨ (envSlots e j).val = 301 + e := by
  have hjv : j.val ≠ 0 := fun h => hj (Fin.ext h)
  have := j.isLt
  simp only [envSlots]
  split_ifs <;> omega

/-- The whole prologue: the seed, the count word, the unary exponentiator, and
the one head bump. -/
noncomputable def prologueMachine (e : ℕ) {ss : ℕ}
    (seed : Machine (218 + (60 + (e + 23)) + 1) ss) :=
  Composition.machine seed
    (Composition.machine (zeroCount e)
      (Composition.machine (CloseoutFinalC10UnaryExpDock.expWordMachine (envSlots e))
        (bumpCounter e)))

/-- The prologue's budget: the seed, then four fixed charges. -/
def prologueFuel (clauseDegree : ℕ) (q seedFuel : ℕ → ℕ) (len : ℕ) : ℕ :=
  seedFuel len + 1 + (4 + 1 +
    ((RepairSource.CloseoutCapacity.Power.budget (clauseWidth clauseDegree (q len)) + 1 +
        RepairSource.ProjectionNormalization.Counter.budget
          (2 ^ clauseWidth clauseDegree (q len))) + 1 + 1))

/-- **`Prologue` from `Seed`.**  Everything between the two unary words and
`call_run`'s `hpre` binder is discharged here: the count word, the docking of
the exponentiator into the `218 + (60 + extra) + 1` bank, the conversion of
`List.replicate (2 ^ r) true` into `CompareMachine.word (2 ^ r)` on the loop's
counter tape, the head bump, and the three bank identities at the junctions.
The residual is exactly `Seed` -- and no weaker statement about it would do,
since `entryWidth` and `q` are arbitrary functions here. -/
theorem prologue_run_of_seed (e : ℕ) (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ) (seedFuel : ℕ → ℕ)
    {ss : ℕ} (seed : Machine (218 + (60 + (e + 23)) + 1) ss)
    (len : ℕ) (x : BitInput len) (bits : List Bool) (junk : ℕ → List Bool)
    (hwindow : ∀ v, 279 ≤ v → v ≤ 300 → junk v = [])
    (hcounter : junk (301 + e) = [])
    (hseedStep : Step seed (seedFuel len) (fun _ => 0)
      (bank [] [] [] (List.ofFn x) bits (fun _ => [])) (fun _ => 0)
      (bank [] [] (List.replicate (entryWidth len) true) (List.ofFn x) bits
        (seedTapes (clauseWidth clauseDegree (q len)) junk))) :
    ∃ w : ℕ → List Bool,
      Step (prologueMachine e seed) (prologueFuel clauseDegree q seedFuel len) (fun _ => 0)
        (bank [] [] [] (List.ofFn x) bits (fun _ => []))
        (Fin.addCases (motive := fun _ => ℕ) (fun _ => 0) (fun _ : Fin 1 => 1))
        (Fin.addCases (motive := fun _ => List Bool)
          (bank [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
            (List.ofFn x) bits w)
          (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree (q len)))) ∧
      (∀ v, 301 ≤ v → v < 301 + e → w v = junk v) := by
  obtain ⟨w2, hzero, hw2⟩ :=
    zeroCount_run e (List.replicate (entryWidth len) true) (List.ofFn x) bits
      (seedTapes (clauseWidth clauseDegree (q len)) junk)
      (by rw [seedTapes, if_neg (by omega)]; exact hwindow 300 (by omega) (by omega))
  obtain ⟨H3, A3, henv, hzero3, _, hcount, hrest3⟩ :=
    CloseoutFinalC10UnaryExpDock.envelopeCounter_dock (m := 218 + (60 + (e + 23)) + 1)
      clauseDegree (q len) (envSlots e) (envSlots_injective e) (fun _ => 0)
      (bank [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
        (List.ofFn x) bits w2) (fun _ => rfl)
      (by rw [bank_apply, envSlots_zero, bankAt_scratch _ _ _ _ _ _ _ (by omega),
          hw2 278 (by omega), seedTapes, if_pos rfl])
      (by
        intro j hj
        obtain ⟨hlow, hne⟩ := envSlots_bounds e j hj
        rw [bank_apply, bankAt_scratch _ _ _ _ _ _ _ (by omega), hw2 _ hne, seedTapes,
          if_neg (by omega)]
        rcases envSlots_window e j hj with h | h
        · exact hwindow _ (by omega) (by omega)
        · rw [h]; exact hcounter)
  have hH3 : H3 = fun _ => 0 := funext hzero3
  refine ⟨fun v => if h : v < 218 + (60 + (e + 23)) + 1 then A3 ⟨v, h⟩ else [], ?_, ?_⟩
  · have hbumped := bumpCounter_run e A3
    rw [← hH3] at hbumped
    have hchain := hseedStep.seq (hzero.seq (henv.seq hbumped))
    have hA3 : A3 = Fin.addCases (motive := fun _ => List Bool)
        (bank [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
          (List.ofFn x) bits
          (fun v => if h : v < 218 + (60 + (e + 23)) + 1 then A3 ⟨v, h⟩ else []))
        (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree (q len))) := by
      funext i
      by_cases hi : i.val = 301 + e
      · have hc : i = counterTape e := Fin.ext hi
        rw [hc, counterTape_natAdd e, Fin.addCases_right, ← counterTape_natAdd e,
          ← envSlots_eighteen e]
        exact hcount
      · have hlt : i.val < 218 + (60 + (e + 23)) := by have := i.isLt; omega
        have hl : i = Fin.castAdd 1 (⟨i.val, hlt⟩ : Fin (218 + (60 + (e + 23)))) := Fin.ext rfl
        have hrhs : Fin.addCases (motive := fun _ => List Bool)
            (bank [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
              (List.ofFn x) bits
              (fun v => if h : v < 218 + (60 + (e + 23)) + 1 then A3 ⟨v, h⟩ else []))
            (fun _ : Fin 1 => CompareMachine.word (2 ^ clauseWidth clauseDegree (q len))) i
            = bankAt [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
              (List.ofFn x) bits
              (fun v => if h : v < 218 + (60 + (e + 23)) + 1 then A3 ⟨v, h⟩ else []) i.val := by
          conv_lhs => rw [hl]
          rw [Fin.addCases_left]
          rfl
        rw [hrhs]
        by_cases h278 : 278 ≤ i.val
        · rw [bankAt_scratch _ _ _ _ _ _ _ h278]
          show A3 i = (if h : i.val < 218 + (60 + (e + 23)) + 1 then A3 ⟨i.val, h⟩ else [])
          rw [dif_pos i.isLt]
        · have hne : ∀ j, envSlots e j ≠ i := by
            intro j hj
            by_cases hj0 : j = 0
            · rw [hj0] at hj
              exact h278 (by rw [← hj, envSlots_zero])
            · obtain ⟨hlow, _⟩ := envSlots_bounds e j hj0
              exact h278 (by rw [← hj]; omega)
          rw [hrest3 i hne, bank_apply]
          unfold bankAt
          split_ifs <;> rfl
    rw [hA3] at hchain
    exact hchain
  · intro v hvlo hvhi
    change (if h : v < 218 + (60 + (e + 23)) + 1 then A3 ⟨v, h⟩ else []) = junk v
    rw [dif_pos (by omega)]
    have hne : ∀ j, envSlots e j ≠ (⟨v, by omega⟩ : Fin (218 + (60 + (e + 23)) + 1)) := by
      intro j hj
      have hv : (envSlots e j).val = v := congrArg Fin.val hj
      by_cases h0 : j = 0
      · rw [h0, envSlots_zero] at hv
        omega
      · rcases envSlots_window e j h0 with h | h <;> omega
    rw [hrest3 _ hne]
    change bankAt [] (CompareMachine.word 0) (List.replicate (entryWidth len) true)
      (List.ofFn x) bits w2 v = junk v
    rw [bankAt_scratch _ _ _ _ _ _ _ (by omega),
      hw2 v (by omega), seedTapes, if_neg (by omega)]

/-- Original prologue interface, forgetting only private scratch preservation. -/
theorem prologue_of_seed (e : ℕ) (entryWidth q : ℕ → ℕ) (clauseDegree : ℕ) (seedFuel : ℕ → ℕ)
    {ss : ℕ} (seed : Machine (218 + (60 + (e + 23)) + 1) ss)
    (hseed : Seed e entryWidth q clauseDegree seedFuel seed) :
    Prologue (e + 23) entryWidth q clauseDegree (prologueFuel clauseDegree q seedFuel)
      (prologueMachine e seed) := by
  intro len x bits
  obtain ⟨junk, hb, hc, hs⟩ := hseed len x bits
  obtain ⟨w, hrun, _⟩ := prologue_run_of_seed e entryWidth q clauseDegree seedFuel seed
    len x bits junk hb hc hs
  exact ⟨w, hrun⟩

end NearCubicWires.RepairSource.CloseoutFinal.C10PrologueUniform
