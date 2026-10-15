import Proof.Assembly.Modes
import Proof.Assembly.Bank
import Proof.MachineModel.Layout
import Proof.MachineModel.ClosureBinaryPool
import Proof.CaseAnalysis.RowsUniversalLowering
import Proof.Supplier.RowThresholdSelections

/-! One physical preparation followed by the native descriptor writer.
The eleven cache fields are outputs of an ordinary machine, never input advice.
The suffix may append private tapes; preparation garbage remains explicit.
Only this immediate composition is implemented here. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.defProp false

namespace CacheComposition
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.SourceInterfaces
open NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.SupplierEstimator NearCubicWires.SupplierPipeline
open NativeRecipes FamilyInitGenerator
open NativeFamilyGenerator PrefixInitializerFront
open PhysicalModeBranches
open P1TopDownPaidReusableReserves P1TopDownPaidBinaryReserves

noncomputable def occurrences (mode : Bool)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) : List (SupportedNormalizedGate q) :=
  if mode then symmetricFourfoldOccurrences
    (⟨q, atoms.map C10NaturalModeAtoms.nativeSymmetricAtom⟩ :
      FourfoldRequest NormalizedSymmetricThresholdCircuit)
  else thresholdFourfoldOccurrences
    (⟨q, atoms.map C10NaturalModeAtoms.nativeThresholdAtom⟩ :
      FourfoldRequest NormalizedThresholdThresholdCircuit)

/-- Ports: live bitmap, complement coordinates, paired children, counts,
absolute offsets, binary-order hardwired pool, lowering atoms, retained top
children (with each arity), residual arity, and the physically computed
policy width/degree. The suffix never evaluates an arbitrary policy function. Empty factors retain framing. -/
noncomputable def cacheWords (sources : EightSources) (mode : Bool) (policy : Policy)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) (L target : Nat) : Fin 11 → List Bool := by
  classical
  let a := decompositionOf sources
  let occ := occurrences mode atoms
  let live := normalizedLiveSet occ L
  let paired := CloseoutRowsUniversal.pool live occ
  let s := liveᶜ.card
  have harity : (s+1)/2+s/2 = liveᶜ.card := by dsimp only [s]; omega
  let top := atoms.map C10NaturalModeAtoms.nativeThresholdAtom
  exact ![
    List.ofFn (fun j : Fin q => decide (j ∈ live)),
    natListWord ((List.finRange q).filterMap
      (fun j => if j ∈ live then none else some j.val)),
    exactListWord (GS a paired),
    natListWord (counts a paired),
    natListWord ((List.range paired.length).map (offset a paired)),
    exactListWord (P1Closure.BinaryPool.pool a live occ s harity),
    (List.range occ.length).flatMap
      (fun code => ExtIncidence.stream (CloseoutRowsUniversal.atomOfCode a live occ code)),
    if mode then [] else natWord top.length ++ top.flatMap
      (fun c => RepairOrdinary.frame (natWord c.top.support.card ++ exactListWord (ThresholdRows.children a c))),
    natWord s,
    natWord (policy.width mode q L target),
    natWord (policy.degree mode q L target)]

structure CacheResult (t : Nat) where
  fuel : Nat
  H : Fin t → Nat
  A : Fin t → List Bool

noncomputable def cachePort (a : WilliamsAlgorithm) (scratch : Nat) (j : Fin 11) :
    Fin (tapes a (7+(11+scratch))) :=
  ⟨r_tapes a+17+j.val, by have hj := j.isLt; unfold tapes; omega⟩

/-- Core ports (including all inputs) are preserved. Other preparation scratch
is not required to be erased or made available for free. -/
noncomputable def CacheReady (sources : EightSources) (mode : Bool) (policy : Policy) (scratch : Nat)
    {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) (L target recordWidth : Nat)
    (r : CacheResult (tapes (williamsOf sources) (7+(11+scratch)))) : Prop :=
  (∀ j : Fin 11, r.H (cachePort (williamsOf sources) scratch j)=0 ∧
    r.A (cachePort (williamsOf sources) scratch j)=cacheWords sources mode policy atoms L target j) ∧
  (∀ j, j.val < r_tapes (williamsOf sources)+17 → r.H j=0 ∧
    r.A j=inputBank (williamsOf sources) (7+(11+scratch))
      (inputOf atoms L target recordWidth mode true) j)

structure Program (sources : EightSources) (mode : Bool) where
  scratch : Nat
  states : Nat
  machine : Machine (tapes (williamsOf sources) (7+(11+scratch))) states
  policy : Policy
  result : Input → CacheResult (tapes (williamsOf sources) (7+(11+scratch)))
  correct : ∀ {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) (L target recordWidth : Nat),
    Admissible sources policy atoms L target recordWidth mode →
    let i := inputOf atoms L target recordWidth mode true
    Step machine (result i).fuel (fun _=>0)
      (inputBank (williamsOf sources) (7+(11+scratch)) i) (result i).H (result i).A ∧
    CacheReady sources mode policy scratch atoms L target recordWidth (result i)

noncomputable def embedding {sources : EightSources} {mode : Bool}
    (a : Program sources mode) (extra : Nat) :=
  slots (williamsOf sources) (11+a.scratch) (11+a.scratch+extra) (by omega)

theorem embedding_injective {sources : EightSources} {mode : Bool}
    (a : Program sources mode) (extra : Nat) : Function.Injective (embedding a extra) := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin (tapes (williamsOf sources) (7+(11+a.scratch+extra))) => k.val) h

theorem inputBank_slots (printer : WilliamsAlgorithm) (small large : Nat)
    (h : small ≤ large) (i : Input) :
    ∀ j, inputBank printer (7+large) i (slots printer small large h j) =
      inputBank printer (7+small) i j := by
  unfold inputBank slots tapes
  dsimp only [id]
  with_reducible exact (BankExtension.bank_extend (r_tapes printer) small large h (inputWords i))

noncomputable def middleH {sources : EightSources} {mode : Bool}
    (a : Program sources mode) (extra : Nat) (i : Input) :=
  dockH (embedding a extra) (fun _=>0) (a.result i).H

noncomputable def middleA {sources : EightSources} {mode : Bool}
    (a : Program sources mode) (extra : Nat) (i : Input) :=
  install (embedding a extra)
    (inputBank (williamsOf sources) (7+(11+a.scratch+extra)) i) (a.result i).A

structure SuffixCode {sources : EightSources} {mode : Bool} (a : Program sources mode) where
  extra : Nat
  states : Nat
  machine : Machine (tapes (williamsOf sources) (7+(11+a.scratch+extra))) states
  result : Input → Result (tapes (williamsOf sources) (7+(11+a.scratch+extra)))

noncomputable def SuffixCode.fixed {sources : EightSources} {mode : Bool}
    {a : Program sources mode} (b : SuffixCode a) : Fixed (williamsOf sources) :=
  { scratch := 11+a.scratch+b.extra, states := b.states, machine := b.machine,
    policy := a.policy, result := b.result }

structure Suffix {sources : EightSources} {mode : Bool} (a : Program sources mode) where
  code : SuffixCode a
  correct : ∀ {q : Nat} {circuit : BooleanCircuit q} {pcpp : PointwisePCPP circuit}
    (atoms : List (C10TotalDecode.Atom pcpp)) (L target recordWidth : Nat),
    Admissible sources a.policy atoms L target recordWidth mode →
    let i := inputOf atoms L target recordWidth mode true
    CacheReady sources mode a.policy a.scratch atoms L target recordWidth (a.result i) →
    let r := code.result i
    Step code.machine r.fuel (middleH a code.extra i) (middleA a code.extra i) r.H r.A ∧
    PrefixReady code.fixed.code i ∧
    NativeRows sources L target mode atoms (williamsOf sources) r.S r.R r.B
      r.rowWidth r.ds r.total r.denominator ∧
    r.rowWidth ≤ recordWidth ∧ r.total < 2^recordWidth

noncomputable def assemble {sources : EightSources} {mode : Bool}
    (a : Program sources mode) (b : Suffix a) : Fixed (williamsOf sources) :=
  { scratch := 11+a.scratch+b.code.extra
    states := _
    machine := Composition.machine
      (RecoveryFocus.machine (embedding a b.code.extra) a.machine) b.code.machine
    policy := a.policy
    result := fun i => { b.code.result i with
      fuel := (a.result i).fuel+1+(b.code.result i).fuel } }

noncomputable def mode {sources : EightSources} {m : Bool}
    (a : Program sources m) (b : Suffix a) : Mode sources m := by
  refine ⟨assemble a b, ?_⟩
  intro q circuit pcpp atoms L target recordWidth hadm
  let i := inputOf atoms L target recordWidth m true
  obtain ⟨hrun, hcache⟩ := a.correct atoms L target recordWidth hadm
  obtain ⟨hsuffix, hready, hrows, hwidth, htotal⟩ :=
    b.correct atoms L target recordWidth hadm hcache
  have hwide := hrun.dock (embedding a b.code.extra) (embedding_injective a b.code.extra)
    (fun _=>0) (inputBank (williamsOf sources) (7+(11+a.scratch+b.code.extra)) i)
    (fun _=>rfl) (inputBank_slots (williamsOf sources) _ _ (by omega) i)
  exact ⟨⟨hwide.seq hsuffix, hready⟩, hrows, hwidth, htotal⟩

abbrev GlobalProgram (mode : Bool) := (sources : EightSources) → (gamma : Real) →
  (hg : 0<gamma) → (hh : gamma<1/2) → (p : Parameters sources gamma) → Program sources mode

abbrev GlobalSuffix {m : Bool} (a : GlobalProgram m) :=
  (sources : EightSources) → (gamma : Real) → (hg : 0<gamma) → (hh : gamma<1/2) →
  (p : Parameters sources gamma) → Suffix (a sources gamma hg hh p)

noncomputable def global {m : Bool} (a : GlobalProgram m) (b : GlobalSuffix a) : GlobalMode m :=
  fun sources gamma hg hh p => mode (a sources gamma hg hh p) (b sources gamma hg hh p)

/-- Both modes use this one preparation implementation family. The row suffix
builder is uniform in the chosen preparation machine and may append its own
scratch, so its construction does not wait for preparation's code choice. -/
abbrev GlobalPreparation := (m : Bool) → GlobalProgram m
abbrev SuffixBuilder (m : Bool) := (a : GlobalProgram m) → GlobalSuffix a

noncomputable def symmetric (a : GlobalPreparation) (b : SuffixBuilder true) :
    GlobalMode true := global (a true) (b (a true))

end CacheComposition
