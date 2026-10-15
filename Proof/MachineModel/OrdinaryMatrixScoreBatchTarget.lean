import Proof.MachineModel.OrdinaryMatrixScoreBatchCodec

/-! Local implementation targets, not source assumptions. No inhabitant of
these targets is supplied here. Every reusable invocation admits arbitrary
bounded old workspace and must return bounded workspace with local heads0;
empty workspace is the cold specialization. -/
namespace NearCubicWires.RepairOrdinary.MatrixScoreBatch
open LocalBitMultitape SupplierPrinter SignedSortKey RepairRepresentation SourceInterfaces
open WilliamsProductCertificate
open WilliamsLoaderForms (encodedNatCellTape rowMajorBitMatrix)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def reusableEntry (p : Program) (source : List Bool) (position : ℕ)
    (out : List Bool) (scratch : Fin p.tapeCount → List Bool) : Configuration p.tapeCount p.stateCount :=
  ⟨p.machine.start,fun i => if i.val=0 then position else if i=p.outputTape then out.length else 0,
    fun i => if i.val=0 then source else if i=p.outputTape then out else scratch i⟩

/-- This input cursor advances past the complete physical outer frame; global
prefix/suffix data are untouched. Clearing, resizing and resetting source-call
scratch is part of this run, not a promise made by the Williams import. -/
def ReusableTarget {R : Type} (p : Program) (input output : R → List Bool)
    (time workCapacity : R → ℕ) : Prop :=
  ∀ r pre suffix out scratch,
    (∀ i : Fin p.tapeCount,i.val≠0 → i≠p.outputTape → (scratch i).length≤workCapacity r) →
    ∃ actual : ExecutionReceipt p.tapeCount p.stateCount,
      runFrom p.machine (time r)
        (reusableEntry p (pre++frame (input r)++suffix) pre.length out scratch)=some actual ∧
      actual.final.tapes ⟨0,by have h:=p.twoTapes; omega⟩=pre++frame (input r)++suffix ∧
      actual.final.heads ⟨0,by have h:=p.twoTapes; omega⟩=pre.length+(frame (input r)).length ∧
      actual.final.tapes p.outputTape=out++output r ∧
      actual.final.heads p.outputTape=(out++output r).length ∧
      (∀ i : Fin p.tapeCount,i.val≠0 → i≠p.outputTape →
        actual.final.heads i=0 ∧ (actual.final.tapes i).length≤workCapacity r) ∧
      actual.steps≤time r

def gateWord (r : Request) (gate : Fin r.Gates) : List Bool :=
  natWord r.d++natWord r.p++cutWord r.p (r.cuts.get gate)
def gateRecords (r : Request) (gate : Fin r.Gates) : List Bool :=
  StablePartition.stream (DominanceSort.records r.S r.M (leftScore r) (rightScore r) gate)

/-- The upstream caller must prove this equality for the actual split it
produces. For odd original residual arity, a separate paid ignored-coordinate
pad/crop supplier or proved parity-adjusted live count is required. -/
def ResidualShape (residual : ℕ) (r : Request) : Prop := residual=2*r.d

/-- First enclosing implementation obligation: a raw cut, including its d/p
headers, produces all 2U score/id records. The batch parent must physically
extract this cut and supply the two copied headers. -/
structure ScoreGenerator where
  program : Program
  coefficient : ℕ
  exponent : ℕ
  coefficientPositive : 0<coefficient
  runs : ReusableTarget program
    (fun x : Σ r : Request,Fin r.Gates => gateWord x.1 x.2)
    (fun x : Σ r : Request,Fin r.Gates => gateRecords x.1 x.2)
    (fun x => coefficient*(x.1.U+1)*(x.1.d+x.1.p+1)^exponent)
    (fun x => coefficient*(x.1.U+1)*(x.1.d+x.1.p+1)^exponent)

def signedLeft (r : Request) := padSignedInner (Capacity := r.Capacity)
  (reindexedLaterBucketLeft (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize) (weight r))
def booleanRight (r : Request) := padBooleanInner (Capacity := r.Capacity)
  (reindexedLaterBucketRight (stableBucketedDominanceLayout (leftScore r) (rightScore r) r.bucketSize))
def planeCounts (r : Request) (negative : Bool) (bit : ℕ) : List Bool :=
  encodedNatCellTape (natBitLength r.U) (rowMajorNatMatrix (integerMatrixProduct
    (fun row inner => LeftPlaneCell.coefficientBit negative (signedLeft r row inner) bit) (booleanRight r)))
def factor (bit : ℕ) : List Bool := frame (List.replicate bit false++[true])
/-- The physical interface to the P4 U²-cell pass. A sequential packet loader
must establish this predicate, including the count cursor and all three
driver heads; it is not supplied by a semantic packet equality. -/
def PlaneBoundary {t s : ℕ} (c : Configuration t s) (r : Request) (W : ℕ)
    (negative : Bool) (bit : ℕ) (countTape signTape factorTape widthTape : Fin t) : Prop :=
  c.tapes countTape=planeCounts r negative bit ∧ c.heads countTape=0 ∧
  c.tapes signTape=[negative] ∧ c.heads signTape=0 ∧
  c.tapes factorTape=factor bit ∧ c.heads factorTape=0 ∧
  c.tapes widthTape=List.replicate W true ∧ c.heads widthTape=0

def PlaneDriversRetained {t s : ℕ} (before after : Configuration t s)
    (signTape factorTape widthTape : Fin t) : Prop :=
  ∀ i,i=signTape ∨ i=factorTape ∨ i=widthTape →
    after.tapes i=before.tapes i ∧ after.heads i=before.heads i
/-- Each packet has one sign bit, one framed factor, then exactly U² raw
native-width counts. Zero counts are present, in unchanged row-major order. -/
def packet (r : Request) (negative : Bool) (bit : ℕ) : List Bool :=
  [negative]++factor bit++planeCounts r negative bit
def output (r : Request) : List Bool := (List.range r.p).flatMap
  (fun bit => packet r false bit++packet r true bit)

/-- Full raw-block scheduler target. Its construction must run the corrected
source, and physically initialize/reuse all source output and scratch. -/
structure Scheduler (source : WilliamsAlgorithm) where
  program : Program
  coefficient : ℕ
  exponent : ℕ
  coefficientPositive : 0<coefficient
  sourceExponentPaid : source.logExponent≤exponent
  runs : ReusableTarget program word output
    (fun r => coefficient*(r.U+1)^2*(r.d+r.p+1)^exponent)
    (fun r => coefficient*(r.U+1)^2*(r.d+r.p+1)^exponent)

theorem planeCounts_length (r : Request) (negative : Bool) (bit : ℕ) :
    (planeCounts r negative bit).length=r.U^2*natBitLength r.U := by
  simp [planeCounts,encodedNatCellTape,WilliamsLoaderForms.fixedWidthNatBits,
    List.length_flatMap,rowMajorNatMatrix_length,pow_two]

theorem cold_entry (p : Program) (bs : List Bool) :
    reusableEntry p (frame bs) 0 [] (fun _ => [])=
      ⟨p.machine.start,fun _ => 0,p.inputTapes bs⟩ := by
  apply configuration_ext
  · rfl
  · funext i; simp [reusableEntry]
  · funext i; simp [reusableEntry,Program.inputTapes]

end NearCubicWires.RepairOrdinary.MatrixScoreBatch
