import Proof.Packets.PacketsXWalkTimeLoop
import Proof.Packets.PacketsXWalkSampleWord
import Proof.Supplier.SupplierWalkBridge

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.WalkBank
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.SupplierWalk NearCubicWires.SupplierWalkBridge
open Theorem25Completion

/-- **The seed index word**: the walk sample's index in `160n + 2r` bits, low bit first. -/
def seedIndexWord (r n : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)) : List Bool :=
  SignedSortKey.binary (160 * n + 2 * r) (positiveWalkSampleFinEquiv (2 ^ r) n sample).val

/-- At `r = toeplitzWalkSideBits rank` the index word is base's walk-sample word (edge labels, then start vertex). -/
theorem seedIndexWord_eq (rank n : ℕ) (sample : MargulisWalkSample (2 ^ toeplitzWalkSideBits rank) (n + 1)) :
    seedIndexWord (toeplitzWalkSideBits rank) n sample = WalkSampleWord.word rank sample :=
  (WalkSampleWord.binary_eq rank sample).symm

/-- The ports at entry: the bank and the counter blank, the framed index word, the rulers `1^r, 1^n, 1^R, 1^LW`. -/
def inPorts (r n R LW : ℕ) (w : List Bool) : Fin 14 → List Bool :=
  ![[], [], [], [], [], [], [], [], [], frame w, List.replicate r true, List.replicate n true, List.replicate R true,
    List.replicate LW true]

/-- The ports at exit: `WalkTimeLoop.run`'s entry bank and counter, then the inputs kept. -/
def outPorts (r n R LW : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)) : Fin 14 → List Bool :=
  Fin.addCases (m := 9) (n := 5) (motive := fun _ => List Bool)
    (Fin.addCases (m := 8) (n := 1) (motive := fun _ => List Bool) (WalkTimeLoop.A R LW sample [] 0)
      (fun _ => RepairSource.VerifierDecoding.CompareMachine.word n))
    ![frame (seedIndexWord r n sample), List.replicate r true, List.replicate n true, List.replicate R true,
      List.replicate LW true]

/-- The heads at exit: `WalkTimeLoop.run`'s entry heads on the bank and the counter, `0` on the kept inputs. -/
def outHeads (n : ℕ) : Fin 14 → ℕ :=
  Fin.addCases (m := 9) (n := 5) (motive := fun _ => ℕ)
    (Fin.addCases (m := 8) (n := 1) (motive := fun _ => ℕ) (WalkTimeLoop.H n 0) (fun _ => 1)) (fun _ => 0)

/-- The producer's time bound (quadratic in the index word and the rulers). -/
def walkBankCost (r n R LW : ℕ) : ℕ := 1000 * (160 * n + 2 * r + R + LW + 2) ^ 2

/-- **The walk-bank producer**: one machine on `14 + x` tapes; for every walk sample, from the framed index word and
the rulers (every other tape blank, every head at `0`), it halts within `walkBankCost` with `WalkTimeLoop.run`'s entry
bank on ports `0 … 8`, the inputs kept on `9 … 13`, and residues bounded by the cost on the scratch tapes. -/
structure WalkBankProducer where
  x : ℕ
  s : ℕ
  M : Machine (14 + x) s
  run : ∀ (r n R LW : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)), 2 * r + 1 ≤ R → 2 * r + 1 ≤ LW →
    ∃ J : Fin x → List Bool, (∀ j, (J j).length ≤ walkBankCost r n R LW) ∧
      Step M (walkBankCost r n R LW) (fun _ => 0)
        (Fin.addCases (m := 14) (n := x) (motive := fun _ => List Bool) (inPorts r n R LW (seedIndexWord r n sample))
          (fun _ => []))
        (Fin.addCases (m := 14) (n := x) (motive := fun _ => ℕ) (outHeads n) (fun _ => 0))
        (Fin.addCases (m := 14) (n := x) (motive := fun _ => List Bool) (outPorts r n R LW sample) J)

/-- The first nine exit ports are `WalkTimeLoop.run`'s entry tapes. -/
theorem bank_entry (r n R LW : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)) (i : Fin 9) :
    outPorts r n R LW sample (Fin.castAdd 5 i) =
      Fin.addCases (m := 8) (n := 1) (motive := fun _ => List Bool) (WalkTimeLoop.A R LW sample [] 0)
        (fun _ => RepairSource.VerifierDecoding.CompareMachine.word n) i := by
  simp [outPorts]

/-- The first nine exit heads are `WalkTimeLoop.run`'s entry heads. -/
theorem heads_entry (n : ℕ) (i : Fin 9) :
    outHeads n (Fin.castAdd 5 i) =
      Fin.addCases (m := 8) (n := 1) (motive := fun _ => ℕ) (WalkTimeLoop.H n 0) (fun _ => 1) i := by
  simp [outHeads]

/-- The kept index word. -/
theorem index_kept (r n R LW : ℕ) (sample : MargulisWalkSample (2 ^ r) (n + 1)) :
    outPorts r n R LW sample 9 = frame (seedIndexWord r n sample) := rfl

end NearCubicWires.WireExponent3_5.PrimT.WalkBank
