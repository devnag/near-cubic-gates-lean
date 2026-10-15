import Proof.Gates.WorkerArith.Classes

set_option autoImplicit false

namespace NearCubicGates.Close.WorkerArith

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming

variable {ns nr : ℕ}

/-- `writeNatM`'s file printing `H k`: `H k`, `H 6 … H 11`, `H 5`. -/
def wIdx (k : Fin 14) : Fin 8 → Fin 14 := ![k, 6, 7, 8, 9, 10, 11, 5]

theorem wIdx_inj (k : Fin 14) (hk : k.val < 5 ∨ k = 12) : Function.Injective (wIdx k) := by
  rcases hk with hk | rfl
  · have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;> decide
  · decide

/-- The `writeNatM` file printing `H k`. -/
def wnR (H : Fin 14 ↪ Fin nr) (k : Fin 14) (hk : k.val < 5 ∨ k = 12) : Fin 8 ↪ Fin nr :=
  ⟨fun i => H (wIdx k i), H.injective.comp (wIdx_inj k hk)⟩

/-- `n` copies of `A` added into `C` (`D` scratch). -/
def dupN (A C D : Fin nr) : ℕ → WM ns nr
  | 0 => .skip
  | n + 1 => .seq (Codec.dupR A C D) (dupN A C D n)

/-- **The I-stream header.** -/
def headerW (VI : Fin (ns + 1)) (H : Fin 14 ↪ Fin nr) : WM ns nr :=
  .seq (writeNatM VI (wnR H 0 (Or.inl (by decide))))
  (.seq (writeNatM VI (wnR H 1 (Or.inl (by decide))))
  (.seq (writeNatM VI (wnR H 2 (Or.inl (by decide))))
  (.seq (writeNatM VI (wnR H 3 (Or.inl (by decide))))
  (.seq (writeNatM VI (wnR H 4 (Or.inl (by decide))))
  (.seq (dupN (H 1) (H 12) (H 13) 10)
  (.seq (writeNatM VI (wnR H 12 (Or.inr rfl))) (WM.clear (H 12))))))))

/-- The header word. -/
def headerWord (q M N rb cl : ℕ) : List Bool :=
  natWord q ++ natWord M ++ natWord N ++ natWord rb ++ natWord cl ++ natWord (10 * M)

/-- The cost class of the header (`S` bounds `q, M, N, rb, cl, 10 M`). -/
def headerCost (S : ℕ) : ℕ := 25000 * (S + 1) ^ 2

def HeaderSpec (cap : ℕ) (VI : Fin (ns + 1)) (H : Fin 14 ↪ Fin nr) (S : ℕ) (σ : WState ns nr) : Prop :=
  σ.sh VI = (σ.st VI).length → (∀ i : Fin 14, 6 ≤ i.val → σ.val (H i) = 0) →
  σ.val (H 0) ≤ S → σ.val (H 2) ≤ S → σ.val (H 3) ≤ S → σ.val (H 4) ≤ S → 10 * σ.val (H 1) ≤ S →
  σ.val (H 5) + 100 * (S + 1) ≤ cap →
  WExec cap (headerW VI H) σ
    (appendO σ VI (H 5) (marks (headerWord (σ.val (H 0)) (σ.val (H 1)) (σ.val (H 2)) (σ.val (H 3)) (σ.val (H 4)))))
    (headerCost S)

/-- **The close.** -/
def closeW (VI : Fin (ns + 1)) (OP : Fin nr) : WM ns nr := emitC VI OP false

def CloseSpec (cap : ℕ) (VI : Fin (ns + 1)) (OP : Fin nr) (σ : WState ns nr) : Prop :=
  σ.sh VI = (σ.st VI).length → σ.val OP < cap → WExec cap (closeW VI OP) σ (appendO σ VI OP [false]) 7

end NearCubicGates.Close.WorkerArith
