import Proof.Gates.Cells.GatherSpec
import Proof.Gates.Cells.Gather

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells.GatherPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

section Emit
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I)

/-- The payload width of the gathering records. -/
def gZ : ℕ := valueWidth c p + keyW c p

/-- The digit vector `kappaOf v` reduced mod `q`, as key fields (entry `r·J + j`). -/
noncomputable def kmod (v : List ℕ) (q : ℕ) : List ℕ :=
  List.ofFn fun k : Fin (nDig c p) => (kappaOf c p wt y v (rjOf c p k.val k.isLt) % (q : ℤ)).toNat

/-- The query keys, in `rowVals` order (parts, digit offsets in counter order, primes increasing, `σ ∈ vecs q d`). -/
noncomputable def rowKeys : List ℕ :=
  (parts c).flatMap fun part => (vecsM (List.replicate (nDig c p) (wWin p))).flatMap fun v =>
    (p.primes.sort (· ≤ ·)).flatMap fun q => (vecs q (roleCount c.kind)).map fun σl =>
      reqKey c p (ReqId.residue part q (kmod c p wt y v q) σl)

/-- The table record of a block record. -/
def tabRec (x : ℕ) : ℕ := tRec (gZ c p) (x / 2 ^ valueWidth c p % 2 ^ keyW c p) (x % 2 ^ valueWidth c p)

/-- The padding record (its key `2^keyW` exceeds every request key). -/
def padRec : ℕ := tRec (gZ c p) (2 ^ keyW c p) 0

/-- **The records of the emission** for cell index `i`: table records, tagged queries, padding. -/
noncomputable def emitL (i : ℕ) : List ℕ :=
  (blk c p wt i).map (tabRec c p) ++
    ((rowKeys c p wt (cellOf wt.I i)).zipIdx.map fun e => qRec (gZ c p) e.1 e.2) ++
    List.replicate (CounterMachine.cellN c p wt).length (padRec c p)

end Emit

def EmitGoal (eP : St VV MM) (t : Ctx → Call → Params → ℕ → ℕ) : Prop :=
  ∀ (C : Ctx) {cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (i : ℕ) (a : DS VV MM) (Big : ℕ),
    Spec cT (header c) p → (∃ w, decodeWitness c p w = some wt) → (∃ B1 B2 : ℕ, c.Admitted B1 B2) →
    i < 2 ^ cellBits wt.I → CellTests c p wt (cellOf wt.I i) → GatherPre c p wt i a →
    (∀ x ∈ CounterMachine.cellN c p wt, natBitLength x ≤ Big) → wdNeed c p wt Big ≤ C.Wd →
    ∃ b n, Ex C eP a b n ∧ n ≤ t C c p Big ∧
      (b.ram sG).Perm (emitL c p wt i) ∧
      (b.ram sB).length ≤ gWork c p wt (cellOf wt.I i) ∧
      (∀ m, m ≠ sG → m ≠ sB → b.ram m = a.ram m) ∧
      (∀ m, b.rc m ≤ (b.ram m).length) ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      (∀ x : Fin VV, ¬ gScratch x → b.env x = a.env x)

/-- **The class of the emission cost** (that of `GatherClass`). -/
def EmitClass (t : Ctx → Call → Params → ℕ → ℕ) : Prop :=
  ∃ K e : ℕ, ∀ (C : Ctx) (c : Call) (p : Params) (Big : ℕ),
    t C c p Big ≤ K * ((reqIds c p).length + wWin p ^ nDig c p + 1) * (c.n + Big + C.Wd + 2) ^ e

end NearCubicGates.Close.Cells.GatherPhase
