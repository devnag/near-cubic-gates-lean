import Proof.Gates.CellsGather.Rows

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells.QueryKey

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

/-! ## Interface variables -/

/-- Inputs (set by the caller, read only): `partCode part`, the prime `q`, the digit counter `t`, the residue
counter `s`. -/
def kPC : Fin VV := ⟨70, by decide⟩
def kQ : Fin VV := ⟨71, by decide⟩
def kT : Fin VV := ⟨72, by decide⟩
def kS : Fin VV := ⟨73, by decide⟩
/-- Output: the key. -/
def kKey : Fin VV := ⟨90, by decide⟩

/-- The variables the key program may change. -/
def keyScratch (x : Fin VV) : Prop :=
  (90 ≤ x.val ∧ x.val ≤ 99) ∨ x = t5 ∨ x = t6 ∨ x = t7 ∨ x = t8 ∨ x = t9 ∨ x = c0 ∨ x = vJ

section Q
variable (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I)

/-- **The key of query `(part, t, q, s)`**: digit offsets `v = digitsM (replicate nDig wWin) t`, residues
`σ = digitsM (replicate roleCount q) s`. -/
noncomputable def qKey (part : Option Bool) (t q s : ℕ) : ℕ :=
  reqKey c p (ReqId.residue part q (GatherPhase.kmod c p wt y (digitsM (List.replicate (nDig c p) (wWin p)) t) q)
    (digitsM (List.replicate (roleCount c.kind) q) s))

/-- The query keys in the enumeration order of the query pass. -/
theorem rowKeys_eq : GatherPhase.rowKeys c p wt y =
    (parts c).flatMap fun part => (List.range (wWin p ^ nDig c p)).flatMap fun t =>
      (p.primes.sort (· ≤ ·)).flatMap fun q => (List.range (q ^ roleCount c.kind)).map fun s =>
        qKey c p wt y part t q s := by
  unfold GatherPhase.rowKeys qKey
  rw [vecsM_eq, prod_replicate]
  simp only [vecs_eq_vecsM, vecsM_eq, prod_replicate, List.flatMap_map, List.map_map]
  rfl

end Q

/-- **The state at the start of the key program** (cell `y`, query `(part, t, q, s)`). -/
structure KPre (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (part : Option Bool) (q t s : ℕ)
    (a : DS VV MM) : Prop where
  cst : Cst a
  ctrs : a.ram sE = ctrL c p wt y
  rcE : a.rc sE ≤ (a.ram sE).length
  hE : a.env vHE = p.hE
  J : a.env gJ = p.J
  rc : a.env gRC = roleCount c.kind
  KB : a.env vKB = 2 ^ keyBits p
  pc : a.env kPC = partCode part
  q : a.env kQ = q
  t : a.env kT = t
  s : a.env kS = s

def KeyGoal (kP : St VV MM) (cost : Ctx → Call → Params → ℕ → ℕ) : Prop :=
  ∀ (C : Ctx) {cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (y : Cells wt.I) (a : DS VV MM) (Big : ℕ)
    (part : Option Bool) (q t s : ℕ),
    Spec cT (header c) p → (∃ w, decodeWitness c p w = some wt) → (∃ B1 B2 : ℕ, c.Admitted B1 B2) →
    (∀ x ∈ CounterMachine.cellN c p wt, natBitLength x ≤ Big) → wdNeed c p wt Big ≤ C.Wd →
    part ∈ parts c → q ∈ p.primes.sort (· ≤ ·) → t < wWin p ^ nDig c p → s < q ^ roleCount c.kind →
    KPre c p wt y part q t s a →
    ∃ b n, Ex C kP a b n ∧ n ≤ cost C c p Big ∧
      b.env kKey = qKey c p wt y part t q s ∧
      b.ram = a.ram ∧ (∀ m, m ≠ sE → b.rc m = a.rc m) ∧ b.rc sE ≤ (b.ram sE).length ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      (∀ x : Fin VV, ¬ keyScratch x → b.env x = a.env x)

/-- **The class of the key cost** (per query). -/
def KeyClass (cost : Ctx → Call → Params → ℕ → ℕ) : Prop :=
  ∃ K e : ℕ, ∀ (C : Ctx) (c : Call) (p : Params) (Big : ℕ), cost C c p Big ≤ K * (c.n + Big + C.Wd + 2) ^ e

/-- Sanity: the key program's variables are gathering workspace variables (inside `RecordEmission.qScratch`'s ranges),
disjoint from its inputs. -/
theorem keyScratch_gScratch (x : Fin VV) (h : keyScratch x) : gScratch x := by
  unfold keyScratch at h; unfold gScratch
  rcases h with h | h
  · left; omega
  · right; tauto

theorem inputs_not_keyScratch : ¬ keyScratch kPC ∧ ¬ keyScratch kQ ∧ ¬ keyScratch kT ∧ ¬ keyScratch kS := by
  unfold keyScratch; decide

end NearCubicGates.Close.Cells.QueryKey
