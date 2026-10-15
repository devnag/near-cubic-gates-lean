import Proof.Gates.CellsGatherE.GW

set_option autoImplicit false

namespace NearCubicGates.Close.Cells.RecordEmission

open NearCubicWires NearCubicGates NearCubicGates.Close.Cells NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Counter

def eG2 : Fin VV := ⟨50, by decide⟩

/-- The variables the query pass may change. -/
def qScratch (x : Fin VV) : Prop :=
  (70 ≤ x.val ∧ x.val ≤ 85) ∨ (90 ≤ x.val ∧ x.val ≤ 99) ∨ x = t0 ∨ x = t1 ∨ x = t2 ∨ x = t3 ∨ x = t4 ∨ x = t5 ∨
    x = t6 ∨ x = t7 ∨ x = t8 ∨ x = t9 ∨ x = c0 ∨ x = c1 ∨ x = c2 ∨ x = c3 ∨ x = c4 ∨ x = c5 ∨ x = vJ

/-- The state before the query pass: `a0` is the `GatherPre` state; since then only `sG`, the cursors and the
variables `gScratch` changed, and `eG2 = 2^{gZ}`. -/
structure QPre (c : Call) (p : Params) (wt : Wit c.n) (i : ℕ) (a0 a : DS VV MM) : Prop where
  pre : GatherPre c p wt i a0
  env : ∀ x : Fin VV, ¬ gScratch x → a.env x = a0.env x
  ram : ∀ m, m ≠ sG → a.ram m = a0.ram m
  rcur : ∀ m, a.rc m ≤ (a.ram m).length
  ip : a.ip = a0.ip
  out : a.out = a0.out
  kin : a.kin = a0.kin
  kout : a.kout = a0.kout
  kc : a.kc = a0.kc
  g2 : a.env eG2 = 2 ^ valueWidth c p * 2 ^ keyW c p

/-- The query records of cell `i`, tagged by position. -/
noncomputable def qRecs (c : Call) (p : Params) (wt : Wit c.n) (i : ℕ) : List ℕ :=
  (GatherPhase.rowKeys c p wt (cellOf wt.I i)).zipIdx.map fun e => qRec (GatherPhase.gZ c p) e.1 e.2

def QryGoal (qP : St VV MM) (t : Ctx → Call → Params → ℕ → ℕ) : Prop :=
  ∀ (C : Ctx) {cT : ℕ} (c : Call) (p : Params) (wt : Wit c.n) (i : ℕ) (a0 a : DS VV MM) (Big : ℕ) (S W0 : List ℕ),
    Spec cT (header c) p → (∃ w, decodeWitness c p w = some wt) → (∃ B1 B2 : ℕ, c.Admitted B1 B2) →
    i < 2 ^ cellBits wt.I → CellTests c p wt (cellOf wt.I i) →
    (∀ x ∈ CounterMachine.cellN c p wt, natBitLength x ≤ Big) → wdNeed c p wt Big ≤ C.Wd →
    QPre c p wt i a0 a → GW a S W0 →
    ∃ b n, Ex C qP a b n ∧ n ≤ t C c p Big ∧
      GW b S (W0 ++ qRecs c p wt i) ∧
      (∀ m, m ≠ sG → b.ram m = a.ram m) ∧
      (∀ m, b.rc m ≤ (b.ram m).length) ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧
      (∀ x : Fin VV, ¬ qScratch x → b.env x = a.env x)

/-- **The class of the query-pass cost** (that of `GatherPhase.EmitClass`). -/
def QryClass (t : Ctx → Call → Params → ℕ → ℕ) : Prop :=
  ∃ K e : ℕ, ∀ (C : Ctx) (c : Call) (p : Params) (Big : ℕ),
    t C c p Big ≤ K * ((reqIds c p).length + wWin p ^ nDig c p + 1) * (c.n + Big + C.Wd + 2) ^ e

theorem qScratch_gScratch (x : Fin VV) (h : qScratch x) : gScratch x := by
  unfold qScratch at h; unfold gScratch
  rcases h with h | h | h
  · left; omega
  · left; omega
  · right; exact h

theorem qScratch_val (x : Fin VV) (hq : qScratch x) :
    (70 ≤ x.val ∧ x.val ≤ 85) ∨ (90 ≤ x.val ∧ x.val ≤ 99) ∨ x.val < 20 := by
  rcases hq with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · left; exact h1
  · right; left; exact h1
  all_goals (right; right; subst h1; decide)

theorem not_qScratch_W (x : Fin VV) (h : (50 ≤ x.val ∧ x.val ≤ 69) ∨ (86 ≤ x.val ∧ x.val ≤ 89)) : ¬ qScratch x :=
  fun hq => by have := qScratch_val x hq; omega

end NearCubicGates.Close.Cells.RecordEmission
