import Proof.Gates.CellsSys.PrI

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Cells.SystemsPhase

open NearCubicGates.Close.Cells
open NearCubicWires NearCubicGates NearCubicWires.RepairRepresentation
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

/-- The reader's state. -/
structure CS (e : DS VV MM) (Rk : List Bool) (b : DS VV MM) : Prop where
  ram : b.ram = e.ram
  ip : b.ip = e.ip
  out : b.out = e.out
  rcA : b.rc sA = e.rc sA
  rc : RcOK b
  kin : b.kin = []
  kout : b.kout.drop b.kc = Rk
  cst : Cst b
  fr : ∀ x : Fin VV, ¬ FragVar x → x ≠ vCnt → b.env x = e.env x

theorem CS.step {e b b' : DS VV MM} {Rk : List Bool} (h : CS e Rk b) (hs : Same b b') {T : List (Fin VV)}
    (hf : Fr b b' T) (hT : ∀ x ∈ T, FragVar x ∨ x = vCnt) : CS e Rk b' :=
  ⟨hs.ram.trans h.ram, hs.ip.trans h.ip, hs.out.trans h.out, by rw [hs.rc]; exact h.rcA, RcOK.same h.rc hs,
    by rw [hs.kin]; exact h.kin, by rw [hs.kout, hs.kc]; exact h.kout,
    cst_of h.cst hf ⟨fun hm => by rcases hT _ hm with h1 | h1 <;> revert h1 <;> decide,
      fun hm => by rcases hT _ hm with h1 | h1 <;> revert h1 <;> decide,
      fun hm => by rcases hT _ hm with h1 | h1 <;> revert h1 <;> decide⟩,
    fun x hx hc => (hf x (fun hm => by rcases hT x hm with h1 | h1; exact hx h1; exact hc h1)).trans (h.fr x hx hc)⟩

theorem o_kcall (S : SolveMachine) (hK : C.K = Callee.ofSolve S) (s : SysReq) (a : DS VV MM)
    (h : a.kin = sysWord s) (hb : S.budget s ≤ C.Bk) :
    Hs C (.op .kcall) a (1 + C.Lk + C.Bk) (fun b => b = a.called (solveWord (S.solve s))) := by
  obtain ⟨Wd, inp, K, Lk, Bk⟩ := C
  simp only at hK
  subst hK
  exact Hs.op (OpEx.kcall (C := ⟨Wd, inp, Callee.ofSolve S, Lk, Bk⟩) s a h hb) rfl

theorem cs_rd {e b : DS VV MM} {R : List Bool} (v Bw : ℕ) (h : CS e (natWord v ++ R) b) (hb : natBitLength v ≤ Bw)
    (hW : Bw + 2 ≤ C.Wd) :
    Hs C rdNatK b (30 * Bw + 30) (fun b' => b'.env t3 = v ∧ CS e R b' ∧ Fr b b' rdNatT) := by
  refine Hs.mono (rdNatK_spec b h.cst v R h.kout (by omega)) (by omega) ?_
  rintro b' ⟨k1, _, k3, k4, k5⟩
  simp only [Prod.mk.injEq] at k4
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := k4
  refine ⟨k1, ⟨e3.trans h.ram, e1.trans h.ip, e2.trans h.out, by rw [e4]; exact h.rcA,
    fun m => by rw [e4, e3]; exact h.rc m, by rw [e5]; exact h.kin, ?_, cst_of h.cst k5 (by decide),
    fun x hx hc => (k5 x (fun hm => hx (by revert hm; revert x; decide))).trans (h.fr x hx hc)⟩, k5⟩
  rw [e6, k3, ← List.drop_drop, h.kout, List.drop_left]

/-- A record of `sN` by index. -/
theorem cs_fetchN {e b : DS VV MM} {Rk : List Bool} (h : CS e Rk b) (x d : Fin VV)
    (hx0 : x ≠ c0) (hxJ : x ≠ vJ) (hd : FragVar d) (hlt : b.env x < (b.ram sN).length) (hW : b.env x < 2 ^ C.Wd) :
    Hs C (fetch sN x d) b (b.rc sN + 5 * b.env x + 9) (fun b' => b'.env d = (b.ram sN).getD (b.env x) 0 ∧
      CS e Rk b' ∧ Fr b b' [c0, vJ, d]) := by
  refine Hs.mono (o_fetch sN x d hx0 hxJ (by decide) b hlt hW) le_rfl ?_
  rintro b' ⟨f1, f2, f3, f4⟩
  have hT : ∀ z ∈ [c0, vJ, d], FragVar z ∨ z = vCnt := fun z hz => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · left; decide
    · left; decide
    · exact Or.inl hd
  refine ⟨f1, ⟨f3.ram.trans h.ram, f3.ip.trans h.ip, f3.out.trans h.out, by rw [f3.rcA]; exact h.rcA,
    RcOK.fetch h.rc f3 f4 hlt, by rw [f3.kin]; exact h.kin, by rw [f3.kout, f3.kc]; exact h.kout,
    cst_of h.cst f2 ⟨fun hm => by rcases hT _ hm with h1 | h1 <;> revert h1 <;> decide,
      fun hm => by rcases hT _ hm with h1 | h1 <;> revert h1 <;> decide,
      fun hm => by rcases hT _ hm with h1 | h1 <;> revert h1 <;> decide⟩,
    fun z hz hc => (f2 z (fun hm => by rcases hT z hm with h1 | h1; exact hz h1; exact hc h1)).trans
      (h.fr z hz hc)⟩, f2⟩

theorem ratWord_nat (m : ℕ) : ratWord ((m : ℕ) : ℚ) = natWord 0 ++ natWord m ++ natWord 1 := by
  unfold ratWord Interfaces.intWord
  simp

end NearCubicGates.Close.Cells.SystemsPhase
