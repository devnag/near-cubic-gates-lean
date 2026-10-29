import SourceAdapters.RAMACSP.GenStageA
import SourceAdapters.ACSP.Affine

/-!
# Printing lists in `FL`: `natWord` of an expression, the neighbor pair

Paper: `def:acsp` ("neighbors `N_ν(X) = a_ν X + b_ν`"), the paragraph "Neighbors" of `app:affine-embedding`
("Every neighbor is a translation `X ↦ X + b` with `b ∈ H`") and `lem:generator` ("It emits the neighbor offsets").

- `emitNatE e`: prints `natWord e` (`emitNatE_spec`); the value of `e` is taken before any scratch changes;
- `pairP e`: prints `pairWord (1, b)`, the neighbor `X + b` as its pair `(a_ν, b_ν) = (1, b)` (`pairP_spec`).
Changed variables: `LW = 50, 51, 52` and the scratch `0 … 19`.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicGates.Adapters.Joins
open NearCubicWires.RepairRepresentation (natWord)

variable {G : Glob}

/-- The variables the printing routines may change: the loop variables `50, 51, 52` and the scratch `0 … 19`. -/
def LW : List Var := (List.finRange NU).filter (fun i => decide (i.val < 20 ∨ (50 ≤ i.val ∧ i.val ≤ 52)))

theorem mem_LW {i : Var} : i ∈ LW ↔ i.val < 20 ∨ (50 ≤ i.val ∧ i.val ≤ 52) := by simp [LW, List.mem_filter]

theorem SW_sub_LW : ∀ x ∈ SW, x ∈ LW := fun x hx => mem_LW.mpr (Or.inl (mem_SW_iff.mp hx))

/-- The states agree on the generator's values (`20 … 49`, `53 … 55`), the field and the read position. -/
def Agree (s t : FS) : Prop := (∀ i : Var, i ∉ LW → t.env i = s.env i) ∧ t.fl = s.fl ∧ t.fp = s.fp

theorem Agree.refl (s : FS) : Agree s s := ⟨fun _ _ => rfl, rfl, rfl⟩

theorem Agree.trans {s t u : FS} (h1 : Agree s t) (h2 : Agree t u) : Agree s u :=
  ⟨fun i hi => (h2.1 i hi).trans (h1.1 i hi), h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem Em.agree {s t : FS} {w : List Bool} (h : Em LW s t w) : Agree s t := ⟨h.env, h.fl, h.fp⟩

theorem Agree.setv {s t : FS} (h : Agree s t) {i : Var} (hi : i ∈ LW) (v : ℕ) : Agree s (t.setv i v) :=
  ⟨fun j hj => by simp [Function.update_of_ne (show j ≠ i from fun e => hj (e ▸ hi)), h.1 j hj], h.2.1, h.2.2⟩

/-! ## `natWord` of an expression -/

/-- Print `natWord e` (the value of `e` at the start). -/
def emitNatE (e : E) : S := .seq (.set 19 e) (emitNatV 19)

theorem emitNatE_spec (s : FS) (e : E) (hL : natBitLength (evalE G s e) + 2 ≤ G.K) (hN : G.K ≤ G.N) :
    Em SW s (evalS G (emitNatE e) s) (natWord (evalE G s e)) := by
  have h1 : Em SW s (s.setv 19 (evalE G s e)) [] := Em.setv s (mem_SW (by decide)) _
  have h2 := emitNatV_spec (G := G) (s.setv 19 (evalE G s e)) 19 (by decide) (by decide) (by simpa using hL) hN
  have := h1.trans (h2.mono (fun x hx => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> exact mem_SW (by decide)))
  show Em SW s (evalS G (emitNatV 19) (s.setv 19 (evalE G s e))) _
  simpa using this

/-- Agreement outside the scratch `0 … 19`. -/
def AgS (s t : FS) : Prop := (∀ i : Var, i ∉ SW → t.env i = s.env i) ∧ t.fl = s.fl ∧ t.fp = s.fp

theorem emAg {s t : FS} {w : List Bool} (h : Em SW s t w) : AgS s t := ⟨h.env, h.fl, h.fp⟩

theorem AgS.trans {s t u : FS} (h1 : AgS s t) (h2 : AgS t u) : AgS s u :=
  ⟨fun i hi => (h2.1 i hi).trans (h1.1 i hi), h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem Em_seq {W : List Var} {a b : S} {s : FS} {w1 w2 : List Bool} (h1 : Em W s (evalS G a s) w1)
    (h2 : Em W (evalS G a s) (evalS G b (evalS G a s)) w2) : Em W s (evalS G (.seq a b) s) (w1 ++ w2) := h1.trans h2

theorem Em_acc {W : List Var} {a b : S} {s : FS} {w1 w2 : List Bool} (h1 : Em W s (evalS G a s) w1)
    (h2 : ∀ t, Em W s t w1 → Em W t (evalS G b t) w2) : Em W s (evalS G (.seq a b) s) (w1 ++ w2) :=
  h1.trans (h2 _ h1)

/-- `natWord c` for a small constant. -/
theorem emitNatK_spec (s : FS) (c : ℕ) (hc : c ≤ G.cap) (hL : natBitLength c + 2 ≤ G.K) (hN : G.K ≤ G.N) :
    Em SW s (evalS G (emitNatE (.k c)) s) (natWord c) := by
  have := emitNatE_spec (G := G) s (.k c) (by rw [eE_k hc]; exact hL) hN
  rwa [eE_k hc] at this

/-! ## The neighbor `X + b` -/

/-- The word of the neighbor `X + b`: its pair `(a_ν, b_ν) = (1, b)` (`Instance.pairWord`). -/
abbrev nbrWord (b : ℕ) : List Bool := ACSP.Affine.Instance.pairWord (1, b)

/-- `pairWord (1, b)`: `natWord 1`, then `natWord b`. -/
def pairP (e : E) : S := .seq (emitNatE (.k 1)) (emitNatE e)

/-- **The neighbor pair is printed.** -/
theorem pairP_spec (s : FS) (e : E) (b : ℕ) (he : ∀ t, AgS s t → evalE G t e = b) (hb : natBitLength b + 2 ≤ G.K)
    (hK : 8 ≤ G.K) (hN : G.K ≤ G.N) :
    Em SW s (evalS G (pairP e) s) (nbrWord b) := by
  have hcap := cap_add G
  have hKl : G.K < 2 ^ G.K := Nat.lt_two_pow_self
  have h1 := emitNatK_spec (G := G) s 1 (by omega) (by have := natBitLength_le 1; omega) hN
  show Em SW s (evalS G (.seq (emitNatE (.k 1)) (emitNatE e)) s) (natWord 1 ++ natWord b)
  refine Em_acc h1 (fun t1 a1 => ?_)
  have ev := he t1 (emAg a1)
  have h2 := emitNatE_spec (G := G) t1 e (by rw [ev]; exact hb) hN
  rw [ev] at h2
  exact h2

end NearCubicGates.Adapters.RAMACSP.Gen
