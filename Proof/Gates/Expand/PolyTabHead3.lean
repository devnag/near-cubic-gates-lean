import Proof.Gates.Expand.PolyTabHead2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicGates.Close.Expand.PolyTab

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicGates.Close.CounterMachine NearCubicGates.Close.Tabulator NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.TabMachine
open NearCubicWires.RepairRepresentation (natWord)
open StablePartition.Workspace (overlay)
open NearCubicWires.RepairRepresentation

variable (E : ExpandMachine) (a : WilliamsAlgorithm)

noncomputable def phB : WMX (NSx (te E) (Qa a)) NRk :=
  .seq (.seq (initB (sS 0) sS0_ne) st6b) (.seq st7b (.seq vLoop (closeOutX (sS 4) (rX 20))))

/-- The state at the start of phase B. -/
structure BIn (r : TabReq) (g : Fin 64 → ℕ) (ρ : WState (NSx (te E) (Qa a)) NRk) : Prop where
  s0 : ρ.st (sS 0) = frame (tabWord r)
  s0h : ρ.sh (sS 0) = 0
  s2 : ρ.st (sS 2) = frame (termsWord (E.expand ⟨r.V, r.F⟩))
  s2h : ρ.sh (sS 2) = 0
  bl : ∀ x, x ∉ sS 1 :: SA1 E a → ρ.st x = [] ∧ ρ.sh x = 0
  rx : ∀ j, ρ.val (rX j) = g j
  oth : ∀ q, (∀ j, q ≠ rX j) → ρ.val q = 0
  regs : A2Regs E r g

/-- The streams phase B writes. -/
noncomputable def SB : List (Fin (NSx (te E) (Qa a) + 1)) := [sS 0, sS 3, sS 4, sZ 57] ++ List.ofFn ubv

/-- The state after phase B. -/
structure BEnd (r : TabReq) (g : Fin 64 → ℕ) (ρ : WState (NSx (te E) (Qa a)) NRk) (τ : WState (NSx (te E) (Qa a)) NRk) :
    Prop where
  ev : ∃ v : Fin 10 → ℕ, EvV U0 RB (Wk E r + 1) (frame (tabWord r)) (encN (preN r)).length 0 v τ ∧ v 8 = 1 ∧ v 9 = 0
  s4 : τ.st (sS 4) = recStream ((VTn E r).map (binary (Wk E r + 1)))
  s4h : τ.sh (sS 4) = 0
  z57 : τ.st (sZ 57) = recStream ((hsK E r).map (binary (Wk E r + 1)))
  z57h : τ.sh (sZ 57) = 0
  rx : ∀ j : Fin 64, j.val < 52 → j.val ∉ [9, 2, 19, 26, 43, 20, 5] → τ.val (rX j) = g j
  r0 : ∀ j : Fin 64, j.val ∈ [9, 19, 26, 20, 5] → τ.val (rX j) = 0
  fr : SameExcept ρ τ (SB E a) RXL

def capB (r : TabReq) : ℕ :=
  2 * (Wk E r + 1) + 1 + ((preN r).length + 1) * (2 * (Wk E r + 1) + 1) + 4 * (preN r).length + 2 ^ r.k *
    (2 * (Wk E r + 1) + 1) + 2 * (Wk E r + 1) + 10 + (r.V + 1) * ((r.k + r.s + 2) * (2 * (Wk E r + 1) + 1)) +
    4 * (Wk E r + 1) + 40 + r.G * (2 * r.n + 3) + (tabWord r).length + 2 ^ (Lt r + 1) + 8 * (Mh r + 1) ^ 2

noncomputable def phBCost (r : TabReq) : ℕ :=
  ((9 * (initCost (Wk E r + 1) + 1) + (41 * (Wk E r + 1) + 7)) + 1 + tcCost (Wk E r + 1) (preN r)) + 1 +
    ((2 ^ r.k * (hCost (Wk E r + 1) r + 4) + 1 + 1 + (5 * (2 ^ r.k * (2 * (Wk E r + 1) + 1)) + 3)) + 1 +
    ((r.V * (vBlockCost (Wk E r + 1) (preN r).length r.G r.n r.k r.s + 4) + 1) + 1 +
    (5 * (vtRecs (Wk E r + 1) E r r.V).length + 3)))

theorem mem_SA1 (x : Fin (NSx (te E) (Qa a) + 1)) (hx : x ∈ sS 1 :: SA1 E a) :
    x.val = 0 ∨ x.val = 65 ∨ x.val = 66 ∨ x.val = 67 ∨ (105 ≤ x.val ∧ x.val < 106 + te E) := by
  simp only [SA1, List.mem_cons, List.mem_append, List.mem_ofFn, List.not_mem_nil, or_false] at hx
  rcases hx with h | (h | h | h | h | h) | ⟨j, h⟩
  all_goals first
    | (subst h; simp; done)
    | (subst h; simp; omega)
    | (subst h; have := j.isLt; simp; omega)

theorem nSA1_ubv (i : Fin 9) : ubv i ∉ sS 1 :: SA1 E a := fun hm => by
  have := mem_SA1 E a _ hm; simp at this; omega

theorem nSA1_sS (i : Fin 40) (hi : i.val ∉ [0, 1, 2]) : sS i ∉ sS 1 :: SA1 E a := fun hm => by
  have := mem_SA1 E a _ hm; simp at this hi; have := i.isLt; omega

theorem nSA1_sZ (i : Fin 64) : sZ i ∉ sS 1 :: SA1 E a := fun hm => by
  have := mem_SA1 E a _ hm; simp at this; have := i.isLt; omega

theorem Wk_two (r : TabReq) : 2 ≤ Wk E r + 1 := by have := Wk_ge E r; omega

theorem bIn_of (r : TabReq) (τ ρ : WState (NSx (te E) (Qa a)) NRk) (h1 : A1End E a r τ) (g : Fin 64 → ℕ) (i : ℕ)
    (hp : PS τ (sS 1) [] (termsN (E.expand ⟨r.V, r.F⟩)) [false] i g ρ) (hg : A2Regs E r g) : BIn E a r g ρ where
  s0 := by rw [hp.fr.st (by polyTabNe), h1.s0]
  s0h := by rw [hp.fr.sh (by polyTabNe), h1.s0h]
  s2 := by rw [hp.fr.st (by polyTabNe), h1.s2]
  s2h := by rw [hp.fr.sh (by polyTabNe), h1.s2h]
  bl := fun x hx => by
    have hx1 : x ∉ [sS 1] := fun hm => hx (by simp at hm; simp [hm])
    have hx2 : x ∉ SA1 E a := fun hm => hx (List.mem_cons_of_mem _ hm)
    have h0 : x ≠ sI := fun e => hx2 (by rw [e]; simp [SA1])
    have hL : x ≠ sL := fun e => hx2 (by rw [e]; simp [SA1])
    rw [hp.fr.st hx1, hp.fr.sh hx1, h1.fr.st hx2, h1.fr.sh hx2, σI_st E a r x h0 hL, σI_sh]; simp
  rx := hp.x
  oth := fun q hq => by
    have hq' : q ∉ (RXL : List (Fin NRk)) := fun hm => by
      simp only [RXL, List.mem_ofFn] at hm; obtain ⟨j, e⟩ := hm; exact hq j e.symm
    rw [hp.fr.val hq', h1.fr.val hq', σI_val]
  regs := hg

end NearCubicGates.Close.Expand.PolyTab
