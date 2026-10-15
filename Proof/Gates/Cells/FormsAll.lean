import Proof.Gates.Cells.FormsV2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine

variable {C : Ctx}

def formsInit : St VV MM :=
  .seq (.op (.rwM sE)) (.seq (.op (.rwM sX)) (.seq (.op (.rwM sZb)) (.seq (.op (.zero fR)) (.op (.copy xB v2)))))

def role1Init : St VV MM := .seq (.op (.inc fR)) (.op (.copy xB gB1))

def formsP : St VV MM :=
  .seq formsInit (.seq setP (.seq roleP (.ite (.eq gRC v2) (.seq role1Init (.seq setP roleP)) skipS)))

def formsT : List (Fin VV) := [fR, xB] ++ setT ++ roleT

def formsMs : List (Fin MM) := [sN, sB, sG, sE, sX, sZb]

theorem flat_one {α : Type} {N : ℕ} (hN : N = 1) (f : Fin N → List α) :
    (List.finRange N).flatMap f = f ⟨0, by omega⟩ := by
  subst hN; simp [List.finRange_succ]

theorem flat_two {α : Type} {N : ℕ} (hN : N = 2) (f : Fin N → List α) :
    (List.finRange N).flatMap f = f ⟨0, by omega⟩ ++ f ⟨1, by omega⟩ := by
  subst hN; simp [List.finRange_succ]

theorem formsInit_spec (a : DS VV MM) (hc : Cst a) :
    Hs C formsInit a (a.rc sE + a.rc sX + a.rc sZb + 10) (fun b => b.env xB = 2 ∧ b.env fR = 0 ∧ b.ram = a.ram ∧
      b.rc sE = 0 ∧ b.rc sX = 0 ∧ b.rc sZb = 0 ∧ Agr a b [sE, sX, sZb] formsT) := by
  have h1 : sX ≠ sE := by decide
  have h2 : sZb ≠ sE := by decide
  have h3 : sZb ≠ sX := by decide
  refine Hs.bseq (hs_rwM C sE a) (by omega) (fun e he => ?_)
  subst he
  refine Hs.bseq (Hs.mono (hs_rwM C sX _) (show (a.rew sE).rc sX + 1 ≤ a.rc sX + 1 by
    simp [DS.rew, Function.update_of_ne h1]) (fun _ h => h)) (by omega) (fun e he => ?_)
  subst he
  refine Hs.bseq (Hs.mono (hs_rwM C sZb _) (show ((a.rew sE).rew sX).rc sZb + 1 ≤ a.rc sZb + 1 by
    simp [DS.rew, Function.update_of_ne h2, Function.update_of_ne h3]) (fun _ h => h)) (by omega) (fun e he => ?_)
  subst he
  refine Hs.bseq (hs_zero C fR _) (by omega) (fun e he => ?_)
  subst he
  refine Hs.mono (hs_copy C xB v2 _ (by decide)) (by omega) ?_
  rintro b rfl
  refine ⟨by vsimp [DS.rew, hc.two], by vsimp [DS.rew], by simp [DS.rew],
    by simp [DS.rew, Function.update_of_ne h1.symm, Function.update_of_ne h2.symm],
    by simp [DS.rew, Function.update_of_ne h3.symm], by simp [DS.rew],
    ⟨fun m hm => by simp [DS.rew], fun m hm => ?_, rfl, rfl, rfl, rfl, rfl, fun y hy => ?_⟩⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hm
    simp [DS.rew, Function.update_of_ne hm.1, Function.update_of_ne hm.2.1, Function.update_of_ne hm.2.2]
  · have h1 : y ≠ fR := fun h => hy (by simp [h, formsT])
    have h2 : y ≠ xB := fun h => hy (by simp [h, formsT])
    vsimp [DS.rew, h1, h2]

theorem role1Init_spec (a : DS VV MM) (h : a.env fR + 1 < 2 ^ C.Wd) :
    Hs C role1Init a 3 (fun b => b.env fR = a.env fR + 1 ∧ b.env xB = a.env gB1 ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
      Agr a b formsMs formsT) := by
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_inc C fR a h) (fun e he => ?_)
  subst he
  refine Hs.mono (hs_copy C xB gB1 _ (by decide)) le_rfl ?_
  rintro b rfl
  refine ⟨by vsimp [], by vsimp [], rfl, rfl,
    (Agr.set _ _ _ (by simp [formsT])).trans (Agr.set _ _ _ (by simp [formsT]))⟩

theorem pairOf_length (z : ℤ) : (pairOf z).length = 2 := rfl

theorem seg_length (J : ℕ) (f : Fin J → ℤ) :
    ((List.finRange J).flatMap fun j => pairOf (f j)).length = 2 * J := by
  rw [List.length_flatMap]
  simp only [pairOf_length]
  rw [List.map_const', List.sum_replicate, List.length_finRange, smul_eq_mul, mul_comm]

/-- What the forms phase assumes of the state. -/
structure FormsPre (c : Call) (p : Params) (wt : Wit c.n) (i : ℕ) (a : DS VV MM) : Prop where
  cst : Cst a
  nram : a.ram sN = cellN c p wt
  zb : a.ram sZb = zbL wt.I i
  n : a.env gN = c.n
  rc : a.env gRC = roleCount c.kind
  J : a.env gJ = p.J
  B1 : a.env gB1 = iG2 (cellN c p wt)
  WS : a.env gWS = iOm (cellN c p wt) + 1 + fld (cellN c p wt) (iOm (cellN c p wt))
  FS : a.env gFS = iPsi (cellN c p wt) + 24 + nPr (cellN c p wt)
  eLen : (a.ram sE).length ≤ (ctrL c p wt (cellOf wt.I i)).length
  xLen : (a.ram sX).length ≤ (kxL c p wt (cellOf wt.I i)).length

end NearCubicGates.Close.Cells
