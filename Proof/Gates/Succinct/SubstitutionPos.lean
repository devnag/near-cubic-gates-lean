import Proof.Gates.Succinct.SubstitutionRead

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms

variable {ns nr : ℕ}

/-- The image formula on a flag list. -/
def posF (fl : List Bool) (c n1 ob : ℕ) : ℕ :=
  1 + c + (fl.take c).count true * n1 + if fl.getD c false then ob else 0

theorem count_take_succ (fl : List Bool) (j : ℕ) :
    (fl.take (j + 1)).count true = (fl.take j).count true + if fl.getD j false then 1 else 0 := by
  rcases Nat.lt_or_ge j fl.length with hj | hj
  · rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.count_append]
    simp [List.getD_eq_getElem?_getD, hj, List.count_singleton]
  · rw [List.take_of_length_le (by omega), List.take_of_length_le hj]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : fl.length ≤ j)]

def posW (OF : Fin (ns + 1)) (X P SC SB NB1 OB T : Fin nr) : WM ns nr :=
  .seq (addTo X P T) (.seq (.inc P) (.seq (addTo X SC T)
    (.seq (.whr SC (.seq (.dec SC) (.seq (.ifs OF (addTo NB1 P T) .skip) (.seq (.fwd OF) (.inc SB)))))
    (.seq (.ifs OF (addTo OB P T) .skip) (WM.rewind OF SB)))))

/-- The cost class of one image. -/
def posCost (c n1 ob : ℕ) : ℕ := c * (18 * n1 + 70) + 18 * ob + 40

set_option hygiene false in
/-- The register disequalities of `posW`. -/
local macro "psimp" : tactic => `(tactic| simp [Function.update_apply, x1, x2, x3, x4, x5, x6, p1, p2, p3, p4, p5, s1, s2, s3, s4, b1, b2, b3, n1', n2', o1, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm p1, Ne.symm p2, Ne.symm p3, Ne.symm p4, Ne.symm p5, Ne.symm s1, Ne.symm s2, Ne.symm s3, Ne.symm s4, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm n1', Ne.symm n2', Ne.symm o1])

set_option hygiene false in
/-- `psimp` with extra facts. -/
local macro "psimp" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp [Function.update_apply, x1, x2, x3, x4, x5, x6, p1, p2, p3, p4, p5, s1, s2, s3, s4, b1, b2, b3, n1', n2', o1, Ne.symm x1, Ne.symm x2, Ne.symm x3, Ne.symm x4, Ne.symm x5, Ne.symm x6, Ne.symm p1, Ne.symm p2, Ne.symm p3, Ne.symm p4, Ne.symm p5, Ne.symm s1, Ne.symm s2, Ne.symm s3, Ne.symm s4, Ne.symm b1, Ne.symm b2, Ne.symm b3, Ne.symm n1', Ne.symm n2', Ne.symm o1, $ts,*])

theorem posW_spec (cap : ℕ) (OF : Fin (ns + 1)) (X P SC SB NB1 OB T : Fin nr) (hR : [X, P, SC, SB, NB1, OB, T].Nodup)
    (σ : WState ns nr) (fl : List Bool) (hOF : σ.st OF = fl) (hOFh : σ.sh OF = 0)
    (hP : σ.val P = 0) (hSC : σ.val SC = 0) (hSB : σ.val SB = 0) (hT : σ.val T = 0)
    (hcap : posF fl (σ.val X) (σ.val NB1) (σ.val OB) + σ.val X * σ.val NB1 + σ.val NB1 + 2 * σ.val X + 2 ≤ cap) :
    WExec cap (posW OF X P SC SB NB1 OB T) σ (σ.setv P (posF fl (σ.val X) (σ.val NB1) (σ.val OB)))
      (posCost (σ.val X) (σ.val NB1) (σ.val OB)) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, not_false_eq_true, List.nodup_nil,
    and_true] at hR
  obtain ⟨⟨x1, x2, x3, x4, x5, x6⟩, ⟨p1, p2, p3, p4, p5⟩, ⟨s1, s2, s3, s4⟩, ⟨b1, b2, b3⟩, ⟨n1', n2'⟩, o1⟩ := hR
  generalize hc : σ.val X = c at hcap ⊢
  generalize hn : σ.val NB1 = n1 at hcap ⊢
  generalize ho : σ.val OB = ob at hcap ⊢
  have hcnt : ∀ j, (fl.take j).count true ≤ j := fun j => (List.count_le_length).trans (by simp)
  have hpf : 1 + c + (fl.take c).count true * n1 ≤ posF fl c n1 ob := by unfold posF; omega
  have hkn : (fl.take c).count true * n1 ≤ c * n1 := Nat.mul_le_mul_right _ (hcnt c)
  -- `P := 1 + c`, `SC := c`
  have e1 := addTo_spec cap X P T x1 x6 p5 σ hT (by omega) (by omega)
  rw [hc, hP, Nat.zero_add] at e1
  have e2 := WExec.inc (cap := cap) P (σ.setv P c) (by simp; omega)
  rw [show (σ.setv P c).setv P ((σ.setv P c).val P + 1) = σ.setv P (c + 1) by simp [wsetv_setv]] at e2
  have e3 := addTo_spec cap X SC T x2 x6 s4 (σ.setv P (c + 1)) (by psimp [hT]) (by psimp [hc]; omega)
    (by psimp [hSC, hc]; omega)
  rw [show (σ.setv P (c + 1)).val SC + (σ.setv P (c + 1)).val X = c by psimp [hSC, hc],
    show (σ.setv P (c + 1)).val X = c by psimp [hc]] at e3
  -- the scan
  let S : ℕ → WState ns nr := fun j =>
    (((σ.setv P (1 + c + (fl.take j).count true * n1)).setv SC (c - j)).setv SB j).seth OF j
  have hS0 : S 0 = (σ.setv P (c + 1)).setv SC c := by
    refine WState.eq ?_ rfl ?_ rfl
    · funext y; by_cases hy : y = OF
      · rw [hy]; simp [S, hOFh]
      · simp [S, Function.update_apply, hy]
    · funext r; by_cases hrB : r = SB
      · rw [hrB]; psimp [S, hSB]
      · by_cases hrS : r = SC
        · rw [hrS]; psimp [S]
        · by_cases hrP : r = P
          · rw [hrP]; psimp [S]; omega
          · psimp [S, hrB, hrS, hrP]
  have e4 := UnionMachine.Round.wloop cap SC
    (.seq (.ifs OF (addTo NB1 P T) .skip) (.seq (.fwd OF) (.inc SB))) (18 * n1 + 12) c S
    (fun j _ => by psimp [S]) (by omega)
    (fun j hj => by
      set τ := (S j).setv SC (c - j - 1) with hτ
      set b := fl.getD j false with hb
      have hbit : wbit τ OF = b := by
        simp [wbit, τ, S, hOF, readTapeBit, hb]
      have hcj := hcnt j
      have hkj : (fl.take j).count true * n1 ≤ c * n1 := Nat.mul_le_mul_right _ (by omega)
      have hk1 : (fl.take (j + 1)).count true * n1 ≤ c * n1 := Nat.mul_le_mul_right _ (by have := hcnt (j + 1); omega)
      have hτP : τ.val P = 1 + c + (fl.take j).count true * n1 := by psimp [τ, S]
      have hτN : τ.val NB1 = n1 := by psimp [τ, S, hn]
      have hτT : τ.val T = 0 := by psimp [τ, S, hT]
      have e5 : WExec cap (.ifs OF (addTo NB1 P T) .skip) τ
          (τ.setv P (1 + c + (fl.take (j + 1)).count true * n1)) (18 * n1 + 4) := by
        rw [count_take_succ, ← hb]
        cases hbv : b
        · refine WExec.mono (WExec.cast cap (WExec.ifsF (by rw [hbit, hbv]) (WExec.skip τ)) ?_ le_rfl) (by omega)
          simp only [Bool.false_eq_true, if_false, Nat.add_zero]
          rw [← hτP]; simp [wsetv_same]
        · have ea := addTo_spec cap NB1 P T (Ne.symm p3) n2' p5 τ hτT (by rw [hτN]; omega)
            (by rw [hτN, hτP]; omega)
          refine WExec.mono (WExec.cast cap (WExec.ifsT (by rw [hbit, hbv]) ea) ?_ le_rfl) (by rw [hτN]; try omega)
          rw [hτP, hτN]; congr 1; simp; ring
      have e6 := WExec.fwd (cap := cap) OF (τ.setv P (1 + c + (fl.take (j + 1)).count true * n1))
      have e7 := WExec.inc (cap := cap) SB ((τ.setv P (1 + c + (fl.take (j + 1)).count true * n1)).seth OF
        ((τ.setv P (1 + c + (fl.take (j + 1)).count true * n1)).sh OF + 1)) (by psimp [τ, S]; omega)
      refine WExec.mono (WExec.cast cap (WExec.seq e5 (WExec.seq e6 e7)) ?_ le_rfl) (by omega)
      refine WState.eq ?_ rfl ?_ rfl
      · funext y; by_cases hy : y = OF
        · rw [hy]; simp [τ, S]
        · simp [τ, S, Function.update_apply, hy]
      · funext r; by_cases hrB : r = SB
        · rw [hrB]; psimp [τ, S]
        · by_cases hrS : r = SC
          · rw [hrS]; psimp [τ, S]; omega
          · by_cases hrP : r = P
            · rw [hrP]; psimp [τ, S]
            · psimp [τ, S, hrB, hrS, hrP])
  rw [hS0] at e4
  -- the flag of `c` itself
  set τ8 := S c with hτ8
  have hbit8 : wbit τ8 OF = fl.getD c false := by simp [wbit, τ8, S, hOF, readTapeBit]
  have hP8 : τ8.val P = 1 + c + (fl.take c).count true * n1 := by psimp [τ8, S]
  have hO8 : τ8.val OB = ob := by psimp [τ8, S, ho]
  have hT8 : τ8.val T = 0 := by psimp [τ8, S, hT]
  have e8 : WExec cap (.ifs OF (addTo OB P T) .skip) τ8 (τ8.setv P (posF fl c n1 ob)) (18 * ob + 4) := by
    unfold posF
    cases hbv : fl.getD c false
    · refine WExec.mono (WExec.cast cap (WExec.ifsF (by rw [hbit8, hbv]) (WExec.skip τ8)) ?_ le_rfl) (by omega)
      rw [← hP8]; simp [wsetv_same]
    · have hpos : posF fl c n1 ob = 1 + c + (fl.take c).count true * n1 + ob := by unfold posF; rw [hbv]; simp
      have ea := addTo_spec cap OB P T (Ne.symm p4) o1 p5 τ8 hT8 (by rw [hO8]; omega)
        (by rw [hO8, hP8]; omega)
      refine WExec.mono (WExec.cast cap (WExec.ifsT (by rw [hbit8, hbv]) ea) ?_ le_rfl) (by rw [hO8])
      rw [hP8, hO8]; simp
  have e9 := wrewind_spec cap OF SB c (τ8.setv P (posF fl c n1 ob)) (by psimp [τ8, S]) (by psimp [τ8, S]; omega)
  refine WExec.mono (WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e8 e9))))) ?_
    le_rfl) ?_
  · refine WState.eq ?_ rfl ?_ rfl
    · funext y; by_cases hy : y = OF
      · rw [hy]; simp [τ8, S, hOFh]
      · simp [τ8, S, Function.update_apply, hy]
    · funext r; by_cases hrB : r = SB
      · rw [hrB]; psimp [τ8, S, hSB]
      · by_cases hrS : r = SC
        · rw [hrS]; psimp [τ8, S, hSC]
        · by_cases hrP : r = P
          · rw [hrP]; psimp [τ8, S]
          · psimp [τ8, S, hrB, hrS, hrP]
  · unfold posCost
    rw [show c * (18 * n1 + 70) = c * (18 * n1 + 12 + 4) + 54 * c by ring]
    omega

end NearCubicGates.Close.Succinct
