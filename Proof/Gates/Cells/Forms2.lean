import Proof.Gates.Cells.Forms
import Proof.Gates.Cells.SysSpec

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter
open NearCubicGates.Close.CounterMachine (gateN intN)

variable {C : Ctx}

/-! ## Normalising a signed pair -/

/-- `(x, y) := pairOf (x − y)`. -/
def normP (x y : Fin VV) : St VV MM :=
  .ite (.lt y x) (.seq (.op (.sub x y)) (.op (.zero y))) (.seq (.op (.sub y x)) (.op (.zero x)))

theorem normP_spec (x y : Fin VV) (hxy : x ≠ y) (a : DS VV MM) :
    Hs C (normP x y) a 4 (fun b => [b.env x, b.env y] = pairOf ((a.env x : ℤ) - a.env y) ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ b.kin = a.kin ∧ b.kout = a.kout ∧
      b.kc = a.kc ∧ Fr a b [x, y]) := by
  refine Hs.ite (show y ≠ x from Ne.symm hxy) (fun h => ?_) (fun h => ?_)
  · simp only [Cnd.eval, decide_eq_true_eq] at h
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_sub C x y a hxy (by omega)) (fun e he => ?_)
    subst he
    refine Hs.mono (hs_zero C y _) le_rfl ?_
    rintro b rfl
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Fr.trans (Fr.set a _ (by simp)) (Fr.set _ _ (by simp))⟩
    simp only [DS.set_env_self, DS.set_env_ne _ _ hxy, pairOf]
    congr 1
    · omega
    · congr 1; omega
  · simp only [Cnd.eval, decide_eq_false_iff_not, not_lt] at h
    refine Hs.seq (t1 := 1) (t2 := 1) (hs_sub C y x a (Ne.symm hxy) h) (fun e he => ?_)
    subst he
    refine Hs.mono (hs_zero C x _) le_rfl ?_
    rintro b rfl
    refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Fr.trans (Fr.set a _ (by simp)) (Fr.set _ _ (by simp))⟩
    simp only [DS.set_env_self, DS.set_env_ne _ _ (Ne.symm hxy), pairOf]
    congr 1
    · omega
    · congr 1; omega

/-! ## List helpers -/

theorem flatMap_range_succ (f : ℕ → List ℕ) (k : ℕ) :
    (List.range (k + 1)).flatMap f = (List.range k).flatMap f ++ f k := by
  rw [List.range_succ, List.flatMap_append]; simp

theorem drop_flatMap_range (f : ℕ → List ℕ) (k J : ℕ) (hk : k < J) (R : List ℕ) :
    ((List.range J).flatMap f ++ R).drop ((List.range k).flatMap f).length =
      f k ++ ((List.range J).flatMap f ++ R).drop ((List.range (k + 1)).flatMap f).length := by
  obtain ⟨d, rfl⟩ : ∃ d, J = k + 1 + d := ⟨J - (k + 1), by omega⟩
  rw [List.range_add, List.flatMap_append, flatMap_range_succ]
  set A := (List.range k).flatMap f
  set B := (List.map (fun x => k + 1 + x) (List.range d)).flatMap f
  rw [show A ++ f k ++ B ++ R = A ++ (f k ++ (B ++ R)) by simp [List.append_assoc], List.drop_left,
    show A ++ (f k ++ (B ++ R)) = (A ++ f k) ++ (B ++ R) by simp [List.append_assoc], List.drop_left]

theorem wr_zero (L W : List ℕ) (v : ℕ) : putAt (wr L 0 W) W.length v = wr L 0 (W ++ [v]) := by
  have := putAt_wr L 0 W v (Nat.zero_le _)
  simpa using this

theorem getD_wr (L W : List ℕ) (i : ℕ) (hi : i < W.length) : (wr L 0 W).getD i 0 = W.getD i 0 := by
  unfold wr; simp only [List.take_zero, List.nil_append, zero_add]
  rw [List.getD_append _ _ _ _ hi]

theorem wr_length (L W : List ℕ) : W.length ≤ (wr L 0 W).length := by
  have := wr_length_ge L 0 W (Nat.zero_le _); omega

/-! ## The stage loop -/

/-- The witness blocks of stages `< k`. -/
def blocksAll (cf : ℕ → ℕ → List ℤ) (rc k : ℕ) : List ℕ := (List.range k).flatMap fun s => blocksOf cf s rc

/-- The `(pos, neg)` parts of the stage forms `K_s^r`, `s < k`, over the gate bits `gb`. -/
def kPairs (cf : ℕ → ℕ → List ℤ) (gb : List ℕ) (r k : ℕ) : List ℕ :=
  (List.range k).flatMap fun s =>
    [posPart (cf s r) (gb.take (cf s r).length), negPart (cf s r) (gb.take (cf s r).length)]

theorem kPairs_length (cf : ℕ → ℕ → List ℤ) (gb : List ℕ) (r k : ℕ) : (kPairs cf gb r k).length = 2 * k := by
  induction k with
  | zero => simp [kPairs]
  | succ k ih =>
    unfold kPairs at ih ⊢
    rw [flatMap_range_succ (fun s => [posPart (cf s r) (gb.take (cf s r).length),
      negPart (cf s r) (gb.take (cf s r).length)]) k]
    simp only [List.length_append, ih, List.length_cons, List.length_nil]; ring

def stagesP : St VV MM := forS c5 gJ stageP

def stT : List (Fin VV) := [c5, fL, c0, c3, gS0, gS1, gZ, gPos, gNeg, vJ]

theorem stagesP_spec (a : DS VV MM) (hc : Cst a) (rc r : ℕ) (hrc : rc = 1 ∨ rc = 2) (hr : r < rc)
    (hR : a.env fR = r) (hRC : a.env gRC = rc) (J : ℕ) (hJ : a.env gJ = J) (hJW : J < 2 ^ C.Wd)
    (cf : ℕ → ℕ → List ℤ) (R : List ℕ) (hsN : (a.ram sN).drop (a.rc sN) = blocksAll cf rc J ++ R)
    (gb Z : List ℕ) (hsB : a.ram sB = gb ++ Z) (hgb : ∀ s < J, (cf s r).length ≤ gb.length) (hB0 : a.rc sB = 0)
    (hG0 : a.rc sG = 0) (Gm : ℕ) (hGm : ∀ s < J, ∀ ρ < rc, (cf s ρ).length ≤ Gm)
    (hLW : Gm < 2 ^ C.Wd) (hW : ∀ s < J, ∀ ρ < rc, ((cf s ρ).map Int.natAbs).sum < 2 ^ C.Wd) :
    Hs C stagesP a (J * (30 * Gm + 40 + 4) + 4) (fun b =>
      b.ram = Function.update a.ram sG (wr (a.ram sG) 0 (kPairs cf gb r J)) ∧
      b.rc = Function.update (Function.update a.rc sN (a.rc sN + (blocksAll cf rc J).length)) sG (2 * J) ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b stT) := by
  have hsg : sN ≠ sG := by decide
  have hsb : sN ≠ sB := by decide
  have hbg : sB ≠ sG := by decide
  set G0 := a.ram sG with hG0d
  let I : ℕ → DS VV MM → Prop := fun k e =>
    e.ram = Function.update a.ram sG (wr G0 0 (kPairs cf gb r k)) ∧
    e.rc = Function.update (Function.update a.rc sN (a.rc sN + (blocksAll cf rc k).length)) sG (2 * k) ∧
    e.ip = a.ip ∧ e.out = a.out ∧ e.kin = a.kin ∧ e.kout = a.kout ∧ e.kc = a.kc ∧ Fr a e stT
  have h0 : I 0 a := by
    refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
    · funext m; by_cases hm : m = sG
      · subst hm; simp [kPairs, wr_nil, hG0d]
      · simp [Function.update_of_ne hm]
    · funext m; by_cases hm : m = sG
      · subst hm; simp [hG0]
      · by_cases hn : m = sN
        · subst hn; simp [blocksAll, Function.update_of_ne hsg]
        · simp [Function.update_of_ne hm, Function.update_of_ne hn]
  have hl := forS_spec' (C := C) c5 gJ (by decide) stageP a J hJW I (30 * Gm + 40)
    (fun k e v ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ => ⟨i1, i2, i3, i4, i5, i6, i7,
      Fr.trans i8 (Fr.set e v (by simp [stT]))⟩) h0 hJ ?_
  · refine Hs.mono hl le_rfl ?_
    rintro b ⟨⟨i1, i2, i3, i4, i5, i6, i7, i8⟩, _, _⟩
    exact ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩
  · intro k hk e ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ hek hem
    have ec : Cst e := Cst.of_fr hc i8 (by decide)
    have eR : e.env fR = r := by rw [i8 fR (by decide)]; exact hR
    have eRC : e.env gRC = rc := by rw [i8 gRC (by decide)]; exact hRC
    have eN : e.ram sN = a.ram sN := by rw [i1, Function.update_of_ne hsg]
    have eNc : e.rc sN = a.rc sN + (blocksAll cf rc k).length := by
      rw [i2, Function.update_of_ne hsg, Function.update_self]
    have eB : e.ram sB = a.ram sB := by rw [i1, Function.update_of_ne hbg]
    have eBc : e.rc sB = 0 := by
      rw [i2, Function.update_of_ne hbg, Function.update_of_ne (Ne.symm hsb)]; exact hB0
    have eG : e.ram sG = wr G0 0 (kPairs cf gb r k) := by rw [i1, Function.update_self]
    have eGc : e.rc sG = 2 * k := by rw [i2, Function.update_self]
    have hdrop : (e.ram sN).drop (e.rc sN) = blocksOf cf k rc ++
        ((blocksAll cf rc J ++ R).drop (blocksAll cf rc (k + 1)).length) := by
      rw [eN, eNc, ← List.drop_drop, hsN]
      exact drop_flatMap_range (fun s => blocksOf cf s rc) k J hk R
    set L := (cf k r).length with hL
    have hsB' : e.ram sB = gb.take L ++ (gb.drop L ++ Z) := by rw [eB, hsB, ← List.append_assoc, List.take_append_drop]
    have hvl : (gb.take L).length = (cf k r).length := by simp [hL]; exact hgb k hk
    have hst := stageP_spec (C := C) e ec rc r hrc hr eR eRC cf k _ hdrop (gb.take L) (gb.drop L ++ Z) hsB' hvl eBc
      (by rw [eGc, eG]; have := wr_length G0 (kPairs cf gb r k); rw [kPairs_length] at this; omega)
      Gm (hGm k hk) hLW (hW k hk)
    refine Hs.mono hst le_rfl ?_
    rintro b ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩
    have hk2 : (kPairs cf gb r k).length = 2 * k := kPairs_length cf gb r k
    refine ⟨⟨?_, ?_, b3.trans i3, b4.trans i4, b5.trans i5, b6.trans i6, b7.trans i7,
      Fr.trans i8 (Fr.weaken b8 (by simp [bkT, stT]))⟩, ?_, ?_⟩
    · rw [b1, eGc, eG, i1, Function.update_idem]
      congr 1
      rw [← hk2, wr_zero, show (kPairs cf gb r k).length + 1 =
        (kPairs cf gb r k ++ [posPart (cf k r) (gb.take L)]).length by simp, wr_zero]
      unfold kPairs
      rw [flatMap_range_succ (fun s => [posPart (cf s r) (gb.take (cf s r).length),
        negPart (cf s r) (gb.take (cf s r).length)]) k]
      simp [List.append_assoc, hL]
    · rw [b2, eNc, eGc, i2]
      have hb : (blocksAll cf rc (k + 1)).length = (blocksAll cf rc k).length + (blocksOf cf k rc).length := by
        unfold blocksAll; rw [flatMap_range_succ]; simp
      funext m; by_cases hm : m = sG
      · subst hm; simp; ring
      · by_cases hn : m = sN
        · subst hn; simp [Function.update_of_ne hsg]; omega
        · simp [Function.update_of_ne hm, Function.update_of_ne hn]
    · rw [b8 c5 (by decide)]; exact hek
    · rw [b8 gJ (by decide)]; exact hem

end NearCubicGates.Close.Cells
