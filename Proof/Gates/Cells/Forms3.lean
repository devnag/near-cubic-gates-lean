import Proof.Gates.Cells.Forms2

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.Cells

open NearCubicWires NearCubicGates
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {C : Ctx}

def ePP : Fin VV := ⟨56, by decide⟩
def ePN : Fin VV := ⟨57, by decide⟩
def eA : Fin VV := ⟨58, by decide⟩
def eB : Fin VV := ⟨59, by decide⟩
def eF : Fin VV := ⟨60, by decide⟩
def eT : Fin VV := ⟨61, by decide⟩
def eX : Fin VV := ⟨62, by decide⟩
def eY : Fin VV := ⟨63, by decide⟩

/-- The digit values `E_j` from the stage values `K_s = kp s − kn s` and the rates `fs`. -/
def eVal (kp kn : ℕ → ℕ) (fs : List ℕ) (j : ℕ) : ℤ :=
  CountingCore.proposedDigit (fun t => (fs.getD t 0 : ℤ)) (fun s => (kp s : ℤ) - kn s) j

def ePairs (kp kn : ℕ → ℕ) (fs : List ℕ) (k : ℕ) : List ℕ :=
  (List.range k).flatMap fun j => pairOf (eVal kp kn fs j)

theorem ePairs_length (kp kn : ℕ → ℕ) (fs : List ℕ) (k : ℕ) : (ePairs kp kn fs k).length = 2 * k := by
  induction k with
  | zero => simp [ePairs]
  | succ k ih =>
    unfold ePairs at ih ⊢
    rw [flatMap_range_succ]; simp [ih, pairOf]; ring

/-- Reads and arithmetic of one step: `eX = K_j^+ + a·prev^−`, `eY = K_j^− + a·prev^+`. -/
def ePre : St VV MM :=
  .seq (.op (.rdM sG eA)) (.seq (.op (.rdM sG eB)) (.seq (.op (.rdM sN eF))
  (.seq (.op (.mul eF ePN eT)) (.seq (.op (.copy eX eA)) (.seq (.op (.add eX eT))
  (.seq (.op (.mul eF ePP eT)) (.seq (.op (.copy eY eB)) (.op (.add eY eT)))))))))

def ePost : St VV MM :=
  .seq (normP eX eY) (.seq (.op (.wrM sE eX)) (.seq (.op (.wrM sE eY))
  (.seq (.op (.copy ePP eA)) (.op (.copy ePN eB)))))

def eBody : St VV MM := .seq ePre ePost

def eLoopP : St VV MM := forS c5 gJ eBody

def eLT : List (Fin VV) := [c5, ePP, ePN, eA, eB, eF, eT, eX, eY]

/-- The previous stage value (zero before the first stage). -/
def prevV (kp : ℕ → ℕ) (k : ℕ) : ℕ := if k = 0 then 0 else kp (k - 1)

theorem eVal_step (kp kn : ℕ → ℕ) (fs : List ℕ) (k f : ℕ) (hf : 1 ≤ k → f = fs.getD (k - 1) 0) :
    ((kp k + f * prevV kn k : ℕ) : ℤ) - ((kn k + f * prevV kp k : ℕ) : ℤ) = eVal kp kn fs k := by
  rcases k with _ | k
  · simp [prevV, eVal, CountingCore.proposedDigit]
  · have := hf (by omega)
    simp only [prevV, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel] at this ⊢
    subst this
    simp only [eVal, CountingCore.proposedDigit]
    push_cast; ring

theorem ePre_spec (a : DS VV MM) (pa pb f pp pn : ℕ)
    (hGl : a.rc sG + 1 < (a.ram sG).length)
    (hGa : (a.ram sG).getD (a.rc sG) 0 = pa) (hGb : (a.ram sG).getD (a.rc sG + 1) 0 = pb)
    (hNl : a.rc sN < (a.ram sN).length) (hNf : (a.ram sN).getD (a.rc sN) 0 = f)
    (hpp : a.env ePP = pp) (hpn : a.env ePN = pn)
    (hW1 : pa + f * pn < 2 ^ C.Wd) (hW2 : pb + f * pp < 2 ^ C.Wd) :
    Hs C ePre a 17 (fun b => b.env eX = pa + f * pn ∧ b.env eY = pb + f * pp ∧ b.env eA = pa ∧ b.env eB = pb ∧
      b.ram = a.ram ∧ b.rc = Function.update (Function.update a.rc sG (a.rc sG + 2)) sN (a.rc sN + 1) ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b (eLT.drop 3)) := by
  have hGN : sG ≠ sN := by decide
  have hm1 : f * pn < 2 ^ C.Wd := by omega
  have hm2 : f * pp < 2 ^ C.Wd := by omega
  have hNf' : (a.ram sN)[a.rc sN]?.getD 0 = f := by rw [← List.getD_eq_getElem?_getD]; exact hNf
  have hGa' : (a.ram sG)[a.rc sG]?.getD 0 = pa := by rw [← List.getD_eq_getElem?_getD]; exact hGa
  have hGb' : (a.ram sG)[a.rc sG + 1]?.getD 0 = pb := by rw [← List.getD_eq_getElem?_getD]; exact hGb
  refine Hs.seq (t1 := 1) (t2 := 15) (hs_rdM C sG eA a (by omega)) (fun e1 he1 => ?_)
  subst he1
  refine Hs.seq (t1 := 1) (t2 := 13) (hs_rdM C sG eB _ (by simp [DS.adv, DS.set]; omega)) (fun e2 he2 => ?_)
  subst he2
  refine Hs.seq (t1 := 1) (t2 := 11) (hs_rdM C sN eF _ (by
    simp [DS.adv, DS.set, Function.update_of_ne (Ne.symm hGN)]; omega)) (fun e3 he3 => ?_)
  subst he3
  refine Hs.seq (t1 := 1) (t2 := 9) (hs_mul C eF ePN eT _ (by decide) (by decide) (by decide)
    (by vsimp [DS.adv, Function.update_of_ne (Ne.symm hGN), hNf, hNf', hpn]; omega)) (fun e4 he4 => ?_)
  subst he4
  refine Hs.seq (t1 := 1) (t2 := 7) (hs_copy C eX eA _ (by decide)) (fun e5 he5 => ?_)
  subst he5
  refine Hs.seq (t1 := 1) (t2 := 5) (hs_add C eX eT _ (by decide)
    (by vsimp [DS.adv, Function.update_of_ne (Ne.symm hGN), hNf, hNf', hpn, hGa, hGa']; omega)) (fun e6 he6 => ?_)
  subst he6
  refine Hs.seq (t1 := 1) (t2 := 3) (hs_mul C eF ePP eT _ (by decide) (by decide) (by decide)
    (by vsimp [DS.adv, Function.update_of_ne (Ne.symm hGN), hNf, hNf', hpp]; omega)) (fun e7 he7 => ?_)
  subst he7
  refine Hs.seq (t1 := 1) (t2 := 1) (hs_copy C eY eB _ (by decide)) (fun e8 he8 => ?_)
  subst he8
  refine Hs.mono (hs_add C eY eT _ (by decide)
    (by vsimp [DS.adv, Function.update_of_ne (Ne.symm hGN), hNf, hNf', hpp, hGb, hGb']; omega)) le_rfl ?_
  rintro b rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · vsimp [DS.adv, Function.update_of_ne (Ne.symm hGN), hNf, hNf', hpn, hGa, hGa']
  · vsimp [DS.adv, Function.update_of_ne (Ne.symm hGN), hNf, hNf', hpp, hGb, hGb']
  · vsimp [DS.adv, hGa, hGa']
  · vsimp [DS.adv, hGb, hGb']
  · simp [DS.adv, DS.set]
  · simp only [DS.adv, DS.set]
    funext m; by_cases h1 : m = sN
    · subst h1; simp [Function.update_of_ne (Ne.symm hGN)]
    · by_cases h2 : m = sG
      · subst h2; simp [Function.update_of_ne h1]
      · simp [Function.update_of_ne h1, Function.update_of_ne h2]
  all_goals try (simp [DS.adv, DS.set]; done)
  intro y hy
  simp only [eLT, List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
  simp only [DS.adv, DS.set]
  repeat rw [Function.update_of_ne (by tauto)]

theorem ePost_spec (a : DS VV MM) (pa pb : ℕ) (hA : a.env eA = pa) (hB : a.env eB = pb)
    (E0 W : List ℕ) (hE : a.ram sE = wr E0 0 W) (hEc : a.rc sE = W.length) :
    Hs C ePost a 15 (fun b =>
      b.ram = Function.update a.ram sE (wr E0 0 (W ++ pairOf ((a.env eX : ℤ) - a.env eY))) ∧
      b.rc = Function.update a.rc sE (W.length + 2) ∧ b.env ePP = pa ∧ b.env ePN = pb ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b (eLT.drop 1)) := by
  refine Hs.seq (t1 := 4) (t2 := 10) (normP_spec eX eY (by decide) a) (fun e1 he1 => ?_)
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, n9⟩ := he1
  have e1E : e1.ram sE = wr E0 0 W := by rw [n4, hE]
  have e1Ec : e1.rc sE = W.length := by rw [n5, hEc]
  refine Hs.seq (t1 := 1) (t2 := 8) (hs_wrM C sE eX e1 (by rw [e1Ec, e1E]; exact wr_length _ _))
    (fun e2 he2 => ?_)
  subst he2
  refine Hs.seq (t1 := 1) (t2 := 6) (hs_wrM C sE eY _ (by
    simp only [DS.put, Function.update_self]; rw [e1Ec, e1E, wr_zero]
    have := wr_length E0 (W ++ [e1.env eX]); simp only [List.length_append, List.length_singleton] at this ⊢
    omega))
    (fun e3 he3 => ?_)
  subst he3
  refine Hs.seq (t1 := 1) (t2 := 4) (hs_copy C ePP eA _ (by decide)) (fun e4 he4 => ?_)
  subst he4
  refine Hs.mono (hs_copy C ePN eB _ (by decide)) (by norm_num) ?_
  rintro b rfl
  have e1A : e1.env eA = pa := by rw [n9 eA (by decide)]; exact hA
  have e1B : e1.env eB = pb := by rw [n9 eB (by decide)]; exact hB
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [DS.set_ram, DS.put, Function.update_self, Function.update_idem]
    rw [e1Ec, e1E, wr_zero, show W.length + 1 = (W ++ [e1.env eX]).length by simp, wr_zero, n4, ← n1]
    simp [List.append_assoc]
  · simp only [DS.set_rc, DS.put, Function.update_self, Function.update_idem]
    rw [n5, hEc]
  · vsimp [DS.put, e1A]
  · vsimp [DS.put, e1B]
  · refine ⟨by simp [DS.put, n2], by simp [DS.put, n3], by simp [DS.put, n6], by simp [DS.put, n7],
      by simp [DS.put, n8], ?_⟩
    refine Fr.trans (Fr.weaken n9 (by decide)) ?_
    intro y hy
    simp only [eLT, List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [DS.set, DS.put]
    rw [Function.update_of_ne hy.2.1, Function.update_of_ne hy.1]

theorem prevV_le (kp : ℕ → ℕ) (J KB k : ℕ) (hk : k ≤ J) (h : ∀ s < J, kp s ≤ KB) : prevV kp k ≤ KB := by
  unfold prevV; split_ifs with h0
  · omega
  · exact h _ (by omega)

/-- **The digit-centre loop of a role.** -/
theorem eLoopP_spec (a : DS VV MM) (J : ℕ) (hJ : a.env gJ = J) (hJW : J < 2 ^ C.Wd) (kp kn : ℕ → ℕ)
    (hG2 : 2 * J ≤ (a.ram sG).length) (hG0 : a.rc sG = 0)
    (hGk : ∀ s < J, (a.ram sG).getD (2 * s) 0 = kp s ∧ (a.ram sG).getD (2 * s + 1) 0 = kn s)
    (fs : List ℕ) (FB KB : ℕ) (hNl : a.rc sN + J ≤ (a.ram sN).length)
    (hF : ∀ j, 1 ≤ j → j < J → (a.ram sN).getD (a.rc sN + j) 0 = fs.getD (j - 1) 0)
    (hFB : ∀ j < J, (a.ram sN).getD (a.rc sN + j) 0 ≤ FB)
    (hKp : ∀ s < J, kp s ≤ KB) (hKn : ∀ s < J, kn s ≤ KB) (hWd : KB + FB * KB < 2 ^ C.Wd)
    (E0 Pre : List ℕ) (hE : a.ram sE = wr E0 0 Pre) (hEc : a.rc sE = Pre.length)
    (hpp : a.env ePP = 0) (hpn : a.env ePN = 0) :
    Hs C eLoopP a (J * (33 + 4) + 4) (fun b =>
      b.ram = Function.update a.ram sE (wr E0 0 (Pre ++ ePairs kp kn fs J)) ∧
      b.rc = Function.update (Function.update (Function.update a.rc sG (2 * J)) sN (a.rc sN + J)) sE
        (Pre.length + 2 * J) ∧
      b.env ePP = prevV kp J ∧ b.env ePN = prevV kn J ∧
      b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout ∧ b.kc = a.kc ∧ Fr a b eLT) := by
  have hGN : sG ≠ sN := by decide
  have hGE : sG ≠ sE := by decide
  have hNE : sN ≠ sE := by decide
  let I : ℕ → DS VV MM → Prop := fun k e =>
    e.ram = Function.update a.ram sE (wr E0 0 (Pre ++ ePairs kp kn fs k)) ∧
    e.rc = Function.update (Function.update (Function.update a.rc sG (2 * k)) sN (a.rc sN + k)) sE
      (Pre.length + 2 * k) ∧
    e.env ePP = prevV kp k ∧ e.env ePN = prevV kn k ∧
    e.ip = a.ip ∧ e.out = a.out ∧ e.kin = a.kin ∧ e.kout = a.kout ∧ e.kc = a.kc ∧ Fr a e eLT
  have h0 : I 0 a := by
    refine ⟨?_, ?_, by simp [prevV, hpp], by simp [prevV, hpn], rfl, rfl, rfl, rfl, rfl, Fr.refl _ _⟩
    · funext m; by_cases hm : m = sE
      · subst hm; simp [ePairs, hE]
      · simp [Function.update_of_ne hm]
    · funext m; by_cases hm : m = sE
      · subst hm; simp [hEc]
      · by_cases hn : m = sN
        · subst hn; simp [Function.update_of_ne hNE]
        · by_cases hg : m = sG
          · subst hg; simp [Function.update_of_ne hGE, Function.update_of_ne hGN, hG0]
          · simp [Function.update_of_ne hm, Function.update_of_ne hn, Function.update_of_ne hg]
  have hl := forS_spec' (C := C) c5 gJ (by decide) eBody a J hJW I 33
    (fun k e v ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ =>
      ⟨i1, i2, by rw [DS.set_env_ne _ _ (by decide)]; exact i3, by rw [DS.set_env_ne _ _ (by decide)]; exact i4,
        i5, i6, i7, i8, i9, Fr.trans i10 (Fr.set e v (by simp [eLT]))⟩) h0 hJ ?_
  · refine Hs.mono hl le_rfl ?_
    rintro b ⟨i, _, _⟩
    exact i
  · intro k hk e ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ hek hem
    have eG : e.ram sG = a.ram sG := by rw [i1, Function.update_of_ne hGE]
    have eGc : e.rc sG = 2 * k := by
      rw [i2, Function.update_of_ne hGE, Function.update_of_ne hGN, Function.update_self]
    have eN : e.ram sN = a.ram sN := by rw [i1, Function.update_of_ne hNE]
    have eNc : e.rc sN = a.rc sN + k := by rw [i2, Function.update_of_ne hNE, Function.update_self]
    have eE : e.ram sE = wr E0 0 (Pre ++ ePairs kp kn fs k) := by rw [i1, Function.update_self]
    have eEc : e.rc sE = (Pre ++ ePairs kp kn fs k).length := by
      rw [i2, Function.update_self, List.length_append, ePairs_length]
    set f := (a.ram sN).getD (a.rc sN + k) 0 with hf
    have hpk1 := prevV_le kp J KB k hk.le hKp
    have hpk2 := prevV_le kn J KB k hk.le hKn
    have hfb : f ≤ FB := hFB k hk
    have m1 : f * prevV kn k ≤ FB * KB := Nat.mul_le_mul hfb hpk2
    have m2 : f * prevV kp k ≤ FB * KB := Nat.mul_le_mul hfb hpk1
    have hpre := ePre_spec (C := C) e (kp k) (kn k) f (prevV kp k) (prevV kn k)
      (by rw [eGc, eG]; omega) (by rw [eGc, eG]; exact (hGk k hk).1) (by rw [eGc, eG]; exact (hGk k hk).2)
      (by rw [eNc, eN]; omega) (by rw [eNc, eN]) i3 i4
      (by have := hKp k hk; omega) (by have := hKn k hk; omega)
    refine Hs.mono (Hs.seq (t2 := 15) hpre (fun e1 he1 => ?_)) (by norm_num) (fun _ h => h)
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := he1
    have hpost := ePost_spec (C := C) e1 (kp k) (kn k) p3 p4 E0 (Pre ++ ePairs kp kn fs k)
      (by rw [p5, eE]) (by rw [p6, Function.update_of_ne (Ne.symm hNE), Function.update_of_ne (Ne.symm hGE), eEc])
    refine Hs.mono hpost le_rfl ?_
    rintro b ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩
    have hval : pairOf ((e1.env eX : ℤ) - e1.env eY) = pairOf (eVal kp kn fs k) := by
      rw [p1, p2]; congr 1
      have := eVal_step kp kn fs k f (fun h1 => (hF k h1 hk).symm ▸ hf ▸ rfl)
      exact_mod_cast this
    have hfr : Fr a b eLT := Fr.trans i10 (Fr.trans (Fr.weaken p12 (by decide)) (Fr.weaken q10 (by decide)))
    refine ⟨⟨?_, ?_, ?_, ?_, q5.trans (p7.trans i5), q6.trans (p8.trans i6), q7.trans (p9.trans i7),
      q8.trans (p10.trans i8), q9.trans (p11.trans i9), hfr⟩, ?_, ?_⟩
    · rw [q1, hval, p5, i1, Function.update_idem]
      unfold ePairs; rw [flatMap_range_succ]; simp [List.append_assoc]
    · rw [q2, p6, i2, List.length_append, ePairs_length]
      funext m; by_cases hm : m = sE
      · subst hm; simp; ring
      · by_cases hn : m = sN
        · subst hn; simp [Function.update_of_ne hNE]; ring
        · by_cases hg : m = sG
          · subst hg; simp [Function.update_of_ne hGE, Function.update_of_ne hGN]; ring
          · simp [Function.update_of_ne hm, Function.update_of_ne hn, Function.update_of_ne hg]
    · rw [q3]; simp [prevV]
    · rw [q4]; simp [prevV]
    · rw [q10 c5 (by decide), p12 c5 (by decide)]; exact hek
    · rw [q10 gJ (by decide), p12 gJ (by decide)]; exact hem

end NearCubicGates.Close.Cells
