import SourceAdapters.RAMACSP.GenParams

/-!
# The generator's first `FL` stage: read, compute, print `frame x̄` and `natWord f`

Paper: `lem:generator` ("The algorithm computes the numbers `w_n`, `τ_n`, `m`, `k_N`, `ℓ_S`, `d`, `q`, `m_H` and
`f` … and writes `x̄`"; "outputs `x̄` and the instance"), `lem:tm-ram` (`x̄ = x10^j`, `|x̄| = 2^m`) and `def:acsp`
(the description begins with the degree `f`).

`stageA` = `readP` (the two frames of the request into `20 … 23`), `paramsP` (the numbers), `xbarP` (the bits of
`x̄`, each as `1 b`, then `0`: the word `frame x̄`), `emitNatV 36` (`natWord f`). Every printed bit `b` is the pair
`1 b` of the outer frame (`Em`).
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

variable {G : Glob} (V : Verifier)

/-! ## Reading the request -/

/-- `20 := bitsValue x`, `21 := |x|`, `22 := bitsValue (bits t)`, `23 := |bits t|`. -/
def readP : S :=
  .seq rdFrame (.seq (.set 20 (.v 0)) (.seq (.set 21 (.v 1)) (.seq rdFrame (.seq (.set 22 (.v 0)) (.set 23 (.v 1))))))

theorem readP_spec (s : FS) (r : ClockRequest) (rest : List Bool)
    (hin : G.inp.drop s.ip = ClockRequest.word r ++ rest)
    (hc1 : 2 * 2 ^ r.1.1 ≤ G.cap) (hc2 : 2 * 2 ^ r.2.bits.length ≤ G.cap)
    (hN1 : r.1.1 + 1 ≤ G.N) (hN2 : r.2.bits.length + 1 ≤ G.N) :
    let u := evalS G readP s
    u.env 20 = CanonicalBinary.bitsValue (List.ofFn r.1.2) ∧ u.env 21 = r.1.1 ∧ u.env 22 = r.2 ∧
      u.env 23 = r.2.bits.length ∧ Wr [0, 1, 2, 3, 4, 20, 21, 22, 23] s u := by
  intro u
  have hxl : (List.ofFn r.1.2).length = r.1.1 := List.length_ofFn
  have hu : u = ((evalS G rdFrame ((evalS G rdFrame s).setv 20 ((evalS G rdFrame s).env 0) |>.setv 21
      ((evalS G rdFrame s).env 1))).setv 22 ((evalS G rdFrame ((evalS G rdFrame s).setv 20 ((evalS G rdFrame s).env 0)
      |>.setv 21 ((evalS G rdFrame s).env 1))).env 0)).setv 23 ((evalS G rdFrame ((evalS G rdFrame s).setv 20
      ((evalS G rdFrame s).env 0) |>.setv 21 ((evalS G rdFrame s).env 1))).env 1) := rfl
  rw [hu]
  have hin1 : G.inp.drop s.ip = frame (List.ofFn r.1.2) ++ (frame r.2.bits ++ rest) := by
    rw [hin]; simp [ClockRequest.word]
  obtain ⟨a0', a1', aip, aW⟩ := rdFrame_spec G s (List.ofFn r.1.2) _ hin1 (by rw [hxl]; exact hc1) (by rw [hxl]; exact hN1)
  generalize hs1 : evalS G rdFrame s = s1 at a0' a1' aip aW
  generalize hs2 : (s1.setv 20 (s1.env 0)).setv 21 (s1.env 1) = s2
  have hs2ip : s2.ip = s.ip + (2 * (List.ofFn r.1.2).length + 1) := by rw [← hs2]; show s1.ip = _; rw [aip]; ring
  have hin2 : G.inp.drop s2.ip = frame r.2.bits ++ rest := by
    rw [hs2ip, ← List.drop_drop, hin1, List.drop_left' (by rw [FL.frame_len])]
  obtain ⟨b0, b1, bip, bW⟩ := rdFrame_spec G s2 r.2.bits rest hin2 hc2 hN2
  generalize hs3 : evalS G rdFrame s2 = s3 at b0 b1 bip bW
  have bv : CanonicalBinary.bitsValue r.2.bits = r.2 := CanonicalBinary.bitsValue_natBits r.2
  have s2_20 : s2.env 20 = CanonicalBinary.bitsValue (List.ofFn r.1.2) := by rw [← hs2]; simp [a0']
  have s2_21 : s2.env 21 = r.1.1 := by rw [← hs2]; simp [a1', hxl]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp (config := { decide := true }) only [FS.setv_env, Function.update_apply, if_false]
    rw [bW.env 20 (by decide), s2_20]
  · simp (config := { decide := true }) only [FS.setv_env, Function.update_apply, if_false]
    rw [bW.env 21 (by decide), s2_21]
  · simp (config := { decide := true }) only [FS.setv_env, Function.update_apply, if_false, if_true]; rw [b0, bv]
  · simp (config := { decide := true }) only [FS.setv_env, Function.update_apply, if_true]; rw [b1]
  · have w12 : Wr [0, 1, 2, 3, 4, 20, 21, 22, 23] s1 s2 := by
      rw [← hs2]; exact Wr.trans (Wr.setv s1 (by decide) _) (Wr.setv _ (by decide) _)
    exact (aW.mono (by decide)).trans (w12.trans ((bW.mono (by decide)).trans
      (Wr.trans (Wr.setv s3 (by decide) _) (Wr.setv _ (by decide) _))))

/-! ## Printing `frame x̄` -/

/-- The bit `i` of `x̄ = x ++ 1 :: 0^j` (`x` in `20`, `n` in `21`, `i` in `50`). -/
def xbitE : E := .add (.mul (.lt (.v 50) (.v 21)) (.md (.shr (.v 20) (.v 50)) (.k 2))) (.eq (.v 50) (.v 21))

/-- `frame x̄`: for `i < |x̄|` (`|x̄|` in `30`) the bit, then `0`. -/
def xbarP : S := .seq (.loop 50 (.v 30) (.seq (emitF (.k 1)) (emitF xbitE))) (emitF (.k 0))

theorem getD_replicate_false (k j : ℕ) : (List.replicate k false).getD j false = false := by
  induction k generalizing j with
  | zero => simp
  | succ k ih => cases j with
    | zero => simp [List.replicate_succ]
    | succ j => simp only [List.replicate_succ, List.getD_cons_succ]; exact ih j

theorem pad_getD (x : List Bool) (k i : ℕ) :
    (x ++ true :: List.replicate k false).getD i false =
      if i < x.length then x.getD i false else decide (i = x.length) := by
  by_cases h : i < x.length
  · rw [if_pos h, List.getD_append _ _ _ _ h]
  · rw [if_neg h, List.getD_append_right _ _ _ _ (by omega)]
    rcases Nat.lt_or_ge x.length i with h2 | h2
    · rw [show i - x.length = (i - x.length - 1) + 1 by omega, List.getD_cons_succ, getD_replicate_false]
      have : i ≠ x.length := by omega
      simp [this]
    · have : i = x.length := by omega
      subst this; simp

theorem inputPadLength_eq (r : ClockRequest) : inputPadLength (clockConst V) r.1.1 r.2 = 2 ^ inExp V r := by
  rw [inExp_eq]; rfl

theorem ownXbar_eq (r : ClockRequest) :
    ownXbar V r = List.ofFn r.1.2 ++ true :: List.replicate (2 ^ inExp V r - r.1.1 - 1) false := by
  unfold ownXbar padInput; rw [inputPadLength_eq]

theorem ownXbar_length (r : ClockRequest) : (ownXbar V r).length = 2 ^ inExp V r := by
  have hle : r.1.1 + 1 ≤ inputPadLength (clockConst V) r.1.1 r.2 := by
    unfold inputPadLength; exact le_trans (le_max_left _ _) (le_two_pow_clog _)
  unfold ownXbar; rw [padInput_length _ _ _ hle, inputPadLength_eq]

theorem range_map_getD (w : List Bool) : (List.range w.length).map (fun i => w.getD i false) = w := by
  apply List.ext_getElem (by simp)
  intro j h1 h2; simp [List.getElem?_eq_getElem h2]

theorem dbl_eq_range (w : List Bool) : dbl w = (List.range w.length).flatMap (fun i => [true, w.getD i false]) := by
  conv_lhs => rw [← range_map_getD w]
  simp [dbl, List.flatMap_map]

theorem xbarP_spec (s : FS) (r : ClockRequest) (h : PV V r s) (hP : 2 ^ inExp V r ≤ G.N) (hc : 2 ≤ G.cap) :
    Em [50] s (evalS G xbarP s) (frame (ownXbar V r)) := by
  set P := 2 ^ inExp V r with hPdef
  set x := List.ofFn r.1.2 with hx
  have hxl : x.length = r.1.1 := List.length_ofFn
  have hm : min (evalE G s (.v 30)) G.N = P := by rw [eE_v, h.P]; exact min_eq_left hP
  have hl := (Em_loop 50 (.v 30) (.seq (emitF (.k 1)) (emitF xbitE)) [50] (by simp) s P hm (fun _ => True) trivial
    (fun i => [true, (ownXbar V r).getD i false]) (fun i hi u _ ue => ⟨trivial, by
      have e1 := emitF_spec (G := G) (u.setv 50 i) (.k 1) [50] (by omega)
      have e2 := emitF_spec (G := G) (evalS G (emitF (.k 1)) (u.setv 50 i)) xbitE [50] (by omega)
      set u1 := evalS G (emitF (.k 1)) (u.setv 50 i) with hu1
      have s50 : u1.env 50 = i := by rw [hu1, emitF_env]; simp
      have s20 : u1.env 20 = CanonicalBinary.bitsValue x := by
        rw [hu1, emitF_env]; simp only [FS.setv_env, Function.update_apply]; rw [if_neg (by decide),
          ue.env 20 (by decide), h.x]
      have s21 : u1.env 21 = r.1.1 := by
        rw [hu1, emitF_env]; simp only [FS.setv_env, Function.update_apply]; rw [if_neg (by decide),
          ue.env 21 (by decide), h.n]
      have bl : CanonicalBinary.bitsValue x / 2 ^ i % 2 ≤ 1 := by
        have := Nat.mod_lt (CanonicalBinary.bitsValue x / 2 ^ i) (show 0 < 2 by norm_num); omega
      have hv : evalE G u1 xbitE =
          (if i < r.1.1 then 1 else 0) * (CanonicalBinary.bitsValue x / 2 ^ i % 2) + (if i = r.1.1 then 1 else 0) :=
        eE_add (eE_mul (eE_lt (by rw [eE_v, s50]) (by rw [eE_v, s21]))
          (eE_md (eE_shr (by rw [eE_v, s20]) (by rw [eE_v, s50])) (eE_k hc)) (by split_ifs <;> omega))
          (eE_eq (by rw [eE_v, s50]) (by rw [eE_v, s21])) (by split_ifs <;> omega)
      have c1 : evalE G (u.setv 50 i) (.k 1) = 1 := min_eq_left (by omega)
      have hbit : (evalE G u1 xbitE != 0) = (ownXbar V r).getD i false := by
        rw [hv, ownXbar_eq, pad_getD, hxl]
        have hb := testBit_bitsValue x i
        by_cases h1 : i < r.1.1
        · have h2 : i ≠ r.1.1 := by omega
          rw [if_pos h1, if_pos h1, if_neg h2, hb]
          cases x.getD i false <;> simp
        · rw [if_neg h1, if_neg h1]
          by_cases h2 : i = r.1.1 <;> simp [h2]
      have := e1.trans e2
      rw [c1, hbit] at this
      exact this⟩)).2
  have e3 := emitF_spec (G := G) (evalS G (.loop 50 (.v 30) (.seq (emitF (.k 1)) (emitF xbitE))) s) (.k 0) [50]
    (by omega)
  have := hl.trans e3
  rw [show evalE G (evalS G (.loop 50 (.v 30) (.seq (emitF (.k 1)) (emitF xbitE))) s) (.k 0) = 0 from
    Nat.zero_min _] at this
  have hw : frame (ownXbar V r) = (List.range P).flatMap (fun i => [true, (ownXbar V r).getD i false]) ++
      [(0 != 0)] := by
    rw [frame_dbl, dbl_eq_range, ownXbar_length]; rfl
  rw [hw]; exact this

/-! ## Stage A -/

/-- **Stage A**: read, compute, print `frame x̄` and `natWord f`. -/
def stageA : S := .seq readP (.seq (paramsP V) (.seq xbarP (emitNatV 36)))

/-- The size condition of stage A. -/
def AFit (r : ClockRequest) (G : Glob) : Prop := ParamFit V r G ∧ 2 ^ inExp V r ≤ G.N

theorem natBitLength_le (v : ℕ) : natBitLength v ≤ v + 1 := by
  unfold natBitLength; have := Nat.log_le_self 2 v; omega

theorem PV.of_wr {r : ClockRequest} {s t : FS} {W : List Var} (h : PV V r s) (hw : ∀ i : Var, 20 ≤ i.val → i.val ≤ 36 →
    i ∉ W) (he : ∀ j, j ∉ W → t.env j = s.env j) : PV V r t :=
  h.keep V (fun i h1 h2 => he i (hw i h1 h2))

theorem notmem_hi {i : Var} {W : List Var} (hW : ∀ j ∈ W, 36 < j.val ∨ j.val < 20) (h1 : 20 ≤ i.val)
    (h2 : i.val ≤ 36) : i ∉ W := fun hi => by have := hW i hi; omega

theorem stageA_spec (s : FS) (r : ClockRequest) (rest : List Bool)
    (hin : G.inp.drop s.ip = ClockRequest.word r ++ rest) (hfit : AFit V r G) :
    let u := evalS G (stageA V) s
    PV V r u ∧ u.out = s.out ++ dbl (frame (ownXbar V r) ++ natWord (fieldExp V r.2)) ∧
      u.bad = s.bad ∧ u.fl = s.fl ∧ u.fp = s.fp := by
  intro u
  obtain ⟨⟨hK, hKN⟩, hP⟩ := hfit
  have hτ : tau V r.2 + 2 ≤ fieldExp V r.2 := by
    have := tau_lt_domExp V r.2; have := domExp_add_two_le_fieldExp V r.2; omega
  have hcap2 : 2 ≤ G.cap := le_trans (by norm_num) (pow_le_cap' (G := G) (a := 0) (by omega))
  obtain ⟨a20, a21, a22, a23, aW⟩ := readP_spec (G := G) s r rest hin (pow_le_cap' (by omega))
    (pow_le_cap' (by omega)) (by omega) (by omega)
  generalize hs1 : evalS G readP s = s1 at a20 a21 a22 a23 aW
  obtain ⟨pv2, w2⟩ := paramsP_spec V (G := G) r s1 a20 a21 a22 a23 ⟨hK, hKN⟩
  generalize hs2 : evalS G (paramsP V) s1 = s2 at pv2 w2
  have e3 := xbarP_spec V (G := G) s2 r pv2 hP hcap2
  generalize hs3 : evalS G xbarP s2 = s3 at e3
  have pv3 : PV V r s3 := pv2.of_wr V (W := [50]) (fun i h1 h2 => notmem_hi (by decide) h1 h2) e3.env
  have hnf := natBitLength_le (fieldExp V r.2)
  have e5 := emitNatV_spec (G := G) s3 36 (by decide) (by decide) (by rw [pv3.f]; omega) (by omega)
  generalize hs5 : evalS G (emitNatV 36) s3 = s5 at e5
  have pv5 : PV V r s5 := pv3.of_wr V (W := [5, 6]) (fun i h1 h2 => notmem_hi (by decide) h1 h2) e5.env
  have hu : u = s5 := by show evalS G (stageA V) s = s5; rw [← hs5, ← hs3, ← hs2, ← hs1]; rfl
  rw [hu]
  refine ⟨pv5, ?_, ?_, ?_, ?_⟩
  · rw [e5.out, e3.out, w2.out, aW.out, pv3.f, dbl_append]; simp
  · rw [e5.bad, e3.bad, w2.bad, aW.bad]
  · rw [e5.fl, e3.fl, w2.fl, aW.fl]
  · rw [e5.fp, e3.fp, w2.fp, aW.fp]

end NearCubicGates.Adapters.RAMACSP.Gen
