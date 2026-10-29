import SourceAdapters.RAMACSP.GenRun
import SourceAdapters.ShortPCP.Machines.FLangPost
import SourceAdapters.ACSP.Encoding

/-!
# The generator's printing primitives in `FL`: `natWord`, gate words, lists

Paper: `lem:generator` ("outputs `x̄` and the instance"; the numbers have `O(log t)` bits) and the description of
`def:acsp` (`Instance.word`: `natWord f ++ natWord irr ++ listWord natWord hBasis ++ natWord hOffset ++
listWord pairWord nbr ++ listWord gateWord cons ++ listWord natWord iBasis ++ natWord iOffset`), written inside
`frame (frame x̄ ++ word)`.

Inside the outer frame every output bit `b` is written as the pair `1 b` (`emitF`; `Em W s t w` = the run appended
`dbl w`). Scratch variables of every printing routine: `0 … 19` (`SW`); the generator's own values live in `20 …`.
- `natLenP a`: `6 := natBitLength (a)` (`natLenP_spec`);
- `emitNatV a`: prints `natWord (a)` (`emitNatV_spec`); `emitNatE e`: prints `natWord e` for an expression `e` that
  reads only variables `≥ 20` (`emitNatE_spec`);
- `emitGateE t x y`: prints `natWord t ++ natWord x ++ natWord y` (= `gateWord` of the gate with tag `t`).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicGates.Adapters.RAMACSP.Gen

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicGates.Adapters.ShortPCP NearCubicGates.Adapters.ShortPCP.Machines
open NearCubicGates.Adapters.ShortPCP.Machines.FL
open NearCubicWires.RepairRepresentation (natWord)

variable {G : Glob}

/-- The scratch variables of the printing routines. -/
def SW : List Var := (List.finRange NU).filter (fun i => decide (i.val < 20))

theorem mem_SW_iff {i : Var} : i ∈ SW ↔ i.val < 20 := by simp [SW, List.mem_filter]

theorem mem_SW {i : Var} (h : i.val < 20) : i ∈ SW := mem_SW_iff.mpr h

theorem not_mem_SW {i : Var} (h : 20 ≤ i.val) : i ∉ SW := fun hi => by have := mem_SW_iff.mp hi; omega

theorem SW_lt : ∀ x ∈ SW, x.val < 20 := fun _ hx => mem_SW_iff.mp hx

/-- An expression reads only variables `≥ 20`. -/
def HiE : E → Prop
  | .v i => 20 ≤ i.val
  | .k _ | .gk => True
  | .add a b | .sub a b | .mul a b | .div a b | .md a b | .shl a b | .shr a b | .bxor a b | .fadd a b
  | .fmul a b | .fpow a b | .lt a b | .eq a b => HiE a ∧ HiE b
  | .finv a => HiE a

/-- An expression reading only variables `≥ 20` has the same value on states that agree there (with the same
field). -/
theorem evalE_hi {s t : FS} (h : ∀ i : Var, 20 ≤ i.val → t.env i = s.env i) (hfl : t.fl = s.fl) (hfp : t.fp = s.fp) :
    ∀ e : E, HiE e → evalE G t e = evalE G s e
  | .v i, he => h i he
  | .k _, _ => rfl
  | .gk, _ => rfl
  | .add a b, he | .sub a b, he | .mul a b, he | .div a b, he | .md a b, he | .shl a b, he | .shr a b, he
  | .bxor a b, he | .lt a b, he | .eq a b, he => by
    simp only [evalE, evalE_hi h hfl hfp a he.1, evalE_hi h hfl hfp b he.2]
  | .fadd a b, he | .fmul a b, he | .fpow a b, he => by
    simp only [evalE, evalE_hi h hfl hfp a he.1, evalE_hi h hfl hfp b he.2, hfl, hfp]
  | .finv a, he => by simp only [evalE, evalE_hi h hfl hfp a he, hfl, hfp]

theorem Em.hi {W : List Var} {s t : FS} {w : List Bool} (h : Em W s t w) (hW : ∀ x ∈ W, x.val < 20) :
    ∀ i : Var, 20 ≤ i.val → t.env i = s.env i := fun i hi => h.env i (fun hm => by have := hW i hm; omega)

/-! ## The length of a number -/

/-- `natBitLength v`: the least `L ≥ 1` with `v < 2^L`. -/
theorem lt_two_pow_natBitLength (v : ℕ) : v < 2 ^ natBitLength v := by
  unfold natBitLength; exact Nat.lt_pow_succ_log_self (by norm_num) v

theorem natBitLength_le_of_lt {v L : ℕ} (hL : 1 ≤ L) (h : v < 2 ^ L) : natBitLength v ≤ L := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · simp; omega
  · have := Nat.log_lt_of_lt_pow (by omega) h; omega

theorem one_le_natBitLength (v : ℕ) : 1 ≤ natBitLength v := by unfold natBitLength; omega

/-- `6 := natBitLength (a)`. -/
def natLenP (a : Var) : S :=
  .seq (.set 6 (.k 1)) (.whl (.lt (.shl (.k 1) (.v 6)) (.add (.v a) (.k 1))) (.set 6 (.add (.v 6) (.k 1))))

theorem natLenP_spec (s : FS) (a : Var) (ha : a ≠ 6) (hL : natBitLength (s.env a) + 2 ≤ G.K) (hN : G.K ≤ G.N) :
    (evalS G (natLenP a) s).env 6 = natBitLength (s.env a) ∧ Em [6] s (evalS G (natLenP a) s) [] := by
  set v := s.env a with hv
  set L := natBitLength v with hLdef
  have hcap := cap_add G
  have hKp : G.K < 2 ^ G.K := Nat.lt_two_pow_self
  have hvL : v < 2 ^ L := lt_two_pow_natBitLength v
  have hL1 : 1 ≤ L := one_le_natBitLength v
  have hpL : 2 ^ (L + 1) < 2 ^ G.K := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hpL2 : 2 * 2 ^ L < 2 ^ G.K := by rw [pow_succ] at hpL; omega
  have c1 : min 1 G.cap = 1 := min_eq_left (by omega)
  set s1 := s.setv 6 (min 1 G.cap) with hs1
  have e1 : Em [6] s s1 [] := Em.setv s (by simp) _
  have hw := whl_inv G (c := .lt (.shl (.k 1) (.v 6)) (.add (.v a) (.k 1))) (body := .set 6 (.add (.v 6) (.k 1)))
    (fun t => 1 ≤ t.env 6 ∧ t.env 6 ≤ L ∧ Em [6] s t []) (fun t => L - t.env 6) s1
    ⟨by simp [s1, c1], by simp [s1, c1]; omega, e1⟩ (by simp [s1, c1]; omega) (by
      rintro t ⟨t1, tL, te⟩ hc
      have ta : t.env a = v := te.env a (by simp [ha])
      have hpt : 2 ^ t.env 6 ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) tL
      have hsh : evalE G t (.shl (.k 1) (.v 6)) = 2 ^ t.env 6 := by
        simp only [evalE, c1, one_mul]; exact min_eq_left (by rw [pow_succ] at hpL; omega)
      have hadd : evalE G t (.add (.v a) (.k 1)) = v + 1 := by
        simp only [evalE, c1, ta]; exact min_eq_left (by omega)
      have hlt : 2 ^ t.env 6 < v + 1 := by
        by_contra hn; apply hc; rw [eE_lt hsh hadd, if_neg hn]
      have htL : t.env 6 < L := by
        by_contra hn
        have : t.env 6 = L := by omega
        rw [this] at hlt; omega
      have he : evalE G t (.add (.v 6) (.k 1)) = t.env 6 + 1 := by
        simp only [evalE, c1]; exact min_eq_left (by omega)
      simp only [evalS_set, he]
      refine ⟨⟨by simp, by simp; omega, te.trans (Em.setv t (by simp) _)⟩, by simp; omega⟩)
  obtain ⟨⟨w1, wL, we⟩, wc⟩ := hw
  have ht : evalS G (natLenP a) s = evalS G (.whl (.lt (.shl (.k 1) (.v 6)) (.add (.v a) (.k 1)))
      (.set 6 (.add (.v 6) (.k 1)))) s1 := rfl
  rw [ht]
  generalize evalS G (.whl (.lt (.shl (.k 1) (.v 6)) (.add (.v a) (.k 1))) (.set 6 (.add (.v 6) (.k 1)))) s1 = t
    at w1 wL we wc
  refine ⟨?_, we⟩
  have ta : t.env a = v := we.env a (by simp [ha])
  have hpt : 2 ^ t.env 6 ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) wL
  have hsh : evalE G t (.shl (.k 1) (.v 6)) = 2 ^ t.env 6 := by
    simp only [evalE, c1, one_mul]; exact min_eq_left (by rw [pow_succ] at hpL; omega)
  have hadd : evalE G t (.add (.v a) (.k 1)) = v + 1 := by
    simp only [evalE, c1, ta]; exact min_eq_left (by omega)
  have hge : v + 1 ≤ 2 ^ t.env 6 := by
    by_contra hn
    rw [eE_lt hsh hadd, if_pos (by omega)] at wc; exact absurd wc one_ne_zero
  have := natBitLength_le_of_lt w1 (show v < 2 ^ t.env 6 by omega)
  omega

/-! ## `natWord` -/

theorem natWord_eq_bits (v : ℕ) : natWord v = List.replicate (natBitLength v) true ++ false ::
    (List.range (natBitLength v)).map (fun j => v / 2 ^ j % 2 == 1) := by
  show WilliamsPublishedForm.framedNatBits v = _
  unfold WilliamsPublishedForm.framedNatBits WilliamsPublishedForm.fixedWidthNatBits
  congr 2
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ j) with h | h <;> simp [h]

theorem range_flatMap_true' (n : ℕ) : (List.range n).flatMap (fun _ => [true]) = List.replicate n true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ, List.flatMap_append, ih, List.replicate_succ']; rfl

/-- Print `natWord (a)` (scratch `5`, `6`). -/
def emitNatV (a : Var) : S :=
  .seq (natLenP a) (.seq (.loop 5 (.v 6) (emitF (.k 1))) (.seq (emitF (.k 0))
    (.loop 5 (.v 6) (emitF (.md (.shr (.v a) (.v 5)) (.k 2))))))

theorem emitNatV_spec (s : FS) (a : Var) (ha5 : a ≠ 5) (ha6 : a ≠ 6) (hL : natBitLength (s.env a) + 2 ≤ G.K)
    (hN : G.K ≤ G.N) : Em [5, 6] s (evalS G (emitNatV a) s) (natWord (s.env a)) := by
  set v := s.env a with hv
  set L := natBitLength v
  have hcap := cap_add G
  have hKp : G.K < 2 ^ G.K := Nat.lt_two_pow_self
  have h2 : 2 ≤ G.cap := by omega
  have ht : evalS G (emitNatV a) s = evalS G (.loop 5 (.v 6) (emitF (.md (.shr (.v a) (.v 5)) (.k 2))))
      (evalS G (emitF (.k 0)) (evalS G (.loop 5 (.v 6) (emitF (.k 1))) (evalS G (natLenP a) s))) := rfl
  rw [ht]
  obtain ⟨l6, e1⟩ := natLenP_spec (G := G) s a ha6 hL hN
  generalize hs1 : evalS G (natLenP a) s = s1 at l6 e1
  have s1a : s1.env a = v := e1.env a (by simp [ha6])
  have l6L : s1.env 6 = L := l6
  have hm : min (evalE G s1 (.v 6)) G.N = L := by rw [eE_v, l6L]; exact min_eq_left (by omega)
  have e2 := (Em_loop 5 (.v 6) (emitF (.k 1)) [5] (by simp) s1 L hm (fun _ => True) trivial (fun _ => [true])
    (fun j _ t _ _ => ⟨trivial, by
      have := emitF_spec (G := G) (t.setv 5 j) (.k 1) [5] (by omega)
      simpa [evalE, min_eq_left (show 1 ≤ G.cap by omega)] using this⟩)).2
  generalize hs2 : evalS G (.loop 5 (.v 6) (emitF (.k 1))) s1 = s2 at e2
  have e3 := emitF_spec (G := G) s2 (.k 0) [5] (by omega)
  generalize hs3 : evalS G (emitF (.k 0)) s2 = s3 at e3
  have s36 : s3.env 6 = L := by rw [e3.env 6 (by simp), e2.env 6 (by simp), l6L]
  have s3a : s3.env a = v := by rw [e3.env a (by simp [ha5]), e2.env a (by simp [ha5]), s1a]
  have hm' : min (evalE G s3 (.v 6)) G.N = L := by rw [eE_v, s36]; exact min_eq_left (by omega)
  have e4 := (Em_loop 5 (.v 6) (emitF (.md (.shr (.v a) (.v 5)) (.k 2))) [5] (by simp) s3 L hm' (fun _ => True) trivial
    (fun j => [v / 2 ^ j % 2 == 1]) (fun j _ t _ te => ⟨trivial, by
      have := emitF_spec (G := G) (t.setv 5 j) (.md (.shr (.v a) (.v 5)) (.k 2)) [5] (by omega)
      have ta : t.env a = v := by rw [te.env a (by simp [ha5]), s3a]
      have hv2 : evalE G (t.setv 5 j) (.md (.shr (.v a) (.v 5)) (.k 2)) = v / 2 ^ j % 2 := by
        simp only [evalE, FS.setv_env, Function.update_self, Function.update_of_ne ha5, ta]
        rw [min_eq_left h2]
      rw [hv2] at this
      have hb : (v / 2 ^ j % 2 != 0) = (v / 2 ^ j % 2 == 1) := by
        rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ j) with h | h <;> simp [h]
      rw [hb] at this; exact this⟩)).2
  generalize hs4 : evalS G (.loop 5 (.v 6) (emitF (.md (.shr (.v a) (.v 5)) (.k 2)))) s3 = s4 at e4
  have hall := (e1.mono (W' := [5, 6]) (by simp)).trans ((e2.trans (e3.trans e4)).mono (by simp))
  convert hall using 1
  rw [natWord_eq_bits, range_flatMap_true', evalE, min_eq_left (show 0 ≤ G.cap by omega)]
  simp [List.flatMap_singleton', List.map_eq_flatMap]
  rfl

end NearCubicGates.Adapters.RAMACSP.Gen
