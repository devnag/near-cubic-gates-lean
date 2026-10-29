import Proof.Gates.Cells.Kit

/-!
# Last printing stage: the framed bits of the query number

proof of `lem:multitape-refuter` (the native balanced query is written as a framed word) and the program contract
`CNFAssembly.CNFProgramRuns`, whose printed word is `frame (sourceSATCode (requestFormula r)).bits`. With polynomially
wide cells the whole query number sits in one register; this stage prints `frame v.bits` (least significant bit
first, `Nat.bits`) by halving.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells
set_option autoImplicit false

/-- The framed pairs of a word: `frame l = framedPairs l ++ [false]`. -/
def framedPairs (l : List Bool) : List Bool := l.flatMap (fun b => [true, b])

theorem framedPairs_append (l1 l2 : List Bool) : framedPairs (l1 ++ l2) = framedPairs l1 ++ framedPairs l2 := by
  simp [framedPairs]

theorem frame_eq_framedPairs (l : List Bool) : RepairOrdinary.frame l = framedPairs l ++ [false] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [RepairOrdinary.frame, framedPairs, ih]

theorem bits_eq_range (v : ℕ) : v.bits = (List.range v.size).map v.testBit := by
  apply List.ext_getElem
  · simp [Nat.size_eq_bits_len]
  · intro i h1 _
    rw [List.getElem_map, List.getElem_range, Nat.testBit_eq_inth, List.getI_eq_getElem _ h1]

/-- One halving step: print `true` and the low bit, keep the quotient. -/
def emitBitsBody : St VV MM :=
  .seq (.op (.dm t5 v2 t8 t9)) (.seq (.op (.emit true)) (.seq (emitB .emit t9) (.op (.copy t5 t8))))

/-- Print `frame (env x).bits` (scratch `t5 t8 t9`). -/
def emitBitsF (x : Fin VV) : St VV MM :=
  .seq (.op (.copy t5 x)) (.seq (.loop (.lt vZ t5) emitBitsBody) (.op (.emit false)))

variable {C : Ctx}

theorem emitBitsF_spec (x : Fin VV) (hx : x ≠ t5) (a : DS VV MM) (hc : Cst a) (hW : 2 ≤ C.Wd) :
    Hs C (emitBitsF x) a (10 * Nat.size (a.env x) + 6) (fun b =>
      b.out = a.out ++ RepairOrdinary.frame (a.env x).bits ∧ b.ip = a.ip ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
        Fr a b [t5, t8, t9] ∧ Cst b) := by
  set v := a.env x with hvdef
  set ℓ := Nat.size v with hℓ
  have h4 : (4 : ℕ) ≤ 2 ^ C.Wd := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) hW
  let I : ℕ → DS VV MM → Prop := fun k b => b.env t5 = v / 2 ^ k ∧
    b.out = a.out ++ framedPairs ((List.range k).map v.testBit) ∧ b.ip = a.ip ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
    Fr a b [t5, t8, t9]
  have hloop : ∀ b, I 0 b → Hs C (.loop (.lt vZ t5) emitBitsBody) b (ℓ * (8 + 2) + 2) (I ℓ) := by
    refine Hs.loopN (c := .lt vZ t5) (show vZ ≠ t5 by decide) I ℓ 8 ?_ ?_
    · intro k hk b ⟨h1, hout, hip, hram, hrc, h6⟩
      have bv1 : b.env v1 = 1 := by rw [h6 v1 (by decide)]; exact hc.one
      have bv2 : b.env v2 = 2 := by rw [h6 v2 (by decide)]; exact hc.two
      have bz : b.env vZ = 0 := by rw [h6 vZ (by decide)]; exact hc.z
      have hpos : 0 < v / 2 ^ k := Nat.div_pos (Nat.lt_size.1 hk) (by positivity)
      refine ⟨by simp only [Cnd.eval, bz, h1, decide_eq_true_eq]; exact hpos, ?_⟩
      refine Hs.seq (t1 := 1) (t2 := 6) (hs_dm C t5 v2 t8 t9 b (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by rw [bv2]; norm_num) (by rw [bv2]; omega)) (fun d hd => ?_)
      subst hd
      refine Hs.seq (t1 := 1) (t2 := 4) (hs_emit C true _) (fun d2 hd2 => ?_)
      subst hd2
      have dc : Cst { (b.set t8 (b.env t5 / b.env v2)).set t9 (b.env t5 % b.env v2) with
          out := ((b.set t8 (b.env t5 / b.env v2)).set t9 (b.env t5 % b.env v2)).out ++ [true] } :=
        ⟨by vsimp [bz], by vsimp [bv1], by vsimp [bv2]⟩
      refine Hs.seq (t1 := 2) (t2 := 1) (emitB_spec (snkO C) t9 (by decide) _ dc trivial) (fun e he => ?_)
      obtain ⟨e1, e2, e4⟩ := he
      simp only [snkO, Prod.mk.injEq] at e1 e2
      refine Hs.mono (hs_copy C t5 t8 e (by decide)) le_rfl ?_
      rintro g rfl
      have et9 : decide (((b.set t8 (b.env t5 / b.env v2)).set t9 (b.env t5 % b.env v2)).env t9 = 1) =
          v.testBit k := by vsimp [h1, bv2]; rw [Nat.testBit_eq_decide_div_mod_eq]
      refine ⟨by vsimp [e4, h1, bv2, Nat.div_div_eq_div_mul, pow_succ], ?_, ?_, ?_, ?_, ?_⟩
      · simp only [DS.set_out]
        rw [e1, et9]
        simp only [DS.set_out]
        rw [hout, List.range_succ, List.map_append, framedPairs_append]
        simp [framedPairs, List.append_assoc]
      · simp only [DS.set_ip]; rw [e2.1]; simp [hip]
      · simp only [DS.set_ram]; rw [e2.2.1]; simpa using hram
      · simp only [DS.set_rc]; rw [e2.2.2.1]; simpa using hrc
      · intro y hy
        have hy' : y ∉ [t5, t8, t9] := hy
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy'
        vsimp [Function.update_of_ne hy'.1, e4, Function.update_of_ne hy'.2.1, Function.update_of_ne hy'.2.2,
          h6 y hy]
    · intro b hb
      obtain ⟨h1, _, _, _, _, h6⟩ := hb
      have bz : b.env vZ = 0 := by rw [h6 vZ (by decide)]; exact hc.z
      simp only [Cnd.eval, bz, h1, decide_eq_false_iff_not, not_lt, Nat.le_zero]
      exact Nat.div_eq_of_lt (Nat.lt_size_self v)
  have e : 10 * ℓ + 6 = 1 + (ℓ * (8 + 2) + 2 + 1 + 1) + 1 := by ring
  rw [e]
  unfold emitBitsF
  refine Hs.seq (t1 := 1) (t2 := ℓ * (8 + 2) + 2 + 1 + 1) (hs_copy C t5 x a (Ne.symm hx)) (fun b0 hb0 => ?_)
  subst hb0
  refine Hs.seq (t1 := ℓ * (8 + 2) + 2) (t2 := 1) (hloop (a.set t5 (a.env x)) ⟨by rw [DS.set_env_self, pow_zero, Nat.div_one], by simp [framedPairs], rfl, rfl, rfl,
    Fr.set a (x := t5) (T := [t5, t8, t9]) v (by decide)⟩)
    (fun b1 hb1 => ?_)
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := hb1
  refine Hs.mono (hs_emit C false b1) le_rfl ?_
  rintro g rfl
  refine ⟨?_, q3, q4, q5, q6, ?_⟩
  · simp only
    rw [q2, frame_eq_framedPairs, bits_eq_range, List.append_assoc]
  · exact Cst.of_fr hc q6 (by decide)

end NearCubicGates.Adapters.Compile
