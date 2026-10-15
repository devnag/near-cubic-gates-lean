import Proof.Wire_3_5.FinalPassFiltRef
import Proof.Wire_3_5.FinalPassListEvalCyc
import Proof.Wire_3_5.FinalPassWordMap

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Filt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## Layout -/

scoped notation "fZ" => (0 : Fin 7)
scoped notation "fF" => (1 : Fin 7)
scoped notation "fB" => (2 : Fin 7)
scoped notation "fA" => (3 : Fin 7)
scoped notation "fT" => (4 : Fin 7)
scoped notation "fU" => (5 : Fin 7)
scoped notation "fX" => (6 : Fin 7)

abbrev FProg := RM 2 7

/-- The state at a phase boundary: heads `z, t, u` (also held by the counters), flag `f`, budget `b`, accepted
visits `a`, failure flag `x`, cell `c`. -/
def S7 (z t u f b a x : ℕ) (c : Bool) : RState 2 7 := ⟨![z, t, u], ![z, f, b, a, t, u, x], c⟩

/-- Close an equality of phase states. -/
syntax "s7_eq" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| s7_eq) => `(tactic| s7_eq [])
  | `(tactic| s7_eq [$ts,*]) => `(tactic| (refine RState.eq ?_ ?_ ?_ <;>
      first
        | (funext i; fin_cases i <;> first | rfl | (simp [S7, $ts,*]; done) | (simp [S7, $ts,*] <;> omega))
        | rfl
        | (simp [$ts,*]; done)))

variable (inp : Fin 3 → List Bool) (cap : ℕ)

/-! ## Steps -/

theorem fwdT_spec (z t u f b a x : ℕ) (c : Bool) (ht : t < cap) :
    RExec inp cap (RM.fwdC 1 fT) (S7 z t u f b a x c) (S7 z (t + 1) u f b a x c) 5 :=
  RExec.cast inp cap (fwdC_spec inp cap 1 fT _ ht) (by s7_eq) le_rfl

theorem fwdZ_spec (z t u f b a x : ℕ) (c : Bool) (hz : z < cap) :
    RExec inp cap (RM.fwdC 0 fZ) (S7 z t u f b a x c) (S7 (z + 1) t u f b a x c) 5 :=
  RExec.cast inp cap (fwdC_spec inp cap 0 fZ _ hz) (by s7_eq) le_rfl

theorem fwdU_spec (z t u f b a x : ℕ) (c : Bool) (hu : u < cap) :
    RExec inp cap (RM.fwdC 2 fU) (S7 z t u f b a x c) (S7 z t (u + 1) f b a x c) 5 :=
  RExec.cast inp cap (fwdC_spec inp cap 2 fU _ hu) (by s7_eq) le_rfl

/-- Flip the parity flag. -/
def flipF : FProg := .ifr fF (.dec fF) (.inc fF)

theorem flipF_spec (z t u b a x : ℕ) (c fb : Bool) (hcap : 1 ≤ cap) :
    RExec inp cap flipF (S7 z t u fb.toNat b a x c) (S7 z t u (!fb).toNat b a x c) 4 := by
  cases fb
  · exact RExec.cast inp cap (RExec.ifrF (by rfl) (RExec.inc (inp := inp) (cap := cap) fF _ (by show 0 < cap; omega)))
      (by s7_eq) le_rfl
  · exact RExec.cast inp cap (RExec.ifrT (by show (1 : ℕ) ≠ 0; omega)
      (RExec.dec (inp := inp) (cap := cap) fF _ (by show 1 ≤ cap; omega))) (by s7_eq) (by omega)

/-- One coordinate: flip the flag when both scanned bits are one. -/
def bitStep7 : FProg := .ifs 1 (.ifs 0 flipF .skip) .skip

theorem bitStep7_spec (z t u b a x : ℕ) (c fb cb zb : Bool) (hcap : 1 ≤ cap)
    (hc : readTapeBit (inp 1) t = cb) (hz : readTapeBit (inp 0) z = zb) :
    RExec inp cap bitStep7 (S7 z t u fb.toNat b a x c) (S7 z t u (xor fb (cb && zb)).toNat b a x c) 6 := by
  cases cb
  · exact RExec.cast inp cap (RExec.ifsF hc (RExec.skip _)) (by cases fb <;> rfl) (by omega)
  · cases zb
    · exact RExec.cast inp cap (RExec.ifsT hc (RExec.ifsF hz (RExec.skip _))) (by cases fb <;> rfl) (by omega)
    · exact RExec.cast inp cap (RExec.ifsT hc (RExec.ifsT hz (flipF_spec inp cap z t u b a x c fb hcap)))
        (by cases fb <;> rfl) (by omega)

/-! ## One parity -/

/-- The parity loop over the framed coefficient word on stream 1 against the framed point on stream 0. -/
def dotLoop : FProg :=
  .whs 1 (.seq (RM.fwdC 1 fT) (.seq (RM.fwdC 0 fZ) (.seq bitStep7 (.seq (RM.fwdC 1 fT) (RM.fwdC 0 fZ)))))

theorem dotLoop_spec (restT restZ : List Bool) (hcap : 1 ≤ cap) :
    ∀ (cs zs : List Bool) (z t u b a x : ℕ) (fb c : Bool), cs.length ≤ zs.length →
      (inp 1).drop t = frameP cs ++ false :: restT → (inp 0).drop z = frameP zs ++ restZ →
      t + 2 * cs.length ≤ cap → z + 2 * cs.length ≤ cap →
      RExec inp cap dotLoop (S7 z t u fb.toNat b a x c)
        (S7 (z + 2 * cs.length) (t + 2 * cs.length) u (xor fb (parityDot cs zs)).toNat b a x c) (32 * cs.length + 1)
  | [], zs, z, t, u, b, a, x, fb, c, _, hT, _, _, _ => by
    have hr : readTapeBit (inp 1) t = false := ListEval.read_of_cons (by simpa using hT)
    exact RExec.cast inp cap (RExec.whsF hr) (by simp [parityDot]) le_rfl
  | c0 :: cs, zs, z, t, u, b, a, x, fb, c, hl, hT, hZ, hTc, hZc => by
    obtain ⟨z0, zs', rfl⟩ : ∃ z0 zs', zs = z0 :: zs' := by
      cases zs with
      | nil => simp at hl
      | cons z0 zs' => exact ⟨z0, zs', rfl⟩
    simp only [List.length_cons] at hl hTc hZc
    have hT0 : (inp 1).drop t = true :: c0 :: (frameP cs ++ false :: restT) := by simpa using hT
    have hZ0 : (inp 0).drop z = true :: z0 :: (frameP zs' ++ restZ) := by simpa using hZ
    have hT1 := ListEval.drop_succ_of_cons hT0
    have hZ1 := ListEval.drop_succ_of_cons hZ0
    have hT2 := ListEval.drop_succ_of_cons hT1
    have hZ2 := ListEval.drop_succ_of_cons hZ1
    have s1 := fwdT_spec inp cap z t u fb.toNat b a x c (by omega)
    have s2 := fwdZ_spec inp cap z (t + 1) u fb.toNat b a x c (by omega)
    have s3 := bitStep7_spec inp cap (z + 1) (t + 1) u b a x c fb c0 z0 hcap (ListEval.read_of_cons hT1)
      (ListEval.read_of_cons hZ1)
    have s4 := fwdT_spec inp cap (z + 1) (t + 1) u (xor fb (c0 && z0)).toNat b a x c (by omega)
    have s5 := fwdZ_spec inp cap (z + 1) (t + 1 + 1) u (xor fb (c0 && z0)).toNat b a x c (by omega)
    have ih := dotLoop_spec restT restZ hcap cs zs' (z + 1 + 1) (t + 1 + 1) u b a x (xor fb (c0 && z0)) c
      (by omega) hT2 hZ2 (by omega) (by omega)
    refine RExec.cast inp cap (RExec.whsT (ListEval.read_of_cons hT0)
      (RExec.seq s1 (RExec.seq s2 (RExec.seq s3 (RExec.seq s4 s5)))) ih) ?_ (by simp; omega)
    have e1 : z + 1 + 1 + 2 * cs.length = z + 2 * (cs.length + 1) := by omega
    have e2 : t + 1 + 1 + 2 * cs.length = t + 2 * (cs.length + 1) := by omega
    rw [e1, e2, List.length_cons, parityDot, Bool.xor_assoc]

/-- The parity pass: the loop, then the point is rewound. -/
def dotPass : FProg := .seq dotLoop (RM.rewind 0 fZ)

theorem dotPass_spec (restT restZ : List Bool) (hcap : 1 ≤ cap) (cs zs : List Bool) (t u b a x : ℕ) (fb c : Bool)
    (hl : cs.length ≤ zs.length) (hT : (inp 1).drop t = frameP cs ++ false :: restT)
    (hZ : (inp 0).drop 0 = frameP zs ++ restZ) (hTc : t + 2 * cs.length ≤ cap) (hZc : 2 * cs.length ≤ cap) :
    RExec inp cap dotPass (S7 0 t u fb.toNat b a x c)
      (S7 0 (t + 2 * cs.length) u (xor fb (parityDot cs zs)).toNat b a x c) (42 * cs.length + 3) := by
  have h1 := dotLoop_spec inp cap restT restZ hcap cs zs 0 t u b a x fb c hl hT hZ hTc (by omega)
  have h2 := rewind_spec inp cap 0 fZ (0 + 2 * cs.length)
    (S7 (0 + 2 * cs.length) (t + 2 * cs.length) u (xor fb (parityDot cs zs)).toNat b a x c) rfl
    (by show 0 + 2 * cs.length ≤ cap; omega)
  exact RExec.cast inp cap (RExec.seq h1 h2) (by s7_eq) (by omega)

/-! ## One copy, all copies -/

/-- Spend one unit of the budget when the parity is one; clear the flag. -/
def budget7 : FProg := .ifr fF (.seq (.dec fF) (.ifr fB (.dec fB) .skip)) .skip

theorem budget7_spec (t u b a x : ℕ) (c d : Bool) (hb : b ≤ cap) (hcap : 1 ≤ cap) :
    RExec inp cap budget7 (S7 0 t u d.toNat b a x c) (S7 0 t u 0 (if d then b - 1 else b) a x c) 5 := by
  cases d
  · exact RExec.cast inp cap (RExec.ifrF (by rfl) (RExec.skip _)) (by s7_eq) (by omega)
  · have h1 := RExec.dec (inp := inp) (cap := cap) fF (S7 0 t u 1 b a x c) (by show 1 ≤ cap; omega)
    by_cases hb0 : b = 0
    · subst hb0
      have h2 : RExec inp cap (.ifr fB (.dec fB) .skip) (S7 0 t u 0 0 a x c) (S7 0 t u 0 0 a x c) 1 :=
        RExec.ifrF (by rfl) (RExec.skip _)
      exact RExec.cast inp cap (RExec.ifrT (by show (1 : ℕ) ≠ 0; omega)
        (RExec.seq (RExec.cast inp cap h1 (by s7_eq) le_rfl) h2)) (by s7_eq) (by omega)
    · have h2 := RExec.dec (inp := inp) (cap := cap) fB (S7 0 t u 0 b a x c) (by show b ≤ cap; omega)
      exact RExec.cast inp cap (RExec.ifrT (by show (1 : ℕ) ≠ 0; omega)
        (RExec.seq (RExec.cast inp cap h1 (by s7_eq) le_rfl)
          (RExec.ifrT (by show b ≠ 0; omega) h2))) (by s7_eq) (by omega)

/-- One copy: past its marker, the parity pass, past the end marker, the budget. -/
def copy7 : FProg := .seq (RM.fwdC 1 fT) (.seq dotPass (.seq (RM.fwdC 1 fT) budget7))

theorem copy7_spec (restT restZ : List Bool) (hcap : 1 ≤ cap) (cs Z : List Bool) (t u b a x : ℕ) (c : Bool)
    (hl : cs.length ≤ Z.length) (hT : (inp 1).drop t = copyWord cs ++ restT) (hZ : (inp 0).drop 0 = frameP Z ++ restZ)
    (hTc : t + (copyWord cs).length ≤ cap) (hZc : 2 * Z.length ≤ cap) (hb : b ≤ cap) :
    RExec inp cap copy7 (S7 0 t u 0 b a x c)
      (S7 0 (t + (copyWord cs).length) u 0 (if parityDot cs Z then b - 1 else b) a x c) (42 * cs.length + 21) := by
  have hlen : (copyWord cs).length = 2 * cs.length + 2 := by simp [copyWord, frame_eq_frameP]
  have hT0 : (inp 1).drop t = true :: (frameP cs ++ false :: restT) := by
    rw [hT]; simp [copyWord, frame_eq_frameP]
  have hT1 := ListEval.drop_succ_of_cons hT0
  have s1 := fwdT_spec inp cap 0 t u 0 b a x c (by omega)
  have s2 := dotPass_spec inp cap restT restZ hcap cs Z (t + 1) u b a x false c hl hT1 hZ (by omega) (by omega)
  rw [Bool.false_xor] at s2
  have s3 := fwdT_spec inp cap 0 (t + 1 + 2 * cs.length) u (parityDot cs Z).toNat b a x c (by omega)
  have s4 := budget7_spec inp cap (t + 1 + 2 * cs.length + 1) u b a x c (parityDot cs Z) hb hcap
  refine RExec.cast inp cap (RExec.seq s1 (RExec.seq s2 (RExec.seq s3 s4))) ?_ (by omega)
  rw [hlen, show t + 1 + 2 * cs.length + 1 = t + (2 * cs.length + 2) by omega]

theorem filter_parityDot_length (Z : List Bool) (cs : List Bool) (vs : List (List Bool)) :
    ((cs :: vs).filter fun c => parityDot c Z).length =
      (vs.filter fun c => parityDot c Z).length + if parityDot cs Z then 1 else 0 := by
  by_cases h : parityDot cs Z <;> simp [h]

theorem flatMap_copyWord_length (vs : List (List Bool)) (cs : List Bool) :
    ((cs :: vs).flatMap copyWord).length = (copyWord cs).length + (vs.flatMap copyWord).length := by
  simp

/-- All copies of one visit. -/
def copies7 : FProg := .whs 1 copy7

theorem copies7_spec (restT restZ : List Bool) (hcap : 1 ≤ cap) (Z : List Bool) (hZ : (inp 0).drop 0 = frameP Z ++ restZ)
    (hZc : 2 * Z.length ≤ cap) :
    ∀ (vs : List (List Bool)) (t u b a x : ℕ) (c : Bool), (∀ cs ∈ vs, cs.length ≤ Z.length) →
      (inp 1).drop t = vs.flatMap copyWord ++ false :: restT → t + (vs.flatMap copyWord).length ≤ cap → b ≤ cap →
      RExec inp cap copies7 (S7 0 t u 0 b a x c)
        (S7 0 (t + (vs.flatMap copyWord).length) u 0 (b - (vs.filter fun c => parityDot c Z).length) a x c)
        (23 * (vs.flatMap copyWord).length + 1)
  | [], t, u, b, a, x, c, _, hT, _, _ => by
    have hr : readTapeBit (inp 1) t = false := ListEval.read_of_cons (by simpa using hT)
    exact RExec.cast inp cap (RExec.whsF hr) (by simp) (by simp)
  | cs :: vs, t, u, b, a, x, c, hlen, hT, hTc, hb => by
    have hT' : (inp 1).drop t = copyWord cs ++ (vs.flatMap copyWord ++ false :: restT) := by rw [hT]; simp
    have hlc := flatMap_copyWord_length vs cs
    have hcw : (copyWord cs).length = 2 * cs.length + 2 := by simp [copyWord, frame_eq_frameP]
    have s1 := copy7_spec inp cap _ restZ hcap cs Z t u b a x c (hlen cs (by simp)) hT' hZ (by omega) hZc hb
    have hread : readTapeBit (inp 1) t = true := ListEval.read_of_cons
      (show (inp 1).drop t = true :: (frame cs ++ (vs.flatMap copyWord ++ false :: restT)) from hT')
    have hT2 := ListEval.drop_add_of_append hT'
    have ih := copies7_spec restT restZ hcap Z hZ hZc vs (t + (copyWord cs).length) u
      (if parityDot cs Z then b - 1 else b) a x c (fun c hc => hlen c (by simp [hc])) hT2 (by omega) (by split <;> omega)
    refine RExec.cast inp cap (RExec.whsT hread s1 ih) ?_ (by rw [hlc]; omega)
    rw [hlc, filter_parityDot_length, Nat.add_assoc]
    by_cases h : parityDot cs Z
    · simp only [h, if_true]; rw [Nat.sub_sub, Nat.add_comm 1]
    · simp only [h, if_false, Bool.false_eq_true, Nat.add_zero]

/-! ## One visit, all visits -/

/-- `r += k`. -/
def incN7 (r : Fin 7) : ℕ → FProg
  | 0 => .skip
  | k + 1 => .seq (.inc r) (incN7 r k)

theorem incB_spec (t u a x : ℕ) (c : Bool) : ∀ (k b : ℕ), b + k ≤ cap →
    RExec inp cap (incN7 fB k) (S7 0 t u 0 b a x c) (S7 0 t u 0 (b + k) a x c) (4 * k)
  | 0, b, _ => RExec.cast inp cap (RExec.skip _) (by simp) le_rfl
  | k + 1, b, hk => by
    have h1 := RExec.inc (inp := inp) (cap := cap) fB (S7 0 t u 0 b a x c) (by show b < cap; omega)
    have h2 := incB_spec t u a x c k (b + 1) (by omega)
    exact RExec.cast inp cap (RExec.seq (RExec.cast inp cap h1 (by s7_eq) le_rfl) h2)
      (by rw [Nat.add_assoc, Nat.add_comm 1 k]) (by omega)

/-- One visit: past its marker, a budget of `33`, the copies, past the end marker, count an accepting visit, clear
the budget. -/
def visit7 : FProg :=
  .seq (RM.fwdC 1 fT) (.seq (incN7 fB 33) (.seq copies7 (.seq (RM.fwdC 1 fT) (.seq (.ifr fB (.inc fA) .skip)
    (RM.clear fB)))))

theorem visit7_spec (restT restZ : List Bool) (hcap : 40 ≤ cap) (Z : List Bool)
    (hZ : (inp 0).drop 0 = frameP Z ++ restZ) (hZc : 2 * Z.length ≤ cap)
    (vs : List (List Bool)) (t u a x : ℕ) (c : Bool) (hlen : ∀ cs ∈ vs, cs.length ≤ Z.length)
    (hT : (inp 1).drop t = visitWord vs ++ restT) (hTc : t + (visitWord vs).length ≤ cap) (ha : a < cap) :
    RExec inp cap visit7 (S7 0 t u 0 0 a x c)
      (S7 0 (t + (visitWord vs).length) u 0 0 (a + if visitOk vs Z then 1 else 0) x c)
      (130 * (visitWord vs).length) := by
  have hvw : (visitWord vs).length = (vs.flatMap copyWord).length + 2 := by simp [visitWord]
  have hT0 : (inp 1).drop t = true :: (vs.flatMap copyWord ++ false :: restT) := by rw [hT]; simp [visitWord]
  have hT1 := ListEval.drop_succ_of_cons hT0
  have s1 := fwdT_spec inp cap 0 t u 0 0 a x c (by omega)
  have s2 := incB_spec inp cap (t + 1) u a x c 33 0 (by omega)
  simp only [Nat.zero_add] at s2
  have s3 := copies7_spec inp cap restT restZ (by omega) Z hZ hZc vs (t + 1) u 33 a x c hlen hT1 (by omega) (by omega)
  have hT2 := ListEval.drop_add_of_append hT1
  have s4 := fwdT_spec inp cap 0 (t + 1 + (vs.flatMap copyWord).length) u 0
    (33 - (vs.filter fun c => parityDot c Z).length) a x c (by omega)
  generalize hk : (vs.filter fun c => parityDot c Z).length = k at s3 s4
  have hok : visitOk vs Z = decide (k ≤ 32) := by simp [visitOk, hk]
  obtain ⟨σ4, hσ4⟩ : ∃ σ, σ = S7 0 (t + 1 + (vs.flatMap copyWord).length + 1) u 0 (33 - k) a x c := ⟨_, rfl⟩
  rw [← hσ4] at s4
  by_cases hk32 : k ≤ 32
  · have s5 : RExec inp cap (.ifr fB (.inc fA) .skip) σ4
        (S7 0 (t + 1 + (vs.flatMap copyWord).length + 1) u 0 (33 - k) (a + 1) x c) 4 := by
      rw [hσ4]
      exact RExec.cast inp cap (RExec.ifrT (by show 33 - k ≠ 0; omega)
        (RExec.inc (inp := inp) (cap := cap) fA _ (by show a < cap; omega))) (by s7_eq) le_rfl
    have s6 := clear_spec inp cap fB (33 - k)
      (S7 0 (t + 1 + (vs.flatMap copyWord).length + 1) u 0 (33 - k) (a + 1) x c) rfl (by show 33 - k ≤ cap; omega)
    refine RExec.cast inp cap (RExec.seq s1 (RExec.seq s2 (RExec.seq s3 (RExec.seq s4 (RExec.seq s5 s6))))) ?_
      (by omega)
    rw [hok, decide_eq_true hk32, if_pos rfl]
    s7_eq [hvw]
  · have hk0 : 33 - k = 0 := by omega
    have s5 : RExec inp cap (.ifr fB (.inc fA) .skip) σ4 σ4 1 := by
      rw [hσ4, hk0]; exact RExec.ifrF (by rfl) (RExec.skip _)
    have s6 := clear_spec inp cap fB 0 σ4 (by rw [hσ4, hk0]; rfl) (by rw [hσ4, hk0]; show 0 ≤ cap; omega)
    refine RExec.cast inp cap (RExec.seq s1 (RExec.seq s2 (RExec.seq s3 (RExec.seq s4 (RExec.seq s5 s6))))) ?_
      (by omega)
    rw [hok, decide_eq_false hk32, hσ4]
    s7_eq [hvw]

/-- All visits. -/
def visits7 : FProg := .whs 1 visit7

theorem visits7_spec (restT restZ : List Bool) (hcap : 40 ≤ cap) (Z : List Bool)
    (hZ : (inp 0).drop 0 = frameP Z ++ restZ) (hZc : 2 * Z.length ≤ cap) :
    ∀ (tbl : List (List (List Bool))) (t u a x : ℕ) (c : Bool), (∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ Z.length) →
      (inp 1).drop t = tbl.flatMap visitWord ++ false :: restT → t + (tbl.flatMap visitWord).length ≤ cap →
      a + tbl.length ≤ cap →
      RExec inp cap visits7 (S7 0 t u 0 0 a x c)
        (S7 0 (t + (tbl.flatMap visitWord).length) u 0 0 (a + (tbl.filter fun vs => visitOk vs Z).length) x c)
        (132 * (tbl.flatMap visitWord).length + 1)
  | [], t, u, a, x, c, _, hT, _, _ => by
    have hr : readTapeBit (inp 1) t = false := ListEval.read_of_cons (by simpa using hT)
    exact RExec.cast inp cap (RExec.whsF hr) (by simp) (by simp)
  | vs :: tbl, t, u, a, x, c, hlen, hT, hTc, ha => by
    have hT' : (inp 1).drop t = visitWord vs ++ (tbl.flatMap visitWord ++ false :: restT) := by rw [hT]; simp
    have hl : ((vs :: tbl).flatMap visitWord).length = (visitWord vs).length + (tbl.flatMap visitWord).length := by
      simp
    simp only [List.length_cons] at ha
    have s1 := visit7_spec inp cap _ restZ hcap Z hZ hZc vs t u a x c (hlen vs (by simp)) hT' (by omega) (by omega)
    have hread : readTapeBit (inp 1) t = true := ListEval.read_of_cons
      (show (inp 1).drop t = true :: ((vs.flatMap copyWord ++ [false]) ++ (tbl.flatMap visitWord ++ false :: restT))
        from hT')
    have hT2 := ListEval.drop_add_of_append hT'
    have ih := visits7_spec restT restZ hcap Z hZ hZc tbl (t + (visitWord vs).length) u
      (a + if visitOk vs Z then 1 else 0) x c (fun v hv => hlen v (by simp [hv])) hT2 (by omega) (by split <;> omega)
    have hvw2 : 2 ≤ (visitWord vs).length := by simp [visitWord]
    refine RExec.cast inp cap (RExec.whsT hread s1 ih) ?_ (by rw [hl]; omega)
    rw [hl, Nat.add_assoc]
    by_cases h : visitOk vs Z
    · simp only [h, if_true, List.filter_cons, List.length_cons]; rw [Nat.add_assoc, Nat.add_comm 1]
    · simp only [h, if_false, Bool.false_eq_true, List.filter_cons, Nat.add_zero]

/-! ## The comparison and the end -/

/-- Compare the accepted count with the threshold `1^thr 0` on stream 2: `X := [A < thr]`. -/
def cmp7 : FProg := .whs 2 (.seq (RM.fwdC 2 fU) (.ifr fA (.dec fA) (RM.setF fX)))

theorem cmp7_spec (restU : List Bool) (T : ℕ) (c : Bool) (hcap : 1 ≤ cap) :
    ∀ (k u a : ℕ) (xb : Bool), (inp 2).drop u = List.replicate k true ++ false :: restU → u + k ≤ cap → a ≤ cap →
      RExec inp cap cmp7 (S7 0 T u 0 0 a xb.toNat c) (S7 0 T (u + k) 0 0 (a - k) (xb || decide (a < k)).toNat c)
        (13 * k + 1)
  | 0, u, a, xb, hU, _, _ => by
    have hr : readTapeBit (inp 2) u = false := ListEval.read_of_cons (by simpa using hU)
    exact RExec.cast inp cap (RExec.whsF hr) (by simp) le_rfl
  | k + 1, u, a, xb, hU, hUc, ha => by
    have hU0 : (inp 2).drop u = true :: (List.replicate k true ++ false :: restU) := by
      rw [hU, List.replicate_succ, List.cons_append]
    have hU1 := ListEval.drop_succ_of_cons hU0
    have s1 := fwdU_spec inp cap 0 T u 0 0 a xb.toNat c (by omega)
    by_cases ha0 : a = 0
    · subst ha0
      have s2 := setF_spec inp cap fX (S7 0 T (u + 1) 0 0 0 xb.toNat c) (by show xb.toNat ≤ 1; cases xb <;> simp)
        hcap
      have s2' : RExec inp cap (.ifr fA (.dec fA) (RM.setF fX)) (S7 0 T (u + 1) 0 0 0 xb.toNat c)
          (S7 0 T (u + 1) 0 0 0 (true).toNat c) 5 :=
        RExec.cast inp cap (RExec.ifrF (by rfl) s2) (by s7_eq) le_rfl
      have ih := cmp7_spec restU T c hcap k (u + 1) 0 true hU1 (by omega) (by omega)
      refine RExec.cast inp cap (RExec.whsT (ListEval.read_of_cons hU0) (RExec.seq s1 s2') ih) ?_ (by omega)
      rw [show u + 1 + k = u + (k + 1) by omega]
      simp
    · have s2 := RExec.dec (inp := inp) (cap := cap) fA (S7 0 T (u + 1) 0 0 a xb.toNat c) (by show a ≤ cap; omega)
      have s2' : RExec inp cap (.ifr fA (.dec fA) (RM.setF fX)) (S7 0 T (u + 1) 0 0 a xb.toNat c)
          (S7 0 T (u + 1) 0 0 (a - 1) xb.toNat c) 2 :=
        RExec.cast inp cap (RExec.ifrT (by show a ≠ 0; omega) s2) (by s7_eq) le_rfl
      have ih := cmp7_spec restU T c hcap k (u + 1) (a - 1) xb hU1 (by omega) (by omega)
      refine RExec.cast inp cap (RExec.whsT (ListEval.read_of_cons hU0) (RExec.seq s1 s2') ih) ?_ (by omega)
      have e1 : u + 1 + k = u + (k + 1) := by omega
      have e2 : a - 1 - k = a - (k + 1) := by omega
      have e3 : decide (a - 1 < k) = decide (a < k + 1) := by
        rw [decide_eq_decide]; omega
      rw [e1, e2, e3]

/-- Write `[thr ≤ A]`. -/
def out7 : FProg := .ifr fX (.setc false) (.setc true)

/-- Clear the counts, rewind the threshold and the table. -/
def cleanup7 : FProg := .seq (RM.clear fA) (.seq (RM.clear fX) (.seq (RM.rewind 2 fU) (RM.rewind 1 fT)))

/-- **The stage-7 program.** -/
def main7 : FProg := .seq visits7 (.seq cmp7 (.seq out7 cleanup7))

/-- The streams: the framed point, the table word, the threshold. -/
def streams7 (Z : List Bool) (tbl : List (List (List Bool))) (thr : ℕ) : Fin 3 → List Bool :=
  ![frame Z, tableWord tbl, ListEval.unary thr]

/-- The register capacity: the table word, the point, the threshold. -/
def capOf7 (L : ℕ) (tbl : List (List (List Bool))) (thr : ℕ) : ℕ :=
  (tableWord tbl).length + 2 * L + thr + 40

/-- One step bound. -/
def cost7 (W thr : ℕ) : ℕ := 140 * W + 20 * thr + 30

theorem visits_le_word (tbl : List (List (List Bool))) : tbl.length ≤ (tbl.flatMap visitWord).length := by
  induction tbl with
  | nil => simp
  | cons vs tbl ih => simp [visitWord]; omega

/-- **The stage-7 evaluator**: from the blank state, the cell becomes `tabEval thr tbl Z`. -/
theorem main7_spec (Z : List Bool) (tbl : List (List (List Bool))) (thr : ℕ) (b : Bool)
    (hlen : ∀ vs ∈ tbl, ∀ cs ∈ vs, cs.length ≤ Z.length) (hcap : capOf7 Z.length tbl thr ≤ cap) :
    RExec (streams7 Z tbl thr) cap main7 (S7 0 0 0 0 0 0 0 b) (S7 0 0 0 0 0 0 0 (tabEval thr tbl Z))
      (cost7 (tableWord tbl).length thr) := by
  have hW : (tableWord tbl).length = (tbl.flatMap visitWord).length + 1 := by simp [tableWord]
  have hvl := visits_le_word tbl
  unfold capOf7 at hcap
  have hZ : (streams7 Z tbl thr 0).drop 0 = frameP Z ++ [false] := by simp [streams7, frame_eq_frameP]
  have hT : (streams7 Z tbl thr 1).drop 0 = tbl.flatMap visitWord ++ false :: [] := by simp [streams7, tableWord]
  have hU : (streams7 Z tbl thr 2).drop 0 = List.replicate thr true ++ false :: [] := by
    simp [streams7, ListEval.unary]
  have s1 := visits7_spec (streams7 Z tbl thr) cap [] [false] (by omega) Z hZ (by omega) tbl 0 0 0 0 b hlen hT
    (by omega) (by omega)
  simp only [Nat.zero_add] at s1
  generalize hA : (tbl.filter fun vs => visitOk vs Z).length = A at s1
  have hAl : A ≤ tbl.length := by rw [← hA]; exact List.length_filter_le _ _
  have s2 := cmp7_spec (streams7 Z tbl thr) cap [] (tbl.flatMap visitWord).length b (by omega) thr 0 A false hU
    (by omega) (by omega)
  simp only [Nat.zero_add, Bool.false_or] at s2
  have hres : tabEval thr tbl Z = !decide (A < thr) := by
    unfold tabEval; rw [hA]; simp only [← Nat.not_lt, decide_not]
  -- the output
  have s3 : RExec (streams7 Z tbl thr) cap out7
      (S7 0 (tbl.flatMap visitWord).length thr 0 0 (A - thr) (decide (A < thr)).toNat b)
      (S7 0 (tbl.flatMap visitWord).length thr 0 0 (A - thr) (decide (A < thr)).toNat (tabEval thr tbl Z)) 2 := by
    rw [hres]
    by_cases h : A < thr
    · have e : (decide (A < thr)).toNat = 1 := by simp [h]
      rw [e]
      exact RExec.cast _ cap (RExec.ifrT (by show (1 : ℕ) ≠ 0; omega) (RExec.setc (inp := streams7 Z tbl thr) (cap := cap)
        false _)) (by simp [h]; s7_eq) le_rfl
    · have e : (decide (A < thr)).toNat = 0 := by simp [h]
      rw [e]
      exact RExec.cast _ cap (RExec.ifrF (by rfl) (RExec.setc (inp := streams7 Z tbl thr) (cap := cap) true _))
        (by simp [h]; s7_eq) le_rfl
  -- the cleanup
  have c1 := clear_spec (streams7 Z tbl thr) cap fA (A - thr)
    (S7 0 (tbl.flatMap visitWord).length thr 0 0 (A - thr) (decide (A < thr)).toNat (tabEval thr tbl Z)) rfl
    (by show A - thr ≤ cap; omega)
  have hx : (decide (A < thr)).toNat ≤ 1 := by cases decide (A < thr) <;> simp
  have c2 := clear_spec (streams7 Z tbl thr) cap fX (decide (A < thr)).toNat
    (S7 0 (tbl.flatMap visitWord).length thr 0 0 0 (decide (A < thr)).toNat (tabEval thr tbl Z)) rfl
    (by show (decide (A < thr)).toNat ≤ cap; omega)
  have c3 := rewind_spec (streams7 Z tbl thr) cap 2 fU thr
    (S7 0 (tbl.flatMap visitWord).length thr 0 0 0 0 (tabEval thr tbl Z)) rfl (by show thr ≤ cap; omega)
  have c4 := rewind_spec (streams7 Z tbl thr) cap 1 fT (tbl.flatMap visitWord).length
    (S7 0 (tbl.flatMap visitWord).length 0 0 0 0 0 (tabEval thr tbl Z)) rfl
    (by show (tbl.flatMap visitWord).length ≤ cap; omega)
  refine RExec.cast _ cap (RExec.seq s1 (RExec.seq s2 (RExec.seq s3 (RExec.seq
    (RExec.cast _ cap c1 (by s7_eq) le_rfl) (RExec.seq (RExec.cast _ cap c2 (by s7_eq) le_rfl)
      (RExec.seq (RExec.cast _ cap c3 (by s7_eq) le_rfl) c4)))))) (by s7_eq) ?_
  unfold cost7
  rw [hW]
  omega

end NearCubicWires.WireExponent3_5.FinalPass.Filt
