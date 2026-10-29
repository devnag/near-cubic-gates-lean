import SourceAdapters.Compile.CNFBalancedC
import Proof.Foundations.CanonicalBinary

/-!
# Reading the request

proof of `lem:multitape-refuter` (the request is the native verifier code, the actual input and the unary resource data; its length is
paid) and the join's `CNFCompilationRequest.word` (five frames). The printing program skips the paid size header
(`Kit.rdNatI_spec`), then reads the five frames: the code bits into `sCB`, the input bits into `sIB` (length in
`dIL`), the witness length into `dN`, the fuel into `dF` (both unary) and `high` into `dH` (`bitsValue` of its bits,
`CanonicalBinary.bitsValue_natBits`). `rdFrP` is one generic frame reader (flag in `pA`, data bit in `pB`).

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.CanonicalBinary NearCubicWires.RepairOrdinary
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

def pA : Fin VV := ⟨100, by decide⟩
def pB : Fin VV := ⟨101, by decide⟩
def pC : Fin VV := ⟨102, by decide⟩
def pT : Fin VV := ⟨103, by decide⟩
def pX : Fin VV := ⟨104, by decide⟩

variable {C : Ctx}

theorem bitOf_frame (inp l rest : List Bool) (ip q : ℕ) (hin : inp.drop ip = frame l ++ rest)
    (hq : q < 2 * l.length + 1) :
    bitOf inp (ip + q) = (if q % 2 = 0 then decide (q / 2 < l.length) else l.getD (q / 2) false).toNat := by
  have hf := frame_len l
  unfold bitOf
  congr 1
  have e : inp.getD (ip + q) false = (inp.drop ip).getD q false := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  rw [e, hin, List.getD_append _ _ _ _ (by omega)]
  exact frame_read l q

theorem drop_frame (inp l rest : List Bool) (ip : ℕ) (hin : inp.drop ip = frame l ++ rest) :
    inp.drop (ip + (2 * l.length + 1)) = rest := by
  rw [← List.drop_drop, hin, ← frame_len, List.drop_left]

/-- Read one frame: the flag into `pA`; while it is `1`, the data bit into `pB`, then `act`. -/
def rdFrP (act : St VV MM) : St VV MM :=
  .seq (.op (.rdI pA)) (.loop (.eq pA v1) (.seq (.op (.rdI pB)) (.seq act (.op (.rdI pA)))))

theorem rdFrP_spec (act : St VV MM) (l rest : List Bool) (Q : ℕ → DS VV MM → Prop) (t : ℕ) (a : DS VV MM)
    (hin : C.inp.drop a.ip = frame l ++ rest) (hQ0 : Q 0 a)
    (hv1 : ∀ k b, Q k b → b.env v1 = 1)
    (hQA : ∀ k b v, Q k b → Q k { b.set pA v with ip := b.ip + 1 })
    (hQB : ∀ k b v, Q k b → Q k { b.set pB v with ip := b.ip + 1 })
    (hact : ∀ k < l.length, ∀ b, Q k b → b.env pB = (l.getD k false).toNat →
      Hs C act b t (fun d => Q (k + 1) d ∧ d.ip = b.ip)) :
    Hs C (rdFrP act) a (l.length * (t + 6) + 4) (fun b => Q l.length b ∧ b.ip = a.ip + 2 * l.length + 1) := by
  have hf := frame_len l
  have hlen : a.ip + 2 * l.length + 1 ≤ C.inp.length := by
    have := congrArg List.length hin; simp [List.length_drop, hf] at this; omega
  let I : ℕ → DS VV MM → Prop := fun k b =>
    Q k b ∧ b.ip = a.ip + 2 * k + 1 ∧ b.env pA = (decide (k < l.length)).toNat
  have hloop := Hs.loopN (C := C) (c := .eq pA v1) (s := .seq (.op (.rdI pB)) (.seq act (.op (.rdI pA))))
    (show pA ≠ v1 by decide) I l.length (t + 4)
    (fun k hk b ⟨hq, hip, hfl⟩ => by
      refine ⟨by simp [Cnd.eval, hfl, hv1 k b hq, hk], ?_⟩
      have hb1 : bitOf C.inp b.ip = (l.getD k false).toNat := by
        rw [hip, show a.ip + 2 * k + 1 = a.ip + (2 * k + 1) by ring, bitOf_frame _ _ _ _ _ hin (by omega)]
        rw [if_neg (by omega), show (2 * k + 1) / 2 = k by omega]
      refine Hs.seqc (t1 := 1) (t2 := t + 2) (hs_rdI C pB b (by omega)) (fun b1 hb1' => ?_) (by omega)
      subst hb1'
      refine Hs.seqc (t1 := t) (t2 := 1) (hact k hk _ (hQB k b _ hq) (by simp [hb1])) (fun d ⟨hd, hdip⟩ => ?_)
        (by omega)
      have hdip' : d.ip = a.ip + 2 * (k + 1) := by rw [hdip]; simp [hip]; omega
      refine Hs.op (OpEx.rdI pA d (by omega)) ⟨hQA _ d _ hd, by simp [hdip']; try omega, ?_⟩
      simp only [DS.set_env_self]
      rw [hdip', bitOf_frame _ _ _ _ _ hin (by omega), if_pos (by omega), show 2 * (k + 1) / 2 = k + 1 by omega])
    (fun b ⟨hq, _, hfl⟩ => by simp [Cnd.eval, hfl, hv1 _ b hq])
  refine Hs.seqc (t1 := 1) (t2 := l.length * (t + 4 + 2) + 2) (hs_rdI C pA a (by omega)) (fun b hb => ?_)
    (by ring_nf; omega)
  subst hb
  refine Hs.mono (hloop _ ⟨hQA 0 a _ hQ0, by simp, ?_⟩) le_rfl (fun b ⟨hq, hip, _⟩ => ⟨hq, hip⟩)
  simp only [DS.set_env_self]
  have := bitOf_frame _ _ _ _ 0 hin (by omega)
  rw [Nat.add_zero] at this
  rw [this]
  simp

/-! ## Three readers -/

/-- Frame bits into store `m` (`0/1` records), counting in `c`. -/
def rdStoreP (m : Fin MM) (c : Fin VV) : St VV MM := rdFrP (.seq (.op (.wrM m pB)) (.op (.inc c)))

theorem rdStoreP_spec (m : Fin MM) (c : Fin VV) (hc : c ∉ [pA, pB, v1]) (l rest : List Bool) (a : DS VV MM)
    (hin : C.inp.drop a.ip = frame l ++ rest) (h1 : a.env v1 = 1) (hm : a.ram m = []) (hrc : a.rc m = 0)
    (hc0 : a.env c = 0) (hW : l.length + 1 < 2 ^ C.Wd) :
    Hs C (rdStoreP m c) a (l.length * 9 + 4) (fun b => b.ram m = l.map Bool.toNat ∧ b.rc m = l.length ∧
      b.env c = l.length ∧ (∀ m', m' ≠ m → b.ram m' = a.ram m' ∧ b.rc m' = a.rc m') ∧ b.out = a.out ∧
      b.ip = a.ip + 2 * l.length + 1 ∧ Fr a b [pA, pB, c]) := by
  have hc' : c ≠ pA ∧ c ≠ pB ∧ c ≠ v1 := by simpa using hc
  let Q : ℕ → DS VV MM → Prop := fun k b => b.ram m = (l.take k).map Bool.toNat ∧ b.rc m = k ∧ b.env c = k ∧
    (∀ m', m' ≠ m → b.ram m' = a.ram m' ∧ b.rc m' = a.rc m') ∧ b.out = a.out ∧ Fr a b [pA, pB, c]
  have h := rdFrP_spec (C := C) (.seq (.op (.wrM m pB)) (.op (.inc c))) l rest Q 3 a hin
    ⟨by simp [hm], hrc, hc0, fun _ _ => ⟨rfl, rfl⟩, rfl, Fr.refl _ _⟩
    (fun k b hq => by rw [hq.2.2.2.2.2 v1 (by simp [Ne.symm hc'.2.2]; decide), h1])
    (fun k b v ⟨q1, q2, q3, q4, q5, q6⟩ => ⟨q1, q2, by simp [DS.set, Function.update_apply, hc'.1, q3], q4, q5,
      Fr.trans q6 (Fr.set b v (by simp))⟩)
    (fun k b v ⟨q1, q2, q3, q4, q5, q6⟩ => ⟨q1, q2, by simp [DS.set, Function.update_apply, hc'.2.1, q3], q4, q5,
      Fr.trans q6 (Fr.set b v (by simp))⟩)
    (fun k hk b ⟨q1, q2, q3, q4, q5, q6⟩ hB => by
      refine Hs.seqc (t1 := 1) (t2 := 1) (hs_wrM C m pB b (by rw [q2, q1]; simp; omega)) (fun d hd => ?_) (by omega)
      subst hd
      refine Hs.op (OpEx.inc c _ (by simp [DS.put, q3]; omega)) ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
      · have htk : (l.take (k + 1)).map Bool.toNat = (l.take k).map Bool.toNat ++ [(l.getD k false).toNat] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.map_append, List.map_singleton,
            List.getD_eq_getElem _ _ hk]
        simp only [DS.set_ram, DS.put, Function.update_self, q2, q1, hB, htk]
        unfold putAt
        rw [if_neg (by simp)]
      · simp [DS.put, q2]
      · simp [DS.put, q3]
      · intro m' hm'; simp only [DS.set_ram, DS.set_rc, DS.put, Function.update_of_ne hm']; exact q4 m' hm'
      · simp [DS.put, q5]
      · exact q6.trans (fun y hy => by
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
          rw [DS.set_env_ne _ _ hy.2.2]; rfl)
      · simp [DS.put])
  refine Hs.mono h (by omega) ?_
  rintro b ⟨⟨q1, q2, q3, q4, q5, q6⟩, hip⟩
  exact ⟨by rw [q1, List.take_length], q2, q3, q4, q5, hip, q6⟩

/-- A unary frame: count its bits in `c`. -/
def rdUnaryP (c : Fin VV) : St VV MM := rdFrP (.op (.inc c))

theorem rdUnaryP_spec (c : Fin VV) (hc : c ∉ [pA, pB, v1]) (l rest : List Bool) (a : DS VV MM)
    (hin : C.inp.drop a.ip = frame l ++ rest) (h1 : a.env v1 = 1) (hc0 : a.env c = 0)
    (hW : l.length + 1 < 2 ^ C.Wd) :
    Hs C (rdUnaryP c) a (l.length * 7 + 4) (fun b => b.env c = l.length ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
      b.out = a.out ∧ b.ip = a.ip + 2 * l.length + 1 ∧ Fr a b [pA, pB, c]) := by
  have hc' : c ≠ pA ∧ c ≠ pB ∧ c ≠ v1 := by simpa using hc
  let Q : ℕ → DS VV MM → Prop := fun k b => b.env c = k ∧ b.ram = a.ram ∧ b.rc = a.rc ∧ b.out = a.out ∧
    Fr a b [pA, pB, c]
  have h := rdFrP_spec (C := C) (.op (.inc c)) l rest Q 1 a hin ⟨hc0, rfl, rfl, rfl, Fr.refl _ _⟩
    (fun k b hq => by rw [hq.2.2.2.2 v1 (by simp [Ne.symm hc'.2.2]; decide), h1])
    (fun k b v ⟨q1, q2, q3, q4, q5⟩ => ⟨by simp [DS.set, Function.update_apply, hc'.1, q1], q2, q3, q4,
      Fr.trans q5 (Fr.set b v (by simp))⟩)
    (fun k b v ⟨q1, q2, q3, q4, q5⟩ => ⟨by simp [DS.set, Function.update_apply, hc'.2.1, q1], q2, q3, q4,
      Fr.trans q5 (Fr.set b v (by simp))⟩)
    (fun k hk b ⟨q1, q2, q3, q4, q5⟩ _ => Hs.op (R := fun d => Q (k + 1) d ∧ d.ip = b.ip)
      (OpEx.inc c b (by rw [q1]; omega)) ⟨⟨by simp [q1], q2, q3, q4, q5.trans (Fr.set b _ (by simp))⟩, rfl⟩)
  refine Hs.mono h (by omega) ?_
  rintro b ⟨⟨q1, q2, q3, q4, q5⟩, hip⟩
  exact ⟨q1, q2, q3, q4, hip, q5⟩

theorem bitsValue_append (u v : List Bool) : bitsValue (u ++ v) = bitsValue u + 2 ^ u.length * bitsValue v := by
  induction u with
  | nil => simp [bitsValue]
  | cons b u ih => simp only [List.cons_append, bitsValue, ih, List.length_cons, pow_succ]; ring

theorem bitsValue_lt (u : List Bool) : bitsValue u < 2 ^ u.length := by
  induction u with
  | nil => simp [bitsValue]
  | cons b u ih => simp only [bitsValue, List.length_cons, pow_succ]; cases b <;> simp <;> omega

/-- A binary frame (least significant bit first): its value in `c` (place value in `pC`, junk `pT`). -/
def rdBinP (c : Fin VV) : St VV MM :=
  .seq (.op (.zero c)) (.seq (.op (.copy pC v1))
    (rdFrP (.seq (.ite (.eq pB v1) (.op (.add c pC)) (.op (.zero pT))) (.op (.shl pC)))))

theorem rdBinP_spec (c : Fin VV) (hc : c ∉ [pA, pB, pC, pT, v1]) (l rest : List Bool) (a : DS VV MM)
    (hin : C.inp.drop a.ip = frame l ++ rest) (h1 : a.env v1 = 1) (hW : 2 ^ (l.length + 1) < 2 ^ C.Wd) :
    Hs C (rdBinP c) a (l.length * 10 + 8) (fun b => b.env c = bitsValue l ∧ b.ram = a.ram ∧ b.rc = a.rc ∧
      b.out = a.out ∧ b.ip = a.ip + 2 * l.length + 1 ∧ Fr a b [pA, pB, pC, pT, c]) := by
  have hc' : c ≠ pA ∧ c ≠ pB ∧ c ≠ pC ∧ c ≠ pT ∧ c ≠ v1 := by simpa using hc
  refine Hs.seqc (t1 := 1) (t2 := l.length * 10 + 6) (hs_zero C c a) (fun a1 ha1 => ?_) (by omega)
  subst ha1
  refine Hs.seqc (t1 := 1) (t2 := l.length * 10 + 4) (hs_copy C pC v1 _ (by decide)) (fun a2 ha2 => ?_) (by omega)
  subst ha2
  set a2 := (a.set c 0).set pC ((a.set c 0).env v1) with ha2
  have e2 : ∀ y, y ≠ c → y ≠ pC → a2.env y = a.env y := fun y h h' => by
    simp [ha2, DS.set, Function.update_apply, h, h']
  have a2c : a2.env c = 0 := by simp [ha2, DS.set, Function.update_apply, hc'.2.2.1, Ne.symm hc'.2.2.1]
  have a2p : a2.env pC = 1 := by simp [ha2, DS.set, Function.update_apply, Ne.symm hc'.2.2.2.2, h1]
  have hF2 : Fr a a2 [pA, pB, pC, pT, c] := fun y hy => e2 y (by intro e; simp [e] at hy) (by intro e; simp [e] at hy)
  let Q : ℕ → DS VV MM → Prop := fun k b => b.env c = bitsValue (l.take k) ∧ b.env pC = 2 ^ k ∧ b.ram = a.ram ∧
    b.rc = a.rc ∧ b.out = a.out ∧ Fr a b [pA, pB, pC, pT, c]
  have hp : 2 ^ l.length < 2 ^ C.Wd := lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) (by omega)) hW
  have h := rdFrP_spec (C := C) (.seq (.ite (.eq pB v1) (.op (.add c pC)) (.op (.zero pT))) (.op (.shl pC))) l rest Q 4
    a2 hin ⟨by simp [a2c, bitsValue], a2p, rfl, rfl, rfl, hF2⟩
    (fun k b hq => by rw [hq.2.2.2.2.2 v1 (by simp [Ne.symm hc'.2.2.2.2]; decide), h1])
    (fun k b v ⟨q1, q2, q3, q4, q5, q6⟩ => ⟨by simp [DS.set, Function.update_apply, hc'.1, q1],
      by vsimp [Function.update_apply, q2], q3, q4, q5, Fr.trans q6 (Fr.set b v (by simp))⟩)
    (fun k b v ⟨q1, q2, q3, q4, q5, q6⟩ => ⟨by simp [DS.set, Function.update_apply, hc'.2.1, q1],
      by vsimp [Function.update_apply, q2], q3, q4, q5, Fr.trans q6 (Fr.set b v (by simp))⟩)
    (fun k hk b ⟨q1, q2, q3, q4, q5, q6⟩ hB => by
      have htk : l.take (k + 1) = l.take k ++ [l.getD k false] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk, List.getD_eq_getElem _ _ hk]; rfl
      have hlt := bitsValue_lt (l.take k)
      have hlk : (l.take k).length = k := by simp; omega
      rw [hlk] at hlt
      have hpk : 2 ^ (k + 1) ≤ 2 ^ l.length := Nat.pow_le_pow_right (by omega) hk
      rw [pow_succ] at hpk
      have hq' : b.env v1 = 1 := by rw [q6 v1 (by simp [Ne.symm hc'.2.2.2.2]; decide), h1]
      have hval : bitsValue (l.take (k + 1)) = bitsValue (l.take k) + (l.getD k false).toNat * 2 ^ k := by
        rw [htk, bitsValue_append, hlk]; simp [bitsValue]; ring
      refine Hs.seqc (t1 := 2) (t2 := 1) (R1 := fun d => d.env c = bitsValue (l.take (k + 1)) ∧ d.env pC = 2 ^ k ∧
          d.ram = a.ram ∧ d.rc = a.rc ∧ d.out = a.out ∧ Fr a d [pA, pB, pC, pT, c] ∧ d.ip = b.ip)
        (Hs.ite (show pB ≠ v1 by decide) (fun hc1 => ?_) (fun hc1 => ?_)) (fun d ⟨d1, d2, d3, d4, d5, d6, dip⟩ => ?_)
        (by omega)
      · have hb : l.getD k false = true := by
          have h1' : b.env pB = 1 := by simpa [Cnd.eval, hq'] using hc1
          rw [hB] at h1'
          cases hh : l.getD k false
          · rw [hh] at h1'; simp at h1'
          · rfl
        refine Hs.mono (Hs.op (OpEx.add c pC b hc'.2.2.1 (by rw [q1, q2]; omega)) rfl) (by omega) ?_
        rintro d rfl
        exact ⟨by rw [DS.set_env_self, q1, q2, hval, hb]; simp, by simp [DS.set, Function.update_apply, hc'.2.2.1, Ne.symm hc'.2.2.1, q2],
          q3, q4, q5, q6.trans (Fr.set b _ (by simp)), rfl⟩
      · have hb : l.getD k false = false := by
          have h1' : b.env pB ≠ 1 := by simpa [Cnd.eval, hq'] using hc1
          rw [hB] at h1'
          cases hh : l.getD k false
          · rfl
          · rw [hh] at h1'; simp at h1'
        refine Hs.mono (Hs.op (OpEx.zero pT b) rfl) (by omega) ?_
        rintro d rfl
        exact ⟨by rw [DS.set_env_ne _ _ hc'.2.2.2.1, q1, hval, hb]; simp, by vsimp [Function.update_apply, q2],
          q3, q4, q5, q6.trans (Fr.set b _ (by simp)), rfl⟩
      · refine Hs.op (OpEx.shl pC d (by rw [d2]; omega)) ⟨⟨by simp [DS.set, Function.update_apply, hc'.2.2.1, d1],
          by simp [d2, pow_succ]; ring, d3, d4, d5, d6.trans (Fr.set d _ (by simp))⟩, by simp [dip]⟩)
  refine Hs.mono h (by omega) ?_
  rintro b ⟨⟨q1, _, q3, q4, q5, q6⟩, hip⟩
  refine ⟨by rw [q1, List.take_length], q3, q4, q5, by rw [hip]; simp [ha2], q6⟩

end NearCubicGates.Adapters.Compile
