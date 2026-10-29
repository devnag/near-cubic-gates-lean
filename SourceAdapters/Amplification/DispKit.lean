import SourceAdapters.Amplification.DispRef
import SourceAdapters.Machine.CappedWordProof

/-!
# Routines of the dispatcher cell program (A05, `app:sources`, "Full-range amplification interface")

: "Fix a time constructor computing `S(n)` from unary `n` within `C(S(n)+1)` steps. For `n ≥ n0`,
run it for only `C(U(n)+1)` simulated steps." The dispatcher (`DispProgram.lean`) calls the capped constructor of
X8 (`Machine.Capped.cappedWordFunction`) through the cell language's call registers. This module gives the routines
around the call and the output writers:

* `FrQ`: a frame in which the call registers (`kin`, `kout`, `kc`) may change;
* `reqP`: writes the request `cappedRequestWord (cap, 1^n) = frame 1^cap ++ frame 1^n` by `kem` loops;
* `parseKP`: reads the doubly framed answer `frame (b :: frame (S n).bits)` (success bit, value) by `rdK`;
* `parP`: writes the parity output on `s` bits, `parityWord s` (`DispRef.lean`), with a Hadamard-bit routine
  (`hadP`, X9's `EncMain.lean`) whose specification is restated here without the encoder's globals (`hadP_gen`).
-/

set_option autoImplicit false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Adapters.Amplification.Enc

open NearCubicGates.Close.Cells NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.ExecutableInterfaces
open NearCubicGates.Adapters.Joins Finset

/-- The dispatcher's cap register. -/
abbrev vCap : Var := 28

/-! ## A frame in which the call registers may change -/

structure FrQ (S : List Var) (w : List Bool) (a b : Ds) : Prop where
  env : ∀ x, x ∉ S → b.env x = a.env x
  ip : b.ip = a.ip
  out : b.out = a.out ++ w

theorem Fr.toQ {S : List Var} {w : List Bool} {a b : Ds} (h : Fr S w a b) : FrQ S w a b := ⟨h.env, h.ip, h.out⟩

theorem FrQ.refl (S : List Var) (a : Ds) : FrQ S [] a a := ⟨fun _ _ => rfl, rfl, by simp⟩

theorem FrQ.trans {S : List Var} {w1 w2 : List Bool} {a b c : Ds} (h1 : FrQ S w1 a b) (h2 : FrQ S w2 b c) :
    FrQ S (w1 ++ w2) a c :=
  ⟨fun x hx => (h2.env x hx).trans (h1.env x hx), h2.ip.trans h1.ip, by rw [h2.out, h1.out, List.append_assoc]⟩

theorem FrQ.trans0 {S : List Var} {a b c : Ds} (h1 : FrQ S [] a b) (h2 : FrQ S [] b c) : FrQ S [] a c := by
  simpa using h1.trans h2

theorem FrQ.mono {S S' : List Var} {w : List Bool} {a b : Ds} (h : FrQ S w a b) (hS : S ⊆ S') : FrQ S' w a b :=
  ⟨fun x hx => h.env x (fun h' => hx (hS h')), h.ip, h.out⟩

theorem FrQ.set_right {S : List Var} {w : List Bool} {a b : Ds} (h : FrQ S w a b) (x : Var) (v : ℕ) (hx : x ∈ S) :
    FrQ S w a (b.set x v) :=
  ⟨fun y hy => (DS.set_env_ne _ _ (fun e : y = x => hy (e ▸ hx))).trans (h.env y hy), h.ip, h.out⟩

theorem FrQ.kin_right {S : List Var} {w : List Bool} {a b : Ds} (h : FrQ S w a b) (k : List Bool) :
    FrQ S w a { b with kin := k } := ⟨h.env, h.ip, h.out⟩

theorem FrQ.called_right {S : List Var} {w : List Bool} {a b : Ds} (h : FrQ S w a b) (o : List Bool) :
    FrQ S w a (b.called o) := ⟨h.env, h.ip, h.out⟩

theorem Consts.of_frq {S : List Var} {w : List Bool} {a b : Ds} (h : Consts a) (hf : FrQ S w a b)
    (hS : vZ ∉ S ∧ vONE ∉ S ∧ vTWO ∉ S) : Consts b :=
  ⟨(hf.env _ hS.1).trans h.1, (hf.env _ hS.2.1).trans h.2.1, (hf.env _ hS.2.2).trans h.2.2⟩

/-! ## Writing the request `frame 1^cap ++ frame 1^n` -/

def kemBody : Sc := .seq (.op (.kem true)) (.seq (.op (.kem true)) (.op (.sub vU vONE)))

theorem length_flatten_pairs (j : ℕ) : ((List.replicate j [true, true]).flatten).length = 2 * j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [List.replicate_succ, List.flatten_cons, List.length_append, ih]; simp; ring

theorem kemLoop_spec (C : Ctx) (a : Ds) (hc : Consts a) (m : ℕ) (hU : a.env vU = m)
    (hL : a.kin.length + 2 * m ≤ C.Lk) :
    ∃ b, Ex C (.loop (.lt vZ vU) kemBody) a b (m * (5 + 2) + 2) ∧ FrQ [vU] [] a b ∧
      b.kin = a.kin ++ (List.replicate m [true, true]).flatten := by
  have hstep : ∀ j < m, ∀ b : Ds, (FrQ [vU] [] a b ∧ b.env vU = m - j ∧
      b.kin = a.kin ++ (List.replicate j [true, true]).flatten) →
      (Cnd.lt vZ vU).eval b = true ∧ ∃ b', Ex C kemBody b b' 5 ∧ (FrQ [vU] [] a b' ∧ b'.env vU = m - (j + 1) ∧
        b'.kin = a.kin ++ (List.replicate (j + 1) [true, true]).flatten) := by
    rintro j hj b ⟨hf, hUb, hkin⟩
    have hz : b.env vZ = 0 := (hf.env vZ (by decide)).trans hc.1
    have h1 : b.env vONE = 1 := (hf.env vONE (by decide)).trans hc.2.1
    have hlen : b.kin.length = a.kin.length + 2 * j := by rw [hkin, List.length_append, length_flatten_pairs]
    set b1 : Ds := { b with kin := b.kin ++ [true] }
    set b2 : Ds := { b1 with kin := b1.kin ++ [true] }
    have e1 : Ex C (.op (.kem true)) b b1 1 := Ex.op (OpEx.kem true b (by omega))
    have e2 : Ex C (.op (.kem true)) b1 b2 1 := Ex.op (OpEx.kem true b1 (by simp [b1]; omega))
    have h1' : b2.env vONE = 1 := h1
    have hUb' : b2.env vU = m - j := hUb
    have e3 : Ex C (.op (.sub vU vONE)) b2 (b2.set vU (b2.env vU - b2.env vONE)) 1 :=
      Ex.op (OpEx.sub vU vONE b2 (by decide) (by rw [h1', hUb']; omega))
    refine ⟨by simp [Cnd.eval, hz, hUb]; omega, _, Ex.seq e1 (Ex.seq e2 e3), ?_, ?_, ?_⟩
    · exact ((hf.kin_right _).kin_right _).set_right _ _ (by decide)
    · simp only [DS.set_env_self, h1', hUb']; omega
    · simp only [DS.set_kin, b2, b1, hkin, List.replicate_succ', List.flatten_append, List.append_assoc]
      simp
  obtain ⟨b, e, hb⟩ := ex_loopN (C := C) (c := .lt vZ vU) (body := kemBody) (by unfold Cnd.wf; decide) m 5
    (fun j b => FrQ [vU] [] a b ∧ b.env vU = m - j ∧ b.kin = a.kin ++ (List.replicate j [true, true]).flatten)
    hstep (by
      rintro b ⟨hf, hUb, -⟩
      have hz : b.env vZ = 0 := (hf.env vZ (by decide)).trans hc.1
      simp [Cnd.eval, hz, hUb])
    a ⟨FrQ.refl _ _, by simp [hU], by simp⟩
  exact ⟨b, e, hb.1, hb.2.2⟩

theorem frame_ones (d : ℕ) : frame (List.replicate d true) = (List.replicate d [true, true]).flatten ++ [false] := by
  have := frame_replicate d []
  rw [List.append_nil] at this
  rw [this]; rfl

def reqP : Sc :=
  .seq (.op (.copy vU vCap)) <| .seq (.loop (.lt vZ vU) kemBody) <| .seq (.op (.kem false)) <|
  .seq (.op (.copy vU vN)) <| .seq (.loop (.lt vZ vU) kemBody) (.op (.kem false))

theorem reqP_spec (C : Ctx) (a : Ds) (hc : Consts a) (cap n : ℕ) (hcap : a.env vCap = cap) (hn : a.env vN = n)
    (hkin : a.kin = []) (hL : 2 * cap + 2 * n + 2 ≤ C.Lk) :
    ∃ b, Ex C reqP a b ((cap + n) * 7 + 20) ∧ FrQ [vU] [] a b ∧
      b.kin = cappedRequestWord (cap, List.replicate n true) := by
  set a1 := a.set vU (a.env vCap) with ha1
  have e1 : Ex C (.op (.copy vU vCap)) a a1 1 := Ex.op (OpEx.copy vU vCap a (by decide))
  have hf1 : FrQ [vU] [] a a1 := (FrQ.refl _ a).set_right _ _ (by decide)
  have hc1 : Consts a1 := hc.of_frq hf1 (by decide)
  obtain ⟨b1, e2, hf2, hk2⟩ := kemLoop_spec C a1 hc1 cap (by simp [a1, hcap])
    (by simp [a1, hkin]; omega)
  have hc2 : Consts b1 := hc1.of_frq hf2 (by decide)
  set b2 : Ds := { b1 with kin := b1.kin ++ [false] } with hb2
  have hl2 : b1.kin.length = 2 * cap := by rw [hk2, List.length_append, length_flatten_pairs]; simp [a1, hkin]
  have e3 : Ex C (.op (.kem false)) b1 b2 1 := Ex.op (OpEx.kem false b1 (by omega))
  set b3 := b2.set vU (b2.env vN) with hb3
  have e4 : Ex C (.op (.copy vU vN)) b2 b3 1 := Ex.op (OpEx.copy vU vN b2 (by decide))
  have hf3 : FrQ [vU] [] a b3 := ((hf1.trans0 hf2).kin_right _).set_right _ _ (by decide)
  have hc3 : Consts b3 := hc.of_frq hf3 (by decide)
  have hN3 : b3.env vU = n := by
    simp only [b3, DS.set_env_self]
    show b1.env vN = n
    rw [(hf1.trans0 hf2).env vN (by decide), hn]
  obtain ⟨b4, e5, hf5, hk5⟩ := kemLoop_spec C b3 hc3 n hN3 (by simp [b3, b2, hl2]; omega)
  have hl4 : b4.kin.length = 2 * cap + 1 + 2 * n := by
    rw [hk5, List.length_append, length_flatten_pairs]; simp [b3, b2, hl2]
  set b5 : Ds := { b4 with kin := b4.kin ++ [false] } with hb5
  have e6 : Ex C (.op (.kem false)) b4 b5 1 := Ex.op (OpEx.kem false b4 (by omega))
  refine ⟨b5, (Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 (Ex.seq e5 e6))))).mono (by nlinarith), ?_, ?_⟩
  · exact (hf3.trans0 hf5).kin_right _
  · simp only [b5, hk5, b3, DS.set_kin, b2, hk2, a1, hkin, cappedRequestWord, frame_ones]
    simp

/-! ## Reading the doubly framed answer -/

theorem frameGetOdd : ∀ (u : List Bool) (k : ℕ), (frame u).getD (2 * k + 1) false = u.getD k false
  | [], k => by simp [frame]
  | b :: u, 0 => by simp [frame]
  | b :: u, k + 1 => by
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring]
    simp only [frame, List.getD_cons_succ]
    exact frameGetOdd u k

theorem frameGetEven : ∀ (u : List Bool) (k : ℕ), (frame u).getD (2 * k) false = decide (k < u.length)
  | [], k => by cases k <;> simp [frame]
  | b :: u, 0 => by simp [frame]
  | b :: u, k + 1 => by
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]
    simp only [frame, List.getD_cons_succ]
    rw [frameGetEven u k]; simp

theorem kout_get (b0 : Bool) (v : List Bool) :
    (frame (b0 :: frame v)).length = 4 * v.length + 5 ∧
    (frame (b0 :: frame v)).getD 1 false = b0 ∧
    (∀ j, (frame (b0 :: frame v)).getD (4 * j + 3) false = decide (j < v.length)) ∧
    (∀ j, (frame (b0 :: frame v)).getD (4 * j + 5) false = v.getD j false) := by
  refine ⟨?_, ?_, fun j => ?_, fun j => ?_⟩
  · simp [frame_length]; omega
  · simp [frame]
  · rw [show 4 * j + 3 = 2 * (2 * j + 1) + 1 by ring, frameGetOdd,
      List.getD_cons_succ, frameGetEven]
  · rw [show 4 * j + 5 = 2 * (2 * j + 1 + 1) + 1 by ring, frameGetOdd,
      List.getD_cons_succ, frameGetOdd]

abbrev vSU : Var := 29

/-- The state after `rdK x`. -/
def rdKst (b : Ds) (x : Var) : Ds := { b.set x (bitOf b.kout b.kc) with kc := b.kc + 1 }

@[simp] theorem rdKst_kout (b : Ds) (x : Var) : (rdKst b x).kout = b.kout := rfl
@[simp] theorem rdKst_kc (b : Ds) (x : Var) : (rdKst b x).kc = b.kc + 1 := rfl
@[simp] theorem rdKst_ip (b : Ds) (x : Var) : (rdKst b x).ip = b.ip := rfl
@[simp] theorem rdKst_out (b : Ds) (x : Var) : (rdKst b x).out = b.out := rfl
theorem rdKst_env (b : Ds) (x y : Var) : (rdKst b x).env y = if y = x then bitOf b.kout b.kc else b.env y :=
  env_set b x y _

theorem ex_rdK (C : Ctx) (b : Ds) (x : Var) (h : b.kc < b.kout.length) : Ex C (.op (.rdK x)) b (rdKst b x) 1 :=
  Ex.op (OpEx.rdK x b h)

theorem FrQ.rdK_right {S : List Var} {w : List Bool} {a b : Ds} (h : FrQ S w a b) (x : Var) (hx : x ∈ S) :
    FrQ S w a (rdKst b x) :=
  ⟨fun y hy => (DS.set_env_ne _ _ (fun e : y = x => hy (e ▸ hx))).trans (h.env y hy), h.ip, h.out⟩

def parseKS : List Var := [vSU, vPV, vPW, vPM, vPB, vPQ]

def parseKBody : Sc :=
  .seq (.op (.rdK vPB)) <| .seq (.op (.rdK vPB)) <|
  .seq (.ite (.eq vPB vONE) (.op (.add vPV vPW)) (.op (.zero vPQ))) <|
  .seq (.op (.shl vPW)) <| .seq (.op (.rdK vPB)) (.op (.rdK vPM))

def parseKP : Sc :=
  .seq (.op (.rdK vPB)) <| .seq (.op (.rdK vSU)) <| .seq (.op (.zero vPV)) <| .seq (.op (.copy vPW vONE)) <|
  .seq (.op (.rdK vPB)) <| .seq (.op (.rdK vPM)) <| .loop (.eq vPM vONE) parseKBody

theorem parseKP_spec (C : Ctx) (a : Ds) (hc : Consts a) (b0 : Bool) (x : ℕ)
    (hk : a.kout = frame (b0 :: frame x.bits)) (hkc : a.kc = 0) (hW : x.size + 2 ≤ C.Wd) :
    ∃ b, Ex C parseKP a b (x.size * 14 + 20) ∧ FrQ parseKS [] a b ∧ b.env vSU = b0.toNat ∧ b.env vPV = x := by
  have hlen : x.bits.length = x.size := Nat.size_eq_bits_len x
  obtain ⟨hkl, hk1, hk3, hk5⟩ := kout_get b0 x.bits
  rw [hlen] at hkl
  have hpw : ∀ j, j ≤ x.size → 2 ^ j < 2 ^ C.Wd := fun j hj => Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- the four reads before the loop
  have e1 := ex_rdK C a vPB (by rw [hk, hkc, hkl]; omega)
  set a1 := rdKst a vPB with ha1
  have e2 := ex_rdK C a1 vSU (by simp [a1, hk, hkc, hkl])
  set a2 := rdKst a1 vSU with ha2
  have hSU : a2.env vSU = b0.toNat := by
    rw [show a2.env vSU = bitOf a1.kout a1.kc from by simp [a2, rdKst_env]]
    simp only [a1, rdKst_kout, rdKst_kc, hk, hkc, bitOf, zero_add, hk1]
  have h1a2 : a2.env vONE = 1 := by simp (config := { decide := true }) [a2, a1, rdKst_env, hc.2.1]
  set a3 := a2.set vPV 0 with ha3
  have e3 : Ex C (.op (.zero vPV)) a2 a3 1 := Ex.op (OpEx.zero vPV a2)
  set a4 := a3.set vPW (a3.env vONE) with ha4
  have e4 : Ex C (.op (.copy vPW vONE)) a3 a4 1 := Ex.op (OpEx.copy vPW vONE a3 (by decide))
  have hf4 : FrQ parseKS [] a a4 :=
    ((((FrQ.refl _ a).rdK_right vPB (by decide)).rdK_right vSU (by decide)).set_right vPV _
      (by decide)).set_right vPW _ (by decide)
  have hkc4 : a4.kc = 2 := by simp [a4, a3, a2, a1, hkc]
  have hko4 : a4.kout = a.kout := by simp [a4, a3, a2, a1]
  have e5 := ex_rdK C a4 vPB (by rw [hko4, hk, hkc4, hkl]; omega)
  set a5 := rdKst a4 vPB with ha5
  have e6 := ex_rdK C a5 vPM (by simp only [a5, rdKst_kc, rdKst_kout]; rw [hko4, hk, hkc4, hkl]; omega)
  set a6 := rdKst a5 vPM with ha6
  -- the loop
  set Inv : ℕ → Ds → Prop := fun j b => FrQ parseKS [] a b ∧ b.kout = a.kout ∧ b.kc = 4 * j + 4 ∧
      b.env vSU = b0.toNat ∧ b.env vPV = x % 2 ^ j ∧ b.env vPW = 2 ^ j ∧
      b.env vPM = if j < x.size then 1 else 0 with hInv
  have hinit : Inv 0 a6 := by
    refine ⟨(hf4.rdK_right vPB (by decide)).rdK_right vPM (by decide), by simp [a6, a5, hko4], by simp [a6, a5, hkc4],
      ?_, ?_, ?_, ?_⟩
    · simp (config := { decide := true }) [a6, a5, a4, a3, rdKst_env, env_set, hSU]
    · simp (config := { decide := true }) [a6, a5, a4, a3, rdKst_env, env_set, Nat.mod_one]
    · simp (config := { decide := true }) [a6, a5, a4, a3, rdKst_env, env_set, h1a2]
    · rw [show a6.env vPM = bitOf a5.kout a5.kc from by simp [a6, rdKst_env]]
      simp only [a5, rdKst_kout, rdKst_kc, hko4, hk, hkc4, bitOf]
      rw [show 2 + 1 = 4 * 0 + 3 from rfl, hk3 0, hlen]
      by_cases h : 0 < x.size <;> simp [h]
  have hstop : ∀ b, Inv x.size b → (Cnd.eq vPM vONE).eval b = false := by
    rintro b ⟨hf, -, -, -, -, -, hM⟩
    have hc1 : b.env vONE = 1 := (hf.env vONE (by decide)).trans hc.2.1
    simp [Cnd.eval, hM, hc1]
  have hstep : ∀ j < x.size, ∀ b, Inv j b → (Cnd.eq vPM vONE).eval b = true ∧
      ∃ b', Ex C parseKBody b b' 12 ∧ Inv (j + 1) b' := by
    rintro j hj b ⟨hf, hko, hkcb, hSUb, hV, hW', hM⟩
    have hc1 : b.env vONE = 1 := (hf.env vONE (by decide)).trans hc.2.1
    refine ⟨by simp [Cnd.eval, hM, hc1, hj], ?_⟩
    have e1 := ex_rdK C b vPB (by rw [hko, hk, hkcb, hkl]; omega)
    set b1 := rdKst b vPB with hb1
    have e2 := ex_rdK C b1 vPB (by simp only [b1, rdKst_kc, rdKst_kout]; rw [hko, hk, hkcb, hkl]; omega)
    set b2 := rdKst b1 vPB with hb2
    have hbit : b2.env vPB = if x.testBit j then 1 else 0 := by
      rw [show b2.env vPB = bitOf b1.kout b1.kc from by simp [b2, rdKst_env]]
      simp only [b1, rdKst_kout, rdKst_kc, hko, hk, hkcb, bitOf]
      rw [show 4 * j + 4 + 1 = 4 * j + 5 by ring, hk5, getD_bits]
      cases x.testBit j <;> rfl
    have hVlt : x % 2 ^ j < 2 ^ j := Nat.mod_lt _ (Nat.two_pow_pos j)
    have hb2V : b2.env vPV = x % 2 ^ j := by simp (config := { decide := true }) [b2, b1, rdKst_env, hV]
    have hb2W : b2.env vPW = 2 ^ j := by simp (config := { decide := true }) [b2, b1, rdKst_env, hW']
    have hb2one : b2.env vONE = 1 := by simp (config := { decide := true }) [b2, b1, rdKst_env, hc1]
    obtain ⟨b3, e3, hb3V, hb3f, hb3W, hb3ko, hb3kc⟩ : ∃ b3, Ex C (.ite (.eq vPB vONE) (.op (.add vPV vPW))
        (.op (.zero vPQ))) b2 b3 2 ∧ b3.env vPV = x % 2 ^ (j + 1) ∧ FrQ [vPV, vPQ] [] b2 b3 ∧ b3.env vPW = 2 ^ j ∧
        b3.kout = b2.kout ∧ b3.kc = b2.kc := by
      by_cases hx : x.testBit j
      · refine ⟨_, Ex.iteT (by unfold Cnd.wf; decide)
          (by simp [Cnd.eval, hbit, hx, hb2one])
          (Ex.op (OpEx.add vPV vPW b2 (by decide) ?_)), ?_, ?_, ?_, rfl, rfl⟩
        · rw [hb2V, hb2W]
          have := hpw (j + 1) (by omega); rw [pow_succ] at this; omega
        · simp only [DS.set_env_self, hb2V, hb2W, mod_two_pow_succ', hx]; simp
        · exact (FrQ.refl _ _).set_right _ _ (by decide)
        · rw [env_set, if_neg (by decide)]; exact hb2W
      · refine ⟨_, Ex.iteF (by unfold Cnd.wf; decide)
          (by simp [Cnd.eval, hbit, hx, hb2one])
          (Ex.op (OpEx.zero vPQ b2)), ?_, ?_, ?_, rfl, rfl⟩
        · rw [env_set, if_neg (by decide), hb2V, mod_two_pow_succ']; simp [hx]
        · exact (FrQ.refl _ _).set_right _ _ (by decide)
        · rw [env_set, if_neg (by decide)]; exact hb2W
    have e4 : Ex C (.op (.shl vPW)) b3 (b3.set vPW (2 * b3.env vPW)) 1 :=
      Ex.op (OpEx.shl vPW b3 (by rw [hb3W]; have := hpw (j + 1) (by omega); rw [pow_succ] at this; omega))
    set b4 := b3.set vPW (2 * b3.env vPW) with hb4
    have hkc4' : b4.kc = 4 * j + 6 := by simp [b4, hb3kc, b2, b1, hkcb]
    have hko4' : b4.kout = a.kout := by simp [b4, hb3ko, b2, b1, hko]
    have e5 := ex_rdK C b4 vPB (by rw [hko4', hk, hkc4', hkl]; omega)
    set b5 := rdKst b4 vPB with hb5
    have e6 := ex_rdK C b5 vPM (by simp only [b5, rdKst_kc, rdKst_kout]; rw [hko4', hk, hkc4', hkl]; omega)
    set b6 := rdKst b5 vPM with hb6
    refine ⟨b6, (Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 (Ex.seq e5 e6))))).mono (by omega), ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · exact (((((hf.rdK_right vPB (by decide)).rdK_right vPB (by decide)).trans0 (hb3f.mono (by decide))).set_right vPW _
        (by decide)).rdK_right vPB (by decide)).rdK_right vPM (by decide)
    · simp [b6, b5, hko4']
    · simp [b6, b5, hkc4']; ring
    · have h3 := hb3f.env vSU (by decide)
      have h2 : b2.env vSU = b0.toNat := by simp (config := { decide := true }) [b2, b1, rdKst_env, hSUb]
      simp (config := { decide := true }) [b6, b5, b4, rdKst_env, env_set, h3, h2]
    · simp (config := { decide := true }) [b6, b5, b4, rdKst_env, env_set, hb3V]
    · simp (config := { decide := true }) [b6, b5, b4, rdKst_env, env_set, hb3W, pow_succ]; ring
    · rw [show b6.env vPM = bitOf b5.kout b5.kc from by simp [b6, rdKst_env]]
      simp only [b5, rdKst_kout, rdKst_kc, hko4', hk, hkc4', bitOf]
      rw [show 4 * j + 6 + 1 = 4 * (j + 1) + 3 by ring, hk3 (j + 1), hlen]
      by_cases h : j + 1 < x.size <;> simp [h]
  obtain ⟨b, eb, hb⟩ := ex_loopN (C := C) (c := .eq vPM vONE) (body := parseKBody) (by unfold Cnd.wf; decide)
    x.size 12 Inv hstep hstop a6 hinit
  refine ⟨b, ?_, hb.1, hb.2.2.2.1, ?_⟩
  · exact (Ex.seq e1 (Ex.seq e2 (Ex.seq e3 (Ex.seq e4 (Ex.seq e5 (Ex.seq e6 eb)))))).mono (by nlinarith)
  · rw [hb.2.2.2.2.1, Nat.mod_eq_of_lt (Nat.lt_size_self x)]

/-! ## The Hadamard bit without the encoder's globals -/

theorem hadP_gen (C : Ctx) (a : Ds) (hc : Consts a) (t : ℕ) (ht : a.env vT = t) (hWt : t + 2 ≤ C.Wd) (Y c : ℕ)
    (hY : a.env vYY = Y) (hcv : a.env vQC = c) :
    Runs C hadP a (hadCost t) hadS [] (fun b => b.env vHP = if hadBit t Y c then 1 else 0) := by
  have hW4 : 2 * 2 ≤ 2 ^ C.Wd := by
    have : 2 ^ 2 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  have hjW : ∀ j < t, j + 1 < 2 ^ C.Wd := fun j hj => by
    have h1 := Nat.lt_two_pow_self (n := C.Wd)
    omega
  refine Runs.op1 (run_copy C hadS a vHA vYY (by decide) (by decide)) ?_ (by unfold hadCost; omega)
  refine Runs.op1 (run_copy C hadS _ vHB vQC (by decide) (by decide)) ?_ (by unfold hadCost; omega)
  refine Runs.op1 (run_zero C hadS _ vHS (by decide)) ?_ (by unfold hadCost; omega)
  refine Runs.op1 (run_zero C hadS _ vHP (by decide)) ?_ (by unfold hadCost; omega)
  norm_env
  rw [hY, hcv]
  refine (Runs.loopN0 (C := C) (c := .lt vHS vT) (body := hadBody) (S := hadS) (by unfold Cnd.wf; decide)
    t 30 (HadInv a Y c) ?step ?stop _ ?init).mono ?cost (List.Subset.refl _) ?post
  case cost => unfold hadCost; omega
  case post =>
    rintro b - ⟨-, -, -, hP, -⟩
    rw [hP]
    change common Y c t % 2 = if decide (common Y c t % 2 = 1) then 1 else 0
    rcases Nat.mod_two_eq_zero_or_one (common Y c t) with h | h <;> simp [h]
  case stop =>
    rintro b ⟨hf, -, -, -, hS⟩
    have htb : b.env vT = t := (hf.env vT (by decide)).trans ht
    simp [Cnd.eval, hS, htb]
  case init =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · repeat (first | exact Fr.refl hadS a | refine Fr.set_right ?_ _ _ (by decide))
    all_goals norm_env
    all_goals simp [common]
  case step =>
    rintro j hj b ⟨hf, hA, hB, hP, hS⟩
    have hcb : Consts b := hc.of_fr hf (by decide)
    have htb : b.env vT = t := (hf.env vT (by decide)).trans ht
    refine ⟨by simp [Cnd.eval, hS, htb, hj], ?_⟩
    have hjW' := hjW j hj
    refine Runs.op1 (run_dm C hadS b vHA vTWO vHQ vHRa (by decide) (by decide) (by decide)
      (by rw [hcb.2.2]; norm_num) (by rw [hcb.2.2]; exact hW4)) ?_ (by omega)
    refine Runs.op1 (run_copy C hadS _ vHA vHQ (by decide) (by decide)) ?_ (by omega)
    norm_env
    refine Runs.op1 (run_dm C hadS _ vHB vTWO vHQ vHRb (by decide) (by decide) (by decide)
      (by norm_env; rw [hcb.2.2]; norm_num) (by norm_env; rw [hcb.2.2]; exact hW4)) ?_ (by omega)
    refine Runs.op1 (run_copy C hadS _ vHB vHQ (by decide) (by decide)) ?_ (by omega)
    norm_env
    rw [hcb.2.2, hA, hB, testBit_div, testBit_div]
    refine Runs.op1 (run_inc C hadS _ vHS (by decide) (by norm_env; rw [hS]; exact hjW')) ?_ (by omega)
    norm_env
    rw [hS]
    have hfin : ∀ (f : Ds), Fr hadS [] b f → f.env vHA = Y / 2 ^ j / 2 → f.env vHB = c / 2 ^ j / 2 →
        f.env vHP = common Y c (j + 1) % 2 → f.env vHS = j + 1 → HadInv a Y c (j + 1) f := by
      intro f hff h1 h2 h3 h4
      refine ⟨hf.trans0 hff, ?_, ?_, h3, h4⟩
      · rw [h1, Nat.div_div_eq_div_mul, ← pow_succ]
      · rw [h2, Nat.div_div_eq_div_mul, ← pow_succ]
    have hfr : ∀ (x : Var) (v : ℕ), x ∈ hadS → Fr hadS [] b
        ((((((b.set vHQ (Y / 2 ^ j / 2)).set vHRa (if Y.testBit j then 1 else 0)).set vHA (Y / 2 ^ j / 2)).set vHQ
          (c / 2 ^ j / 2)).set vHRb (if c.testBit j then 1 else 0)).set vHB (c / 2 ^ j / 2) |>.set vHS (j + 1)
          |>.set x v) := by
      intro x v hx
      refine Fr.set_right ?_ _ _ hx
      repeat (first | exact Fr.refl hadS b | refine Fr.set_right ?_ _ _ (by decide))
    by_cases hya : Y.testBit j = true
    · refine Runs.iteT' (by unfold Cnd.wf; decide)
        (by simp (config := { decide := true }) [Cnd.eval, env_set, hya, hcb.2.1]) ?_ (by omega)
      by_cases hcbt : c.testBit j = true
      · refine Runs.iteT' (by unfold Cnd.wf; decide)
          (by simp (config := { decide := true }) [Cnd.eval, env_set, hcbt, hcb.2.1]) ?_ (by omega)
        rcases Nat.mod_two_eq_zero_or_one (common Y c j) with hpar | hpar
        · refine Runs.iteT' (by unfold Cnd.wf; decide)
            (by simp (config := { decide := true }) [Cnd.eval, env_set, hP, hpar, hcb.1]) ?_ (by omega)
          refine Runs.last (run_inc C hadS _ vHP (by decide) (by norm_env; rw [hP, hpar]; omega)) ?_ (by omega)
          intro hff
          refine hfin _ ?_ ?_ ?_ ?_ ?_ <;> norm_env
          · exact hfr vHP _ (by decide)
          · rw [hP, common_succ, hya, hcbt]; simp; omega
        · refine Runs.iteF' (by unfold Cnd.wf; decide)
            (by simp (config := { decide := true }) [Cnd.eval, env_set, hP, hpar, hcb.1]) ?_ (by omega)
          refine Runs.last (run_zero C hadS _ vHP (by decide)) ?_ (by omega)
          intro hff
          refine hfin _ ?_ ?_ ?_ ?_ ?_ <;> norm_env
          · exact hfr vHP _ (by decide)
          · rw [common_succ, hya, hcbt]; simp; omega
      · refine Runs.iteF' (by unfold Cnd.wf; decide)
          (by simp (config := { decide := true }) [Cnd.eval, env_set, hcbt, hcb.2.1]) ?_ (by omega)
        refine Runs.last (run_zero C hadS _ vHQ (by decide)) ?_ (by omega)
        intro hff
        refine hfin _ ?_ ?_ ?_ ?_ ?_ <;> norm_env
        · exact hfr vHQ _ (by decide)
        · rw [hP, common_succ, hya]; simp [hcbt]
    · refine Runs.iteF' (by unfold Cnd.wf; decide)
        (by simp (config := { decide := true }) [Cnd.eval, env_set, hya, hcb.2.1]) ?_ (by omega)
      refine Runs.last (run_zero C hadS _ vHQ (by decide)) ?_ (by omega)
      intro hff
      refine hfin _ ?_ ?_ ?_ ?_ ?_ <;> norm_env
      · exact hfr vHQ _ (by decide)
      · rw [hP, common_succ]; simp [hya]

/-! ## The parity output on `s` bits (`s` in `vT`) -/

def parS : List Var := [vL, vEE, vYY, vQC] ++ emitS ++ pow2S ++ hadS

def parBody : Sc := .seq hadP <| .seq (.ite (.eq vHP vONE) (.op (.emit true)) (.op (.emit false))) (.op (.inc vQC))

def parP : Sc :=
  .seq (.op (.copy vL vT)) <| .seq emitFrameP <| .seq (.op (.copy vEE vT)) <| .seq pow2P <|
  .seq (.op (.copy vYY vPD)) <| .seq (.op (.sub vYY vONE)) <| .seq (.op (.zero vQC)) <| .loop (.lt vQC vPD) parBody

def parCost (s : ℕ) : ℕ := s.size * 12 + s * 5 + 2 ^ s * (hadCost s + 5 + 2) + 40

theorem parP_spec (C : Ctx) (a : Ds) (hc : Consts a) (s : ℕ) (hs : a.env vT = s) (hW : s + 2 ≤ C.Wd) :
    Runs C parP a (parCost s) parS (parityWord s) (fun _ => True) := by
  have hW4 : 2 * 2 ≤ 2 ^ C.Wd := by
    have : 2 ^ 2 ≤ 2 ^ C.Wd := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  have hsW : 2 ^ s < 2 ^ C.Wd := Nat.pow_lt_pow_right (by norm_num) (by omega)
  refine Runs.op1 (run_copy C parS a vL vT (by decide) (by decide)) ?_ (by unfold parCost; omega)
  have hc1 : Consts (a.set vL (a.env vT)) := hc.of_fr (Fr.set parS a vL _ (by decide)) (by decide)
  unfold parityWord
  have hE : Runs C emitFrameP (a.set vL (a.env vT)) (s.size * 12 + 10) parS (frame s.bits) (fun _ => True) :=
    (emitFrameP_spec C _ hc1 s (by rw [env_set, if_pos rfl, hs]) hW4).mono le_rfl (by decide)
      (fun _ _ _ => trivial)
  refine (Runs.seq (n' := parCost s - 2 - (s.size * 12 + 10) - 1) hE ?_).costLe (by unfold parCost; omega)
  intro b1 hb1 _
  have hc2 : Consts b1 := hc1.of_fr hb1 (by decide)
  have hs2 : b1.env vT = s := by rw [hb1.env vT (by decide), env_set, if_neg (by decide), hs]
  refine Runs.op1 (run_copy C parS b1 vEE vT (by decide) (by decide)) ?_ (by unfold parCost; omega)
  have hc2' : Consts (b1.set vEE (b1.env vT)) := hc2.of_fr (Fr.set parS b1 vEE _ (by decide)) (by decide)
  refine Runs.callS (pow2P_spec C _ hc2' s (by rw [env_set, if_pos rfl, hs2]) (by omega)) (by decide) ?_
    (by unfold parCost; omega)
  intro b2 hb2 hD
  have hc3 : Consts b2 := hc2'.of_fr hb2 (by decide)
  have hs3 : b2.env vT = s := by rw [hb2.env vT (by decide), env_set, if_neg (by decide), hs2]
  refine Runs.op1 (run_copy C parS b2 vYY vPD (by decide) (by decide)) ?_ (by unfold parCost; omega)
  refine Runs.op1 (run_sub C parS _ vYY vONE (by decide) (by decide)
    (by norm_env; rw [hD, hc3.2.1]; exact Nat.one_le_two_pow)) ?_ (by unfold parCost; omega)
  refine Runs.op1 (run_zero C parS _ vQC (by decide)) ?_ (by unfold parCost; omega)
  set Inv : ℕ → Ds → Prop := fun j b => Consts b ∧ b.env vT = s ∧ b.env vYY = 2 ^ s - 1 ∧ b.env vPD = 2 ^ s ∧
    b.env vQC = j with hInv
  rw [← flatMap_single]
  refine (Runs.loopN (C := C) (c := .lt vQC vPD) (body := parBody) (S := parS) (by unfold Cnd.wf; decide)
    (2 ^ s) (hadCost s + 5) (fun j => [hadBit s (2 ^ s - 1) j]) Inv ?step ?stop _ ?init).mono
    (by unfold parCost; omega) (List.Subset.refl _) (fun _ _ _ => trivial)
  case init =>
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> norm_env
    · exact hc3.1
    · exact hc3.2.1
    · exact hc3.2.2
    · exact hs3
    · rw [hD, hc3.2.1]
    · exact hD
  case stop =>
    rintro b ⟨-, -, -, hD', hQ⟩
    simp [Cnd.eval, hD', hQ]
  case step =>
    rintro j hj b ⟨hcb, hsb, hYb, hDb, hQb⟩
    refine ⟨by simp [Cnd.eval, hDb, hQb, hj], ?_⟩
    refine Runs.callS (hadP_gen C b hcb s hsb hW (2 ^ s - 1) j hYb hQb) (by decide) ?_ (by omega)
    intro b4 hb4 hP
    have hc4 : Consts b4 := hcb.of_fr hb4 (by decide)
    have hQ4 : b4.env vQC = j := by rw [hb4.env vQC (by decide), hQb]
    have hinc : ∀ f : Ds, f.env = b4.env → Runs C (.op (.inc vQC)) f 1 parS [] (Inv (j + 1)) := by
      intro f hff
      refine (run_inc C parS f vQC (by decide) (by rw [hff, hQ4]; omega)).post ?_
      intro _
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩ <;> rw [env_set]
      · rw [if_neg (by decide), hff]; exact hc4.1
      · rw [if_neg (by decide), hff]; exact hc4.2.1
      · rw [if_neg (by decide), hff]; exact hc4.2.2
      · rw [if_neg (by decide), hff, hb4.env vT (by decide), hsb]
      · rw [if_neg (by decide), hff, hb4.env vYY (by decide), hYb]
      · rw [if_neg (by decide), hff, hb4.env vPD (by decide), hDb]
      · rw [if_pos rfl, hff, hQ4]
    have hone : b4.env vONE = 1 := hc4.2.1
    cases hbit : hadBit s (2 ^ s - 1) j
    · have hite : Runs C (.ite (.eq vHP vONE) (.op (.emit true)) (.op (.emit false))) b4 2 parS [false]
          (· = { b4 with out := b4.out ++ [false] }) :=
        Runs.iteF' (by unfold Cnd.wf; decide) (by simp [Cnd.eval, hP, hbit, hone])
          (run_emit C parS b4 false) (by omega)
      have := Runs.seq hite (fun f _ hf => by subst hf; exact hinc _ rfl)
      exact this.costLe (by omega)
    · have hite : Runs C (.ite (.eq vHP vONE) (.op (.emit true)) (.op (.emit false))) b4 2 parS [true]
          (· = { b4 with out := b4.out ++ [true] }) :=
        Runs.iteT' (by unfold Cnd.wf; decide) (by simp [Cnd.eval, hP, hbit, hone])
          (run_emit C parS b4 true) (by omega)
      have := Runs.seq hite (fun f _ hf => by subst hf; exact hinc _ rfl)
      exact this.costLe (by omega)

/-! ## The constant output `[false, false]` (arity `0`, value `false`) -/

def constOutP : Sc := .seq (.op (.emit false)) (.op (.emit false))

theorem constOutP_spec (C : Ctx) (S : List Var) (a : Ds) : Runs C constOutP a 3 S [false, false] (fun _ => True) :=
  (Runs.emit1 (run_emit C S a false) ((run_emit C S _ false).post (fun _ => trivial)) (by omega))

end NearCubicGates.Adapters.Amplification.Enc
