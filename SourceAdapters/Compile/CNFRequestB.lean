import SourceAdapters.Compile.CNFRequest

/-!
# The generator context of the request

proof of `lem:multitape-refuter`: after `parseP`, `dimsP` derives the dimensions of the finite control from its code bits and leaves
the generator context `GC (reqGD r)` (`CNFGenA.GC`): the code and input bits rewound, `t`, `s`, `w`, width
`fuel + 1`, `t·width`, `windowBits`, `2^t`, record length, the two table offsets, `n`, the start state.

-/

namespace NearCubicGates.Adapters.Compile
open NearCubicWires NearCubicGates.Close.Cells NearCubicWires.RepairOrdinary
  NearCubicWires.RepairSource.VerifierEncoding
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- The request's generator data. -/
def reqGD (r : CNFCompilationRequest) : GD :=
  ⟨codeBits r.verifier, r.input.map Bool.toNat, r.verifier.tapeCount, r.verifier.stateCount, codeW r.verifier,
    r.fuel + 1, r.witnessLength, r.verifier.machine.start.val, codeO2 r.verifier⟩

theorem reqGD_td (r : CNFCompilationRequest) :
    (reqGD r).td = TD.ofBits (codeBits r.verifier) r.verifier.tapeCount (codeW r.verifier) (codeO2 r.verifier)
      (codeO3 r.verifier) (codeR r.verifier) := rfl

theorem pow_tape_le_code (v : Verifier) : 2 ^ v.tapeCount ≤ (code v).length := by
  rw [code_length]
  have hs : 1 ≤ v.stateCount := Nat.pos_of_ne_zero (fun h => by have := v.machine.start.isLt; omega)
  have hR : 1 ≤ codeR v := by unfold codeR; omega
  have : 2 ^ v.tapeCount ≤ v.stateCount * 2 ^ v.tapeCount * codeR v := by
    calc 2 ^ v.tapeCount = 1 * 2 ^ v.tapeCount * 1 := by ring
      _ ≤ v.stateCount * 2 ^ v.tapeCount * codeR v := by gcongr
  omega

/-- `dWd dTW dW dR dO2 dO3` from `dT dS dWb dF`. -/
def arithP : St VV MM :=
  .seq (.op (.copy dWd dF)) (.seq (.op (.inc dWd)) (.seq (.op (.mul dT dWd dTW)) (.seq (.op (.copy dW dTW))
  (.seq (.op (.add dW dTW)) (.seq (.op (.add dW dS)) (.seq (.op (.mul dT kc4 dR)) (.seq (.op (.add dR dWb))
  (.seq (.op (.inc dR)) (.seq (.op (.copy dO2 dT)) (.seq (.op (.add dO2 dS)) (.seq (.op (.add dO2 v2))
  (.seq (.op (.add dO2 dWb)) (.seq (.op (.copy dO3 dO2)) (.seq (.op (.add dO3 dS)) (.op (.add dO3 dS))))))))))))))))

/-- `dM := 2^dT` (counter `pT`). -/
def powMP : St VV MM := .seq (.op (.copy dM v1)) (forP pT dT (.op (.shl dM)))

def dimsP : St VV MM :=
  .seq (.op (.rwM sCB)) (.seq (onesP dT) (.seq (onesP dS) (.seq bitLenP (.seq startP (.seq arithP (.seq powMP
    (.seq (.op (.rwM sCB)) (.op (.rwM sIB)))))))))

def dimsCost (r : CNFCompilationRequest) : ℕ := 100 * (code r.verifier).length + 2 * r.input.length + 200

variable {C : Ctx}

/-- Strengthen a post-condition by the state the program leaves untouched. -/
theorem Hs.addKeep {s : St VV MM} {a : DS VV MM} {t : ℕ} {R : DS VV MM → Prop}
    (h : Hs C s a t (fun b => (∀ x, sAny (opWr x) s = false → b.env x = a.env x) →
      (∀ m, sAny (opMs m) s = false → b.ram m = a.ram m ∧ b.rc m = a.rc m) → R b)) : Hs C s a t R := by
  obtain ⟨b, n, he, hn, hb⟩ := h
  obtain ⟨k1, k2, _, _⟩ := ex_keep he
  exact ⟨b, n, he, hn, hb k1 k2⟩

theorem powMP_spec (t : ℕ) (a : DS VV MM) (ht : a.env dT = t) (h1 : a.env v1 = 1) (hW : 2 ^ t < 2 ^ C.Wd) :
    Hs C powMP a (t * 5 + 6) (fun b => b.env dM = 2 ^ t) := by
  have htW : t < 2 ^ C.Wd := lt_trans Nat.lt_two_pow_self hW
  refine Hs.seqc (t1 := 1) (t2 := t * (1 + 4) + 4) (hs_copy C dM v1 a (by decide)) (fun b hb => ?_) (by omega)
  subst hb
  refine Hs.mono (forP_ind (C := C) pT dT (.op (.shl dM)) (by decide) t 1
    (fun i b => b.env dM = 2 ^ i ∧ b.env dT = t) htW (fun i b h => h.2)
    (fun i b v h => ⟨by vsimp [h.1], by vsimp [h.2]⟩) (fun i hi b hb hc => ?_) _ ⟨by vsimp [h1], by vsimp [ht]⟩)
    le_rfl (fun b h => h.1)
  have hp : 2 ^ (i + 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by omega) hi
  refine Hs.op (OpEx.shl dM b (by rw [hb.1]; rw [pow_succ] at hp; omega)) ⟨⟨by vsimp [hb.1, pow_succ]; ring,
    by vsimp [hb.2]⟩, by vsimp [hc]⟩

theorem arithP_spec (a : DS VV MM) (hk : KC a) (t s w f : ℕ) (ht : a.env dT = t) (hs : a.env dS = s)
    (hw : a.env dWb = w) (hf : a.env dF = f) (hB : (t + s + w + f + 4) ^ 2 < 2 ^ C.Wd) :
    Hs C arithP a 31 (fun b => b.env dWd = f + 1 ∧ b.env dTW = t * (f + 1) ∧ b.env dW = windowBits t s (f + 1) ∧
      b.env dR = 1 + w + 4 * t ∧ b.env dO2 = t + 1 + s + 1 + w ∧ b.env dO3 = t + 1 + s + 1 + w + 2 * s) := by
  have e1 : 2 * (t * (f + 1)) + 4 * t + 3 * s + w + f + 4 ≤ (t + s + w + f + 4) ^ 2 := by nlinarith
  apply hs_of_wpc
  simp only [arithP, wpc, opwp]
  vsimp [ht, hs, hw, hf, hk.k4, hk.two]
  and_split
  all_goals first | omega | (unfold windowBits; omega)


theorem DS.rew_rc_self (x : DS VV MM) (m : Fin MM) : (x.rew m).rc m = 0 := by simp [DS.rew]
theorem DS.rew_rc_ne (x : DS VV MM) {m m' : Fin MM} (h : m' ≠ m) : (x.rew m).rc m' = x.rc m' := by
  simp [DS.rew, Function.update_of_ne h]

theorem dimsP_spec (r : CNFCompilationRequest) (a : DS VV MM) (hk : KC a)
    (hcb : a.ram sCB = codeBits r.verifier) (hrcb : a.rc sCB = (code r.verifier).length)
    (hib : a.ram sIB = r.input.map Bool.toNat) (hrib : a.rc sIB = r.input.length)
    (hil : a.env dIL = r.input.length) (hn : a.env dN = r.witnessLength) (hf : a.env dF = r.fuel)
    (htt : TTend a) (hW : ((code r.verifier).length + r.fuel + 2) ^ 2 + 10 ≤ C.Wd) :
    Hs C dimsP a (dimsCost r) (fun b => GC (reqGD r) b) := by
  set v := r.verifier with hv
  set L := (code v).length with hL
  have hWd : C.Wd < 2 ^ C.Wd := Nat.lt_two_pow_self
  have hsq : L + r.fuel + 2 ≤ (L + r.fuel + 2) ^ 2 := by nlinarith
  obtain ⟨hh1, hh2, hh3, hh4⟩ := code_header v
  have hL' : (codeBits v).length = L := by rw [codeBits, List.length_map]
  have hO2 : codeO2 v ≤ L := by rw [hL, code_length]; unfold codeO3; omega
  have hO1' : codeO1 v = v.tapeCount + 1 + v.stateCount + 1 := rfl
  have hO2' : codeO2 v = codeO1 v + codeW v := rfl
  have hs1 : 1 ≤ v.stateCount := Nat.pos_of_ne_zero (fun h => by have := v.machine.start.isLt; omega)
  have hwS : natBitLength v.stateCount ≤ v.stateCount := by
    unfold natBitLength; have := Nat.log_lt_self 2 (show v.stateCount ≠ 0 by omega); omega
  have hwS' : codeW v ≤ v.stateCount := hwS
  have hpt := pow_tape_le_code v
  have hlt : ∀ x, x ≤ (L + r.fuel + 2) ^ 2 → x < 2 ^ C.Wd := fun x hx => by omega
  have hst := codeBits_start v
  apply Hs.addKeep
  have hL3 : 3 ≤ L := by omega
  refine Hs.mono (?_ : Hs C dimsP a (8 * (10 * L + 11) + (r.input.length + 1)) _) ?cost (fun b h => h)
  refine Hs.seqc (t1 := 10 * L + 10) (t2 := 7 * (10 * L + 11) + (r.input.length + 1))
    (Hs.mono (hs_rwM C sCB a) (by omega) (fun b h => h)) (fun b1 hb1 => ?_) (by omega)
  subst hb1
  refine Hs.seqc (t1 := 10 * L + 10) (t2 := 6 * (10 * L + 11) + (r.input.length + 1))
    (Hs.mono (Hs.keep (onesP_spec dT (by decide) (codeBits v) 0 v.tapeCount (a.rew sCB) hk.one
      (by simp [DS.rew, hcb]) (by simp [DS.rew]) (fun i hi => by simpa using hh1 i hi) (by simpa using hh2)
      (by omega) (hlt _ (by omega)))) (by omega) (fun b h => h)) (fun b2 ⟨⟨d2, r2, m2, o2⟩, k2, s2, _, _⟩ => ?_)
    (by omega)
  refine Hs.seqc (t1 := 10 * L + 10) (t2 := 5 * (10 * L + 11) + (r.input.length + 1))
    (Hs.mono (Hs.keep (onesP_spec dS (by decide) (codeBits v) (v.tapeCount + 1) v.stateCount b2 o2
      (by rw [m2]; exact hcb) (by rw [r2]; omega) (fun i hi => hh3 i hi) hh4 (by omega) (hlt _ (by omega))))
      (by omega) (fun b h => h)) (fun b3 ⟨⟨d3, r3, m3, o3⟩, k3, s3, _, _⟩ => ?_) (by omega)
  refine Hs.seqc (t1 := 10 * L + 10) (t2 := 4 * (10 * L + 11) + (r.input.length + 1))
    (Hs.mono (Hs.keep (bitLenP_spec v.stateCount hs1 b3 d3
      (by rw [k3 vZ (by decide), k2 vZ (by decide)]; exact hk.z) (hlt _ (by omega)))) (by omega) (fun b h => h))
    (fun b4 ⟨⟨d4, m4, c4⟩, k4, s4, _, _⟩ => ?_) (by omega)
  have kc4 : KC b4 := KC.of_keep (s := bitLenP) (KC.of_keep (s := onesP dS) (KC.of_keep (s := onesP dT)
    (KC.of_keep (s := .op (.rwM sCB)) hk (by decide) (fun x _ => rfl)) (by decide) k2) (by decide) k3)
    (by decide) k4
  refine Hs.seqc (t1 := 10 * L + 10) (t2 := 3 * (10 * L + 11) + (r.input.length + 1))
    (Hs.mono (Hs.keep (startP_spec (codeBits v) (codeO1 v) (codeW v) b4 kc4 (by rw [m4, m3, m2]; exact hcb)
      (by rw [c4, r3]; exact hO1'.symm) (codeBits_le_one v) (by omega) d4
      (Nat.pow_lt_pow_right (by norm_num) (by omega)))) (by omega) (fun b h => h))
    (fun b5 ⟨⟨d5, m5, r5, kc5⟩, k5, s5, _, _⟩ => ?_) (by omega)
  have hB : (v.tapeCount + v.stateCount + codeW v + r.fuel + 4) ^ 2 < 2 ^ C.Wd :=
    hlt _ (Nat.pow_le_pow_left (by omega) 2)
  refine Hs.seqc (t1 := 10 * L + 10) (t2 := 2 * (10 * L + 11) + (r.input.length + 1))
    (Hs.mono (Hs.keep (arithP_spec b5 kc5 v.tapeCount v.stateCount (codeW v) r.fuel
      (by rw [k5 dT (by decide), k4 dT (by decide), k3 dT (by decide), d2])
      (by rw [k5 dS (by decide), k4 dS (by decide), d3]) (by rw [k5 dWb (by decide)]; exact d4)
      (by rw [k5 dF (by decide), k4 dF (by decide), k3 dF (by decide), k2 dF (by decide)]; exact hf) hB))
      (by omega) (fun b h => h))
    (fun b6 ⟨⟨e1, e2, e3, e4, e5, e6⟩, k6, s6, _, _⟩ => ?_) (by omega)
  refine Hs.seqc (t1 := 10 * L + 10) (t2 := 1 * (10 * L + 11) + (r.input.length + 1))
    (Hs.mono (Hs.keep (powMP_spec v.tapeCount b6
      (by rw [k6 dT (by decide), k5 dT (by decide), k4 dT (by decide), k3 dT (by decide), d2])
      (by rw [k6 v1 (by decide)]; exact kc5.one)
      (lt_of_le_of_lt hpt (hlt L (le_trans (by omega) hsq))))) (by omega)
      (fun b h => h))
    (fun b7 ⟨d7, k7, s7, _, _⟩ => ?_) (by omega)
  refine Hs.seqc (t1 := 10 * L + 10) (t2 := r.input.length + 1)
    (Hs.mono (hs_rwM C sCB b7) (show b7.rc sCB + 1 ≤ 10 * L + 10 by
      rw [(s7 sCB (by decide)).2, (s6 sCB (by decide)).2, r5]; omega) (fun b h => h)) (fun b8 hb8 => ?_) (by omega)
  subst hb8
  have rib : b7.rc sIB = r.input.length := by
    rw [(s7 sIB (by decide)).2, (s6 sIB (by decide)).2, (s5 sIB (by decide)).2, c4, (s3 sIB (by decide)).2,
      (s2 sIB (by decide)).2]; exact hrib
  refine Hs.mono (hs_rwM C sIB (b7.rew sCB)) (show (b7.rew sCB).rc sIB + 1 ≤ r.input.length + 1 by
    rw [DS.rew_rc_ne _ (by decide), rib]) (fun b hb K1 K2 => ?_)
  subst hb
  have kT : ∀ x, sAny (opWr x) (onesP dS) = false → sAny (opWr x) bitLenP = false →
      sAny (opWr x) startP = false → sAny (opWr x) arithP = false → sAny (opWr x) powMP = false →
      b7.env x = b2.env x := fun x h3 h4 h5 h6 h7 => by rw [k7 x h7, k6 x h6, k5 x h5, k4 x h4, k3 x h3]
  have rcb7 : b7.ram sCB = codeBits v := by
    rw [(s7 sCB (by decide)).1, (s6 sCB (by decide)).1, m5, m4, m3, m2]; exact hcb
  have rib7 : b7.ram sIB = r.input.map Bool.toNat := by
    rw [(s7 sIB (by decide)).1, (s6 sIB (by decide)).1, m5, m4, m3, m2]; exact hib
  refine ⟨KC.of_keep (s := dimsP) hk (by decide) K1, ?_, rcb7,
    rib7, by rw [DS.rew_rc_ne _ (by decide), DS.rew_rc_self], DS.rew_rc_self _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [K1 dN (by decide)]; exact hn, ?_, by rw [K1 dIL (by decide), hil]; simp [reqGD]⟩
  · unfold TTend; rw [(K2 sTT (by decide)).1, (K2 sTT (by decide)).2]; exact htt
  · show b7.env dT = _; rw [kT dT (by decide) (by decide) (by decide) (by decide) (by decide), d2]; rfl
  · show b7.env dS = _; rw [k7 dS (by decide), k6 dS (by decide), k5 dS (by decide), k4 dS (by decide), d3]; rfl
  · show b7.env dWb = _; rw [k7 dWb (by decide), k6 dWb (by decide), k5 dWb (by decide), d4]; rfl
  · show b7.env dWd = _; rw [k7 dWd (by decide), e1]; rfl
  · show b7.env dTW = _; rw [k7 dTW (by decide), e2]; rfl
  · show b7.env dW = _; rw [k7 dW (by decide), e3]; rfl
  · show b7.env dM = _; rw [d7]; rfl
  · show b7.env dR = _; rw [k7 dR (by decide), e4]; rfl
  · show b7.env dO2 = _; rw [k7 dO2 (by decide), e5]; rfl
  · show b7.env dO3 = _; rw [k7 dO3 (by decide), e6]; rfl
  · show b7.env dSt = _; rw [k7 dSt (by decide), k6 dSt (by decide), d5]; exact hst
  case cost => show _ ≤ 100 * L + 2 * r.input.length + 200; omega


end NearCubicGates.Adapters.Compile
