import Proof.Gates.Dispatch.Zero
import Proof.Gates.Dispatch.Run

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxRecDepth 4000

namespace NearCubicGates.Close.Dispatch

open NearCubicGates NearCubicGates.Close.Counter NearCubicWires NearCubicWires.RepairRepresentation
  NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats

variable {C : Ctx}

/-! ## `W ≠ 0` forces `n ≤ |callWord c|` -/

theorem length_le_flatMap_of_pos {α : Type} (f : α → List Bool) (hf : ∀ x, 1 ≤ (f x).length) (xs : List α) :
    xs.length ≤ (xs.flatMap f).length := by
  induction xs with
  | nil => simp
  | cons y ys ih => simp only [List.length_cons, List.flatMap_cons, List.length_append]; have := hf y; omega

theorem n_le_circuit {n B : ℕ} (Cc : NCircuit n) (hwf : Cc.WellFormed B) (hW : Cc.topWeight ≠ 0) :
    n ≤ (circuitWord Cc).length := by
  have hco : Cc.coeffs ≠ [] := by
    intro h; apply hW; unfold NCircuit.topWeight; rw [h]; rfl
  have hg : Cc.gates ≠ [] := by
    intro h; apply hco; have := hwf.1; rw [h] at this; exact List.length_eq_zero_iff.1 this.symm
  obtain ⟨g, hgm⟩ := List.exists_mem_of_ne_nil _ hg
  have h1 : (gateWord g).length ≤ (Cc.gates.flatMap gateWord).length := len_le_flatMap gateWord Cc.gates g hgm
  have h2 : n ≤ (gateWord g).length := by
    have : n ≤ ((List.ofFn g.weight).flatMap Interfaces.intWord).length := by
      have := length_le_flatMap_of_pos Interfaces.intWord (fun x => by
        simp only [Interfaces.intWord, List.length_append, natWord_length]; omega) (List.ofFn g.weight)
      simpa using this
    simp only [gateWord, listWord, List.length_append]; omega
  simp only [circuitWord, listWord, List.length_append]; omega

theorem n_le_callWord (B1 B2 : ℕ) (c : Call) (hadm : c.Admitted B1 B2) (hW : c.W ≠ 0) :
    c.n ≤ (callWord c).length := by
  obtain ⟨-, hw1, hw2, -⟩ := hadm
  have hL := congrArg List.length (callWord_eq c)
  simp only [List.length_append] at hL
  unfold Call.W at hW
  by_cases h1 : c.first.topWeight = 0
  · have := n_le_circuit c.second hw2 (by omega); omega
  · have := n_le_circuit c.first hw1 h1; omega

/-! ## Polynomially bounded step counts -/

/-- `f` is bounded by a polynomial in `L`. -/
def PolyB (f : ℕ → ℕ) : Prop := ∃ K e : ℕ, ∀ L, f L ≤ K * (L + 1) ^ e

theorem PolyB.const (c : ℕ) : PolyB (fun _ => c) := ⟨c, 0, fun L => by simp⟩

theorem PolyB.id : PolyB (fun L => L) := ⟨1, 1, fun L => by simp⟩

theorem PolyB.add {f g : ℕ → ℕ} (hf : PolyB f) (hg : PolyB g) : PolyB (fun L => f L + g L) := by
  obtain ⟨K1, e1, h1⟩ := hf
  obtain ⟨K2, e2, h2⟩ := hg
  refine ⟨K1 + K2, e1 + e2, fun L => ?_⟩
  have p1 : (L + 1) ^ e1 ≤ (L + 1) ^ (e1 + e2) := Nat.pow_le_pow_right (by omega) (by omega)
  have p2 : (L + 1) ^ e2 ≤ (L + 1) ^ (e1 + e2) := Nat.pow_le_pow_right (by omega) (by omega)
  calc f L + g L ≤ K1 * (L + 1) ^ e1 + K2 * (L + 1) ^ e2 := Nat.add_le_add (h1 L) (h2 L)
    _ ≤ K1 * (L + 1) ^ (e1 + e2) + K2 * (L + 1) ^ (e1 + e2) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ p1) (Nat.mul_le_mul_left _ p2)
    _ = (K1 + K2) * (L + 1) ^ (e1 + e2) := by ring

theorem PolyB.mul {f g : ℕ → ℕ} (hf : PolyB f) (hg : PolyB g) : PolyB (fun L => f L * g L) := by
  obtain ⟨K1, e1, h1⟩ := hf
  obtain ⟨K2, e2, h2⟩ := hg
  refine ⟨K1 * K2, e1 + e2, fun L => ?_⟩
  calc f L * g L ≤ (K1 * (L + 1) ^ e1) * (K2 * (L + 1) ^ e2) := Nat.mul_le_mul (h1 L) (h2 L)
    _ = K1 * K2 * (L + 1) ^ (e1 + e2) := by ring

theorem PolyB.pow {f : ℕ → ℕ} (hf : PolyB f) (k : ℕ) : PolyB (fun L => f L ^ k) := by
  induction k with
  | zero => simpa using PolyB.const 1
  | succ k ih => simpa [pow_succ] using PolyB.mul ih hf

theorem PolyB.mono {f g : ℕ → ℕ} (hg : PolyB g) (h : ∀ L, f L ≤ g L) : PolyB f := by
  obtain ⟨K, e, hK⟩ := hg
  exact ⟨K, e, fun L => le_trans (h L) (hK L)⟩

/-- Closes `PolyB` goals for `+`, `*`, `^`, constants and the variable. -/
syntax "polyb" : tactic
macro_rules
  | `(tactic| polyb) =>
    `(tactic| repeat (first | with_reducible exact PolyB.const _ | with_reducible exact PolyB.id |
      with_reducible apply PolyB.add | with_reducible apply PolyB.mul | with_reducible apply PolyB.pow))

example (K : ℕ) : PolyB (fun L => 3 * (L + K) ^ 4 + L * (L + 2)) := by polyb

/-! ## The value of `dispatchWord` on each branch -/

section DW
variable (B1 B2 cT : ℕ) (c : Call) (w : List Bool)
theorem dw_none (hA : c.Admitted B1 B2) (hW : c.W ≠ 0) (hs : selectParams cT (header c) = none) :
    dispatchWord B1 B2 cT c w = natWord 0 ++ outputWord defaultValue := by
  unfold dispatchWord counterOnCall; simp only [hA, hW, hs, ne_eq, not_false_eq_true, and_self, if_true, if_false]
theorem dw_dnone (hA : c.Admitted B1 B2) (hW : c.W ≠ 0) (p : Params) (hs : selectParams cT (header c) = some p)
    (hd : decodeWitness c p w = none) : dispatchWord B1 B2 cT c w = natWord 0 ++ outputWord defaultValue := by
  unfold dispatchWord counterOnCall; simp only [hA, hW, hs, hd, ne_eq, not_false_eq_true, and_self, if_true, if_false]
theorem dw_some (hA : c.Admitted B1 B2) (hW : c.W ≠ 0) (p : Params) (hs : selectParams cT (header c) = some p)
    (wt : Wit c.n) (hd : decodeWitness c p w = some wt) :
    dispatchWord B1 B2 cT c w = natWord 1 ++ (callWord c ++ paramsWord p ++ witWord c p wt) := by
  unfold dispatchWord; simp only [hA, hW, hs, hd, ne_eq, not_false_eq_true, and_self, if_true]
theorem dw_zero (hA : c.Admitted B1 B2) (hW : c.W = 0) :
    dispatchWord B1 B2 cT c w = natWord 0 ++ outputWord (zeroWeightValue c) := by
  unfold dispatchWord counterOnCall; simp [hA, hW]
theorem dw_def (hA : ¬ c.Admitted B1 B2) :
    dispatchWord B1 B2 cT c w = natWord 0 ++ outputWord defaultValue := by
  unfold dispatchWord counterOnCall; simp [hA]
end DW

/-! ## Agreement on the parsed fields -/

theorem ParseOut.congr {c : Call} {a b : DS VV} (h : ParseOut c a)
    (hb : ∀ y : Fin VV, 17 ≤ y.val → y.val < 56 → b.env y = a.env y) : ParseOut c b := by
  have F := fun (y : Fin VV) (h1 : 17 ≤ y.val ∧ y.val < 56) => hb y h1.1 h1.2
  exact ⟨by rw [F vN (by decide)]; exact h.n, by rw [F vTAG (by decide)]; exact h.tag,
    by rw [F vB0 (by decide)]; exact h.b0,
    ⟨by rw [F vG1 (by decide)]; exact h.c1.g, by rw [F vC1 (by decide)]; exact h.c1.c,
      by rw [F vTW1 (by decide)]; exact h.c1.tw, by rw [F vT1 (by decide)]; exact h.c1.t,
      by rw [F vTB1 (by decide)]; exact h.c1.tb, by rw [F vWOK1 (by decide)]; exact h.c1.wok,
      by rw [F vNZ1 (by decide)]; exact h.c1.nz, by rw [F vCO1 (by decide)]; exact h.c1.co⟩,
    ⟨by rw [F vG2 (by decide)]; exact h.c2.g, by rw [F vC2 (by decide)]; exact h.c2.c,
      by rw [F vTW2 (by decide)]; exact h.c2.tw, by rw [F vT2 (by decide)]; exact h.c2.t,
      by rw [F vTB2 (by decide)]; exact h.c2.tb, by rw [F vWOK2 (by decide)]; exact h.c2.wok,
      by rw [F vNZ2 (by decide)]; exact h.c2.nz, by rw [F vCO2 (by decide)]; exact h.c2.co⟩,
    by rw [F vPL (by decide)]; exact h.pl, by rw [F vPP (by decide)]; exact h.pp,
    by rw [F vPOK (by decide)]; exact h.pok, by rw [F vSG (by decide)]; exact h.sg,
    by rw [F vNUM (by decide)]; exact h.num, by rw [F vDEN (by decide)]; exact h.den,
    by rw [F vRL (by decide)]; exact h.rl, by rw [F vCL (by decide)]; exact h.cl⟩

theorem agree_of_frS {a b : DS VV} {T : List (Fin VV)} (hf : FrS a b T) (hT : ∀ z ∈ T, z.val < 17 ∨ 56 ≤ z.val) :
    ∀ y : Fin VV, 17 ≤ y.val → y.val < 56 → b.env y = a.env y :=
  fun y h1 h2 => hf y (by omega) (fun hm => by have := hT y hm; omega)

theorem agree_of_frW {a b : DS VV} (hf : FrW a b) : ∀ y : Fin VV, 17 ≤ y.val → y.val < 56 → b.env y = a.env y :=
  fun y h1 h2 => hf y (by omega) (by unfold WitVar; omega)

/-! ## The prefix: constants, parse, admission, `W ≠ 0` -/

def vAD0 : Fin VV := ⟨131, by decide⟩

def initP : St VV := .seq (.op (.inc v1)) (.seq (.op (.inc v2)) (.op (.inc v2)))

open AE in
def prefixP (B1 B2 : ℕ) : St VV :=
  .seq initP (.seq parseCall (.seq (admitP B1 B2) (.seq (.op (.copy vAD0 vADM))
    (.seq (assign pX1 (add (var vTW1) (var vTW2))) (killIf (.eq pX1 vZ) vADM)))))

def prefixCost (B1 B2 L : ℕ) : ℕ := 30 + parseCost L + admCost B1 B2 + 40

open Classical in
theorem prefix_spec (B1 B2 : ℕ) (c : Call) (hcw : C.cw = callWord c) (hW : 2 * C.cw.length + 8 ≤ C.Wd)
    (hL : C.cw.length + 2 < 2 ^ C.Wd) (hA : (B1 + B2 + 5) * ((callWord c).length + 1) ≤ C.Wd) :
    Hs C (prefixP B1 B2) (a0 (V := VV)) (prefixCost B1 B2 C.cw.length) (fun b => ParseOut c b ∧
      b.env vADM = bnat (c.Admitted B1 B2 ∧ c.W ≠ 0) ∧ b.env vAD0 = bnat (c.Admitted B1 B2) ∧
      b.wq = 0 ∧ b.out = [] ∧ Cst b ∧ Valid C b) := by
  have hW1 : 1 ≤ C.Wd := by omega
  have h4 : 4 < 2 ^ C.Wd := lt_of_lt_of_le (by norm_num : 4 < 2 ^ 3) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hv0 : Valid C (a0 (V := VV)) := ⟨fun y => by simp [a0], by simp [a0], by simp [a0]⟩
  -- constants
  have hinit : Hs C initP (a0 (V := VV)) 5 (fun b => Cst b ∧ b.cp = 0 ∧ b.wq = 0 ∧ b.out = [] ∧ Valid C b) := by
    refine Hx.hs (Hs.then (Hs.addValid hW1 hv0 (hs_inc C v1 _ (by simp [a0]; omega))) (fun b1 ⟨e1, hv1⟩ k1 hk1 => ?_))
    subst e1
    refine Hs.then (Hs.addValid hW1 hv1 (hs_inc C v2 _ (by rw [DS.set_env_ne _ _ (by decide)]; simp [a0]; omega)))
      (fun b2 ⟨e2, hv2⟩ k2 hk2 => ?_)
    subst e2
    refine Hs.last (Hs.addValid hW1 hv2 (hs_inc C v2 _ (by
      rw [DS.set_env_self, DS.set_env_ne _ _ (by decide)]; simp [a0]; omega)))
      (fun b3 ⟨e3, hv3⟩ k3 hk3 => ?_)
    subst e3
    refine ⟨⟨⟨by simp [a0, DS.set, vZ, v1, v2], by simp [a0, DS.set, vZ, v1, v2], by simp [a0, DS.set, vZ, v1, v2],
      by simp [a0, DS.set, vZ, v1, v2, vPOS]⟩, rfl, rfl, rfl, hv3⟩, by omega⟩
  refine Hx.hs (Hs.then hinit (fun aI ⟨hcI, hcp, hwq0, hout0, hv3⟩ k3 hk3 => ?_))
  -- parse
  refine Hs.then (Hs.addValid hW1 hv3 (parseCall_spec c aI hcI hcp hcw (by omega) hL))
    (fun b4 ⟨⟨p1, p2, p3, p4, p5, p6⟩, hv4⟩ k4 hk4 => ?_)
  -- admission
  refine Hs.then (Hs.addValid hW1 hv4 (admitP_spec B1 B2 c b4 p5 p1 hA))
    (fun b5 ⟨⟨q1, q2, q3, q4, q5, q6⟩, hv5⟩ k5 hk5 => ?_)
  have q1' : b5.env vADM = bnat (c.Admitted B1 B2) := by rw [q1]; exact bnat_congr (admFlag_iff B1 B2 c)
  have hp5 : ParseOut c b5 := p1.congr (agree_of_frS q6.toS (by decide))
  refine Hs.then (Hs.addValid hW1 hv5 (hs_copy C vAD0 vADM b5 (by decide))) (fun b6 ⟨e6, hv6⟩ k6 hk6 => ?_)
  subst e6
  have hc6 : Cst (b5.set vAD0 (b5.env vADM)) := Cst.set q5 _ _ (by decide)
  have hW6 : (b5.set vAD0 (b5.env vADM)).env vTW1 + (b5.set vAD0 (b5.env vADM)).env vTW2 = c.W := by
    rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide), hp5.c1.tw, hp5.c2.tw]; rfl
  have hWlt : c.W < 2 ^ C.Wd := by
    have := hv6.env_lt vTW1; have := hv6.env_lt vTW2
    rw [← hW6]
    have h1 := (hv5.env_lt vTW1); have h2 := hv5.env_lt vTW2
    rw [DS.set_env_ne _ _ (by decide), DS.set_env_ne _ _ (by decide)]
    rw [hp5.c1.tw] at h1 ⊢; rw [hp5.c2.tw] at h2 ⊢
    have hb := call_bounds c
    have : 2 ^ (callWord c).length * 2 ≤ 2 ^ C.Wd := by
      rw [← pow_succ]; exact Nat.pow_le_pow_right (by norm_num) (by rw [← hcw]; omega)
    omega
  refine Hs.then (Hs.addValid hW1 hv6 (assign_spec pX1 (by decide) (by decide) (.add (.var vTW1) (.var vTW2)) _
    (by aevar) (by aevar) hc6 (by simp only [AE.ok, AE.eval]; exact ⟨trivial, trivial, by rw [hW6]; exact hWlt⟩)))
    (fun b7 ⟨⟨r1, r2, r3, r4, r5, r6⟩, hv7⟩ k7 hk7 => ?_)
  simp only [AE.eval] at r1
  rw [hW6] at r1
  refine Hs.last (Hs.addValid hW1 hv7 (killIf_spec (.eq pX1 vZ) vADM (show pX1 ≠ vZ by decide) (by decide) b7))
    (fun g ⟨⟨g1, g2, g3, g4, g5⟩, hv8⟩ k8 hk8 => ?_)
  have b7A : b7.env vADM = bnat (c.Admitted B1 B2) := by
    rw [r2 vADM (by decide) (by decide) (by decide), DS.set_env_ne _ _ (by decide)]; exact q1'
  refine ⟨⟨?_, ?_, ?_, by rw [g3, r4]; show b5.wq = 0; rw [q3, p3, hwq0], by rw [g4, r5]; show b5.out = []; rw [q4, p4, hout0],
    Cst.of_fr r6 g5 (by decide) (by rw [g5 vPOS (by decide), g2]; exact r6.pos), hv8⟩, ?_⟩
  · refine hp5.congr (fun y h1 h2 => ?_)
    rw [g5 y (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]; exact
      ⟨fun h => by subst h; simp [vADM] at h1 h2, fun h => by subst h; simp [vJ] at h1⟩),
      r2 y (by omega) (fun h => by subst h; simp [vJ] at h1) (fun h => by subst h; simp [pX1] at h2),
      DS.set_env_ne _ _ (fun h => by subst h; simp [vAD0] at h2)]
  · rw [g1]
    simp only [Cnd.eval, r1, r6.z]
    by_cases hW0 : c.W = 0
    · rw [if_pos (by simp [hW0])]; symm; exact bnat_zero_of_not (fun h => h.2 hW0)
    · rw [if_neg (by simp [hW0]), b7A]; exact bnat_congr ⟨fun h => ⟨h, hW0⟩, fun h => h.1⟩
  · rw [g5 vAD0 (by decide), r2 vAD0 (by decide) (by decide) (by decide), DS.set_env_self, q1']
  · simp only [AE.cost] at hk7
    unfold prefixCost
    omega

/-! ## Branch B: no parameters (not admitted, or `W = 0`) -/

theorem parity_len_le (c : Call) : c.parity.length ≤ (callWord c).length := by
  have h1 := length_le_flatMap_of_pos natWord (fun x => by rw [natWord_length]; omega) c.parity
  have h2 := congrArg List.length (drop_parity c)
  rw [List.length_drop, List.length_append] at h2
  omega

def branchB : St VV := .ite (.eq vAD0 v1) zeroOut defOut

theorem oddCostT_mono {L len W : ℕ} (h : len ≤ L) : oddCostT L len W ≤ oddCostT L L W := by
  unfold oddCostT oddCost; gcongr

def costB (L W : ℕ) : ℕ := oddCostT L L W + 2 * zwLen + 2 * defW.length + 60

open Classical in
theorem branchB_spec (B1 B2 cT : ℕ) (c : Call) (w : List Bool) (hcw : C.cw = callWord c)
    (hW : 2 * C.cw.length + 8 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd) (b : DS VV) (hp : ParseOut c b) (hc : Cst b)
    (hout : b.out = []) (hA0 : b.env vAD0 = bnat (c.Admitted B1 B2)) (hnot : ¬ (c.Admitted B1 B2 ∧ c.W ≠ 0)) :
    Hs C branchB b (costB C.cw.length C.Wd) (fun g => g.out = dispatchWord B1 B2 cT c w) := by
  refine Hs.ite (show vAD0 ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
  · have hadm : c.Admitted B1 B2 := by
      have : b.env vAD0 = 1 := by simpa [Cnd.eval, hc.one] using he
      rw [hA0] at this; exact (bnat_eq_one _).1 this
    have hW0 : c.W = 0 := by by_contra h; exact hnot ⟨hadm, h⟩
    have hlen : c.parity.length ≤ C.cw.length := by rw [hcw]; exact parity_len_le c
    refine Hs.mono (zeroOut_spec B1 B2 c hadm hW0 b hc hp hcw hW hL) (by
      have := oddCostT_mono (L := C.cw.length) (W := C.Wd) hlen; omega) ?_
    rintro g ⟨g1, -, -, -⟩
    rw [g1, hout, List.nil_append, dw_zero B1 B2 cT c w hadm hW0]
  · have hadm : ¬ c.Admitted B1 B2 := by
      intro h
      have : b.env vAD0 = 1 := by rw [hA0]; exact bnat_one_of h
      simp [Cnd.eval, hc.one, this] at he
    refine Hs.mono (defOut_spec b hc) (by omega) ?_
    rintro g ⟨g1, -⟩
    rw [g1, hout, List.nil_append, dw_def B1 B2 cT c w hadm]

/-! ## Branch A: parameters, witness, printing -/

theorem PV.congr {p : Params} {a b : DS VV} (h : PV p a)
    (hb : ∀ y : Fin VV, (y.val = 30 ∨ (140 ≤ y.val ∧ y.val < 200)) → b.env y = a.env y) : PV p b := by
  have F := hb
  exact ⟨by rw [F vN (by decide)]; exact h.n, by rw [F pW (by decide)]; exact h.W, by rw [F pK (by decide)]; exact h.k,
    by rw [F pT (by decide)]; exact h.T, by rw [F pM (by decide)]; exact h.m, by rw [F pDM (by decide)]; exact h.Dmax,
    by rw [F pP (by decide)]; exact h.P, by rw [F pE (by decide)]; exact h.e, by rw [F pNP (by decide)]; exact h.card,
    by rw [F pWIN (by decide)]; exact h.window, by rw [F pL2 (by decide)]; exact h.L2,
    by rw [F pLW (by decide)]; exact h.Lw, by rw [F pHE (by decide)]; exact h.hE, by rw [F pH (by decide)]; exact h.h,
    by rw [F pR0 (by decide)]; exact h.R0, by rw [F pEN (by decide)]; exact h.en, by rw [F pED (by decide)]; exact h.ed,
    by rw [F pM1 (by decide)]; exact h.M1, by rw [F pJ (by decide)]; exact h.J, by rw [F pA (by decide)]; exact h.A,
    by rw [F pLB (by decide)]; exact h.Lam, by rw [F pJM (by decide)]; exact h.JM,
    by rw [F pLAM (by decide)]; exact h.lam, by rw [F pXN (by decide), F pXD (by decide)]; exact h.x1,
    by rw [F pXN (by decide)]; exact h.xn, by rw [F pXN (by decide), F pXD (by decide)]; exact h.xnd,
    by rw [F pXN (by decide), F pXD (by decide)]; exact h.xd⟩

theorem printCost_mono {P J h W P' J' h' : ℕ} (hP : P ≤ P') (hJ : J ≤ J') (hh : h ≤ h') :
    printCost P J h W ≤ printCost P' J' h' W := by
  unfold printCost prPrintCost chainCost bodyCost; gcongr

def printAll (wf : WitFrag) : St VV := .seq (emitL (natWord 1)) (.seq copyCW (.seq printParams wf.print))

def branchA (cT : ℕ) (wf : WitFrag) : St VV :=
  .seq (paramsP cT) (.ite (.eq vADM v1) (.seq wf.check (.ite (.eq vWF v1) (printAll wf) defOut)) defOut)

def costA (cT L W : ℕ) (wc : ℕ → ℕ) : ℕ :=
  paramsCost (L + cT + 4) + wc L + (2 * (natWord 1).length + 1) + (L * 8 + 6) + printCost L (L + 1) L W + wc L +
    2 * defW.length + 40

theorem notin_of {y : Fin VV} {T : List (Fin VV)} {P : ℕ → Prop} (hT : ∀ z ∈ T, ¬ P z.val) (hy : P y.val) :
    y ∉ T := fun hm => hT y hm hy

theorem agree_range_of_frS {a b : DS VV} {T : List (Fin VV)} (hf : FrS a b T) (lo hi : ℕ) (hhi : hi ≤ 200)
    (hT : ∀ z ∈ T, z.val < lo ∨ hi ≤ z.val) : ∀ y : Fin VV, lo ≤ y.val → y.val < hi → b.env y = a.env y :=
  fun y h1 h2 => hf y (by omega) (fun hm => by have := hT y hm; omega)

open Classical in
theorem branchA_spec (B1 B2 cT : ℕ) (wf : WitFrag) (c : Call) (w : List Bool) (hcw : C.cw = callWord c)
    (hwit : C.wit = w) (hW : 2 * C.cw.length + 8 ≤ C.Wd) (hL : C.cw.length + 2 < 2 ^ C.Wd)
    (hBig : 4000 * (C.cw.length + cT + 4) ^ 2 ≤ C.Wd) (b : DS VV) (hp : ParseOut c b) (hc : Cst b) (hv : Valid C b)
    (hwq : b.wq = 0) (hout : b.out = []) (hadm : c.Admitted B1 B2) (hW0 : c.W ≠ 0) :
    Hs C (branchA cT wf) b (costA cT C.cw.length C.Wd wf.cost) (fun g => g.out = dispatchWord B1 B2 cT c w) := by
  have hW1 : 1 ≤ C.Wd := by omega
  have hW3 : 3 ≤ C.Wd := by omega
  have hnL : c.n ≤ C.cw.length := by rw [hcw]; exact n_le_callWord B1 B2 c hadm hW0
  obtain ⟨-, -, -, hnum, hden, -⟩ := call_bounds c
  rw [← hcw] at hnum hden
  have hwd : 4000 * (C.cw.length + 4) ^ 2 ≤ C.Wd :=
    le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)) hBig
  refine Hx.hs (Hs.then (Hs.addValid hW1 hv (paramsP_spec B1 B2 cT c b hc hp hadm hW0 C.cw.length hnL hnum hden hBig))
    (fun b1 ⟨⟨hdisj, p2, p3, p4, p5, p6⟩, hv1⟩ k1 hk1 => ?_))
  have hp1 : ParseOut c b1 := hp.congr (agree_of_frS p6 (by decide))
  set T := wf.cost C.cw.length + (2 * (natWord 1).length + 1) + (C.cw.length * 8 + 6) +
    printCost C.cw.length (C.cw.length + 1) C.cw.length C.Wd + wf.cost C.cw.length + 2 * defW.length + 30 with hT
  have hbr : Hs C (.ite (.eq vADM v1) (.seq wf.check (.ite (.eq vWF v1) (printAll wf) defOut)) defOut) b1 (T + 1)
      (fun g => g.out = dispatchWord B1 B2 cT c w) := by
    refine Hs.ite (show vADM ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
    · have hA1 : b1.env vADM = 1 := by simpa [Cnd.eval, p5.one] using he
      obtain ⟨p, hsp, hpv, hrep⟩ : ∃ p, selectParams cT (header c) = some p ∧ PV p b1 ∧
          1024 * b1.env pXD + (p.h + 33) * (p.h + 33) + Jmax p.n + 1000 < 2 ^ C.Wd := by
        rcases hdisj with ⟨h0, _⟩ | ⟨_, h⟩
        · rw [h0] at hA1; exact absurd hA1 (by decide)
        · exact h
      have hS := selectParams_spec cT (header c) p hsp
      have hpn : p.n = c.n := hS.n_eq
      have hJn : p.J ≤ c.n + 1 := by
        have h1 := (leastUpTo_spec _ _ _ hS.J_eq).2.1
        have h2 := hS.J_pos
        have h3 := (jmax_le (header c).n).2
        have : (header c).n = c.n := rfl
        omega
      have hpre : WitPre C c p b1 := ⟨p5, hp1, hpv.k, by rw [hpv.lam, hpn], hpv.J, hcw, hnL,
        by have := hS.k_lt; exact this.le, hJn, hwd⟩
      set TT := (2 * (natWord 1).length + 1) + (C.cw.length * 8 + 6) +
        printCost C.cw.length (C.cw.length + 1) C.cw.length C.Wd + wf.cost C.cw.length + 2 * defW.length + 26 with hTT
      refine Hs.mono (Hs.seq (t1 := wf.cost C.cw.length) (t2 := TT + 1)
        (Hs.addValid hW1 hv1 (wf.spec C c p b1 hpre (by rw [p3, hwq])))
        (fun b2 ⟨⟨q1, q2, q3, q4, q5⟩, hv2⟩ => ?_)) (by omega) (fun g hg => hg)
      have hp2 : ParseOut c b2 := hp1.congr (agree_of_frW q4)
      have hPle : p.P ≤ C.cw.length := by
        rw [hS.P_eq]; exact le_trans (Nat.findGreatest_le _) (le_trans (min_le_left _ _) hnL)
      have hhle : p.h ≤ p.P := by rw [hS.h_eq, hS.hE_eq]; exact sqrt_hE_le p.P
      have hJle : Jmax p.n ≤ C.cw.length + 1 := by have := (jmax_le p.n).2; rw [hpn] at this ⊢; omega
      have hpc := printCost_mono (W := C.Wd) (P := p.P) (J := Jmax p.n) (h := p.h)
        (P' := C.cw.length) (J' := C.cw.length + 1) (h' := C.cw.length) hPle hJle (by omega)
      refine Hs.ite (c := .eq vWF v1) (show vWF ≠ v1 by decide) (fun he2 => ?_) (fun he2 => ?_)
      · obtain ⟨wt, hdec⟩ : ∃ wt, decodeWitness c p C.wit = some wt := by
          have : b2.env vWF = 1 := by simpa [Cnd.eval, q3.one] using he2
          rw [q1] at this
          exact Option.isSome_iff_exists.1 ((bnat_eq_one _).1 this)
        refine Hs.mono (Hs.seq (t2 := (C.cw.length * 8 + 6) + (printCost p.P (Jmax p.n) p.h C.Wd +
          wf.cost C.cw.length + 1) + 1) (Hs.addValid hW1 hv2 (emitL_spec (natWord 1) b2))
          (fun b3 ⟨⟨r1, r2, r3, r4⟩, hv3⟩ => ?_)) (by omega) (fun g hg => hg)
        have hc3 : Cst b3 := Cst.of_fr q3 r4 (by decide) (by rw [r4 vPOS (by decide), r2]; exact q3.pos)
        have hp3 : ParseOut c b3 := hp2.congr (fun y h1 h2 => r4 y (notin_of (P := fun v => 17 ≤ v ∧ v < 56)
          (by decide) ⟨h1, h2⟩))
        refine Hs.seq (copyCW_spec b3 hc3 hv3 (by rw [hp3.cl, hcw]) (by omega) hW1)
          (fun b4 ⟨s1, s2, s3, s4, s5, s6⟩ => ?_)
        have hp4 : ParseOut c b4 := hp3.congr (agree_of_frS s6 (by decide))
        have A41 : ∀ y : Fin VV, (y.val = 30 ∨ (140 ≤ y.val ∧ y.val < 200)) → b4.env y = b1.env y := by
          intro y hy
          rw [s6 y (by omega) (notin_of (P := fun v => v = 30 ∨ (140 ≤ v ∧ v < 200)) (by decide) hy),
            r4 y (notin_of (P := fun v => v = 30 ∨ (140 ≤ v ∧ v < 200)) (by decide) hy),
            q4 y (by omega) (by unfold WitVar; omega)]
        have hpv4 : PV p b4 := hpv.congr A41
        have hPW : 2 * (p.P + 1) + 8 < 2 ^ C.Wd := by have := wd_small C.Wd hW3; omega
        refine Hs.seq (printParams_spec cT c p hS b4 s4 s5 hpv4 hp4 hW3
          (by rw [A41 pXD (by decide)]; exact hrep) hPW) (fun b5 ⟨u1, u2, u3, u4, u5, u6⟩ => ?_)
        have hp5 : ParseOut c b5 := hp4.congr (agree_of_frS u6 (by decide))
        have hpre5 : WitPre C c p b5 := ⟨u4, hp5,
          by rw [u6 pK (by decide) (by decide), A41 pK (by decide)]; exact hpv.k,
          by rw [u6 pLAM (by decide) (by decide), A41 pLAM (by decide), hpv.lam, hpn],
          by rw [u6 pJ (by decide) (by decide), A41 pJ (by decide)]; exact hpv.J, hcw, hnL,
          by have := hS.k_lt; exact this.le, hJn, hwd⟩
        have hag : ∀ y : Fin VV, 61 ≤ y.val → y.val < 98 → b5.env y = b2.env y := by
          intro y h1 h2
          rw [u6 y (by omega) (notin_of (P := fun v => 61 ≤ v ∧ v < 98) (by decide) ⟨h1, h2⟩),
            s6 y (by omega) (notin_of (P := fun v => 61 ≤ v ∧ v < 98) (by decide) ⟨h1, h2⟩),
            r4 y (notin_of (P := fun v => 61 ≤ v ∧ v < 98) (by decide) ⟨h1, h2⟩)]
        refine Hs.mono (q5 wt hdec b5 hpre5 hag) le_rfl ?_
        rintro g ⟨g1, -, -⟩
        rw [g1, u1, s1, r1, q2, p4, hout, List.nil_append, hcw, ← hwit,
          dw_some B1 B2 cT c C.wit hadm hW0 p hsp wt hdec]
        simp only [List.append_assoc]
      · have hdn : decodeWitness c p C.wit = none := by
          have : b2.env vWF ≠ 1 := by simpa [Cnd.eval, q3.one] using he2
          rw [q1] at this
          cases hd : decodeWitness c p C.wit with
          | none => rfl
          | some _ => exact absurd (bnat_one_of (by rw [hd]; rfl)) this
        refine Hs.mono (defOut_spec b2 q3) (by omega) ?_
        rintro g ⟨g1, -⟩
        rw [g1, q2, p4, hout, List.nil_append, ← hwit, dw_dnone B1 B2 cT c C.wit hadm hW0 p hsp hdn]
    · have hsn : selectParams cT (header c) = none := by
        rcases hdisj with ⟨_, h⟩ | ⟨h1, _⟩
        · exact h
        · exfalso; simp [Cnd.eval, p5.one, h1] at he
      refine Hs.mono (defOut_spec b1 p5) (by omega) ?_
      rintro g ⟨g1, -⟩
      rw [g1, p4, hout, List.nil_append, ← hwit, dw_none B1 B2 cT c C.wit hadm hW0 hsn]
  refine Hs.last hbr (fun g hg k2 hk2 => ⟨hg, ?_⟩)
  unfold costA
  omega

/-! ## The whole program -/

def mainP (B1 B2 cT : ℕ) (wf : WitFrag) : St VV :=
  .seq (prefixP B1 B2) (.ite (.eq vADM v1) (branchA cT wf) branchB)

/-- The step bound, a polynomial in `L = |callWord c|`. -/
def NB (B1 B2 cT K : ℕ) (wc : ℕ → ℕ) (L : ℕ) : ℕ :=
  prefixCost B1 B2 L + (costA cT L (wdOf K L) wc + costB L (wdOf K L)) + 2

theorem widths (B1 B2 cT K L : ℕ) (hK : B1 + B2 + cT + 70 ≤ K) :
    2 * L + 8 ≤ wdOf K L ∧ L + 2 < 2 ^ wdOf K L ∧ (B1 + B2 + 5) * (L + 1) ≤ wdOf K L ∧
    4000 * (L + cT + 4) ^ 2 ≤ wdOf K L := by
  unfold wdOf
  set X := L + K with hX
  have hX70 : 70 ≤ X := by omega
  have hX2 : X ^ 4 = X ^ 2 * X ^ 2 := by ring
  have hXX : X ≤ X ^ 2 := by nlinarith
  have hX2b : 4900 ≤ X ^ 2 := by nlinarith
  have h1 : 2 * L + 8 ≤ X ^ 4 := by nlinarith
  have hp : X ^ 4 < 2 ^ X ^ 4 := Nat.lt_two_pow_self
  refine ⟨h1, by omega, ?_, ?_⟩
  · have : (B1 + B2 + 5) * (L + 1) ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  · have : (L + cT + 4) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left (by omega) 2
    nlinarith

open Classical in
theorem mainP_spec (B1 B2 cT K : ℕ) (wf : WitFrag) (hK : B1 + B2 + cT + 70 ≤ K) (c : Call) (w : List Bool) :
    Hs (ctxOf K (callWord c) w) (mainP B1 B2 cT wf) (a0 (V := VV)) (NB B1 B2 cT K wf.cost (callWord c).length)
      (fun b => b.out = dispatchWord B1 B2 cT c w) := by
  set C := ctxOf K (callWord c) w with hC
  have hcw : C.cw = callWord c := rfl
  have hwit : C.wit = w := rfl
  have hwd : C.Wd = wdOf K (callWord c).length := rfl
  obtain ⟨hW, hL, hA, hBig⟩ := widths B1 B2 cT K (callWord c).length hK
  rw [← hwd] at hW hL hA hBig
  rw [← hcw] at hW hL hBig
  have hNB : NB B1 B2 cT K wf.cost (callWord c).length = prefixCost B1 B2 C.cw.length +
      (costA cT C.cw.length C.Wd wf.cost + costB C.cw.length C.Wd) + 2 := by
    rw [hcw, hwd]; rfl
  rw [hNB]
  have hpre := prefix_spec (C := C) B1 B2 c hcw hW hL (by rw [← hcw]; exact hA)
  have hm : Hs C (mainP B1 B2 cT wf) (a0 (V := VV))
      (prefixCost B1 B2 C.cw.length + (costA cT C.cw.length C.Wd wf.cost + costB C.cw.length C.Wd + 1) + 1)
      (fun b => b.out = dispatchWord B1 B2 cT c w) := by
    refine Hs.seq hpre (fun b ⟨h1, h2, h3, h4, h5, h6, h7⟩ => ?_)
    refine Hs.ite (c := .eq vADM v1) (show vADM ≠ v1 by decide) (fun he => ?_) (fun he => ?_)
    · have hAW : c.Admitted B1 B2 ∧ c.W ≠ 0 := by
        have : b.env vADM = 1 := by simpa [Cnd.eval, h6.one] using he
        rw [h2] at this; exact (bnat_eq_one _).1 this
      exact Hs.mono (branchA_spec (C := C) B1 B2 cT wf c w hcw hwit hW hL hBig b h1 h6 h7 h4 h5 hAW.1 hAW.2)
        (Nat.le_add_right _ _) (fun g hg => hg)
    · have hnot : ¬ (c.Admitted B1 B2 ∧ c.W ≠ 0) := by
        intro h'
        have : b.env vADM = 1 := by rw [h2]; exact bnat_one_of h'
        simp [Cnd.eval, h6.one, this] at he
      exact Hs.mono (branchB_spec (C := C) B1 B2 cT c w hcw hW hL b h1 h6 h5 h3 hnot)
        (Nat.le_add_left _ _) (fun g hg => hg)
  exact Hs.mono hm (by omega) (fun g hg => hg)

theorem poly_params (cT : ℕ) : PolyB (fun L => paramsCost (L + cT + 4)) := by
  unfold paramsCost s1Bound s2Cost dmaxCost primeCost liftCost s3Cost primesCost pairCost aCost chainCost bodyCost
  polyb

theorem poly_print (K : ℕ) : PolyB (fun L => printCost L (L + 1) L (wdOf K L)) := by
  unfold printCost prPrintCost chainCost bodyCost pvCost wdOf
  polyb

theorem poly_B (K : ℕ) : PolyB (fun L => costB L (wdOf K L)) := by
  unfold costB oddCostT oddCost wdOf
  polyb

theorem NB_poly (B1 B2 cT K : ℕ) (wc : ℕ → ℕ) (hwc : PolyB wc) : PolyB (NB B1 B2 cT K wc) := by
  have hpre : PolyB (fun L => prefixCost B1 B2 L) := by unfold prefixCost parseCost; polyb
  have hA : PolyB (fun L => costA cT L (wdOf K L) wc) := by
    unfold costA
    exact PolyB.add (PolyB.add (PolyB.add (PolyB.add (PolyB.add (PolyB.add (PolyB.add (poly_params cT) hwc)
      (PolyB.const _)) (by polyb)) (poly_print K)) hwc) (PolyB.const _)) (PolyB.const _)
  unfold NB
  exact PolyB.add (PolyB.add hpre (PolyB.add hA (poly_B K))) (PolyB.const _)

noncomputable def dispatchMachine (B1 B2 cT : ℕ) (wf : WitFrag) : DispatchMachine B1 B2 cT :=
  dispatchMachineOf B1 B2 cT (B1 + B2 + cT + 70) (by omega) (mainP B1 B2 cT wf)
    (NB B1 B2 cT (B1 + B2 + cT + 70) wf.cost)
    (fun c w => by
      obtain ⟨b, n, hx, hn, hb⟩ := mainP_spec B1 B2 cT (B1 + B2 + cT + 70) wf le_rfl c w
      exact ⟨b, n, hx, hb, hn⟩)
    (NB_poly B1 B2 cT _ wf.cost wf.cost_poly)

end NearCubicGates.Close.Dispatch
