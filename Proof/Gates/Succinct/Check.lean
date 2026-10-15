import Proof.Gates.Succinct.PointLoop
import Proof.Gates.WordPrograms.BinW
import Proof.Gates.Outer.Interface

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicGates.Close.Succinct

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.WordPrograms.BinW
open NearCubicWires.WireExponent3_5.UnionMachine.Round (mapS_keepA)

variable {ns nr : ℕ}

/-- **The CHECK program** (paper §11.4, eq:source-check): the table of `d` at the `N` points, compared with `X`;
flag `E .f`, scratch `E .k2`. -/
def checkW (D P VV TT X : Fin (ns + 1)) (E : VReg → Fin nr) : WM ns nr :=
  .seq (pointsW D P VV TT E) (.seq (.inc (E .f)) (mapPass keepA eqN TT X (E .f) (E .k2)))

def checkCost (dl lb lp N : ℕ) : ℕ := (N + 1) * (pointCost dl lb lp N + 10) + 80 * N + 40

/-- **CHECK on any description** (paper §11.4, eq:source-check): the flag is `[ttWord d lb lp N = z]`; the table
stays on `TT`; only `P`, `VV`, `TT` and the flag change. -/
theorem checkW_spec (cap : ℕ) (D P VV TT X : Fin (ns + 1)) (hR : [D, P, VV, TT, X].Nodup) (E : VReg → Fin nr)
    (hE : Function.Injective E) (σ : WState ns nr) (d : List Bool) (lb lp N : ℕ) (z : List Bool)
    (hrd : EvalReady D P VV E d lb lp σ) (hP : σ.st P = []) (hTT : σ.st TT = []) (hTTh : σ.sh TT = 0)
    (hN : σ.val (E .nN) = N) (hz : ∀ r ∈ [VReg.i, .t, .top, .c, .f, .k2], σ.val (E r) = 0)
    (hX : σ.st X = RepairOrdinary.frame z) (hXh : σ.sh X = 0) (hzl : z.length = N)
    (hcap : 10 * d.length + 8 * (lb + lp) + 16 * 2 ^ (lb + lp + 1) + 4 * N + 200 ≤ cap) :
    ∃ τ, WExec cap (checkW D P VV TT X E) σ τ (checkCost d.length lb lp N) ∧
      τ.val (E .f) = (decide (ttWord d lb lp N = z)).toNat ∧
      τ.st TT = RepairOrdinary.frame (ttWord d lb lp N) ∧ τ.sh TT = 0 ∧ SameExcept σ τ [P, VV, TT] [E .f] ∧
      τ.sh P = 0 ∧ τ.sh VV = 0 := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hR
  obtain ⟨⟨hDP, hDV, hDT, hDX⟩, ⟨hPV, hPT, hPX⟩, ⟨hVT, hVX⟩, hTX⟩ := hR
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
  obtain ⟨τ1, e1, h1TT, h1TTh, hse1, h1P, h1V⟩ := pointsW_spec cap D P VV TT
    (by simp [hDP, hDV, hDT, hPV, hPT, hVT]) E hE σ d lb lp N hrd hP hTT hTTh hN
    (fun r hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr; exact hz r (by tauto)) hcap
  have hf1 : τ1.val (E .f) = 0 := by rw [hse1.val (by simp)]; exact hz .f (by simp)
  have hk1 : τ1.val (E .k2) = 0 := by rw [hse1.val (by simp)]; exact hz .k2 (by simp)
  have h1X : τ1.st X = RepairOrdinary.frame z := by rw [hse1.st (by simp [Ne.symm hPX, Ne.symm hVX, Ne.symm hTX])]; exact hX
  have h1Xh : τ1.sh X = 0 := by rw [hse1.sh (by simp [Ne.symm hPX, Ne.symm hVX, Ne.symm hTX])]; exact hXh
  have hpow : 1 ≤ 2 ^ (lb + lp + 1) := Nat.one_le_two_pow
  have e2 := WExec.inc (cap := cap) (E .f) τ1 (by rw [hf1]; omega)
  rw [hf1, Nat.zero_add] at e2
  generalize hτ2 : τ1.setv (E .f) 1 = τ2 at e2
  have hfk : E .f ≠ E .k2 := hE.ne (by decide)
  have hlen : (ttWord d lb lp N).length = z.length := by rw [ttWord_length, hzl]
  have e3 := mapPass_spec cap keepA eqN TT X (E .f) (E .k2) hTX hfk (by omega) (ttWord d lb lp N) z [] [false] true τ2
    hlen (by rw [← hτ2]; simp [h1TT, frame_eq_frameP]) (by rw [← hτ2]; simpa using h1TTh)
    (by rw [← hτ2]; simp [h1X, frame_eq_frameP]) (by rw [← hτ2]; simpa using h1Xh) (by rw [← hτ2]; simp)
    (by rw [← hτ2]; simp [Function.update_apply, Ne.symm hfk, hk1]) (by rw [ttWord_length]; omega)
  rw [mapS_keepA eqN _ _ _ hlen, mapS_eq _ _ _ hlen, Bool.true_and] at e3
  refine ⟨_, WExec.mono (WExec.seq e1 (WExec.seq e2 e3)) ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold checkCost; rw [ttWord_length]; omega
  · simp
  · rw [← hτ2]; simp [frame_eq_frameP]
  · rw [← hτ2]; simpa using h1TTh
  · refine ⟨fun y hy => ⟨?_, ?_⟩, fun r hr => ?_, ?_⟩
    · have hyT : y ≠ TT := by intro h; subst h; simp at hy
      rw [← hτ2]; simp [Function.update_apply, hyT]; exact hse1.st hy
    · rw [← hτ2]; simp; exact hse1.sh hy
    · have hrf : r ≠ E .f := by intro h; subst h; simp at hr
      rw [← hτ2]; simp [Function.update_apply, hrf]; exact hse1.val (by simp)
    · rw [← hτ2]; simp; exact hse1.2.2
  · rw [← hτ2]; simpa using h1P
  · rw [← hτ2]; simpa using h1V

/-- **The table is the source check** (paper §11.4, eq:source-check; F-c5): on `d = descriptor B ++ rest`, with the
evaluator's guards met (`B.nodes + 5 ≤ 2^lb`, `ν < 2^lp`) and `N ≤ 2^ν`, the table at the points `bin(i)`, `i < N`, is
`z` exactly when `B(bin_ν(i)0^{m−ν}) = z_i` for every `i < N`. -/
theorem ttWord_check {m : ℕ} (B : BooleanCircuit m) (rest : List Bool) (ν lb lp : ℕ) {N : ℕ} (z : BitInput N)
    (hNν : N ≤ 2 ^ ν) (hs : B.nodes.length + 5 ≤ 2 ^ lb) (hlp : ν < 2 ^ lp) :
    ttWord (PCPPNative.descriptor B ++ rest) lb lp N = List.ofFn z ↔ Outer.CheckAt ν z B := by
  have key : ∀ i : Fin N, evalModel (PCPPNative.descriptor B ++ rest) lb lp (fun j => (i : ℕ).testBit j) =
      B.eval (Outer.pointOf ν m i.val) := by
    intro i
    have hiν : (i : ℕ) < 2 ^ ν := lt_of_lt_of_le i.isLt hNν
    rw [evalModel_descriptor B rest lb lp _ hs ?_]
    · congr 1
      funext j
      unfold Outer.pointOf
      split_ifs with hj
      · rfl
      · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hiν (Nat.pow_le_pow_right (by norm_num) (by omega)))
    · intro j hj
      apply Nat.testBit_eq_false_of_lt
      unfold natBitLength at hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · rw [Nat.log_zero_right] at hj
        have hlp0 : lp = 0 := by omega
        rw [hlp0] at hlp
        have hν0 : ν = 0 := by simpa using hlp
        rw [hν0] at hiν
        simpa using hiν
      · have h2 : 2 ^ lp ≤ 2 ^ Nat.log 2 j := Nat.pow_le_pow_right (by norm_num) (by omega)
        have h3 := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp hj0)
        exact lt_of_lt_of_le hiν (Nat.pow_le_pow_right (by norm_num) (by omega))
  unfold ttWord Outer.CheckAt
  rw [List.ofFn_inj]
  constructor
  · intro h i; rw [← key]; exact congrFun h i
  · intro h; funext i; rw [key]; exact h i

theorem checkW_check (cap : ℕ) (D P VV TT X : Fin (ns + 1)) (hR : [D, P, VV, TT, X].Nodup) (E : VReg → Fin nr)
    (hE : Function.Injective E) (σ : WState ns nr) {m : ℕ} (B : BooleanCircuit m) (rest : List Bool)
    (ν lb lp : ℕ) {N : ℕ} (z : BitInput N)
    (hrd : EvalReady D P VV E (PCPPNative.descriptor B ++ rest) lb lp σ) (hP : σ.st P = []) (hTT : σ.st TT = [])
    (hTTh : σ.sh TT = 0) (hN : σ.val (E .nN) = N) (hz : ∀ r ∈ [VReg.i, .t, .top, .c, .f, .k2], σ.val (E r) = 0)
    (hX : σ.st X = RepairOrdinary.frame (List.ofFn z)) (hXh : σ.sh X = 0)
    (hNν : N ≤ 2 ^ ν) (hs : B.nodes.length + 5 ≤ 2 ^ lb) (hlp : ν < 2 ^ lp)
    (hcap : 10 * (PCPPNative.descriptor B ++ rest).length + 8 * (lb + lp) + 16 * 2 ^ (lb + lp + 1) + 4 * N + 200 ≤
      cap) :
    ∃ τ, WExec cap (checkW D P VV TT X E) σ τ (checkCost (PCPPNative.descriptor B ++ rest).length lb lp N) ∧
      τ.val (E .f) ≤ 1 ∧ (τ.val (E .f) = 1 ↔ Outer.CheckAt ν z B) ∧ τ.sh TT = 0 ∧
      SameExcept σ τ [P, VV, TT] [E .f] ∧ τ.sh P = 0 ∧ τ.sh VV = 0 := by
  obtain ⟨τ, e, hf, _, hTTh', hse, hPh', hVh'⟩ := checkW_spec cap D P VV TT X hR E hE σ _ lb lp N (List.ofFn z) hrd hP hTT hTTh hN
    hz hX hXh (by simp) hcap
  refine ⟨τ, e, ?_, ?_, hTTh', hse, hPh', hVh'⟩
  · rw [hf]; cases decide (ttWord (PCPPNative.descriptor B ++ rest) lb lp N = List.ofFn z) <;> simp
  · rw [hf, ← ttWord_check B rest ν lb lp z hNν hs hlp]
    by_cases h : ttWord (PCPPNative.descriptor B ++ rest) lb lp N = List.ofFn z <;> simp [h]

end NearCubicGates.Close.Succinct
