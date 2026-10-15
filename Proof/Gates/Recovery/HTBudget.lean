import Proof.Gates.Recovery.HTRun
import Proof.Gates.Recovery.HTWord
import Proof.Gates.CheckedPCPP.PolyClass
import Proof.CaseAnalysis.CaseTwoBudget

set_option autoImplicit false

namespace NearCubicGates.Close.Recovery.HT

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicGates.Close NearCubicGates.Close.Gadget
open NearCubicGates.PublishedSources.PCPP NearCubicWires.Bindings.CLW20Lemma311
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound oracleDepth)

/-- One Case 2 source input `z` at source length `2^ν ≥ 2` past the onset of `𝒱_G`, at a final length `n ≥ ν`. -/
structure Inst (s : GateSources) (g : Transfer.GateParams) where
  n : ℕ
  ν : ℕ
  z : BitInput (2 ^ ν)
  hν : ν ≤ n
  hcut : 2 ≤ 2 ^ ν
  hon : (g.sv s).onset ≤ ν
  h : g.IsCaseTwo s ν z

section Budget

variable {s : GateSources} {P : ThreeQueryPCPP} {g : Transfer.GateParams}

/-- The native width `q` of an instance. -/
noncomputable def Inst.R (i : Inst s g) : ℕ := Outer.width s.mw (g.sv s) (2 ^ i.ν)

/-- The oracle size bound `B` of an instance. -/
noncomputable def Inst.B (i : Inst s g) : ℕ := g.bound s i.ν

/-- `B*_src` of an instance. -/
noncomputable def Inst.Bs (i : Inst s g) : BooleanCircuit (Outer.width s.mw (g.sv s) (2 ^ i.ν)) :=
  (g.selectedPair s i.ν i.z i.h).src

/-- `B*_pf` of an instance. -/
noncomputable def Inst.c (i : Inst s g) : BooleanCircuit (Outer.width s.mw (g.sv s) (2 ^ i.ν)) :=
  (g.selectedPair s i.ν i.z i.h).pf

/-- The checked circuit of an instance. -/
noncomputable def Inst.C (P : ThreeQueryPCPP) (i : Inst s g) : Circuit :=
  checkedCircuit P.code (substitutedAt s g i.z ⟨i.Bs, i.c⟩)

theorem Inst.one_le (i : Inst s g) : 1 ≤ i.ν := by
  rcases Nat.eq_zero_or_pos i.ν with h0 | h0
  · have := i.hcut; rw [h0] at this; norm_num at this
  · exact h0

theorem Inst.two_le (i : Inst s g) : 2 ≤ Outer.width s.mw (g.sv s) (2 ^ i.ν) := by
  have := g.nu_lt_width s i.ν
  have := i.one_le
  unfold Transfer.GateParams.width at *
  omega

theorem Inst.c_size (i : Inst s g) : i.c.size ≤ i.B :=
  (RecoveryChoice.oracleSelector _ g.degree i.z i.h.2.2.2).sizeBounded

/-- The size `2^n`. -/
def Inst.S (i : Inst s g) : ℕ := 2 ^ i.n

theorem bits_len_le_self (v : ℕ) : v.bits.length ≤ v := by
  have e := Nat.size_eq_bits_len v
  have := Nat.size_le.mpr (Nat.lt_two_pow_self (n := v))
  omega

theorem two_pow_size_le (v : ℕ) : 2 ^ v.size ≤ 2 * v + 1 := by
  rcases Nat.eq_zero_or_pos v with h | h
  · subst h; simp
  · obtain ⟨t, ht⟩ : ∃ t, v.size = t + 1 := ⟨v.size - 1, by have := Nat.size_pos.mpr h; omega⟩
    have h2 : 2 ^ t ≤ v := Nat.lt_size.mp (by omega)
    rw [ht, pow_succ]; omega

theorem poly_nu : PolyB (Inst.S (s := s) (g := g)) (fun i => 2 ^ i.ν) :=
  PolyB.size.mono fun i => Nat.pow_le_pow_right (by norm_num) i.hν

theorem poly_n : PolyB (Inst.S (s := s) (g := g)) (fun i => i.n) :=
  PolyB.size.mono fun _ => Nat.lt_two_pow_self.le

theorem poly_R : PolyB (Inst.S (s := s) (g := g)) (fun i => i.R) := by
  obtain ⟨Cw, m, hW⟩ := Outer.widthOf_pow g.k (Outer.apad s.mw (g.sv s))
  refine (PolyB.mul (PolyB.const Cw) (PolyB.pow (PolyB.add poly_nu (PolyB.const 1)) m)).mono fun i => ?_
  exact Nat.lt_two_pow_self.le.trans (hW (2 ^ i.ν))

theorem poly_B : PolyB (Inst.S (s := s) (g := g)) (fun i => i.B) := by
  refine (PolyB.pow (PolyB.add poly_R (PolyB.const 1)) (2 ^ oracleDepth g.degree)).mono fun i => ?_
  have h := NearCubicWires.PolynomialClock.pairIter_add_one_le_pow (oracleDepth g.degree) i.R
  unfold Inst.B Transfer.GateParams.bound
  change NearCubicWires.PolynomialClock.pairIter (oracleDepth g.degree) i.R ≤ _
  omega

theorem poly_mw : PolyB (Inst.S (s := s) (g := g)) (fun i => (mwWord s g (2 ^ i.ν) i.Bs).length) := by
  obtain ⟨C, e, hCe⟩ := mwWord_poly s g
  refine (PolyB.mul (PolyB.const C) (PolyB.pow (PolyB.add poly_nu (PolyB.const 1)) e)).mono fun i => ?_
  exact hCe i.ν i.Bs i.one_le i.hon

theorem poly_desc : PolyB (Inst.S (s := s) (g := g)) (fun i => (PCPPNative.descriptor i.c).length) := by
  refine (PolyB.add (PolyB.mul (PolyB.add poly_B (PolyB.const 1))
    (PolyB.add (PolyB.mul (PolyB.const 6) (PolyB.add (PolyB.add poly_B poly_R) (PolyB.const 4))) (PolyB.const 9)))
    (PolyB.add (PolyB.mul (PolyB.const 2) poly_R) (PolyB.add (PolyB.mul (PolyB.const 4) poly_B)
      (PolyB.const 9)))).mono fun i => ?_
  have h := desc_len_le' i.c
  have hc := i.c_size
  have h1 : (i.c.size + 1) * (6 * (i.c.size + Outer.width s.mw (g.sv s) (2 ^ i.ν) + 4) + 9) ≤
      (i.B + 1) * (6 * (i.B + i.R + 4) + 9) :=
    Nat.mul_le_mul (by omega) (by unfold Inst.R; omega)
  unfold Inst.R at h1 ⊢
  omega

theorem poly_cold : PolyB (Inst.S (s := s) (g := g)) (fun i => CloseoutCaseTwo.Cold.budget i.B i.c) := by
  obtain ⟨Cc, Ec, -, hcold⟩ := CloseoutCaseTwo.ColdBudget.polynomial
  refine (PolyB.mul (PolyB.const Cc) (PolyB.pow (PolyB.add (PolyB.add poly_R poly_B) (PolyB.const 1)) Ec)).mono
    fun i => ?_
  exact hcold _ i.B i.c i.c_size

/-- The composite's fuel at an instance. -/
noncomputable def cxFuel (cx : Setup.CompFull s P g) (i : Inst s g) : ℕ :=
  cx.C * ((mwWord s g (2 ^ i.ν) i.Bs).length + (PCPPNative.descriptor i.c).length + i.R + 1) ^ cx.e

theorem poly_cxFuel (cx : Setup.CompFull s P g) : PolyB (Inst.S (s := s) (g := g)) (cxFuel cx) :=
  PolyB.mul (PolyB.const cx.C) (PolyB.pow (PolyB.add (PolyB.add (PolyB.add poly_mw poly_desc) poly_R)
    (PolyB.const 1)) cx.e)

/-- The composite's outputs are at most its input plus its fuel. -/
theorem cx_out_le (cx : Setup.CompFull s P g) (i : Inst s g) :
    (i.C P).word.length + (P.output (i.C P)).word.length ≤
      2 * ((mwWord s g (2 ^ i.ν) i.Bs).length + (PCPPNative.descriptor i.c).length + cxFuel cx i) := by
  obtain ⟨out, hrun, h1, h2, -, -, -⟩ := cx.run i.z ⟨i.Bs, i.c⟩ i.two_le
  have hl := Dock.ready_len hrun ((mwWord s g (2 ^ i.ν) i.Bs).length + (PCPPNative.descriptor i.c).length)
    (fun j => by unfold portBank; split_ifs <;> simp)
  have l1 := hl cx.cOut
  have l2 := hl cx.wOut
  rw [h1, frame_length] at l1
  rw [h2] at l2
  dsimp only at l1 l2
  unfold cxFuel Inst.C Inst.R at *
  omega

theorem poly_Cw (cx : Setup.CompFull s P g) : PolyB (Inst.S (s := s) (g := g))
    (fun i => (i.C P).word.length + (P.output (i.C P)).word.length) :=
  (PolyB.mul (PolyB.const 2) (PolyB.add (PolyB.add poly_mw poly_desc) (poly_cxFuel cx))).mono fun i => cx_out_le cx i

theorem code_len_le (pe : Program) (Ke ee : ℕ)
    (hpe : ∀ m : MessageRequest, ∃ out, ClockJoin.ReadyRun pe.machine (Ke * ((messageWord m).length + 1) ^ ee)
      (pe.inputTapes (messageWord m)) out ∧ out pe.outputTape = FramedSim.pairs (List.ofFn (P.code.enc m.1 m.2.val)))
    (q : ℕ) (hq : 2 ≤ q) : P.code.length q ≤ 4 * q + 3 + Ke * (4 * q + 3) ^ ee := by
  obtain ⟨out, hrun, hout⟩ := hpe ⟨q, ⟨fun _ => false, hq⟩⟩
  have hm := messageWord_len q (fun _ => false) hq
  have hl := Dock.ready_len hrun (2 * (messageWord ⟨q, ⟨fun _ => false, hq⟩⟩).length + 1)
    (fun j => by unfold Program.inputTapes; split_ifs <;> simp [frame_length])
  have l1 := hl pe.outputTape
  rw [hout, FramedSim.pairs_length, List.length_ofFn] at l1
  change 2 * P.code.length q ≤ _ at l1
  have hb := bits_len_le_self q
  have hp : ((messageWord ⟨q, ⟨fun _ => false, hq⟩⟩).length + 1) ^ ee ≤ (4 * q + 3) ^ ee :=
    Nat.pow_le_pow_left (by omega) _
  have := Nat.mul_le_mul_left Ke hp
  omega

theorem poly_L (pe : Program) (Ke ee : ℕ)
    (hpe : ∀ m : MessageRequest, ∃ out, ClockJoin.ReadyRun pe.machine (Ke * ((messageWord m).length + 1) ^ ee)
      (pe.inputTapes (messageWord m)) out ∧ out pe.outputTape = FramedSim.pairs (List.ofFn (P.code.enc m.1 m.2.val))) :
    PolyB (Inst.S (s := s) (g := g)) (fun i => P.code.length i.R) :=
  (PolyB.add (PolyB.add (PolyB.mul (PolyB.const 4) poly_R) (PolyB.const 3))
    (PolyB.mul (PolyB.const Ke) (PolyB.pow (PolyB.add (PolyB.mul (PolyB.const 4) poly_R) (PolyB.const 3)) ee))).mono
    fun i => code_len_le pe Ke ee hpe i.R i.two_le

theorem C_n (i : Inst s g) : (i.C P).n = i.R + P.code.length i.R := rfl

theorem proofBits_le (ph : Program) (Kh eh : ℕ)
    (hph : ∀ a : AcceptedCircuitInput, ∃ out, ClockJoin.ReadyRun ph.machine
      (Kh * ((acceptedCircuitInputWord a).length + 1) ^ eh) (ph.inputTapes (acceptedCircuitInputWord a)) out ∧
      out ph.outputTape = FramedSim.pairs (List.ofFn (P.honest a)))
    (i : Inst s g) :
    (P.output (i.C P)).proofBits ≤ 2 * ((i.C P).word.length + (i.C P).n) + 1 +
      Kh * ((i.C P).word.length + (i.C P).n + 1) ^ eh := by
  have hacc : (substitutedAt s g i.z ⟨i.Bs, i.c⟩).D.eval (fun _ => false) = true :=
    eval_subst (substitutedAt_pow s g i.ν i.z (g.selectedPair s i.ν i.z i.h)) _ _ HEq.rfl
      (g.selected_taut s i.ν i.z i.h (fun _ => false))
  obtain ⟨out, hrun, hout⟩ := hph (acceptedInput P.code (substitutedAt s g i.z ⟨i.Bs, i.c⟩) (fun _ => false) hacc)
  have hw := acceptedWord_len P.code (substitutedAt s g i.z ⟨i.Bs, i.c⟩) (fun _ => false) hacc
  have hl := Dock.ready_len hrun (2 * (acceptedCircuitInputWord
      (acceptedInput P.code (substitutedAt s g i.z ⟨i.Bs, i.c⟩) (fun _ => false) hacc)).length + 1)
    (fun j => by unfold Program.inputTapes; split_ifs <;> simp [frame_length])
  have l1 := hl ph.outputTape
  rw [hout, FramedSim.pairs_length, List.length_ofFn, hw] at l1
  unfold Inst.C
  change (P.output (checkedCircuit P.code (substitutedAt s g i.z ⟨i.Bs, i.c⟩))).proofBits ≤ _
  change 2 * (P.output (checkedCircuit P.code (substitutedAt s g i.z ⟨i.Bs, i.c⟩))).proofBits ≤ _ at l1
  omega

end Budget

end NearCubicGates.Close.Recovery.HT
