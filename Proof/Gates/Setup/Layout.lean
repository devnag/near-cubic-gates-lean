import Proof.Gates.Setup.PhaseA
import Proof.Gates.Worker.Oracle

set_option autoImplicit false

namespace NearCubicGates.Close.Setup

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SourceInterfaces NearCubicWires.RepairSource NearCubicWires.RepairSource.CloseoutLanguage
open NearCubicWires.Bindings.CLW20Lemma311
open NearCubicGates.PublishedSources.PCPP NearCubicGates.Close.Gadget NearCubicGates.Close.Transfer
open NearCubicGates.Close NearCubicGates.Close.WordPrograms NearCubicGates.Close.CheckedPCPP NearCubicGates.Close.Interfaces

/-! ## Registers of the guard phases (`110 … 127`; the term loop's, phase A's and phase D's are below `110`) -/

abbrev rNu : Fin nrW := 110
abbrev rBs : Fin nrW := 111
abbrev pT1 : Fin nrW := 112
abbrev pT2 : Fin nrW := 113
abbrev pT3 : Fin nrW := 114
abbrev pH : Fin nrW := 115
abbrev pB : Fin nrW := 116
abbrev pF : Fin nrW := 117
abbrev pU : Fin nrW := 118
abbrev pK : Fin nrW := 119
abbrev pT : Fin nrW := 120
abbrev pX1 : Fin nrW := 121
abbrev pX2 : Fin nrW := 122
abbrev pX3 : Fin nrW := 123

/-- Register-file case analysis (`split_ifs` on `Function.update_apply`): substitute the register variable, unfold the
named registers to literals (so clashes of distinct registers simplify to `False`), close by `rfl`/`omega`/`simp_all`. -/
macro "wregs" : tactic => `(tactic| (split_ifs <;> (try subst_vars) <;>
  (try simp only [rN, rM, rRB, rCL, rSC, rA, rLC, rPB, gN0, gU, gK, gT, gF, kQ, dS, hH, hBr, oW, bR, tW, rNu, rBs, pT1,
    pT2, pT3, pH, pB, pF, pU, pK, pT, pX1, pX2, pX3] at *) <;> (first
  | rfl
  | omega
  | (simp_all; done))))

noncomputable section

variable {s : GateSources} {P : ThreeQueryPCPP} {g : GateParams}

/-- The cold decoder's tape count. -/
abbrev tO : ℕ := RepairOrdinary.CloseoutWitness.Oracle.tapes + 1

theorem tO_eq : tO = 1381 := rfl

section Sizes
variable (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s))

abbrev tWB : ℕ := (Worker.wdB W).tapeCount

abbrev tWU : ℕ := (Worker.wdU W).tapeCount

def oW1 : ℕ := 5
def oU1 : ℕ := 5 + tWB W
def oW2 : ℕ := 5 + tWB W + tWU W
def oU2 : ℕ := 5 + 2 * tWB W + tWU W
def oO1 : ℕ := 5 + 2 * tWB W + 2 * tWU W
def oO2 : ℕ := 5 + 2 * tWB W + 2 * tWU W + tO
def oR : ℕ := 5 + 2 * tWB W + 2 * tWU W + 2 * tO

def tAOf : ℕ := oR W + R.t

end Sizes

structure Lay (D : SetupData s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s)) :
    Prop where
  tA : D.tA = tAOf W R
  flag : D.flag.val = 0

section Streams
variable (D : SetupData s P g)

@[simp] theorem sX_val : (sX D).val = 0 := rfl
@[simp] theorem sBW_val : (sBW D).val = 1 := rfl
@[simp] theorem sWT_val : (sWT D).val = 2 := rfl
@[simp] theorem sCW_val : (sCW D).val = 3 := rfl
@[simp] theorem sVI_val : (sVI D).val = 4 := rfl
@[simp] theorem sS1_val : (sS1 D).val = 5 := rfl
@[simp] theorem sS2_val : (sS2 D).val = 6 := rfl
@[simp] theorem sTL_val : (sTL D).val = 7 := rfl
@[simp] theorem sG_val : (sG D).val = 8 := rfl
@[simp] theorem sL_val : (sL D).val = 9 := rfl
@[simp] theorem kB_val (j : Fin D.cf.t) : (kB D j).val = 16 + D.tA + j.val := rfl
@[simp] theorem cB_val (j : Fin D.tc) : (cB D j).val = 16 + D.tA + D.cf.t + j.val := rfl

def bS (j : ℕ) : Fin (nsW D + 1) := ⟨(16 + j) % (nsW D + 1), Nat.mod_lt _ (by omega)⟩

theorem bS_val {j : ℕ} (hj : j < D.tA) : (bS D j).val = 16 + j := by
  unfold bS; simp only
  apply Nat.mod_eq_of_lt
  unfold nsW; omega

/-- The stream `1^ν`. -/
def sNU : Fin (nsW D + 1) := bS D 1
/-- CHECK's point stream. -/
def sPT : Fin (nsW D + 1) := bS D 2
/-- CHECK's value stream. -/
def sVV : Fin (nsW D + 1) := bS D 3
/-- CHECK's table stream. -/
def sTT : Fin (nsW D + 1) := bS D 4

end Streams

section Maps
variable (D : SetupData s P g) (W : OuterM.WidthDonor s.mw (g.sv s)) (R : OuterM.ARun s.mw (g.sv s))

def mW1 (j : Fin (tWB W)) : Fin (nsW D + 1) := bS D (oW1 + j.val)

def mU1 (j : Fin (tWU W)) : Fin (nsW D + 1) := bS D (oU1 W + j.val)

def mW2 (j : Fin (tWB W)) : Fin (nsW D + 1) := bS D (oW2 W + j.val)

def mU2 (j : Fin (tWU W)) : Fin (nsW D + 1) := bS D (oU2 W + j.val)

def mO1 (j : Fin tO) : Fin (nsW D + 1) :=
  if j.val = 2 then mW1 D W (Worker.wdB W).outputTape
  else if j.val = 3 then mU1 D W (Worker.wdU W).outputTape
  else bS D (oO1 W + j.val)

def mO2 (j : Fin tO) : Fin (nsW D + 1) :=
  if j.val = 2 then mW2 D W (Worker.wdB W).outputTape
  else if j.val = 3 then mU2 D W (Worker.wdU W).outputTape
  else bS D (oO2 W + j.val)

def sD1 : Fin (nsW D + 1) := bS D (oO1 W + 1299)

def sD2 : Fin (nsW D + 1) := bS D (oO2 W + 1299)

def sF1 : Fin (nsW D + 1) := bS D (oO1 W + 1379)

def sF2 : Fin (nsW D + 1) := bS D (oO2 W + 1379)

/-- The A-run: `dIn` on `B_src`'s descriptor slot, `nIn` on `NU`, the others its own block. -/
def mR (j : Fin R.t) : Fin (nsW D + 1) :=
  if j = R.dIn then sD1 D W else if j = R.nIn then sNU D else bS D (oR W + j.val)

/-- The A-run's word port `wOut` (the word of `C^O_{⟨B_src⟩_ν}`). -/
def sMW : Fin (nsW D + 1) := bS D (oR W + R.wOut.val)
/-- The A-run's flag port `fOut` (`SrcFits`). -/
def sRF : Fin (nsW D + 1) := bS D (oR W + R.fOut.val)

/-- The composite: `cIn` on the A-run's `wOut`, `dIn` on `B_pf`'s descriptor slot, the others its block `kB`. -/
def mK (j : Fin D.cf.t) : Fin (nsW D + 1) :=
  if j = D.cf.cIn then sMW D W R else if j = D.cf.dIn then sD2 D W else kB D j

end Maps

theorem fin_ne_of_val {n : ℕ} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

/-- A register write elsewhere does not change a register. -/
theorem upd_ne {ns nr : ℕ} (σ : WireExponent3_5.FinalPass.Tm.WState ns nr) {a r : Fin nr} (x : ℕ) (h : r ≠ a) : (σ.setv a x).val r = σ.val r := by
  simp [Function.update_of_ne h]

/-! ## Values of the stream indices under the layout -/

section Vals
variable {D : SetupData s P g} {W : OuterM.WidthDonor s.mw (g.sv s)} {R : OuterM.ARun s.mw (g.sv s)}
  (hL : Lay D W R)
include hL

theorem tA_eq : D.tA = 5 + 2 * tWB W + 2 * tWU W + 2 * tO + R.t := by rw [hL.tA]; rfl

theorem sFL_val : (sFL D).val = 16 := by unfold sFL aB; simp [hL.flag]
theorem sNU_val : (sNU D).val = 17 := by unfold sNU; rw [bS_val D (by rw [tA_eq hL]; omega)]
theorem sPT_val : (sPT D).val = 18 := by unfold sPT; rw [bS_val D (by rw [tA_eq hL]; omega)]
theorem sVV_val : (sVV D).val = 19 := by unfold sVV; rw [bS_val D (by rw [tA_eq hL]; omega)]
theorem sTT_val : (sTT D).val = 20 := by unfold sTT; rw [bS_val D (by rw [tA_eq hL]; omega)]

theorem sFL_eq : sFL D = bS D 0 := Fin.ext (by rw [sFL_val hL, bS_val D (by rw [tA_eq hL]; omega)])

theorem mW1_val (j : Fin (tWB W)) : (mW1 D W j).val = 21 + j.val := by
  have := j.isLt; unfold mW1 oW1; rw [bS_val D (by rw [tA_eq hL]; omega)]; omega
theorem mU1_val (j : Fin (tWU W)) : (mU1 D W j).val = 21 + tWB W + j.val := by
  have := j.isLt; unfold mU1 oU1; rw [bS_val D (by rw [tA_eq hL]; omega)]; omega
theorem mW2_val (j : Fin (tWB W)) : (mW2 D W j).val = 21 + tWB W + tWU W + j.val := by
  have := j.isLt; unfold mW2 oW2; rw [bS_val D (by rw [tA_eq hL]; omega)]; omega
theorem mU2_val (j : Fin (tWU W)) : (mU2 D W j).val = 21 + 2 * tWB W + tWU W + j.val := by
  have := j.isLt; unfold mU2 oU2; rw [bS_val D (by rw [tA_eq hL]; omega)]; omega

theorem own1_val (j : ℕ) (hj : j < tO) : (bS D (oO1 W + j)).val = 21 + 2 * tWB W + 2 * tWU W + j := by
  unfold oO1; rw [bS_val D (by rw [tA_eq hL]; omega)]; omega
theorem own2_val (j : ℕ) (hj : j < tO) : (bS D (oO2 W + j)).val = 21 + 2 * tWB W + 2 * tWU W + tO + j := by
  unfold oO2; rw [bS_val D (by rw [tA_eq hL]; omega)]; omega
theorem ownR_val (j : ℕ) (hj : j < R.t) : (bS D (oR W + j)).val = 21 + 2 * tWB W + 2 * tWU W + 2 * tO + j := by
  unfold oR; rw [bS_val D (by rw [tA_eq hL]; omega)]; omega

theorem sD1_val : (sD1 D W).val = 21 + 2 * tWB W + 2 * tWU W + 1299 := own1_val hL 1299 (by decide)
theorem sD2_val : (sD2 D W).val = 21 + 2 * tWB W + 2 * tWU W + tO + 1299 := own2_val hL 1299 (by decide)
theorem sF1_val : (sF1 D W).val = 21 + 2 * tWB W + 2 * tWU W + 1379 := own1_val hL 1379 (by decide)
theorem sF2_val : (sF2 D W).val = 21 + 2 * tWB W + 2 * tWU W + tO + 1379 := own2_val hL 1379 (by decide)
theorem sMW_val : (sMW D W R).val = 21 + 2 * tWB W + 2 * tWU W + 2 * tO + R.wOut.val :=
  ownR_val hL _ R.wOut.isLt
theorem sRF_val : (sRF D W R).val = 21 + 2 * tWB W + 2 * tWU W + 2 * tO + R.fOut.val :=
  ownR_val hL _ R.fOut.isLt

theorem kB_val' (j : Fin D.cf.t) : (kB D j).val = 21 + 2 * tWB W + 2 * tWU W + 2 * tO + R.t + j.val := by
  unfold kB; simp only; rw [tA_eq hL]; omega

abbrev oB (W : OuterM.WidthDonor s.mw (g.sv s)) : Fin (tWB W) := (Worker.wdB W).outputTape

abbrev oU (W : OuterM.WidthDonor s.mw (g.sv s)) : Fin (tWU W) := (Worker.wdU W).outputTape

theorem mO1_val (j : Fin tO) : (mO1 D W j).val =
    if j.val = 2 then 21 + (oB W).val else if j.val = 3 then 21 + tWB W + (oU W).val
    else 21 + 2 * tWB W + 2 * tWU W + j.val := by
  unfold mO1
  split_ifs
  · exact mW1_val hL _
  · exact mU1_val hL _
  · exact own1_val hL _ j.isLt

theorem mO2_val (j : Fin tO) : (mO2 D W j).val =
    if j.val = 2 then 21 + tWB W + tWU W + (oB W).val else if j.val = 3 then 21 + 2 * tWB W + tWU W + (oU W).val
    else 21 + 2 * tWB W + 2 * tWU W + tO + j.val := by
  unfold mO2
  split_ifs
  · exact mW2_val hL _
  · exact mU2_val hL _
  · exact own2_val hL _ j.isLt

theorem mR_val (j : Fin R.t) : (mR D W R j).val =
    if j = R.dIn then 21 + 2 * tWB W + 2 * tWU W + 1299 else if j = R.nIn then 17
    else 21 + 2 * tWB W + 2 * tWU W + 2 * tO + j.val := by
  unfold mR
  split_ifs
  · exact sD1_val hL
  · exact sNU_val hL
  · exact ownR_val hL _ j.isLt

theorem mK_val (j : Fin D.cf.t) : (mK D W R j).val =
    if j = D.cf.cIn then 21 + 2 * tWB W + 2 * tWU W + 2 * tO + R.wOut.val
    else if j = D.cf.dIn then 21 + 2 * tWB W + 2 * tWU W + tO + 1299
    else 21 + 2 * tWB W + 2 * tWU W + 2 * tO + R.t + j.val := by
  unfold mK
  split_ifs
  · exact sMW_val hL
  · exact sD2_val hL
  · exact kB_val' hL j

theorem mW1_inj : Function.Injective (mW1 D W) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; rw [mW1_val hL, mW1_val hL] at this; omega)
theorem mU1_inj : Function.Injective (mU1 D W) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; rw [mU1_val hL, mU1_val hL] at this; omega)
theorem mW2_inj : Function.Injective (mW2 D W) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; rw [mW2_val hL, mW2_val hL] at this; omega)
theorem mU2_inj : Function.Injective (mU2 D W) := fun a b h => Fin.ext (by
  have := congrArg Fin.val h; rw [mU2_val hL, mU2_val hL] at this; omega)

theorem mO1_inj : Function.Injective (mO1 D W) := fun a b h => Fin.ext (by
  have e := congrArg Fin.val h
  rw [mO1_val hL, mO1_val hL] at e
  have h1 := (oB W).isLt; have h2 := (oU W).isLt; have htO := tO_eq; have ha := a.isLt; have hb := b.isLt
  split_ifs at e <;> omega)
theorem mO2_inj : Function.Injective (mO2 D W) := fun a b h => Fin.ext (by
  have e := congrArg Fin.val h
  rw [mO2_val hL, mO2_val hL] at e
  have h1 := (oB W).isLt; have h2 := (oU W).isLt; have htO := tO_eq; have ha := a.isLt; have hb := b.isLt
  split_ifs at e <;> omega)

theorem mR_inj : Function.Injective (mR D W R) := by
  intro a b h
  have e := congrArg Fin.val h
  have ea := mR_val hL a
  have eb := mR_val hL b
  have ha := a.isLt; have hb := b.isLt; have htO := tO_eq
  apply Fin.ext
  split_ifs at ea eb <;> (try subst_vars) <;> omega

theorem mK_inj : Function.Injective (mK D W R) := by
  intro a b h
  have e := congrArg Fin.val h
  have ea := mK_val hL a
  have eb := mK_val hL b
  have ha := a.isLt; have hb := b.isLt; have hw := R.wOut.isLt; have htO := tO_eq
  apply Fin.ext
  split_ifs at ea eb <;> (try subst_vars) <;> omega

end Vals

end

end NearCubicGates.Close.Setup
