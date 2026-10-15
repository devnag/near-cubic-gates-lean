import Proof.Gates.Succinct.SubstitutionPos
import Proof.Gates.Succinct.IntegerRootW
import Proof.Gates.Succinct.SubstitutionModel
import Proof.Gates.CheckedPCPP.NodeEmit
import Proof.Gates.WordPrograms.RegArith

set_option autoImplicit false

namespace NearCubicGates.Close.Succinct.SubstMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicGates.Close.WordPrograms NearCubicGates.Close.Succinct

inductive HReg where
  | f (r : FReg)
  | cdW | cdB | cdL | cdA
  | w (i : Fin 8) | wt
  | pk | pt | z | jk
  | q | nC | nB | oB | oC | L | k | nB1 | sz | M | pd | cur
  | tag | tagB | f1 | f2 | p1 | p2 | g | lt | bq
  | iC | tC | sk | x | t | h | sc | sb | ga | gb | gz
  deriving DecidableEq, Fintype

def nrH : ℕ := Fintype.card HReg
noncomputable def regH : HReg → Fin nrH := Fintype.equivFin HReg
theorem regH_inj : Function.Injective regH := (Fintype.equivFin HReg).injective
@[simp] theorem regH_eq_iff (u₁ u₂ : HReg) : regH u₁ = regH u₂ ↔ u₁ = u₂ := regH_inj.eq_iff

/-- A field-reader family with its own position counter. -/
noncomputable def fam (cd : HReg) : FReg → Fin nrH := fun k => if k = .cd then regH cd else regH (.f k)

theorem fam_inj (cd : HReg) (hcd : ∀ r, cd ≠ .f r) : Function.Injective (fam cd) := by
  intro u₁ u₂ e
  unfold fam at e
  by_cases h1 : u₁ = .cd <;> by_cases h2 : u₂ = .cd <;> simp [h1, h2] at e
  · rw [h1, h2]
  · exact absurd e.symm (fun h => hcd u₂ h.symm)
  · exact absurd e (fun h => hcd u₁ h.symm)
  · exact e

@[simp] theorem fam_cd (cd : HReg) : fam cd .cd = regH cd := by simp [fam]
@[simp] theorem fam_ne (cd : HReg) (k : FReg) (hk : k ≠ .cd) : fam cd k = regH (.f k) := by simp [fam, hk]

/-- The node writer's registers. -/
noncomputable def WR : Fin 8 ↪ Fin nrH := ⟨fun i => regH (.w i), fun a b e => by simpa using e⟩

/-- Streams. -/
def sW : Fin (4 + 1) := ⟨0, by omega⟩
def sD : Fin (4 + 1) := ⟨1, by omega⟩
def sO : Fin (4 + 1) := ⟨2, by omega⟩
def sF : Fin (4 + 1) := ⟨3, by omega⟩
def sL : Fin (4 + 1) := ⟨4, by omega⟩

@[simp] theorem sW_ne_sD : sW ≠ sD := by decide
@[simp] theorem sW_ne_sO : sW ≠ sO := by decide
@[simp] theorem sW_ne_sF : sW ≠ sF := by decide
@[simp] theorem sW_ne_sL : sW ≠ sL := by decide
@[simp] theorem sD_ne_sO : sD ≠ sO := by decide
@[simp] theorem sD_ne_sF : sD ≠ sF := by decide
@[simp] theorem sD_ne_sL : sD ≠ sL := by decide
@[simp] theorem sO_ne_sF : sO ≠ sF := by decide
@[simp] theorem sO_ne_sL : sO ≠ sL := by decide
@[simp] theorem sF_ne_sL : sF ≠ sL := by decide
@[simp] theorem sD_ne_sW : sD ≠ sW := by decide
@[simp] theorem sO_ne_sW : sO ≠ sW := by decide
@[simp] theorem sF_ne_sW : sF ≠ sW := by decide
@[simp] theorem sL_ne_sW : sL ≠ sW := by decide
@[simp] theorem sO_ne_sD : sO ≠ sD := by decide
@[simp] theorem sF_ne_sD : sF ≠ sD := by decide
@[simp] theorem sL_ne_sD : sL ≠ sD := by decide
@[simp] theorem sF_ne_sO : sF ≠ sO := by decide
@[simp] theorem sL_ne_sO : sL ≠ sO := by decide
@[simp] theorem sL_ne_sF : sL ≠ sF := by decide

/-- Short names. -/
noncomputable abbrev rr (u : HReg) : Fin nrH := regH u
noncomputable abbrev RW : FReg → Fin nrH := fam .cdW
noncomputable abbrev RB : FReg → Fin nrH := fam .cdB
noncomputable abbrev RL : FReg → Fin nrH := fam .cdL
noncomputable abbrev RA : FReg → Fin nrH := fam .cdA

@[simp] theorem fam_f (cd : HReg) (k : FReg) (hk : k ≠ .cd) : fam cd k = regH (.f k) := fam_ne cd k hk

/-- The registers of an exact read into `tgt` with the family `fam cd`. -/
theorem rdRegs (cd tgt : HReg) (h1 : ∀ r, cd ≠ .f r) (h2 : ∀ r, tgt ≠ .f r) (h3 : tgt ≠ cd) (h4 : tgt ≠ .pk)
    (h5 : tgt ≠ .pt) (h6 : cd ≠ .pk) (h7 : cd ≠ .pt) :
    ReadRegs (fam cd) (regH .pk) (regH .pt) (regH tgt) := by
  have h3' := Ne.symm h3
  have h2' : ∀ r, HReg.f r ≠ tgt := fun r e => h2 r e.symm
  refine ⟨fam_inj cd h1, by simp, by simp [Ne.symm h4], by simp [Ne.symm h5], ?_, ?_, ?_⟩ <;>
  · intro k; unfold fam; split_ifs <;> simp_all

/-- The fields of a family other than its counter. -/
theorem famZero (cd : HReg) (σ : WState 4 nrH) (h : ∀ r, σ.val (regH (.f r)) = 0) :
    ∀ k : FReg, k ≠ .cd → σ.val (fam cd k) = 0 := fun k hk => by rw [fam_ne cd k hk]; exact h k

/-- Registers outside a family. -/
theorem famNe (cd u : HReg) (h1 : ∀ r, u ≠ .f r) (h2 : u ≠ cd) : ∀ k, fam cd k ≠ regH u := by
  intro k; unfold fam; split_ifs <;> simp_all [eq_comm]

/-- A node template from three field templates. -/
def tm (a b c : CheckedPCPP.NodeEmit.Field nrH) : CheckedPCPP.NodeEmit.NodeT nrH := ![a, b, c]

/-- Emit one node. -/
noncomputable def emit (a b c : CheckedPCPP.NodeEmit.Field nrH) : WM 4 nrH :=
  CheckedPCPP.NodeEmit.nodeW sO WR (regH .wt) (tm a b c)

/-- Emit `const false`. -/
noncomputable def emit0 : WM 4 nrH := emit ([], 0) ([], 0) ([], 0)

/-- Read one field of a stream exactly. -/
noncomputable def rd (i : Fin (4 + 1)) (R : FReg → Fin nrH) (u : HReg) : WM 4 nrH :=
  readEx i R (regH .pk) (regH .pt) (regH u)

/-- Skip one field. -/
noncomputable def sk1 (i : Fin (4 + 1)) (R : FReg → Fin nrH) : WM 4 nrH := fieldTo i R (regH .z) (regH .jk)

/-- Skip `sk` fields. -/
noncomputable def skN (i : Fin (4 + 1)) (R : FReg → Fin nrH) : WM 4 nrH := skipN i R (regH .z) (regH .jk) (regH .sk)

/-- `dst += src` (scratch `t`). -/
noncomputable def add (src dst : HReg) : WM 4 nrH := addTo (regH src) (regH dst) (regH .t)

/-- `P := image of node X`. -/
noncomputable def pos (X P : HReg) : WM 4 nrH :=
  posW sF (regH X) (regH P) (regH .sc) (regH .sb) (regH .nB1) (regH .oB) (regH .t)

/-- `lt := [A < B]`. -/
noncomputable def lessW (A B : HReg) : WM 4 nrH :=
  ltWM (regH A) (regH B) (regH .ga) (regH .gb) (regH .gz) (regH .lt) (regH .t)

/-- `L := ℓ` from the copy of its field. -/
noncomputable def getL : WM 4 nrH := .seq (rd sL RL .L) (WM.rewind sL (regH .cdL))

/-! ## Header -/

/-- Header, part A: copy `ℓ`'s field to `sL` (head back at `0`). -/
noncomputable def headerA : WM 4 nrH :=
  .seq (peekW sW (regH .pk) (regH .pt))
  (.seq (add .pk .sk) (.seq (add .pk .sk) (.seq (.inc (regH .sk))
  (.seq (copyCells sW sL (regH .sk))
  (.seq (add .pk .sk) (.seq (add .pk .sk) (.seq (.inc (regH .sk)) (.seq (WM.rewind sL (regH .sk))
    (WM.clear (regH .pk))))))))))

/-- Header, part B: `n_C`, `q`, `n_B`. -/
noncomputable def headerB : WM 4 nrH :=
  .seq (rd sW RW .nC) (.seq (rd sD RB .q) (.seq (rd sD RB .nB) (WM.clear (regH .cdB))))

/-- Header, part C: `hc q + 1`, `n_B − 1`, `3 n_B`. -/
noncomputable def headerC : WM 4 nrH :=
  .seq (add .q .x) (.seq (hcW (regH .x) (regH .bq) (regH .h)) (.seq (.inc (regH .bq))
  (.seq (add .nB .nB1) (.seq (.dec (regH .nB1))
  (.seq (add .nB .sk) (.seq (add .nB .sk) (add .nB .sk)))))))

/-- Header, part D: `o_B`, back to `B`'s nodes. -/
noncomputable def headerD : WM 4 nrH :=
  .seq (skN sD RB) (.seq (rd sD RB .oB) (WM.rewind sD (regH .cdB)))

/-- Phase 1: the header. -/
noncomputable def header : WM 4 nrH := .seq headerA (.seq headerB (.seq headerC headerD))

/-! ## Count pass -/

/-- Count pass, a plain node: skip its two fields, flag `false`. -/
noncomputable def cPlain : WM 4 nrH := .seq (sk1 sW RW) (.seq (sk1 sW RW) (.seq (.wr sF false) (.fwd sF)))

/-- Count pass, an oracle gate: flag `true`, `k += 1`, skip its `ℓ` arguments. -/
noncomputable def cOracle : WM 4 nrH :=
  .seq (.wr sF true) (.seq (.fwd sF) (.seq (.inc (regH .k)) (.seq getL (.seq (add .L .sk) (.seq (skN sW RW)
    (WM.clear (regH .L)))))))

/-- One node of the count pass. -/
noncomputable def countBody : WM 4 nrH :=
  .seq (rd sW RW .tag) (caseL (regH .tag) [cPlain, cPlain, cPlain, cPlain, cPlain, cOracle])

/-- Phase 2: the count pass. -/
noncomputable def countPass : WM 4 nrH :=
  .seq (WM.clear (regH .cdW)) (.seq (add .nC .iC) (.seq (.whr (regH .iC) (.seq (.dec (regH .iC)) countBody))
  (.seq (rd sW RW .oC) (.seq (WM.rewind sW (regH .cdW)) (.seq (add .nC .sb) (WM.rewind sF (regH .sb)))))))

/-! ## Sizes -/

/-- Phase 3: `sz = 1 + n_C + k·(n_B − 1)`, `pd = q − (sz + 1)`, `M = sz + 1 + pd`. -/
noncomputable def sizes : WMX 4 nrH :=
  .seq (mulR (regH .k) (regH .gb) (regH .nB1) (regH .sz) (regH .t))
  (.wm (.seq (add .nC .sz) (.seq (.inc (regH .sz))
  (.seq (add .q .pd) (.seq (add .sz .x) (.seq (.inc (regH .x)) (.seq (.whr (regH .x) (.seq (.dec (regH .x)) (.dec (regH .pd))))
  (.seq (add .sz .M) (.seq (.inc (regH .M)) (add .pd .M))))))))))

/-! ## Emission -/

/-- `B`'s input `j < ℓ`: the image of the gate's argument `j` (seek `j` fields past the arguments' start). -/
noncomputable def wireW : WM 4 nrH :=
  .seq (add .f1 .sk) (.seq (skN sW RA) (.seq (rd sW RA .f2) (.seq (pos .f2 .p1)
    (.seq (WM.rewind sW (regH .cdA)) (.seq (emit ([], 4) ([regH .p1], 0) ([regH .p1], 0))
    (.seq (WM.clear (regH .f2)) (WM.clear (regH .p1))))))))

/-- `B`'s node kinds, copied at offset `cur`. -/
noncomputable def cB0 : WM 4 nrH :=
  .seq (rd sD RB .f1) (.seq (sk1 sD RB) (.seq (emit ([], 0) ([regH .f1], 0) ([], 0)) (WM.clear (regH .f1))))
noncomputable def cB1 : WM 4 nrH :=
  .seq (rd sD RB .f1) (.seq (sk1 sD RB) (.seq (lessW .f1 .L) (.seq (.ifr (regH .lt) wireW emit0)
    (.seq (WM.clear (regH .lt)) (WM.clear (regH .f1))))))
noncomputable def cB2 : WM 4 nrH :=
  .seq (rd sD RB .f1) (.seq (sk1 sD RB) (.seq (emit ([], 2) ([regH .cur, regH .f1], 0) ([], 0)) (WM.clear (regH .f1))))
noncomputable def cB34 (tg : ℕ) : WM 4 nrH :=
  .seq (rd sD RB .f1) (.seq (rd sD RB .f2) (.seq (emit ([], tg) ([regH .cur, regH .f1], 0) ([regH .cur, regH .f2], 0))
    (.seq (WM.clear (regH .f1)) (WM.clear (regH .f2)))))

/-- One node of `B`, copied at offset `cur` (inside an oracle gate). -/
noncomputable def copyBody : WM 4 nrH :=
  .seq (rd sD RB .tagB) (caseL (regH .tagB) [cB0, cB1, cB2, cB34 3, cB34 4])

/-- `C`'s node kinds (the body before `cur += 1`). -/
noncomputable def nC0b : WM 4 nrH :=
  .seq (rd sW RW .f1) (.seq (sk1 sW RW) (.seq (emit ([], 0) ([regH .f1], 0) ([], 0)) (WM.clear (regH .f1))))
noncomputable def nC1b : WM 4 nrH :=
  .seq (fieldToG sW RW (regH .bq) (regH .f1) (regH .g)) (.seq (sk1 sW RW) (.seq (lessW .f1 .q)
    (.seq (.ifr (regH .g) emit0 (.ifr (regH .lt) (emit ([], 1) ([regH .f1], 0) ([], 0)) emit0))
    (.seq (WM.clear (regH .f1)) (.seq (WM.clear (regH .g)) (WM.clear (regH .lt)))))))
noncomputable def nC2b : WM 4 nrH :=
  .seq (rd sW RW .f1) (.seq (sk1 sW RW) (.seq (pos .f1 .p1) (.seq (emit ([], 2) ([regH .p1], 0) ([], 0))
    (.seq (WM.clear (regH .f1)) (WM.clear (regH .p1))))))
noncomputable def nC34b (tg : ℕ) : WM 4 nrH :=
  .seq (rd sW RW .f1) (.seq (rd sW RW .f2) (.seq (pos .f1 .p1) (.seq (pos .f2 .p2)
    (.seq (emit ([], tg) ([regH .p1], 0) ([regH .p2], 0)) (.seq (WM.clear (regH .f1)) (.seq (WM.clear (regH .f2))
    (.seq (WM.clear (regH .p1)) (WM.clear (regH .p2)))))))))
noncomputable def nC0 : WM 4 nrH := .seq nC0b (.inc (regH .cur))
noncomputable def nC1 : WM 4 nrH := .seq nC1b (.inc (regH .cur))
noncomputable def nC2 : WM 4 nrH := .seq nC2b (.inc (regH .cur))
noncomputable def nC34 (tg : ℕ) : WM 4 nrH := .seq (nC34b tg) (.inc (regH .cur))
noncomputable def nC5 : WM 4 nrH :=
  .seq getL (.seq (add .nB .tC) (.seq (.whr (regH .tC) (.seq (.dec (regH .tC)) copyBody))
    (.seq (WM.rewind sD (regH .cdB)) (.seq (add .L .sk) (.seq (skN sW RW) (.seq (WM.clear (regH .L))
    (add .nB .cur)))))))

/-- One node of `C`: its image. -/
noncomputable def nodeBody : WM 4 nrH :=
  .seq (rd sW RW .tag) (caseL (regH .tag) [nC0, nC1, nC2, nC34 3, nC34 4, nC5])

/-- Phase 4, end: the negation of `o_C`'s image, the padding, the output index, the closing cell. -/
noncomputable def emissionEnd : WM 4 nrH :=
  .seq (pos .oC .p1) (.seq (emit ([], 2) ([regH .p1], 0) ([], 0))
  (.seq (add .pd .x) (.seq (.whr (regH .x) (.seq (.dec (regH .x)) emit0))
  (.seq (CheckedPCPP.NodeEmit.fieldW sO WR (regH .wt) ([regH .sz], 0)) (.seq (.wr sO false) (.fwd sO))))))

/-- Phase 4, start: the header of `D_B`, node `0`, `cur := 1`, the loop counter. -/
noncomputable def emStart : WM 4 nrH :=
  .seq (CheckedPCPP.NodeEmit.fieldW sO WR (regH .wt) ([regH .q], 0))
  (.seq (CheckedPCPP.NodeEmit.fieldW sO WR (regH .wt) ([regH .M], 0)) (.seq emit0
  (.seq (.inc (regH .cur)) (add .nC .iC))))

/-- Phase 4: emission. -/
noncomputable def emission : WM 4 nrH :=
  .seq emStart (.seq (.whr (regH .iC) (.seq (.dec (regH .iC)) nodeBody)) emissionEnd)

noncomputable def substProg : WMX 4 nrH :=
  .seq (.wm header) (.seq (.wm countPass) (.seq sizes (.wm emission)))

end NearCubicGates.Close.Succinct.SubstMachine
