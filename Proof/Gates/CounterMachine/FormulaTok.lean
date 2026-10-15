import Proof.Gates.CounterMachine.FormulaPrim

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (writeNatM writeNatM_spec appendO appendO_append)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec
open NearCubicGates.Close.Interfaces.Formats (Tok tokWord)
open NearCubicGates.Close.Tabulator

variable {ns nr : ℕ} (cap : ℕ)

section Tok
variable (O I : Fin (ns + 1)) (Rg : Fin 16 ↪ Fin nr)

/-- `writeNatM`'s register file: the first eight of `Rg`. -/
def wR : Fin 8 ↪ Fin nr := (Fin.castLEEmb (by norm_num : 8 ≤ 16)).trans Rg

theorem wR_apply (i : Fin 8) : wR Rg i = Rg (Fin.castLE (by norm_num) i) := rfl

/-- `d := d + v` (scratch `t`, `v` restored). -/
def copyR (v d t : Fin nr) : WM ns nr :=
  .seq (NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup v d t) (WM.move t v)

theorem copyR_spec {v d t : Fin nr} (hvd : v ≠ d) (hvt : v ≠ t) (hdt : d ≠ t) (σ : WState ns nr)
    (ht : σ.val t = 0) (hcap : σ.val d + σ.val v ≤ cap) :
    WExec cap (copyR v d t) σ (σ.setv d (σ.val d + σ.val v)) (18 * σ.val v + 3) := by
  have h1 := NearCubicWires.WireExponent3_5.FinalPass.Hash4.wdup_spec (cap := cap) v d t hvd hvt hdt (σ.val v) σ rfl
    (by omega) (by omega) (by rw [ht]; omega)
  have h2 := wmove_spec (cap := cap) t v (Ne.symm hvt) (σ.val v)
    (((σ.setv v 0).setv d (σ.val d + σ.val v)).setv t (σ.val t + σ.val v)) (by simp [ht])
    (by simp [ht]; omega) (by simp [Function.update_apply, hvt, hvd, ht]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
  apply WState.eq <;> try rfl
  funext r
  simp only [WState.setv_val, Function.update_apply]
  by_cases r1 : r = v
  · rw [r1]; simp [hvd, hvt, ht, Ne.symm hvt]
  · by_cases r2 : r = t
    · rw [r2]; simp [Ne.symm hvt, Ne.symm hdt, ht]
    · simp [r1, r2]

theorem nbl_le (v : ℕ) : natBitLength v ≤ v + 1 := by
  have h1 := Nat.log_lt_self 2 (show v + 1 ≠ 0 by omega)
  have h2 := Nat.log_mono_right (show v ≤ v + 1 by omega) (b := 2)
  unfold natBitLength; omega

theorem natWord_length' (v : ℕ) : (natWord v).length = 2 * natBitLength v + 1 := by simp [natWord]

/-- The printer at rest: the scratch registers are `0`, the output head at its end. -/
structure PrRest (σ : WState ns nr) : Prop where
  out : σ.sh O = (σ.st O).length
  zero : ∀ i : Fin 16, i ∈ ([0, 1, 2, 3, 4, 5, 6, 8] : List (Fin 16)) → σ.val (Rg i) = 0

theorem PrRest.append {σ : WState ns nr} (h : PrRest O Rg σ) (w : List Bool) : PrRest O Rg (appendO σ O (Rg 7) w) :=
  ⟨by simp [appendO, h.out], fun i hi => by
    have hne : Rg i ≠ Rg 7 := Rg.injective.ne (by revert i; decide)
    simp [appendO, Function.update_of_ne hne]; exact h.zero i hi⟩

/-- `marks (natWord v)` from the register `v` (outside `Rg 0 … Rg 8`). -/
def printReg (v : Fin nr) : WM ns nr :=
  .seq (copyR v (Rg 0) (Rg 8)) (.seq (writeNatM O (wR Rg)) (WM.clear (Rg 0)))

def printCost (x : ℕ) : ℕ := 18 * x + 3 + 1 + ((natBitLength x + 10) * (100 * x + 200) + 1 + (3 * x + 1))

theorem printReg_spec (v : Fin nr) (hv : ∀ i : Fin 16, i.val ≤ 8 → Rg i ≠ v) (σ : WState ns nr) (h : PrRest O Rg σ)
    (hcap : σ.val (Rg 7) + 7 * σ.val v + 12 ≤ cap) :
    WExec cap (printReg O Rg v) σ (appendO σ O (Rg 7) (marks (natWord (σ.val v)))) (printCost (σ.val v)) := by
  have hrn : ∀ {a b : Fin 16}, a ≠ b → Rg a ≠ Rg b := fun h => Rg.injective.ne h
  have h1 := copyR_spec cap (v := v) (d := Rg 0) (t := Rg 8) (hv 0 (by decide)).symm (hv 8 (by decide)).symm
    (hrn (by decide)) σ (h.zero 8 (by decide)) (by rw [h.zero 0 (by decide)]; omega)
  rw [h.zero 0 (by decide), Nat.zero_add] at h1
  set σ1 := σ.setv (Rg 0) (σ.val v) with hσ1
  have hnb := nbl_le (σ.val v)
  have h2 := writeNatM_spec cap O (wR Rg) σ1
    (by simp [hσ1, wR_apply, Function.update_of_ne (hrn (show (1 : Fin 16) ≠ 0 by decide))]; exact h.zero 1 (by decide))
    (by simp [hσ1, wR_apply, Function.update_of_ne (hrn (show (2 : Fin 16) ≠ 0 by decide))]; exact h.zero 2 (by decide))
    (by simp [hσ1, wR_apply, Function.update_of_ne (hrn (show (3 : Fin 16) ≠ 0 by decide))]; exact h.zero 3 (by decide))
    (by simp [hσ1, wR_apply, Function.update_of_ne (hrn (show (4 : Fin 16) ≠ 0 by decide))]; exact h.zero 4 (by decide))
    (by simp [hσ1, wR_apply, Function.update_of_ne (hrn (show (5 : Fin 16) ≠ 0 by decide))]; exact h.zero 5 (by decide))
    (by simp [hσ1, wR_apply, Function.update_of_ne (hrn (show (6 : Fin 16) ≠ 0 by decide))]; exact h.zero 6 (by decide))
    (by simp [hσ1, h.out])
    (by simp [hσ1, wR_apply, Function.update_of_ne (hrn (show (7 : Fin 16) ≠ 0 by decide))]; omega)
  have e0 : σ1.val (wR Rg 0) = σ.val v := by simp [hσ1, wR_apply]
  have e7 : wR Rg 7 = Rg 7 := rfl
  rw [e0, e7] at h2
  have h3 := wclear_spec (cap := cap) (Rg 0) (σ.val v) (appendO σ1 O (Rg 7) (marks (natWord (σ.val v))))
    (by simp [appendO, hσ1, Function.update_of_ne (hrn (show (0 : Fin 16) ≠ 7 by decide))])
    (by simp [appendO, hσ1, Function.update_of_ne (hrn (show (0 : Fin 16) ≠ 7 by decide))]; omega)
  refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by unfold printCost; omega)
  apply WState.eq
  · simp [appendO, hσ1]
  · simp [appendO, hσ1]
  · funext r; by_cases c0 : r = Rg 0
    · subst c0; simp [appendO, hσ1, Function.update_of_ne (hrn (show (0 : Fin 16) ≠ 7 by decide)), h.zero 0 (by decide)]
    · by_cases c7 : r = Rg 7
      · subst c7; simp [appendO, hσ1, Function.update_of_ne (hrn (show (7 : Fin 16) ≠ 0 by decide))]
      · simp [appendO, hσ1, Function.update_of_ne c0, Function.update_of_ne c7]
  · simp [appendO, hσ1]

/-! ## Tokens -/

theorem tokWord_const_nat (v : ℕ) : tokWord (.const (v : ℤ)) = natWord 0 ++ natWord 0 ++ natWord v := by
  simp [tokWord, NearCubicGates.Close.Interfaces.intWord, List.append_assoc]

/-- A token whose word is `natWord tag ++ natWord v` with `v` in a register (`var`, `pow`). -/
def tokTagReg (tag : ℕ) (v : Fin nr) : WM ns nr := .seq (emitMarks O (Rg 7) (natWord tag)) (printReg O Rg v)

theorem tokTagReg_spec (tag : ℕ) (v : Fin nr) (hv : ∀ i : Fin 16, i.val ≤ 8 → Rg i ≠ v) (σ : WState ns nr)
    (h : PrRest O Rg σ) (hcap : σ.val (Rg 7) + 2 * (natWord tag).length + 7 * σ.val v + 12 ≤ cap) :
    WExec cap (tokTagReg O Rg tag v) σ (appendO σ O (Rg 7) (marks (natWord tag ++ natWord (σ.val v))))
      (16 * (natWord tag).length + 1 + printCost (σ.val v)) := by
  have h1 := emitMarks_spec cap O (Rg 7) (natWord tag) σ h.out (by omega)
  have hv7 : Rg 7 ≠ v := hv 7 (by decide)
  have h2 := printReg_spec cap O Rg v hv (appendO σ O (Rg 7) (marks (natWord tag))) (h.append O Rg _)
    (by simp only [appendO, WState.setv_val, WState.seth_val, WState.sets_val, Function.update_self,
          Function.update_of_ne hv7.symm, marks_length]; omega)
  have ev : (appendO σ O (Rg 7) (marks (natWord tag))).val v = σ.val v := by
    simp [appendO, Function.update_of_ne hv7.symm]
  rw [ev] at h2
  refine WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl
  rw [appendO_append, marksApp]

/-- A constant token from the input stream (an `intWord` in framed form). -/
def tokConstIn : WM ns nr := .seq (emitMarks O (Rg 7) (natWord 0)) (copyInt true I O (wR Rg))

theorem tokConstIn_spec (hIO : I ≠ O) (z : ℤ) (pre rest : List Bool) (σ : WState ns nr) (h : PrRest O Rg σ)
    (hst : σ.st I = pre ++ enc true (Interfaces.intWord z) ++ rest) (hsh : σ.sh I = pre.length)
    (hcap : σ.val (Rg 7) + 2 * (natWord 0).length + 2 * (Interfaces.intWord z).length + 4 ≤ cap) :
    WExec cap (tokConstIn O I Rg) σ ((appendO σ O (Rg 7) (marks (tokWord (.const z)))).seth I
      (pre.length + 2 * (Interfaces.intWord z).length)) (16 * (natWord 0).length + 1 + (60 * (Interfaces.intWord z).length + 121)) := by
  have hrn : ∀ {a b : Fin 16}, a ≠ b → Rg a ≠ Rg b := fun h => Rg.injective.ne h
  have h1 := emitMarks_spec cap O (Rg 7) (natWord 0) σ h.out (by omega)
  have h2 := copyInt_spec cap true I O hIO (wR Rg) z pre rest (appendO σ O (Rg 7) (marks (natWord 0)))
    (by simp [appendO, Function.update_of_ne hIO, hst]) (by simp [appendO, Function.update_of_ne hIO, hsh])
    (by simp [appendO, h.out])
    (by simp [appendO, wR_apply, Function.update_of_ne (hrn (show (1 : Fin 16) ≠ 7 by decide))]; exact h.zero 1 (by decide))
    (by simp [appendO, wR_apply, Function.update_of_ne (hrn (show (2 : Fin 16) ≠ 7 by decide))]; exact h.zero 2 (by decide))
    (by simp only [appendO, wR_apply, WState.setv_val, WState.seth_val, WState.sets_val, marks_length]
        have : Rg (Fin.castLE (by norm_num) (7 : Fin 8)) = Rg 7 := rfl
        rw [this, Function.update_self]; omega)
  refine WExec.cast cap (WExec.seq h1 h2) ?_ le_rfl
  have e7 : wR Rg 7 = Rg 7 := rfl
  rw [e7, appendO_append, ← marksApp]
  simp [tokWord, stp]

/-- An operator or constant-literal token. -/
def tokLit (t : Tok) : WM ns nr := emitMarks O (Rg 7) (tokWord t)

theorem tokLit_spec (t : Tok) (σ : WState ns nr) (h : PrRest O Rg σ)
    (hcap : σ.val (Rg 7) + 2 * (tokWord t).length ≤ cap) :
    WExec cap (tokLit O Rg t) σ (appendO σ O (Rg 7) (marks (tokWord t))) (16 * (tokWord t).length) :=
  emitMarks_spec cap O (Rg 7) (tokWord t) σ h.out hcap

end Tok

end NearCubicGates.Close.CounterMachine
