import SourceAdapters.Code.CountedParsing

/-! `app:sources`, "Uniform three-query PCPP and code interfaces": the three balanced block sizes are computed by
ordinary cell instructions; division is the checked cell-language primitive. -/

set_option autoImplicit false

namespace NearCubicGates.Adapters.Code.BlockArithmetic

open NearCubicGates.Close.Cells CountedParsing

variable {V M : ℕ}

/-- Generalization of `Cells.incS` to the code constructor's register bank. -/
def addConstant (zero dst : Fin V) : ℕ → St V M
  | 0 => .op (.zero zero)
  | k + 1 => .seq (.op (.inc dst)) (addConstant zero dst k)

theorem add_constant (C : Ctx) (zero dst : Fin V) (hzd : zero ≠ dst) :
    ∀ (k : ℕ) (a : DS V M), a.env zero = 0 → a.env dst + k < 2 ^ C.Wd →
      Ex C (addConstant zero dst k) a (a.set dst (a.env dst + k)) (2 * k + 1) := by
  intro k
  induction k with
  | zero =>
    intro a hz _
    have he : a.set zero 0 = a.set dst (a.env dst + 0) := by
      apply state_ext <;> try rfl
      funext i
      by_cases hi : i = zero
      · subst i; simp [DS.set, hz]
      · by_cases hd : i = dst
        · subst i; simp [DS.set, Ne.symm hzd]
        · simp [DS.set, hi]
    simpa [addConstant, he] using Ex.op (OpEx.zero (C := C) zero a)
  | succ k ih =>
    intro a hz hk
    have e1 := Ex.op (OpEx.inc (C := C) dst a (by omega))
    have e2 := ih (a.set dst (a.env dst + 1))
      (by simp [DS.set, hzd, hz]) (by simp [DS.set]; omega)
    have h := Ex.seq e1 e2
    have he : (a.set dst (a.env dst + 1)).set dst ((a.set dst (a.env dst + 1)).env dst + k) =
        a.set dst (a.env dst + (k + 1)) := by
      apply state_ext <;> try rfl
      funext i
      simp [DS.set, Nat.add_assoc, Nat.add_comm]
    rw [he] at h
    convert h using 1 <;> simp [addConstant]
    omega

abbrev State := DS 12 0
abbrev Script := St 12 0

/-- `n` is register 2, divisor 3 is register 3, quotient and remainder are 4,5;
register 9 is scratch and the three outputs are 6,7,8. -/
def quotient (extra : ℕ) (dst : Fin 12) : Script :=
  .seq (.op (.copy 9 2)) (.seq (addConstant 0 9 extra)
    (.seq (.op (.dm 9 3 4 5)) (.op (.copy dst 4))))

def quotientState (a : State) (extra : ℕ) (dst : Fin 12) : State :=
  (((a.set 9 (a.env 2 + extra)).set 4 ((a.env 2 + extra) / 3)).set 5 ((a.env 2 + extra) % 3)).set dst
    ((a.env 2 + extra) / 3)

theorem quotient_spec (C : Ctx) (extra : ℕ) (dst : Fin 12) (hd : dst ≠ 4)
    (a : State) (hz : a.env 0 = 0) (h3 : a.env 3 = 3)
    (hc : a.env 2 + extra < 2 ^ C.Wd) (hW : 6 ≤ 2 ^ C.Wd) :
    Ex C (quotient extra dst) a (quotientState a extra dst) (2 * extra + 7) := by
  have e1 := Ex.op (OpEx.copy (C := C) (9 : Fin 12) 2 a (by decide))
  let a1 := a.set 9 (a.env 2)
  have e2 := add_constant C (0 : Fin 12) 9 (by decide) extra a1
    (by simp [a1, DS.set, hz]) (by simpa [a1, DS.set] using hc)
  let a2 := a1.set 9 (a1.env 9 + extra)
  have e3 := Ex.op (OpEx.dm (C := C) (9 : Fin 12) 3 4 5 a2
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by simp [a2, a1, DS.set, h3]) (by simpa [a2, a1, DS.set, h3] using hW))
  let a3 := (a2.set 4 (a2.env 9 / a2.env 3)).set 5 (a2.env 9 % a2.env 3)
  have e4 := Ex.op (OpEx.copy (C := C) dst 4 a3 hd)
  have h := Ex.seq e1 (Ex.seq e2 (Ex.seq e3 e4))
  have hf : a3.set dst (a3.env 4) = quotientState a extra dst := by
    apply state_ext <;> try rfl
    funext i
    simp [a3, a2, a1, quotientState, DS.set, h3]
  rw [hf] at h
  convert h using 1 <;> simp [quotient]
  omega

def blockScript : Script := .seq (quotient 2 6) (.seq (quotient 1 7) (quotient 0 8))

theorem block_script (C : Ctx) (a : State) (hz : a.env 0 = 0) (h3 : a.env 3 = 3)
    (hc : a.env 2 + 2 < 2 ^ C.Wd) (hW : 6 ≤ 2 ^ C.Wd) :
    ∃ b, Ex C blockScript a b 29 ∧ b.env 6 = blockSize (a.env 2) 0 ∧
      b.env 7 = blockSize (a.env 2) 1 ∧ b.env 8 = blockSize (a.env 2) 2 ∧
      b.env 2 = a.env 2 ∧ b.ip = a.ip ∧ b.out = a.out ∧ b.kin = a.kin ∧ b.kout = a.kout := by
  have e1 := quotient_spec C 2 6 (by decide) a hz h3 hc hW
  let a1 := quotientState a 2 6
  have e2 := quotient_spec C 1 7 (by decide) a1
    (by simp [a1, quotientState, DS.set, hz]) (by simp [a1, quotientState, DS.set, h3])
    (by simp [a1, quotientState, DS.set]; omega) hW
  let a2 := quotientState a1 1 7
  have e3 := quotient_spec C 0 8 (by decide) a2
    (by simp [a2, a1, quotientState, DS.set, hz]) (by simp [a2, a1, quotientState, DS.set, h3])
    (by simp [a2, a1, quotientState, DS.set]; omega) hW
  refine ⟨_, (Ex.seq e1 (Ex.seq e2 e3)).mono (by omega), ?_⟩
  simp [a2, a1, quotientState, DS.set, blockSize]

def blockState (a : State) : State := quotientState (quotientState (quotientState a 2 6) 1 7) 0 8

theorem block_script_exact (C : Ctx) (a : State) (hz : a.env 0 = 0) (h3 : a.env 3 = 3)
    (hc : a.env 2 + 2 < 2 ^ C.Wd) (hW : 6 ≤ 2 ^ C.Wd) :
    Ex C blockScript a (blockState a) 29 := by
  have e1 := quotient_spec C 2 6 (by decide) a hz h3 hc hW
  let a1 := quotientState a 2 6
  have e2 := quotient_spec C 1 7 (by decide) a1
    (by simp [a1, quotientState, DS.set, hz]) (by simp [a1, quotientState, DS.set, h3])
    (by simp [a1, quotientState, DS.set]; omega) hW
  let a2 := quotientState a1 1 7
  have e3 := quotient_spec C 0 8 (by decide) a2
    (by simp [a2, a1, quotientState, DS.set, hz]) (by simp [a2, a1, quotientState, DS.set, h3])
    (by simp [a2, a1, quotientState, DS.set]; omega) hW
  exact (Ex.seq e1 (Ex.seq e2 e3)).mono (by omega)

end NearCubicGates.Adapters.Code.BlockArithmetic
