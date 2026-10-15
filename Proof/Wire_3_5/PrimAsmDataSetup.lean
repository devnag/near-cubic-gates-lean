import Proof.Wire_3_5.PrimAsmCopyNat
import Proof.Wire_3_5.PrimAsmUnaryPow

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.ParseNat
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat NearCubicWires.WireExponent3_5.PrimAsm.CopyNat
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-! ## Generic loops -/

section Gen
variable {ns nr : ℕ} (cap : ℕ)

/-- A `whs` loop along a state sequence: the scanned bit set before each of the `m` rounds, clear after them. -/
theorem whsLoop (i : Fin (ns + 1)) (body : WM ns nr) (c m : ℕ) (S : ℕ → WState ns nr)
    (hT : ∀ k < m, wbit (S k) i = true) (hF : wbit (S m) i = false)
    (hb : ∀ k < m, WExec cap body (S k) (S (k + 1)) c) :
    WExec cap (.whs i body) (S 0) (S m) (m * (c + 2) + 1) := by
  have key : ∀ r j, j + r = m → WExec cap (.whs i body) (S j) (S m) (r * (c + 2) + 1) := by
    intro r
    induction r with
    | zero =>
      intro j hj
      rw [Nat.add_zero] at hj
      subst hj
      exact WExec.mono (WExec.whsF hF) (by omega)
    | succ r ih =>
      intro j hj
      exact WExec.mono (WExec.whsT (hT j (by omega)) (hb j (by omega)) (ih (j + 1) (by omega))) (by nlinarith)
  exact key m 0 (by omega)

theorem rep_read (m k : ℕ) : readTapeBit (List.replicate m true) k = decide (k < m) := by
  unfold readTapeBit
  by_cases h : k < m
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]
    simp [h]
  · rw [List.getD_eq_default _ _ (by simpa using h)]
    simp [h]

theorem rep_write (m : ℕ) : writeTapeBit (List.replicate m true) m true = List.replicate (m + 1) true := by
  have e : ∀ l : List Bool, writeTapeBit l l.length true = l ++ [true] := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [writeTapeBit, ih]
  have := e (List.replicate m true)
  rw [List.length_replicate] at this
  rw [this, List.replicate_succ']

/-- Copy `1^m` from `S` onto the blank `D`, counting in `c`; then walk both heads back. -/
def ucopyW (S D : Fin (ns + 1)) (c : Fin nr) : WM ns nr :=
  .seq (.whs S (.seq (.wr D true) (.seq (.fwd D) (.seq (.fwd S) (.inc c)))))
    (.whr c (.seq (.bwd D) (.seq (.bwd S) (.dec c))))

theorem ucopyW_spec (S D : Fin (ns + 1)) (hSD : S ≠ D) (c : Fin nr) (m : ℕ) (σ : WState ns nr)
    (hS : σ.st S = List.replicate m true) (hSh : σ.sh S = 0) (hD : σ.st D = []) (hDh : σ.sh D = 0)
    (hc : σ.val c = 0) (hm : m ≤ cap) :
    WExec cap (ucopyW S D c) σ (σ.sets D (List.replicate m true)) (18 * m + 3) := by
  set S1 : ℕ → WState ns nr := fun k =>
    (((σ.sets D (List.replicate k true)).seth D k).seth S k).setv c k with hS1
  have l1 := whsLoop cap S (.seq (.wr D true) (.seq (.fwd D) (.seq (.fwd S) (.inc c)))) 9 m S1
    (fun k hk => by
      simp [wbit, hS1, Function.update_apply, hSD, Ne.symm hSD, hS, rep_read, hk])
    (by
      simp [wbit, hS1, Function.update_apply, hSD, Ne.symm hSD, hS, rep_read])
    (fun k hk => by
      have h1 := WExec.wr (cap := cap) D true (S1 k)
      have h2 := WExec.fwd (cap := cap) D ((S1 k).sets D (writeTapeBit ((S1 k).st D) ((S1 k).sh D) true))
      have h3 := WExec.fwd (cap := cap) S (((S1 k).sets D (writeTapeBit ((S1 k).st D) ((S1 k).sh D) true)).seth D
        (((S1 k).sets D (writeTapeBit ((S1 k).st D) ((S1 k).sh D) true)).sh D + 1))
      have h4 := WExec.inc (cap := cap) c ((((S1 k).sets D (writeTapeBit ((S1 k).st D) ((S1 k).sh D) true)).seth D
        (((S1 k).sets D (writeTapeBit ((S1 k).st D) ((S1 k).sh D) true)).sh D + 1)).seth S
        ((((S1 k).sets D (writeTapeBit ((S1 k).st D) ((S1 k).sh D) true)).seth D
        (((S1 k).sets D (writeTapeBit ((S1 k).st D) ((S1 k).sh D) true)).sh D + 1)).sh S + 1))
        (by simp [hS1]; omega)
      refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 (WExec.seq h3 h4))) ?_ (by omega)
      apply WState.eq
      · funext j
        by_cases hjS : j = S
        · subst hjS; simp [hS1, Function.update_apply, hSD]
        · by_cases hjD : j = D
          · subst hjD; simp [hS1, Function.update_apply, hjS]
          · simp [hS1, Function.update_apply, hjS, hjD]
      · funext j
        by_cases hjD : j = D
        · subst hjD; simp [hS1, Function.update_apply, rep_write]
        · simp [hS1, Function.update_apply, hjD]
      · funext j
        by_cases hjc : j = c
        · subst hjc; simp [hS1, Function.update_apply]
        · simp [hS1, Function.update_apply, hjc]
      · simp [hS1])
  set S2 : ℕ → WState ns nr := fun q =>
    (((σ.sets D (List.replicate m true)).seth D (m - q)).seth S (m - q)).setv c (m - q) with hS2
  have l2 := UnaryPow.flagLoop cap c (.seq (.bwd D) (.seq (.bwd S) (.dec c))) 5 m S2
    (fun k hk => by simp [hS2]; omega) (by simp [hS2])
    (fun k hk => by
      have h1 := WExec.bwd (cap := cap) D (S2 k)
      have h2 := WExec.bwd (cap := cap) S ((S2 k).seth D ((S2 k).sh D - 1))
      have h3 := WExec.dec (cap := cap) c (((S2 k).seth D ((S2 k).sh D - 1)).seth S
        (((S2 k).seth D ((S2 k).sh D - 1)).sh S - 1)) (by simp [hS2]; omega)
      refine WExec.cast cap (WExec.seq h1 (WExec.seq h2 h3)) ?_ (by omega)
      apply WState.eq
      · funext j
        by_cases hjS : j = S
        · subst hjS; simp [hS2, Function.update_apply, hSD]; omega
        · by_cases hjD : j = D
          · subst hjD; simp [hS2, Function.update_apply, hjS]; omega
          · simp [hS2, Function.update_apply, hjS, hjD]
      · funext j; simp [hS2]
      · funext j
        by_cases hjc : j = c
        · subst hjc; simp [hS2, Function.update_apply]; omega
        · simp [hS2, Function.update_apply, hjc]
      · simp [hS2])
  have e0 : S1 0 = σ := by
    apply WState.eq
    · funext j
      by_cases hjS : j = S
      · subst hjS; simp [hS1, Function.update_apply, hSh]
      · by_cases hjD : j = D
        · subst hjD; simp [hS1, Function.update_apply, hjS, hDh]
        · simp [hS1, Function.update_apply, hjS, hjD]
    · funext j
      by_cases hjD : j = D
      · subst hjD; simp [hS1, Function.update_apply, hD]
      · simp [hS1, Function.update_apply, hjD]
    · funext j
      by_cases hjc : j = c
      · subst hjc; simp [hS1, Function.update_apply, hc]
      · simp [hS1, Function.update_apply, hjc]
    · simp [hS1]
  have em : S1 m = S2 0 := by simp [hS1, hS2]
  have ef : S2 m = σ.sets D (List.replicate m true) := by
    apply WState.eq
    · funext j
      by_cases hjS : j = S
      · subst hjS; simp [hS2, Function.update_apply, hSh, hSD]
      · by_cases hjD : j = D
        · subst hjD; simp [hS2, Function.update_apply, hjS, hDh]
        · simp [hS2, Function.update_apply, hjS, hjD]
    · funext j; simp [hS2]
    · funext j
      by_cases hjc : j = c
      · subst hjc; simp [hS2, Function.update_apply, hc]
      · simp [hS2, Function.update_apply, hjc]
    · simp [hS2]
  rw [e0, em] at l1
  rw [ef] at l2
  exact WExec.cast cap (WExec.seq l1 l2) rfl (by nlinarith)

/-- Walk the head of `o` back by the count in `r`, clearing `r`. -/
def rewindW (o : Fin (ns + 1)) (r : Fin nr) : WM ns nr := .whr r (.seq (.bwd o) (.dec r))

theorem rewindW_spec (o : Fin (ns + 1)) (r : Fin nr) (m : ℕ) (σ : WState ns nr) (ho : σ.sh o = m)
    (hr : σ.val r = m) (hm : m ≤ cap) :
    WExec cap (rewindW o r) σ ((σ.seth o 0).setv r 0) (5 * m + 1) := by
  set S : ℕ → WState ns nr := fun q => (σ.seth o (m - q)).setv r (m - q) with hSd
  have l := UnaryPow.flagLoop cap r (.seq (.bwd o) (.dec r)) 3 m S (fun k hk => by simp [hSd]; omega)
    (by simp [hSd])
    (fun k hk => by
      have h1 := WExec.bwd (cap := cap) o (S k)
      have h2 := WExec.dec (cap := cap) r ((S k).seth o ((S k).sh o - 1)) (by simp [hSd]; omega)
      refine WExec.cast cap (WExec.seq h1 h2) ?_ (by omega)
      apply WState.eq
      · funext j
        by_cases hj : j = o
        · subst hj; simp [hSd, Function.update_apply]; omega
        · simp [hSd, Function.update_apply, hj]
      · funext j; simp [hSd]
      · funext j
        by_cases hj : j = r
        · subst hj; simp [hSd, Function.update_apply]; omega
        · simp [hSd, Function.update_apply, hj]
      · simp [hSd])
  have e0 : S 0 = σ := by
    apply WState.eq
    · funext j
      by_cases hj : j = o
      · subst hj; simp [hSd, Function.update_apply, ho]
      · simp [hSd, Function.update_apply, hj]
    · funext j; simp [hSd]
    · funext j
      by_cases hj : j = r
      · subst hj; simp [hSd, Function.update_apply, hr]
      · simp [hSd, Function.update_apply, hj]
    · simp [hSd]
  have em : S m = (σ.seth o 0).setv r 0 := by simp [hSd]
  rw [e0, em] at l
  exact WExec.mono l (by omega)

end Gen

/-! ## The layout -/

/-- The stage's streams: `0` the request, `1` `1^n`, `2` `1^L`, `3` the fill count, `4` the fill's marker tape,
`5` the output, `6 … 13` spare, then four SYM table slots (`1789` streams each) and two carrier slots (`1357`). -/
abbrev DS : ℕ := 9883

/-- The stage's registers. -/
abbrev DR : ℕ := 16

def sIN : Fin (DS + 1) := 0
def sNT : Fin (DS + 1) := 1
def sLT : Fin (DS + 1) := 2
def sCT : Fin (DS + 1) := 3
def sAUX : Fin (DS + 1) := 4
def sOUT : Fin (DS + 1) := 5

/-- Stream `j` of SYM table slot `i`. -/
def sSym (i : Fin 4) (j : Fin 1789) : Fin (DS + 1) :=
  ⟨14 + 1789 * i.val + j.val, by have := i.isLt; have := j.isLt; unfold DS; omega⟩

/-- Stream `j` of carrier table slot `k`. -/
def sCar (k : Fin 2) (j : Fin 1357) : Fin (DS + 1) :=
  ⟨7170 + 1357 * k.val + j.val, by have := k.isLt; have := j.isLt; unfold DS; omega⟩

def rA : Fin DR := 0
def rK : Fin DR := 1
def rf : Fin DR := 2
def rc : Fin DR := 3
def rp : Fin DR := 4
def rt : Fin DR := 5
def rOP : Fin DR := 6
def rN : Fin DR := 7

theorem sSym_val (i : Fin 4) (j : Fin 1789) : (sSym i j).val = 14 + 1789 * i.val + j.val := rfl
theorem sCar_val (k : Fin 2) (j : Fin 1357) : (sCar k j).val = 7170 + 1357 * k.val + j.val := rfl

theorem sSym_inj (i : Fin 4) : Function.Injective (sSym i) := by
  intro a b h
  have := congrArg Fin.val h
  rw [sSym_val, sSym_val] at this
  exact Fin.ext (by omega)

theorem sCar_inj (k : Fin 2) : Function.Injective (sCar k) := by
  intro a b h
  have := congrArg Fin.val h
  rw [sCar_val, sCar_val] at this
  exact Fin.ext (by omega)

theorem sSym_eq_iff (i i' : Fin 4) (j j' : Fin 1789) : sSym i j = sSym i' j' ↔ i = i' ∧ j = j' := by
  constructor
  · intro h
    have := congrArg Fin.val h
    rw [sSym_val, sSym_val] at this
    have hj := j.isLt
    have hj' := j'.isLt
    have hi : i.val = i'.val := by omega
    exact ⟨Fin.ext hi, Fin.ext (by omega)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem sCar_eq_iff (k k' : Fin 2) (j j' : Fin 1357) : sCar k j = sCar k' j' ↔ k = k' ∧ j = j' := by
  constructor
  · intro h
    have := congrArg Fin.val h
    rw [sCar_val, sCar_val] at this
    have hj := j.isLt
    have hj' := j'.isLt
    have hk : k.val = k'.val := by omega
    exact ⟨Fin.ext hk, Fin.ext (by omega)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem sSym_ne_sCar (i : Fin 4) (j : Fin 1789) (k : Fin 2) (j' : Fin 1357) : sSym i j ≠ sCar k j' := by
  intro h
  have := congrArg Fin.val h
  rw [sSym_val, sCar_val] at this
  have := i.isLt
  have := j.isLt
  omega

theorem sSym_ne_low (i : Fin 4) (j : Fin 1789) (s : Fin (DS + 1)) (hs : s.val < 14) : sSym i j ≠ s := by
  intro h
  have := congrArg Fin.val h
  rw [sSym_val] at this
  omega

theorem sCar_ne_low (k : Fin 2) (j : Fin 1357) (s : Fin (DS + 1)) (hs : s.val < 14) : sCar k j ≠ s := by
  intro h
  have := congrArg Fin.val h
  rw [sCar_val] at this
  omega

theorem wtb_end (l : List Bool) (v : Bool) : writeTapeBit l l.length v = l ++ [v] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [writeTapeBit, ih]

/-! ## One table slot's inputs -/

/-- A slot's cost. -/
def slotCost (x n L : ℕ) : ℕ :=
  1 + 1 + (60 * (RepairRepresentation.natWord x).length + 60 + 1 + (1 + 1 +
    (5 * (2 * (RepairRepresentation.natWord x).length) + 1 + 1 + (18 * n + 3 + 1 + (18 * L + 3))))) + 1

section Slot
variable (cap : ℕ)

/-- **A present slot, generically** (any three distinct target streams, countdown `A`): the next code field framed,
`1^n`, `1^L`, the request's head past the field, the countdown decremented. -/
theorem slot_on (A : Fin DR) (hAf : A ≠ rf) (hAc' : A ≠ rc) (hAO : A ≠ rOP) (hAN : A ≠ rN)
    (o0 o1 o2 : Fin (DS + 1)) (h01 : o0 ≠ o1) (h02 : o0 ≠ o2) (h12 : o1 ≠ o2)
    (hI0 : sIN ≠ o0) (hI1 : sIN ≠ o1) (hI2 : sIN ≠ o2) (hN1 : sNT ≠ o1) (hL2 : sLT ≠ o2) (hN0 : sNT ≠ o0)
    (hL0 : sLT ≠ o0) (hL1 : sLT ≠ o1) (hN2 : sNT ≠ o2)
    (x n L : ℕ) (pre rest : List Bool) (σ : WState DS DR)
    (hA : σ.val A ≠ 0) (hAc : σ.val A ≤ cap)
    (hIN : σ.st sIN = pre ++ enc true (RepairRepresentation.natWord x) ++ rest) (hINh : σ.sh sIN = pre.length)
    (h0 : σ.st o0 = []) (h0h : σ.sh o0 = 0) (h1 : σ.st o1 = []) (h1h : σ.sh o1 = 0)
    (h2 : σ.st o2 = []) (h2h : σ.sh o2 = 0)
    (hNT : σ.st sNT = List.replicate n true) (hNTh : σ.sh sNT = 0)
    (hLT : σ.st sLT = List.replicate L true) (hLTh : σ.sh sLT = 0)
    (hf : σ.val rf = 0) (hc : σ.val rc = 0) (hOP : σ.val rOP = 0) (hN : σ.val rN = 0)
    (hcap : 2 * (RepairRepresentation.natWord x).length + 2 + n + L ≤ cap) :
    WExec cap (.ifr A (.seq (.dec A) (.seq (copyNatM true sIN o0 rf rc rOP) (.seq (.wr o0 false)
      (.seq (rewindW o0 rOP) (.seq (ucopyW sNT o1 rN) (ucopyW sLT o2 rN)))))) .skip) σ
      (((((σ.setv A (σ.val A - 1)).seth sIN (pre.length + 2 * (RepairRepresentation.natWord x).length)).sets o0
        (frame (RepairRepresentation.natWord x))).sets o1 (List.replicate n true)).sets o2 (List.replicate L true))
      (slotCost x n L) := by
  have hmk := RepairOrdinary.Streaming.marks_length (RepairRepresentation.natWord x)
  have hnl := natWord_length x
  have d := WExec.dec (cap := cap) A σ hAc
  set σa := σ.setv A (σ.val A - 1) with hσa
  have c1 := copyNatM_spec cap true sIN o0 hI0 rf rc rOP (by decide) (by decide) (by decide) x pre rest σa
    (by simp [hσa, hIN]) (by simp [hσa, hINh]) (by simp [hσa, h0, h0h]) (by simp [hσa, Function.update_apply, hf,
      Ne.symm hAf]) (by simp [hσa, Function.update_apply, hc, Ne.symm hAc'])
    (by simp [hσa, Function.update_apply, hOP, Ne.symm hAO]; omega)
  set τ1 := (appendO σa o0 rOP (marks (RepairRepresentation.natWord x))).seth sIN
    (pre.length + stp true * (RepairRepresentation.natWord x).length) with hτ1
  have w2 := WExec.wr (cap := cap) o0 false τ1
  set τ2 := τ1.sets o0 (writeTapeBit (τ1.st o0) (τ1.sh o0) false) with hτ2
  have r3 := rewindW_spec cap o0 rOP (marks (RepairRepresentation.natWord x)).length τ2
    (by simp [hτ2, hτ1, hσa, Function.update_apply, Ne.symm hI0, h0h])
    (by simp [hτ2, hτ1, hσa, Function.update_apply, hOP, Ne.symm hAO]) (by omega)
  set τ3 := (τ2.seth o0 0).setv rOP 0 with hτ3
  have u4 := ucopyW_spec cap sNT o1 hN1 rN n τ3
    (by simp [hτ3, hτ2, hτ1, hσa, Function.update_apply, hNT, hN0, Ne.symm hI0, show sNT ≠ sIN by decide])
    (by simp [hτ3, hτ2, hτ1, hσa, Function.update_apply, hNTh, hN0, show sNT ≠ sIN by decide])
    (by simp [hτ3, hτ2, hτ1, hσa, Function.update_apply, h1, Ne.symm h01, Ne.symm hI1])
    (by simp [hτ3, hτ2, hτ1, hσa, Function.update_apply, h1h, Ne.symm h01, Ne.symm hI1])
    (by simp [hτ3, hτ2, hτ1, hσa, Function.update_apply, hN, Ne.symm hAN, show rN ≠ rOP by decide]) (by omega)
  set τ4 := τ3.sets o1 (List.replicate n true) with hτ4
  have u5 := ucopyW_spec cap sLT o2 hL2 rN L τ4
    (by simp [hτ4, hτ3, hτ2, hτ1, hσa, Function.update_apply, hLT, hL0, hL1, show sLT ≠ sIN by decide])
    (by simp [hτ4, hτ3, hτ2, hτ1, hσa, Function.update_apply, hLTh, hL0, show sLT ≠ sIN by decide])
    (by simp [hτ4, hτ3, hτ2, hτ1, hσa, Function.update_apply, h2, Ne.symm h02, Ne.symm h12, Ne.symm hI2])
    (by simp [hτ4, hτ3, hτ2, hτ1, hσa, Function.update_apply, h2h, Ne.symm h02, Ne.symm hI2])
    (by simp [hτ4, hτ3, hτ2, hτ1, hσa, Function.update_apply, hN, Ne.symm hAN, show rN ≠ rOP by decide]) (by omega)
  have whole := WExec.ifrT (Q := .skip) hA (WExec.seq d (WExec.seq c1 (WExec.seq w2 (WExec.seq r3
    (WExec.seq u4 u5)))))
  have hw2 : writeTapeBit (marks (RepairRepresentation.natWord x)) (2 * (2 * natBitLength x + 1)) false =
      frame (RepairRepresentation.natWord x) := by
    have e : (marks (RepairRepresentation.natWord x)).length = 2 * (2 * natBitLength x + 1) := by
      rw [hmk, natWord_length]
    rw [← e, wtb_end, RankBody.marks_frame]
  refine WExec.cast cap whole ?_ (by unfold slotCost; omega)
  apply WState.eq
  · funext j
    by_cases hjI : j = sIN
    · subst hjI
      simp [hτ4, hτ3, hτ2, hτ1, hσa, Function.update_apply, hI0, stp]
    · by_cases hj0 : j = o0
      · subst hj0
        simp [hτ4, hτ3, hτ2, hτ1, hσa, Function.update_apply, Ne.symm hI0, h0h]
      · simp [hτ4, hτ3, hτ2, hτ1, hσa, Function.update_apply, hjI, hj0]
  · funext j
    by_cases hj2 : j = o2
    · subst hj2
      simp [hτ4, hτ3, hτ2, hτ1, hσa, Function.update_apply]
    · by_cases hj1 : j = o1
      · subst hj1
        simp [hτ4, hτ3, hτ2, hτ1, hσa, Function.update_apply, hj2]
      · by_cases hj0 : j = o0
        · subst hj0
          simp [hτ4, hτ3, hτ2, hτ1, hσa, Function.update_apply, hj1, hj2, h0, h0h, Ne.symm hI0, hw2]
        · simp [hτ4, hτ3, hτ2, hτ1, hσa, Function.update_apply, hj0, hj1, hj2]
  · funext r
    by_cases hrO : r = rOP
    · subst hrO
      simp [hτ4, hτ3, hτ2, hτ1, hσa, Function.update_apply, Ne.symm hAO, hOP]
    · simp [hτ4, hτ3, hτ2, hτ1, hσa, Function.update_apply, hrO]
  · simp [hτ4, hτ3, hτ2, hτ1, hσa]

end Slot

/-! ## A run of slots -/

/-- A slot's three input streams (the code, `1^n`, `1^L`). -/
abbrev Trip := Fin (DS + 1) × Fin (DS + 1) × Fin (DS + 1)

/-- A stream of a slot. -/
def tmem (s : Fin (DS + 1)) (t : Trip) : Prop := s = t.1 ∨ s = t.2.1 ∨ s = t.2.2

/-- A slot's streams are distinct, and none is the request, `1^n` or `1^L`. -/
def Trip.ok (t : Trip) : Prop :=
  t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 ∧ ¬ tmem sIN t ∧ ¬ tmem sNT t ∧ ¬ tmem sLT t

/-- Two slots share no stream. -/
def Trip.disj (t t' : Trip) : Prop := ∀ s, tmem s t → ¬ tmem s t'

/-- **One slot**: while the countdown `A` is positive, the next code field framed onto `t.1` (rewound), `1^n` onto
`t.2.1`, `1^L` onto `t.2.2`. -/
def blockOf (A : Fin DR) (t : Trip) : WM DS DR :=
  .ifr A (.seq (.dec A) (.seq (copyNatM true sIN t.1 rf rc rOP) (.seq (.wr t.1 false)
    (.seq (rewindW t.1 rOP) (.seq (ucopyW sNT t.2.1 rN) (ucopyW sLT t.2.2 rN)))))) .skip

/-- The slots in order. -/
def blocks (A : Fin DR) : List Trip → WM DS DR
  | [] => .skip
  | t :: l => .seq (blockOf A t) (blocks A l)

/-- The slots' cost: a present slot `slotCost`, an absent one `1`, one bridge each. -/
def blocksCost (n L : ℕ) : List Trip → List ℕ → ℕ
  | [], _ => 0
  | _ :: l, [] => 1 + 1 + blocksCost n L l []
  | _ :: l, x :: cs => slotCost x n L + 1 + blocksCost n L l cs

/-- A slot holding the inputs of code `x`. -/
def Done (σ : WState DS DR) (t : Trip) (x n L : ℕ) : Prop :=
  σ.st t.1 = frame (RepairRepresentation.natWord x) ∧ σ.sh t.1 = 0 ∧ σ.st t.2.1 = List.replicate n true ∧
    σ.sh t.2.1 = 0 ∧ σ.st t.2.2 = List.replicate L true ∧ σ.sh t.2.2 = 0

/-- A blank slot. -/
def Blank (σ : WState DS DR) (t : Trip) : Prop :=
  σ.st t.1 = [] ∧ σ.sh t.1 = 0 ∧ σ.st t.2.1 = [] ∧ σ.sh t.2.1 = 0 ∧ σ.st t.2.2 = [] ∧ σ.sh t.2.2 = 0

theorem enc_flatMap_cons (x : ℕ) (cs : List ℕ) :
    enc true ((x :: cs).flatMap RepairRepresentation.natWord) =
      enc true (RepairRepresentation.natWord x) ++ enc true (cs.flatMap RepairRepresentation.natWord) := by
  simp [ParseNat.enc, marks_append]

section Slots
variable (cap : ℕ)

/-- **A run of slots**: the codes' fields, in order, onto the first `|codes|` slots; the rest stay blank; the request's
head past the fields; the countdown at `0`; nothing else changed. -/
theorem blocks_spec (A : Fin DR) (hAf : A ≠ rf) (hAc' : A ≠ rc) (hAO : A ≠ rOP) (hAN : A ≠ rN) (n L : ℕ) :
    ∀ (l : List Trip) (codes : List ℕ) (pre rest : List Bool) (σ : WState DS DR),
    codes.length ≤ l.length → (∀ t ∈ l, t.ok) → l.Pairwise Trip.disj → (∀ t ∈ l, Blank σ t) →
    σ.val A = codes.length →
    σ.st sIN = pre ++ enc true (codes.flatMap RepairRepresentation.natWord) ++ rest → σ.sh sIN = pre.length →
    σ.st sNT = List.replicate n true → σ.sh sNT = 0 → σ.st sLT = List.replicate L true → σ.sh sLT = 0 →
    σ.val rf = 0 → σ.val rc = 0 → σ.val rOP = 0 → σ.val rN = 0 →
    (∀ x ∈ codes, 2 * (RepairRepresentation.natWord x).length + 2 + n + L ≤ cap) → codes.length ≤ cap →
    ∃ τ : WState DS DR, WExec cap (blocks A l) σ τ (blocksCost n L l codes) ∧ τ.val A = 0 ∧
      τ.st sIN = σ.st sIN ∧ τ.sh sIN = pre.length + 2 * (codes.flatMap RepairRepresentation.natWord).length ∧
      (∀ i (h : i < codes.length) (hl : i < l.length), Done τ (l.get ⟨i, hl⟩) (codes.get ⟨i, h⟩) n L) ∧
      (∀ i (hl : i < l.length), codes.length ≤ i → Blank τ (l.get ⟨i, hl⟩)) ∧
      (∀ s, (∀ t ∈ l, ¬ tmem s t) → s ≠ sIN → τ.st s = σ.st s ∧ τ.sh s = σ.sh s) ∧
      (∀ r, r ≠ A → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  intro l
  induction l with
  | nil =>
    intro codes pre rest σ hlen _ _ _ hA _ hINh _ _ _ _ _ _ _ _ _ _
    have hc0 : codes = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    subst hc0
    refine ⟨σ, WExec.skip σ, by simpa using hA, rfl, by simpa using hINh, fun i h => by simp at h,
      fun i hl => by simp at hl, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, rfl⟩
  | cons t l ih =>
    intro codes pre rest σ hlen hok hpw hbl hA hIN hINh hNT hNTh hLT hLTh hf hc hOP hN hcx hcl
    have hok1 := hok t (by simp)
    have hokl : ∀ t' ∈ l, t'.ok := fun t' h => hok t' (by simp [h])
    have hpw' := List.pairwise_cons.mp hpw
    have hbt := hbl t (by simp)
    obtain ⟨o01, o02, o12, hnI, hnN, hnL⟩ := hok1
    simp only [tmem, not_or] at hnI hnN hnL
    cases codes with
    | nil =>
      have skipE : WExec cap (blockOf A t) σ σ 1 :=
        WExec.mono (WExec.ifrF (P := .seq (.dec A) (.seq (copyNatM true sIN t.1 rf rc rOP) (.seq (.wr t.1 false)
          (.seq (rewindW t.1 rOP) (.seq (ucopyW sNT t.2.1 rN) (ucopyW sLT t.2.2 rN)))))) (by simpa using hA)
          (WExec.skip σ)) (by omega)
      obtain ⟨τ, hτ, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih [] pre rest σ (by simp) hokl hpw'.2
        (fun t' h => hbl t' (by simp [h])) hA hIN hINh hNT hNTh hLT hLTh hf hc hOP hN (by simp) (by simp)
      refine ⟨τ, WExec.cast cap (WExec.seq skipE hτ) rfl (by simp [blocksCost]), h1, h2, h3, fun i h => by simp at h,
        fun i hl _ => ?_, fun s hs hsI => h6 s (fun t' h => hs t' (by simp [h])) hsI, h7, h8⟩
      · cases i with
        | zero =>
          simp only [List.get_eq_getElem, List.getElem_cons_zero]
          have hsd : ∀ s, tmem s t → τ.st s = σ.st s ∧ τ.sh s = σ.sh s := by
            intro s hs
            refine h6 s (fun t' ht' => hpw'.1 t' ht' s hs) ?_
            rintro rfl
            rcases hs with h | h | h
            · exact hnI.1 h
            · exact hnI.2.1 h
            · exact hnI.2.2 h
          obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hbt
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [(hsd t.1 (Or.inl rfl)).1, b1]
          · rw [(hsd t.1 (Or.inl rfl)).2, b2]
          · rw [(hsd t.2.1 (Or.inr (Or.inl rfl))).1, b3]
          · rw [(hsd t.2.1 (Or.inr (Or.inl rfl))).2, b4]
          · rw [(hsd t.2.2 (Or.inr (Or.inr rfl))).1, b5]
          · rw [(hsd t.2.2 (Or.inr (Or.inr rfl))).2, b6]
        | succ i =>
          simp only [List.get_eq_getElem, List.getElem_cons_succ]
          have := h5 i (by simpa using hl) (by simp)
          simpa using this
    | cons x cs =>
      obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hbt
      have hx := hcx x (by simp)
      have s1 := slot_on cap A hAf hAc' hAO hAN t.1 t.2.1 t.2.2 o01 o02 o12 (fun h => hnI.1 h)
        (fun h => hnI.2.1 h) (fun h => hnI.2.2 h) (fun h => hnN.2.1 h) (fun h => hnL.2.2 h) (fun h => hnN.1 h)
        (fun h => hnL.1 h) (fun h => hnL.2.1 h) (fun h => hnN.2.2 h) x n L pre
        (enc true (cs.flatMap RepairRepresentation.natWord) ++ rest) σ (by rw [hA]; simp) (by rw [hA]; simpa using hcl)
        (by rw [hIN, enc_flatMap_cons]; simp [List.append_assoc]) hINh b1 b2 b3 b4 b5 b6 hNT hNTh hLT hLTh hf hc hOP hN hx
      set σ1 := (((((σ.setv A (σ.val A - 1)).seth sIN (pre.length + 2 * (RepairRepresentation.natWord x).length)).sets
        t.1 (frame (RepairRepresentation.natWord x))).sets t.2.1 (List.replicate n true)).sets t.2.2
          (List.replicate L true)) with hσ1
      have hne : ∀ s, tmem s t → s ≠ sIN ∧ s ≠ sNT ∧ s ≠ sLT := by
        intro s hs
        rcases hs with h | h | h <;> subst h
        · exact ⟨fun e => hnI.1 e.symm, fun e => hnN.1 e.symm, fun e => hnL.1 e.symm⟩
        · exact ⟨fun e => hnI.2.1 e.symm, fun e => hnN.2.1 e.symm, fun e => hnL.2.1 e.symm⟩
        · exact ⟨fun e => hnI.2.2 e.symm, fun e => hnN.2.2 e.symm, fun e => hnL.2.2 e.symm⟩
      have keep : ∀ s, ¬ tmem s t → s ≠ sIN → σ1.st s = σ.st s ∧ σ1.sh s = σ.sh s := by
        intro s hs hsI
        simp only [tmem, not_or] at hs
        simp [hσ1, Function.update_apply, hs.1, hs.2.1, hs.2.2, hsI]
      have hIN1 : σ1.st sIN = σ.st sIN := by
        simp [hσ1, Function.update_apply, hnI.1, hnI.2.1, hnI.2.2]
      obtain ⟨τ, hτ, h1, h2, h3, h4, h5, h6, h7, h8⟩ := ih cs (pre ++ enc true (RepairRepresentation.natWord x)) rest σ1
        (by simpa using hlen) hokl hpw'.2
        (fun t' ht' => by
          obtain ⟨c1, c2, c3, c4, c5, c6⟩ := hbl t' (by simp [ht'])
          have hd := hpw'.1 t' ht'
          have k1 := keep t'.1 (fun h => hd t'.1 h (Or.inl rfl)) (fun e => (hok t' (by simp [ht'])).2.2.2.1 (Or.inl e.symm))
          have k2 := keep t'.2.1 (fun h => hd t'.2.1 h (Or.inr (Or.inl rfl)))
            (fun e => (hok t' (by simp [ht'])).2.2.2.1 (Or.inr (Or.inl e.symm)))
          have k3 := keep t'.2.2 (fun h => hd t'.2.2 h (Or.inr (Or.inr rfl)))
            (fun e => (hok t' (by simp [ht'])).2.2.2.1 (Or.inr (Or.inr e.symm)))
          exact ⟨k1.1.trans c1, k1.2.trans c2, k2.1.trans c3, k2.2.trans c4, k3.1.trans c5, k3.2.trans c6⟩)
        (by simp [hσ1, hA])
        (by rw [hIN1, hIN, enc_flatMap_cons]; simp [List.append_assoc])
        (by simp [hσ1, hINh, enc_length, stp])
        (by rw [(keep sNT (fun h => hnN.1 (by rcases h with h | h | h <;> [exact h; exact absurd h hnN.2.1; exact absurd h hnN.2.2]) ) (by decide)).1, hNT])
        (by rw [(keep sNT (fun h => by rcases h with h | h | h <;> [exact hnN.1 h; exact hnN.2.1 h; exact hnN.2.2 h]) (by decide)).2, hNTh])
        (by rw [(keep sLT (fun h => by rcases h with h | h | h <;> [exact hnL.1 h; exact hnL.2.1 h; exact hnL.2.2 h]) (by decide)).1, hLT])
        (by rw [(keep sLT (fun h => by rcases h with h | h | h <;> [exact hnL.1 h; exact hnL.2.1 h; exact hnL.2.2 h]) (by decide)).2, hLTh])
        (by simp [hσ1, Function.update_apply, hf, Ne.symm hAf])
        (by simp [hσ1, Function.update_apply, hc, Ne.symm hAc'])
        (by simp [hσ1, Function.update_apply, hOP, Ne.symm hAO])
        (by simp [hσ1, Function.update_apply, hN, Ne.symm hAN])
        (fun y hy => hcx y (by simp [hy])) (by simp at hcl ⊢; omega)
      refine ⟨τ, WExec.cast cap (WExec.seq s1 hτ) rfl (by simp [blocksCost]), h1, by rw [h2, hIN1], ?_, ?_, ?_, ?_, ?_,
        by rw [h8]; simp [hσ1]⟩
      · rw [h3]
        simp [enc_length, stp, List.flatMap_cons]
        ring
      · intro i h hl
        cases i with
        | zero =>
          simp only [List.get_eq_getElem, List.getElem_cons_zero]
          have hsd : ∀ s, tmem s t → τ.st s = σ1.st s ∧ τ.sh s = σ1.sh s := by
            intro s hs
            exact h6 s (fun t' ht' => hpw'.1 t' ht' s hs) (hne s hs).1
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [(hsd t.1 (Or.inl rfl)).1]; simp [hσ1, Function.update_apply, o01, o02]
          · rw [(hsd t.1 (Or.inl rfl)).2]; simp [hσ1, Function.update_apply, show t.1 ≠ sIN from fun h => hnI.1 h.symm, b2]
          · rw [(hsd t.2.1 (Or.inr (Or.inl rfl))).1]; simp [hσ1, Function.update_apply, o12]
          · rw [(hsd t.2.1 (Or.inr (Or.inl rfl))).2]; simp [hσ1, Function.update_apply, show t.2.1 ≠ sIN from fun h => hnI.2.1 h.symm, b4]
          · rw [(hsd t.2.2 (Or.inr (Or.inr rfl))).1]; simp [hσ1, Function.update_apply]
          · rw [(hsd t.2.2 (Or.inr (Or.inr rfl))).2]; simp [hσ1, Function.update_apply, show t.2.2 ≠ sIN from fun h => hnI.2.2 h.symm, b6]
        | succ i =>
          simp only [List.get_eq_getElem, List.getElem_cons_succ]
          have := h4 i (by simpa using h) (by simpa using hl)
          simpa using this
      · intro i hl hi
        cases i with
        | zero => simp at hi
        | succ i =>
          simp only [List.get_eq_getElem, List.getElem_cons_succ]
          have := h5 i (by simpa using hl) (by simpa using hi)
          simpa using this
      · intro s hs hsI
        have a1 := h6 s (fun t' ht' => hs t' (by simp [ht'])) hsI
        have a2 := keep s (hs t (by simp)) hsI
        exact ⟨a1.1.trans a2.1, a1.2.trans a2.2⟩
      · intro r hr
        rw [h7 r hr]
        simp [hσ1, Function.update_apply, hr]

end Slots

/-! ## The slots of the stage -/

/-- SYM slot `i`'s input streams. -/
def symTrip (i : Fin 4) : Trip := (sSym i 0, sSym i 1, sSym i 2)

/-- Carrier slot `k`'s input streams. -/
def carTrip (k : Fin 2) : Trip := (sCar k 0, sCar k 1, sCar k 2)

def symTrips : List Trip := [symTrip 0, symTrip 1, symTrip 2, symTrip 3]
def carTrips : List Trip := [carTrip 0, carTrip 1]

theorem low_ne_sSym (s : Fin (DS + 1)) (hs : s.val < 14) (i : Fin 4) (j : Fin 1789) : s ≠ sSym i j :=
  fun e => sSym_ne_low i j s hs e.symm

theorem low_ne_sCar (s : Fin (DS + 1)) (hs : s.val < 14) (k : Fin 2) (j : Fin 1357) : s ≠ sCar k j :=
  fun e => sCar_ne_low k j s hs e.symm

theorem symTrip_ok (i : Fin 4) : (symTrip i).ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [symTrip, tmem, not_or]
  · simp [sSym_eq_iff]
  · simp [sSym_eq_iff]
  · simp [sSym_eq_iff]
  · exact ⟨low_ne_sSym _ (by decide) _ _, low_ne_sSym _ (by decide) _ _, low_ne_sSym _ (by decide) _ _⟩
  · exact ⟨low_ne_sSym _ (by decide) _ _, low_ne_sSym _ (by decide) _ _, low_ne_sSym _ (by decide) _ _⟩
  · exact ⟨low_ne_sSym _ (by decide) _ _, low_ne_sSym _ (by decide) _ _, low_ne_sSym _ (by decide) _ _⟩

theorem carTrip_ok (k : Fin 2) : (carTrip k).ok := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [carTrip, tmem, not_or]
  · simp [sCar_eq_iff]
  · simp [sCar_eq_iff]
  · simp [sCar_eq_iff]
  · exact ⟨low_ne_sCar _ (by decide) _ _, low_ne_sCar _ (by decide) _ _, low_ne_sCar _ (by decide) _ _⟩
  · exact ⟨low_ne_sCar _ (by decide) _ _, low_ne_sCar _ (by decide) _ _, low_ne_sCar _ (by decide) _ _⟩
  · exact ⟨low_ne_sCar _ (by decide) _ _, low_ne_sCar _ (by decide) _ _, low_ne_sCar _ (by decide) _ _⟩

theorem symTrip_disj (i i' : Fin 4) (h : i ≠ i') : (symTrip i).disj (symTrip i') := by
  intro s hs hs'
  simp only [symTrip, tmem] at hs hs'
  rcases hs with rfl | rfl | rfl <;> rcases hs' with e | e | e <;> exact h ((sSym_eq_iff _ _ _ _).mp e).1

theorem carTrip_disj (k k' : Fin 2) (h : k ≠ k') : (carTrip k).disj (carTrip k') := by
  intro s hs hs'
  simp only [carTrip, tmem] at hs hs'
  rcases hs with rfl | rfl | rfl <;> rcases hs' with e | e | e <;> exact h ((sCar_eq_iff _ _ _ _).mp e).1

theorem symTrips_ok : ∀ t ∈ symTrips, t.ok := by
  intro t ht
  simp only [symTrips, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;> exact symTrip_ok _

theorem carTrips_ok : ∀ t ∈ carTrips, t.ok := by
  intro t ht
  simp only [carTrips, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> exact carTrip_ok _

theorem symTrips_pw : symTrips.Pairwise Trip.disj := by
  unfold symTrips
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)))
  all_goals
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  · rcases ht with rfl | rfl | rfl <;> exact symTrip_disj _ _ (by decide)
  · rcases ht with rfl | rfl <;> exact symTrip_disj _ _ (by decide)
  · subst ht; exact symTrip_disj _ _ (by decide)

theorem carTrips_pw : carTrips.Pairwise Trip.disj := by
  unfold carTrips
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ List.Pairwise.nil)
  all_goals
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  · subst ht; exact carTrip_disj _ _ (by decide)

theorem not_tmem_symTrip_of_car (k : Fin 2) (j : Fin 1357) (i : Fin 4) : ¬ tmem (sCar k j) (symTrip i) := by
  simp only [symTrip, tmem, not_or]
  exact ⟨fun e => sSym_ne_sCar _ _ _ _ e.symm, fun e => sSym_ne_sCar _ _ _ _ e.symm,
    fun e => sSym_ne_sCar _ _ _ _ e.symm⟩

/-! ## The inputs of every slot -/

/-- **The stage's input program**: skip `n`, the mode bit, read `a` into the SYM countdown, fill the SYM slots, read the
carrier count into the carrier countdown, fill the carrier slots. -/
def setupW : WM DS DR :=
  .seq (skipNatM true sIN rf rc) (.seq (.fwd sIN) (.seq (.fwd sIN) (.seq (readNatM true sIN rf rc rA rp rt)
    (.seq (blocks rA symTrips) (.seq (readNatM true sIN rf rc rK rp rt) (blocks rK carTrips))))))

/-- The request word's shape: `n`, the mode bit, `a`, the codes, the carriers' codes, any tail. -/
def reqW (n : ℕ) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) : List Bool :=
  RepairRepresentation.natWord n ++ [mb] ++ RepairRepresentation.natWord codes.length ++
    codes.flatMap RepairRepresentation.natWord ++ RepairRepresentation.natListWord cc ++ tl

/-- The input program's cost. -/
def setupCost (n L : ℕ) (codes cc : List ℕ) : ℕ :=
  20 * natBitLength n + 20 + 1 + (1 + 1 + (1 + 1 + ((natBitLength codes.length + 2) *
    (40 * 2 ^ natBitLength codes.length + 40) + 1 + (blocksCost n L symTrips codes + 1 +
    ((natBitLength cc.length + 2) * (40 * 2 ^ natBitLength cc.length + 40) + 1 + blocksCost n L carTrips cc)))))

theorem symTrips_get (i : ℕ) (hl : i < symTrips.length) :
    symTrips.get ⟨i, hl⟩ = symTrip ⟨i, by simpa [symTrips] using hl⟩ := by
  have : i < 4 := by simpa [symTrips] using hl
  interval_cases i <;> rfl

theorem carTrips_get (k : ℕ) (hl : k < carTrips.length) :
    carTrips.get ⟨k, hl⟩ = carTrip ⟨k, by simpa [carTrips] using hl⟩ := by
  have : k < 2 := by simpa [carTrips] using hl
  interval_cases k <;> rfl

theorem not_tmem_carTrip_of_sym (i : Fin 4) (j : Fin 1789) (k : Fin 2) : ¬ tmem (sSym i j) (carTrip k) := by
  simp only [carTrip, tmem, not_or]
  exact ⟨sSym_ne_sCar _ _ _ _, sSym_ne_sCar _ _ _ _, sSym_ne_sCar _ _ _ _⟩

theorem low_not_tmem_sym (s : Fin (DS + 1)) (hs : s.val < 14) (i : Fin 4) : ¬ tmem s (symTrip i) := by
  simp only [symTrip, tmem, not_or]
  exact ⟨low_ne_sSym s hs _ _, low_ne_sSym s hs _ _, low_ne_sSym s hs _ _⟩

theorem low_not_tmem_car (s : Fin (DS + 1)) (hs : s.val < 14) (k : Fin 2) : ¬ tmem s (carTrip k) := by
  simp only [carTrip, tmem, not_or]
  exact ⟨low_ne_sCar s hs _ _, low_ne_sCar s hs _ _, low_ne_sCar s hs _ _⟩

theorem enc_reqW (n : ℕ) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) :
    RepairOrdinary.frame (reqW n mb codes cc tl) =
      ParseNat.enc true (RepairRepresentation.natWord n) ++ (ParseNat.enc true [mb] ++
        (ParseNat.enc true (RepairRepresentation.natWord codes.length) ++
          (ParseNat.enc true (codes.flatMap RepairRepresentation.natWord) ++
            (ParseNat.enc true (RepairRepresentation.natWord cc.length) ++
              (ParseNat.enc true (cc.flatMap RepairRepresentation.natWord) ++ (ParseNat.enc true tl ++ [false])))))) := by
  rw [← RankBody.marks_frame]
  simp only [reqW, ParseNat.enc, ↓reduceIte, RepairRepresentation.natListWord, marks_append, List.append_assoc]

section Setup
variable (cap : ℕ)

/-- **The inputs of every slot**: from the framed request, `1^n`, `1^L` and blank slots, the first `a` SYM slots hold
the circuits' framed codes with `1^n`, `1^L`, the rest stay blank; the same for the carriers; nothing else changes
but the request's head and the two countdowns. -/
theorem setup_spec (n L : ℕ) (mb : Bool) (codes cc : List ℕ) (tl : List Bool) (σ : WState DS DR)
    (ha : codes.length ≤ 4) (hk : cc.length ≤ 2)
    (hIN : σ.st sIN = RepairOrdinary.frame (reqW n mb codes cc tl)) (hINh : σ.sh sIN = 0)
    (hNT : σ.st sNT = List.replicate n true) (hNTh : σ.sh sNT = 0)
    (hLT : σ.st sLT = List.replicate L true) (hLTh : σ.sh sLT = 0)
    (hbs : ∀ i, Blank σ (symTrip i)) (hbc : ∀ k, Blank σ (carTrip k))
    (hA : σ.val rA = 0) (hK : σ.val rK = 0) (hf : σ.val rf = 0) (hc : σ.val rc = 0) (hp : σ.val rp = 0)
    (ht : σ.val rt = 0) (hOP : σ.val rOP = 0) (hN : σ.val rN = 0)
    (hcapN : natBitLength n + 1 ≤ cap) (hcapA : 2 ^ (natBitLength codes.length + 1) ≤ cap)
    (hcapK : 2 ^ (natBitLength cc.length + 1) ≤ cap)
    (hcx : ∀ x ∈ codes, 2 * (RepairRepresentation.natWord x).length + 2 + n + L ≤ cap)
    (hcy : ∀ y ∈ cc, 2 * (RepairRepresentation.natWord y).length + 2 + n + L ≤ cap) (hc4 : 4 ≤ cap) :
    ∃ τ : WState DS DR, WExec cap setupW σ τ (setupCost n L codes cc) ∧
      (∀ i : Fin 4, ∀ h : i.val < codes.length, Done τ (symTrip i) (codes.get ⟨i.val, h⟩) n L) ∧
      (∀ i : Fin 4, codes.length ≤ i.val → Blank τ (symTrip i)) ∧
      (∀ k : Fin 2, ∀ h : k.val < cc.length, Done τ (carTrip k) (cc.get ⟨k.val, h⟩) n L) ∧
      (∀ k : Fin 2, cc.length ≤ k.val → Blank τ (carTrip k)) ∧
      (∀ s, (∀ i, ¬ tmem s (symTrip i)) → (∀ k, ¬ tmem s (carTrip k)) → s ≠ sIN →
        τ.st s = σ.st s ∧ τ.sh s = σ.sh s) ∧
      τ.st sIN = σ.st sIN ∧ (∀ r, r ≠ rA → r ≠ rK → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  have hIN' := hIN
  rw [enc_reqW] at hIN'
  -- 1: skip `n`
  have p1 := skipNatM_spec cap true sIN rf rc (by decide) n []
    (ParseNat.enc true [mb] ++ (ParseNat.enc true (RepairRepresentation.natWord codes.length) ++
      (ParseNat.enc true (codes.flatMap RepairRepresentation.natWord) ++
        (ParseNat.enc true (RepairRepresentation.natWord cc.length) ++
          (ParseNat.enc true (cc.flatMap RepairRepresentation.natWord) ++ (ParseNat.enc true tl ++ [false]))))))
    σ (by rw [hIN']; rfl) (by simp [hINh]) hf hc hcapN
  set σ1 := σ.seth sIN ([].length + stp true * (RepairRepresentation.natWord n).length) with hσ1
  -- 2: the mode bit
  have p2 := WExec.fwd (cap := cap) sIN σ1
  have p3 := WExec.fwd (cap := cap) sIN (σ1.seth sIN (σ1.sh sIN + 1))
  set σ2 := (σ1.seth sIN (σ1.sh sIN + 1)).seth sIN ((σ1.seth sIN (σ1.sh sIN + 1)).sh sIN + 1) with hσ2
  -- 3: read `a`
  have p4 := readNatM_spec cap true sIN rf rc rA rp rt (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) codes.length
    (ParseNat.enc true (RepairRepresentation.natWord n) ++ ParseNat.enc true [mb])
    (ParseNat.enc true (codes.flatMap RepairRepresentation.natWord) ++
      (ParseNat.enc true (RepairRepresentation.natWord cc.length) ++
        (ParseNat.enc true (cc.flatMap RepairRepresentation.natWord) ++ (ParseNat.enc true tl ++ [false])))) σ2
    (by simp [hσ2, hσ1, hIN', List.append_assoc])
    (by simp [hσ2, hσ1, ParseNat.enc_length, stp])
    (by simp [hσ2, hσ1, hf]) (by simp [hσ2, hσ1, hc]) (by simp [hσ2, hσ1, hp]) (by simp [hσ2, hσ1, ht])
    (by simp [hσ2, hσ1, hA]; omega)
  set pre4 := ParseNat.enc true (RepairRepresentation.natWord n) ++ ParseNat.enc true [mb] ++
    ParseNat.enc true (RepairRepresentation.natWord codes.length) with hpre4
  set σ3 := (σ2.seth sIN ((ParseNat.enc true (RepairRepresentation.natWord n) ++ ParseNat.enc true [mb]).length +
    stp true * (RepairRepresentation.natWord codes.length).length)).setv rA (σ2.val rA + codes.length) with hσ3
  have e3st : ∀ s, σ3.st s = σ.st s := fun s => by simp [hσ3, hσ2, hσ1]
  have e3sh : ∀ s, s ≠ sIN → σ3.sh s = σ.sh s := fun s hs => by simp [hσ3, hσ2, hσ1, Function.update_apply, hs]
  have e3v : ∀ r, r ≠ rA → σ3.val r = σ.val r := fun r hr => by simp [hσ3, hσ2, hσ1, Function.update_apply, hr]
  -- 4: the SYM slots
  obtain ⟨τ4, q4, a4, b4, c4, d4, f4, g4, h4, i4⟩ := blocks_spec cap rA (by decide) (by decide) (by decide)
    (by decide) n L symTrips codes pre4
    (ParseNat.enc true (RepairRepresentation.natWord cc.length) ++ (ParseNat.enc true (cc.flatMap
      RepairRepresentation.natWord) ++ (ParseNat.enc true tl ++ [false]))) σ3
    (by simpa [symTrips] using ha) symTrips_ok symTrips_pw
    (fun t htm => by
      simp only [symTrips, List.mem_cons, List.not_mem_nil, or_false] at htm
      have key : ∀ i, Blank σ3 (symTrip i) := by
        intro i
        obtain ⟨b1, b2, b3, b4, b5, b6⟩ := hbs i
        simp only [Blank, symTrip] at b1 b2 b3 b4 b5 b6 ⊢
        refine ⟨by rw [e3st, b1], by rw [e3sh _ (low_ne_sSym _ (by decide) _ _).symm, b2], by rw [e3st, b3],
          by rw [e3sh _ (low_ne_sSym _ (by decide) _ _).symm, b4], by rw [e3st, b5],
          by rw [e3sh _ (low_ne_sSym _ (by decide) _ _).symm, b6]⟩
      rcases htm with rfl | rfl | rfl | rfl <;> exact key _)
    (by simp [hσ3, hσ2, hσ1, hA])
    (by rw [e3st, hIN']; simp [hpre4, List.append_assoc])
    (by simp [hσ3, hσ2, hσ1, hpre4, ParseNat.enc_length, stp]; ring)
    (by rw [e3st, hNT]) (by rw [e3sh _ (by decide), hNTh]) (by rw [e3st, hLT]) (by rw [e3sh _ (by decide), hLTh])
    (by rw [e3v _ (by decide), hf]) (by rw [e3v _ (by decide), hc]) (by rw [e3v _ (by decide), hOP])
    (by rw [e3v _ (by decide), hN]) hcx (by omega)
  -- 5: read the carrier count
  have p5 := readNatM_spec cap true sIN rf rc rK rp rt (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) cc.length
    (pre4 ++ ParseNat.enc true (codes.flatMap RepairRepresentation.natWord))
    (ParseNat.enc true (cc.flatMap RepairRepresentation.natWord) ++ (ParseNat.enc true tl ++ [false])) τ4
    (by rw [b4, e3st, hIN']; simp [hpre4, List.append_assoc])
    (by rw [c4]; simp [ParseNat.enc_length, stp])
    (by rw [h4 _ (by decide), e3v _ (by decide), hf]) (by rw [h4 _ (by decide), e3v _ (by decide), hc])
    (by rw [h4 _ (by decide), e3v _ (by decide), hp]) (by rw [h4 _ (by decide), e3v _ (by decide), ht])
    (by rw [h4 _ (by decide), e3v _ (by decide), hK]; omega)
  set pre6 := pre4 ++ ParseNat.enc true (codes.flatMap RepairRepresentation.natWord) ++
    ParseNat.enc true (RepairRepresentation.natWord cc.length) with hpre6
  set σ5 := (τ4.seth sIN ((pre4 ++ ParseNat.enc true (codes.flatMap RepairRepresentation.natWord)).length +
    stp true * (RepairRepresentation.natWord cc.length).length)).setv rK (τ4.val rK + cc.length) with hσ5
  have e5st : ∀ s, σ5.st s = τ4.st s := fun s => by simp [hσ5]
  have e5sh : ∀ s, s ≠ sIN → σ5.sh s = τ4.sh s := fun s hs => by simp [hσ5, Function.update_apply, hs]
  have e5v : ∀ r, r ≠ rK → σ5.val r = τ4.val r := fun r hr => by simp [hσ5, Function.update_apply, hr]
  -- the stream facts before the carrier slots
  have keep4 : ∀ s, (∀ i, ¬ tmem s (symTrip i)) → s ≠ sIN → τ4.st s = σ.st s ∧ τ4.sh s = σ.sh s := by
    intro s hs hsI
    have := g4 s (fun t htm => by
      simp only [symTrips, List.mem_cons, List.not_mem_nil, or_false] at htm
      rcases htm with rfl | rfl | rfl | rfl <;> exact hs _) hsI
    rw [this.1, this.2, e3st, e3sh _ hsI]
    exact ⟨rfl, rfl⟩
  -- 6: the carrier slots
  obtain ⟨τ6, q6, a6, b6, c6, d6, f6, g6, h6, i6⟩ := blocks_spec cap rK (by decide) (by decide) (by decide)
    (by decide) n L carTrips cc pre6 (ParseNat.enc true tl ++ [false]) σ5
    (by simpa [carTrips] using hk) carTrips_ok carTrips_pw
    (fun t htm => by
      simp only [carTrips, List.mem_cons, List.not_mem_nil, or_false] at htm
      have key : ∀ k, Blank σ5 (carTrip k) := by
        intro k
        obtain ⟨b1, b2, b3, b4', b5, b6'⟩ := hbc k
        simp only [Blank, carTrip] at b1 b2 b3 b4' b5 b6' ⊢
        have k0 := keep4 (sCar k 0) (fun i => not_tmem_symTrip_of_car _ _ _) (low_ne_sCar _ (by decide) _ _).symm
        have k1 := keep4 (sCar k 1) (fun i => not_tmem_symTrip_of_car _ _ _) (low_ne_sCar _ (by decide) _ _).symm
        have k2 := keep4 (sCar k 2) (fun i => not_tmem_symTrip_of_car _ _ _) (low_ne_sCar _ (by decide) _ _).symm
        refine ⟨by rw [e5st, k0.1, b1], by rw [e5sh _ (low_ne_sCar _ (by decide) _ _).symm, k0.2, b2],
          by rw [e5st, k1.1, b3], by rw [e5sh _ (low_ne_sCar _ (by decide) _ _).symm, k1.2, b4'],
          by rw [e5st, k2.1, b5], by rw [e5sh _ (low_ne_sCar _ (by decide) _ _).symm, k2.2, b6']⟩
      rcases htm with rfl | rfl <;> exact key _)
    (by simp [hσ5, h4 rK (by decide), e3v rK (by decide), hK])
    (by rw [e5st, b4, e3st, hIN']; simp [hpre6, hpre4, List.append_assoc])
    (by simp [hσ5, hpre6, ParseNat.enc_length, stp]; ring)
    (by rw [e5st, (keep4 sNT (fun i => low_not_tmem_sym _ (by decide) i) (by decide)).1, hNT])
    (by rw [e5sh _ (by decide), (keep4 sNT (fun i => low_not_tmem_sym _ (by decide) i) (by decide)).2, hNTh])
    (by rw [e5st, (keep4 sLT (fun i => low_not_tmem_sym _ (by decide) i) (by decide)).1, hLT])
    (by rw [e5sh _ (by decide), (keep4 sLT (fun i => low_not_tmem_sym _ (by decide) i) (by decide)).2, hLTh])
    (by rw [e5v _ (by decide), h4 _ (by decide), e3v _ (by decide), hf])
    (by rw [e5v _ (by decide), h4 _ (by decide), e3v _ (by decide), hc])
    (by rw [e5v _ (by decide), h4 _ (by decide), e3v _ (by decide), hOP])
    (by rw [e5v _ (by decide), h4 _ (by decide), e3v _ (by decide), hN]) hcy (by omega)
  refine ⟨τ6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have w := WExec.seq p1 (WExec.seq p2 (WExec.seq p3 (WExec.seq p4 (WExec.seq q4 (WExec.seq p5 q6)))))
    exact WExec.cast cap w rfl (by unfold setupCost; omega)
  · intro i h
    have hd := d4 i.val h (by simp [symTrips])
    rw [symTrips_get] at hd
    obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hd
    have k0 := g6 (sSym i 0) (fun t htm => by
      simp only [carTrips, List.mem_cons, List.not_mem_nil, or_false] at htm
      rcases htm with rfl | rfl <;> exact not_tmem_carTrip_of_sym _ _ _) (low_ne_sSym _ (by decide) _ _).symm
    have k1 := g6 (sSym i 1) (fun t htm => by
      simp only [carTrips, List.mem_cons, List.not_mem_nil, or_false] at htm
      rcases htm with rfl | rfl <;> exact not_tmem_carTrip_of_sym _ _ _) (low_ne_sSym _ (by decide) _ _).symm
    have k2 := g6 (sSym i 2) (fun t htm => by
      simp only [carTrips, List.mem_cons, List.not_mem_nil, or_false] at htm
      rcases htm with rfl | rfl <;> exact not_tmem_carTrip_of_sym _ _ _) (low_ne_sSym _ (by decide) _ _).symm
    simp only [symTrip] at x1 x2 x3 x4 x5 x6 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [k0.1, e5st, x1]
    · rw [k0.2, e5sh _ (low_ne_sSym _ (by decide) _ _).symm, x2]
    · rw [k1.1, e5st, x3]
    · rw [k1.2, e5sh _ (low_ne_sSym _ (by decide) _ _).symm, x4]
    · rw [k2.1, e5st, x5]
    · rw [k2.2, e5sh _ (low_ne_sSym _ (by decide) _ _).symm, x6]
  · intro i h
    have hd := f4 i.val (by simp [symTrips]) h
    rw [symTrips_get] at hd
    obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hd
    have k0 := g6 (sSym i 0) (fun t htm => by
      simp only [carTrips, List.mem_cons, List.not_mem_nil, or_false] at htm
      rcases htm with rfl | rfl <;> exact not_tmem_carTrip_of_sym _ _ _) (low_ne_sSym _ (by decide) _ _).symm
    have k1 := g6 (sSym i 1) (fun t htm => by
      simp only [carTrips, List.mem_cons, List.not_mem_nil, or_false] at htm
      rcases htm with rfl | rfl <;> exact not_tmem_carTrip_of_sym _ _ _) (low_ne_sSym _ (by decide) _ _).symm
    have k2 := g6 (sSym i 2) (fun t htm => by
      simp only [carTrips, List.mem_cons, List.not_mem_nil, or_false] at htm
      rcases htm with rfl | rfl <;> exact not_tmem_carTrip_of_sym _ _ _) (low_ne_sSym _ (by decide) _ _).symm
    simp only [symTrip] at x1 x2 x3 x4 x5 x6 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [k0.1, e5st, x1]
    · rw [k0.2, e5sh _ (low_ne_sSym _ (by decide) _ _).symm, x2]
    · rw [k1.1, e5st, x3]
    · rw [k1.2, e5sh _ (low_ne_sSym _ (by decide) _ _).symm, x4]
    · rw [k2.1, e5st, x5]
    · rw [k2.2, e5sh _ (low_ne_sSym _ (by decide) _ _).symm, x6]
  · intro k h
    have hd := d6 k.val h (by have := k.isLt; simp [carTrips]; omega)
    rw [carTrips_get] at hd
    exact hd
  · intro k h
    have hd := f6 k.val (by have := k.isLt; simp [carTrips]; omega) h
    rw [carTrips_get] at hd
    exact hd
  · intro s hs hs' hsI
    have k6 := g6 s (fun t htm => by
      simp only [carTrips, List.mem_cons, List.not_mem_nil, or_false] at htm
      rcases htm with rfl | rfl <;> exact hs' _) hsI
    have k4 := keep4 s hs hsI
    rw [k6.1, k6.2, e5st, e5sh _ hsI]
    exact k4
  · rw [b6, e5st, b4, e3st]
  · intro r hrA hrK
    rw [h6 r hrK, e5v r hrK, h4 r hrA, e3v r hrA]
  · rw [i6]
    simp [hσ5, i4, hσ3, hσ2, hσ1]

end Setup

end NearCubicWires.WireExponent3_5.PrimAsm.Data
