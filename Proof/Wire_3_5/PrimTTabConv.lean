import Proof.Wire_3_5.PrimTTabRef
import Proof.Wire_3_5.FinalPassWordMap

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Corner

section Conv
variable {ns nr : ℕ} (cap : ℕ)

/-! ## Moves -/

/-- `τ` is `σ` with the input head at `pI`, `w` appended to the output (head at its end), the ruler head at `pR`,
the registers `c, f` at `cv, fv`, and nothing else changed. -/
structure Mv (I O R : Fin (ns + 1)) (c f : Fin nr) (σ τ : WState ns nr) (pI : ℕ) (w : List Bool)
    (pR cv fv : ℕ) : Prop where
  sI : τ.st I = σ.st I
  hI : τ.sh I = pI
  sO : τ.st O = σ.st O ++ w
  hO : τ.sh O = (τ.st O).length
  sR : τ.st R = σ.st R
  hR : τ.sh R = pR
  vc : τ.val c = cv
  vf : τ.val f = fv
  fr : WFrame (fun i => i = I ∨ i = O ∨ i = R) (fun r => r = c ∨ r = f) σ τ

theorem Mv.trans {I O R : Fin (ns + 1)} {c f : Fin nr} {σ τ ρ : WState ns nr} {pI pI' pR pR' cv cv' fv fv' : ℕ}
    {w w' : List Bool} (h1 : Mv I O R c f σ τ pI w pR cv fv) (h2 : Mv I O R c f τ ρ pI' w' pR' cv' fv') :
    Mv I O R c f σ ρ pI' (w ++ w') pR' cv' fv' :=
  ⟨h2.sI.trans h1.sI, h2.hI, by rw [h2.sO, h1.sO, List.append_assoc], h2.hO, h2.sR.trans h1.sR, h2.hR, h2.vc, h2.vf,
    h1.fr.trans h2.fr⟩

theorem Mv.refl (I O R : Fin (ns + 1)) (c f : Fin nr) (σ : WState ns nr) (hO : σ.sh O = (σ.st O).length) :
    Mv I O R c f σ σ (σ.sh I) [] (σ.sh R) (σ.val c) (σ.val f) :=
  ⟨rfl, rfl, by simp, hO, rfl, rfl, rfl, rfl, WFrame.refl _ _ σ⟩

theorem Mv.trans_eq {I O R : Fin (ns + 1)} {c f : Fin nr} {σ τ ρ : WState ns nr} {pI pI' pR pR' cv cv' fv fv' qI qR qc qf : ℕ}
    {w w' u : List Bool} (h1 : Mv I O R c f σ τ pI w pR cv fv) (h2 : Mv I O R c f τ ρ pI' w' pR' cv' fv')
    (e1 : pI' = qI) (e2 : w ++ w' = u) (e3 : pR' = qR) (e4 : cv' = qc) (e5 : fv' = qf) :
    Mv I O R c f σ ρ qI u qR qc qf := by
  subst e1 e2 e3 e4 e5; exact h1.trans h2

/-! ## Reading framed words -/

theorem rd_shift (pre l : List Bool) (j : ℕ) : readTapeBit (pre ++ l) (pre.length + j) = readTapeBit l j := by
  unfold readTapeBit
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp

theorem rd_marker (pre bs rest : List Bool) (j : ℕ) (hj : j < bs.length) :
    readTapeBit (pre ++ (frameP bs ++ rest)) (pre.length + 2 * j) = true := by
  rw [rd_shift]; exact readTapeBit_frameP_marker bs rest j hj

theorem rd_bit (pre bs rest : List Bool) (j : ℕ) (hj : j < bs.length) :
    readTapeBit (pre ++ (frameP bs ++ rest)) (pre.length + (2 * j + 1)) = bs.getD j false := by
  rw [rd_shift]; exact readTapeBit_frameP bs rest j hj

/-! ## The programs -/

/-- Write one cell at the end of a stream and step past it. -/
def emitW (O : Fin (ns + 1)) (b : Bool) : WM ns nr := .seq (.wr O b) (.fwd O)

def o3 (out : Bool → Bool → Bool) : Bool → Bool → Bool → Bool := fun a _ c => out a c
def n3 (nxt : Bool → Bool → Bool) : Bool → Bool → Bool → Bool := fun a _ c => nxt a c

/-- One source bit through the carry map: from the input while `c ≠ 0`, else `false`. -/
def srcBit (I O : Fin (ns + 1)) (c f : Fin nr) (out nxt : Bool → Bool → Bool) : WM ns nr :=
  .ifr c (.seq (.fwd I) (.seq (.ifs I (leaf (o3 out) (n3 nxt) O f true false) (leaf (o3 out) (n3 nxt) O f false false))
    (.seq (.fwd I) (.dec c))))
    (leaf (o3 out) (n3 nxt) O f false false)

/-- One ruler cell: a marker and one mapped bit. -/
def cellW (I O R : Fin (ns + 1)) (c f : Fin nr) (out nxt : Bool → Bool → Bool) : WM ns nr :=
  .seq (emitW O true) (.seq (srcBit I O c f out nxt) (.seq (.fwd O) (.fwd R)))

/-- **One `h`-bit framed word** along the ruler `false :: 1^h`; the ruler returns to its sentinel, the carry to `0`. -/
def wordW (I O R : Fin (ns + 1)) (c f : Fin nr) (out nxt : Bool → Bool → Bool) : WM ns nr :=
  .seq (.fwd R) (.seq (.whs R (cellW I O R c f out nxt)) (.seq (emitW O false) (.seq (.bwd R)
    (.seq (.whs R (.bwd R)) (WM.clear f)))))

/-- Count the unary length of a framed `natWord`; stop at the marker of its first bit. -/
def countW (I : Fin (ns + 1)) (c : Fin nr) : WM ns nr :=
  .seq (.fwd I) (.seq (.whs I (.seq (.fwd I) (.seq (.fwd I) (.inc c)))) (.fwd I))

/-- Skip a framed `natWord`. -/
def skipNatW (I : Fin (ns + 1)) (c : Fin nr) : WM ns nr :=
  .seq (countW I c) (.whr c (.seq (.fwd I) (.seq (.fwd I) (.dec c))))

/-- A framed `natWord` as an `h`-bit framed word through a carry map. -/
def convNatW (I O R : Fin (ns + 1)) (c f : Fin nr) (out nxt : Bool → Bool → Bool) : WM ns nr :=
  .seq (countW I c) (wordW I O R c f out nxt)

/-- The `h`-bit framed zero word. -/
def zeroW (I O R : Fin (ns + 1)) (c f : Fin nr) : WM ns nr := wordW I O R c f cpyOut cpyNxt

/-- Skip a framed `intWord`. -/
def skipIntW (I : Fin (ns + 1)) (c : Fin nr) : WM ns nr := .seq (.fwd I) (.seq (.fwd I) (skipNatW I c))

/-- **A weight's pair** from its framed `intWord`. -/
def convIntW (I O R : Fin (ns + 1)) (c f : Fin nr) : WM ns nr :=
  .seq (.fwd I) (.ifs I (.seq (.fwd I) (.seq (zeroW I O R c f) (convNatW I O R c f cpyOut cpyNxt)))
    (.seq (.fwd I) (.seq (convNatW I O R c f cpyOut cpyNxt) (zeroW I O R c f))))

/-- **The pair of `−θ`** from the framed `intWord` of `t = θ − 1`: `(|t| − 1, 0)` if `t < 0`, else `(0, t + 1)`. -/
def convThrW (I O R : Fin (ns + 1)) (c f : Fin nr) : WM ns nr :=
  .seq (.fwd I) (.ifs I (.seq (.fwd I) (.seq (.inc f) (.seq (convNatW I O R c f decOut decNxt) (zeroW I O R c f))))
    (.seq (.fwd I) (.seq (zeroW I O R c f) (.seq (.inc f) (convNatW I O R c f incOut incNxt)))))

/-! ## Emitting -/

theorem emitW_spec (O : Fin (ns + 1)) (b : Bool) (σ : WState ns nr) (hO : σ.sh O = (σ.st O).length) :
    WExec cap (emitW O b) σ ((σ.sets O (σ.st O ++ [b])).seth O ((σ.st O).length + 1)) 3 := by
  have h1 := WExec.wr (cap := cap) O b σ
  rw [hO, writeTapeBit_end'] at h1
  have h2 := WExec.fwd (cap := cap) O (σ.sets O (σ.st O ++ [b]))
  exact WExec.mono (WExec.seq h1 (by simpa [hO] using h2)) (by omega)

/-- The carry after a carry map. -/
def cfin (nxt : Bool → Bool → Bool) : List Bool → Bool → Bool
  | [], c => c
  | b :: bs, c => cfin nxt bs (nxt b c)

/-! ## Returning the ruler -/

theorem rewindR_spec (R : Fin (ns + 1)) : ∀ (m : ℕ) (σ : WState ns nr), σ.sh R = m →
    (∀ j, 1 ≤ j → j ≤ m → readTapeBit (σ.st R) j = true) → readTapeBit (σ.st R) 0 = false →
    WExec cap (.whs R (.bwd R)) σ (σ.seth R 0) (3 * m + 1)
  | 0, σ, hm, _, h0 => by
    have e : σ.seth R 0 = σ := by rw [← hm]; exact wseth_same σ R
    rw [e]; exact WExec.whsF (by simpa [wbit, hm] using h0)
  | m + 1, σ, hm, hT, h0 => by
    have s1 := WExec.bwd (cap := cap) R σ
    have s2 := rewindR_spec R m (σ.seth R (σ.sh R - 1)) (by simp [hm]) (fun j h1 h2 => by simpa using hT j h1 (by omega))
      (by simpa using h0)
    rw [wseth_seth] at s2
    exact WExec.mono (WExec.whsT (by simpa [wbit, hm] using hT (m + 1) (by omega) le_rfl) s1 s2) (by omega)

/-- The ruler `false :: 1^h`, read from cell `1 + j`. -/
theorem ruler_read (h j : ℕ) : readTapeBit (false :: List.replicate h true) (1 + j) = decide (j < h) := by
  unfold readTapeBit
  rw [show 1 + j = j + 1 by omega, List.getD_cons_succ]
  by_cases hj : j < h
  · rw [List.getD_eq_getElem _ _ (by simpa using hj)]; simp [hj]
  · rw [List.getD_eq_default _ _ (by simpa using hj)]; simp [hj]

theorem ruler_read0 (h : ℕ) : readTapeBit (false :: List.replicate h true) 0 = false := rfl

theorem natWord_getD_lt (v i : ℕ) (hi : i < natBitLength v) : (natWord v).getD i false = true := by
  rw [CompilerMachine.Pool.natWord_eq, List.getD_append _ _ _ _ (by simpa using hi)]
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]; simp

theorem natWord_getD_k (v : ℕ) : (natWord v).getD (natBitLength v) false = false := by
  rw [CompilerMachine.Pool.natWord_eq, List.getD_append_right _ _ _ _ (by simp)]
  simp

theorem countLoop_spec (I : Fin (ns + 1)) (c : Fin nr) : ∀ (m : ℕ) (σ : WState ns nr), (∀ i < m, readTapeBit (σ.st I) (σ.sh I + 2 * i) = true) →
    readTapeBit (σ.st I) (σ.sh I + 2 * m) = false → σ.val c + m ≤ cap →
    WExec cap (.whs I (.seq (.fwd I) (.seq (.fwd I) (.inc c)))) σ ((σ.seth I (σ.sh I + 2 * m)).setv c (σ.val c + m))
      (m * 9 + 1)
  | 0, σ, _, hz, _ => by
    have e : (σ.seth I (σ.sh I + 2 * 0)).setv c (σ.val c + 0) = σ := by
      simp only [Nat.mul_zero, Nat.add_zero, wseth_same]; exact wsetv_same σ c
    rw [e]; exact WExec.whsF (by simpa [wbit] using hz)
  | m + 1, σ, hT, hz, hcap => by
    have s1 := WExec.fwd (cap := cap) I σ
    have s2 := WExec.fwd (cap := cap) I (σ.seth I (σ.sh I + 1))
    have s3 := WExec.inc (cap := cap) c ((σ.seth I (σ.sh I + 1)).seth I ((σ.seth I (σ.sh I + 1)).sh I + 1))
      (by simp; omega)
    set σ3 := ((σ.seth I (σ.sh I + 1)).seth I ((σ.seth I (σ.sh I + 1)).sh I + 1)).setv c (σ.val c + 1) with hσ3
    have e3 : ((σ.seth I (σ.sh I + 1)).seth I ((σ.seth I (σ.sh I + 1)).sh I + 1)).setv c
        (((σ.seth I (σ.sh I + 1)).seth I ((σ.seth I (σ.sh I + 1)).sh I + 1)).val c + 1) = σ3 := by
      rw [hσ3]; simp
    rw [e3] at s3
    have h3I : σ3.sh I = σ.sh I + 2 := by simp [hσ3]
    have h3s : σ3.st I = σ.st I := by simp [hσ3]
    have h3c : σ3.val c = σ.val c + 1 := by simp [hσ3]
    have ih := countLoop_spec I c m σ3 (fun i hi => by
        rw [h3s, h3I, show σ.sh I + 2 + 2 * i = σ.sh I + 2 * (i + 1) by omega]; exact hT _ (by omega)) (by rw [h3s, h3I, show σ.sh I + 2 + 2 * m = σ.sh I + 2 * (m + 1) by omega]; exact hz)
      (by rw [h3c]; omega)
    have e : (σ3.seth I (σ3.sh I + 2 * m)).setv c (σ3.val c + m) =
        (σ.seth I (σ.sh I + 2 * (m + 1))).setv c (σ.val c + (m + 1)) := by
      rw [h3I, h3c, show σ.sh I + 2 + 2 * m = σ.sh I + 2 * (m + 1) by omega,
        show σ.val c + 1 + m = σ.val c + (m + 1) by omega]
      apply WState.eq <;> simp [hσ3]
    rw [e] at ih
    have hw : wbit σ I = true := by simpa [wbit] using hT 0 (by omega)
    exact WExec.mono (WExec.whsT hw (WExec.seq s1 (WExec.seq s2 s3)) ih) (by rw [Nat.succ_mul]; omega)

theorem skipLoop_spec (I : Fin (ns + 1)) (c : Fin nr) : ∀ (m : ℕ) (σ : WState ns nr), σ.val c = m → m ≤ cap →
    WExec cap (.whr c (.seq (.fwd I) (.seq (.fwd I) (.dec c)))) σ ((σ.seth I (σ.sh I + 2 * m)).setv c 0) (m * 7 + 1)
  | 0, σ, hm, _ => by
    have e : (σ.seth I (σ.sh I + 2 * 0)).setv c 0 = σ := by
      simp only [Nat.mul_zero, Nat.add_zero, wseth_same]; rw [← hm]; exact wsetv_same σ c
    rw [e]; exact WExec.whrF hm
  | m + 1, σ, hm, hcap => by
    have s1 := WExec.fwd (cap := cap) I σ
    have s2 := WExec.fwd (cap := cap) I (σ.seth I (σ.sh I + 1))
    have s3 := WExec.dec (cap := cap) c ((σ.seth I (σ.sh I + 1)).seth I ((σ.seth I (σ.sh I + 1)).sh I + 1))
      (by simp; omega)
    set σ3 := ((σ.seth I (σ.sh I + 1)).seth I ((σ.seth I (σ.sh I + 1)).sh I + 1)).setv c m with hσ3
    have e3 : ((σ.seth I (σ.sh I + 1)).seth I ((σ.seth I (σ.sh I + 1)).sh I + 1)).setv c
        (((σ.seth I (σ.sh I + 1)).seth I ((σ.seth I (σ.sh I + 1)).sh I + 1)).val c - 1) = σ3 := by
      rw [hσ3]; simp [hm]
    rw [e3] at s3
    have h3I : σ3.sh I = σ.sh I + 2 := by simp [hσ3]
    have ih := skipLoop_spec I c m σ3 (by simp [hσ3]) (by omega)
    have e : (σ3.seth I (σ3.sh I + 2 * m)).setv c 0 = (σ.seth I (σ.sh I + 2 * (m + 1))).setv c 0 := by
      rw [h3I, show σ.sh I + 2 + 2 * m = σ.sh I + 2 * (m + 1) by omega]
      apply WState.eq <;> simp [hσ3]
    rw [e] at ih
    exact WExec.mono (WExec.whrT (by omega) (WExec.seq s1 (WExec.seq s2 s3)) ih) (by rw [Nat.succ_mul]; omega)

def countCost (k : ℕ) : ℕ := 9 * k + 5

def wordCost (h : ℕ) : ℕ := 30 * h + 20

theorem frameP_intWord (z : ℤ) : frameP (intWord z) = true :: decide (z < 0) :: frameP (natWord z.natAbs) := rfl

def convIntCost (k h : ℕ) : ℕ := countCost k + 2 * wordCost h + 10

theorem ifsLeaf_spec (I O : Fin (ns + 1)) (f : Fin nr) (out nxt : Bool → Bool → Bool) (b cy : Bool)
    (σ : WState ns nr) (hb : wbit σ I = b) (hf : σ.val f = cy.toNat) (hcap : 1 ≤ cap) :
    WExec cap (.ifs I (leaf (o3 out) (n3 nxt) O f true false) (leaf (o3 out) (n3 nxt) O f false false)) σ
      ((σ.sets O (writeTapeBit (σ.st O) (σ.sh O) (out b cy))).setv f (nxt b cy).toNat) 8 := by
  cases b
  · exact WExec.mono (WExec.ifsF hb (leaf_spec cap (o3 out) (n3 nxt) O f false false cy σ hf hcap)) (by omega)
  · exact WExec.mono (WExec.ifsT hb (leaf_spec cap (o3 out) (n3 nxt) O f true false cy σ hf hcap)) (by omega)

/-! ## One ruler cell -/

section Cell
variable (I O R : Fin (ns + 1)) (c f : Fin nr) (out nxt : Bool → Bool → Bool)
  (hIO : I ≠ O) (hIR : I ≠ R) (hOR : O ≠ R) (hcf : c ≠ f)
include hIO hIR hOR hcf

/-- A cell whose bit comes from the input. -/
theorem cellB_spec (hcap : 1 ≤ cap) (pre rest : List Bool) (b : Bool) (bs : List Bool) (cy : Bool) (k : ℕ)
    (σ : WState ns nr) (hI : σ.st I = pre ++ (frameP (b :: bs) ++ rest)) (hIh : σ.sh I = pre.length)
    (hc : σ.val c = k + 1) (hck : k + 1 ≤ cap) (hf : σ.val f = cy.toNat) (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (cellW I O R c f out nxt) σ τ 23 ∧
      Mv I O R c f σ τ (pre.length + 2) [true, out b cy] (σ.sh R + 1) k (nxt b cy).toNat := by
  have hOI : O ≠ I := fun h => hIO h.symm
  have hRI : R ≠ I := fun h => hIR h.symm
  have hRO : R ≠ O := fun h => hOR h.symm
  have hfc : f ≠ c := fun h => hcf h.symm
  have s1 := emitW_spec cap O true σ hO
  set σ1 := (σ.sets O (σ.st O ++ [true])).seth O ((σ.st O).length + 1) with hσ1
  have s2 := WExec.fwd (cap := cap) I σ1
  set σ2 := σ1.seth I (σ1.sh I + 1) with hσ2
  have hb : wbit σ2 I = b := by
    simp only [wbit, hσ2, hσ1, WState.seth_st, WState.seth_sh, WState.sets_st, WState.sets_sh, Function.update_self,
      Function.update_of_ne hIO, hI, hIh]
    have := rd_bit pre (b :: bs) rest 0 (by simp)
    simpa using this
  have s3 := ifsLeaf_spec cap I O f out nxt b cy σ2 hb (by simp [hσ2, hσ1, hf]) hcap
  set σ3 := (σ2.sets O (writeTapeBit (σ2.st O) (σ2.sh O) (out b cy))).setv f (nxt b cy).toNat with hσ3
  have s4 := WExec.fwd (cap := cap) I σ3
  set σ4 := σ3.seth I (σ3.sh I + 1) with hσ4
  have s5 := WExec.dec (cap := cap) c σ4 (by simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hcf, hc]; omega)
  set σ5 := σ4.setv c (σ4.val c - 1) with hσ5
  have s6 := WExec.fwd (cap := cap) O σ5
  set σ6 := σ5.seth O (σ5.sh O + 1) with hσ6
  have s7 := WExec.fwd (cap := cap) R σ6
  have hcnz : σ1.val c ≠ 0 := by simp [hσ1, hc]
  have run : WExec cap (cellW I O R c f out nxt) σ (σ6.seth R (σ6.sh R + 1)) _ :=
    WExec.seq s1 (WExec.seq (WExec.ifrT hcnz (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5))))
    (WExec.seq s6 s7))
  refine ⟨_, WExec.mono run (by omega), ?_⟩
  have hw : writeTapeBit (σ2.st O) (σ2.sh O) (out b cy) = σ.st O ++ [true, out b cy] := by
    simp only [hσ2, hσ1, WState.seth_st, WState.seth_sh, WState.sets_st, Function.update_self,
      Function.update_of_ne hOI]
    have := writeTapeBit_end' (σ.st O ++ [true]) (out b cy)
    simpa using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hIO, Function.update_of_ne hIR]
  · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hIO, Function.update_of_ne hIR,
      Function.update_of_ne hOI, hIh]
  · simp only [hσ6, hσ5, hσ4, WState.seth_st, WState.setv_st, Function.update_of_ne hRO]
    rw [hσ3]; simp only [WState.setv_st, WState.sets_st, Function.update_self]
    rw [hw]
  · simp only [hσ6, hσ5, hσ4, WState.seth_st, WState.seth_sh, WState.setv_st, WState.setv_sh,
      Function.update_of_ne hRO, Function.update_self]
    rw [hσ3]; simp only [WState.setv_st, WState.setv_sh, WState.sets_st, WState.sets_sh, Function.update_self]
    rw [hw]
    simp [hσ2, hσ1, Function.update_of_ne hOI, Function.update_of_ne hOR]
  · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hRO, Function.update_of_ne hRI]
  · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hRO, Function.update_of_ne hRI]
  · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hcf, hc]
  · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hfc]
  · refine ⟨fun i hi => ?_, fun r hr => ?_, ?_⟩
    · have h1 : i ≠ I := fun h => hi (Or.inl h)
      have h2 : i ≠ O := fun h => hi (Or.inr (Or.inl h))
      have h3 : i ≠ R := fun h => hi (Or.inr (Or.inr h))
      simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne h1, Function.update_of_ne h2,
        Function.update_of_ne h3]
    · have h1 : r ≠ c := fun h => hr (Or.inl h)
      have h2 : r ≠ f := fun h => hr (Or.inr h)
      simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1, Function.update_of_ne h1, Function.update_of_ne h2]
    · simp [hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]

/-- A cell past the input's bits: the bit is `false`. -/
theorem cellZ_spec (hcap : 1 ≤ cap) (cy : Bool) (σ : WState ns nr) (hc : σ.val c = 0) (hf : σ.val f = cy.toNat)
    (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (cellW I O R c f out nxt) σ τ 23 ∧
      Mv I O R c f σ τ (σ.sh I) [true, out false cy] (σ.sh R + 1) 0 (nxt false cy).toNat := by
  have hOI : O ≠ I := fun h => hIO h.symm
  have hRO : R ≠ O := fun h => hOR h.symm
  have hRI : R ≠ I := fun h => hIR h.symm
  have hfc : f ≠ c := fun h => hcf h.symm
  have s1 := emitW_spec cap O true σ hO
  set σ1 := (σ.sets O (σ.st O ++ [true])).seth O ((σ.st O).length + 1) with hσ1
  have s3 := leaf_spec cap (o3 out) (n3 nxt) O f false false cy σ1 (by simp [hσ1, hf]) hcap
  set σ3 := (σ1.sets O (writeTapeBit (σ1.st O) (σ1.sh O) (o3 out false false cy))).setv f
    (n3 nxt false false cy).toNat with hσ3
  have s6 := WExec.fwd (cap := cap) O σ3
  set σ6 := σ3.seth O (σ3.sh O + 1) with hσ6
  have s7 := WExec.fwd (cap := cap) R σ6
  have hcz : σ1.val c = 0 := by simp [hσ1, hc]
  have run : WExec cap (cellW I O R c f out nxt) σ (σ6.seth R (σ6.sh R + 1)) _ :=
    WExec.seq s1 (WExec.seq (WExec.ifrF hcz s3) (WExec.seq s6 s7))
  refine ⟨_, WExec.mono run (by omega), ?_⟩
  have hw : writeTapeBit (σ1.st O) (σ1.sh O) (o3 out false false cy) = σ.st O ++ [true, out false cy] := by
    simp only [hσ1, WState.seth_st, WState.seth_sh, WState.sets_st, Function.update_self]
    have := writeTapeBit_end' (σ.st O ++ [true]) (out false cy)
    simpa [o3] using this
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hσ6, hσ3, hσ1, Function.update_of_ne hIO, Function.update_of_ne hIR]
  · simp [hσ6, hσ3, hσ1, Function.update_of_ne hIO, Function.update_of_ne hIR]
  · simp only [hσ6, WState.seth_st, Function.update_of_ne hRO]
    rw [hσ3]; simp only [WState.setv_st, WState.sets_st, Function.update_self]
    rw [hw]
  · simp only [hσ6, WState.seth_st, WState.seth_sh, Function.update_of_ne hRO, Function.update_self]
    rw [hσ3]; simp only [WState.setv_st, WState.setv_sh, WState.sets_st, WState.sets_sh, Function.update_self]
    rw [hw]
    simp [hσ1, Function.update_of_ne hOR]
  · simp [hσ6, hσ3, hσ1, Function.update_of_ne hRO]
  · simp [hσ6, hσ3, hσ1, Function.update_of_ne hRO]
  · simp [hσ6, hσ3, hσ1, Function.update_of_ne hcf, hc]
  · simp [hσ6, hσ3, hσ1, n3]
  · refine ⟨fun i hi => ?_, fun r hr => ?_, ?_⟩
    · have h2 : i ≠ O := fun h => hi (Or.inr (Or.inl h))
      have h3 : i ≠ R := fun h => hi (Or.inr (Or.inr h))
      simp [hσ6, hσ3, hσ1, Function.update_of_ne h2, Function.update_of_ne h3]
    · have h2 : r ≠ f := fun h => hr (Or.inr h)
      simp [hσ6, hσ3, hσ1, Function.update_of_ne h2]
    · simp [hσ6, hσ3, hσ1]

/-! ## The ruler loop -/

theorem loopZ_spec (hcap : 1 ≤ cap) : ∀ (z : ℕ) (cy : Bool) (σ : WState ns nr), σ.val c = 0 →
    σ.val f = cy.toNat → σ.sh O = (σ.st O).length →
    (∀ j < z, readTapeBit (σ.st R) (σ.sh R + j) = true) → readTapeBit (σ.st R) (σ.sh R + z) = false →
    ∃ τ, WExec cap (.whs R (cellW I O R c f out nxt)) σ τ (z * 25 + 1) ∧
      Mv I O R c f σ τ (σ.sh I) (frameP (cmap out nxt (List.replicate z false) cy)) (σ.sh R + z) 0
        (cfin nxt (List.replicate z false) cy).toNat
  | 0, cy, σ, hc, hf, hO, _, hz => by
    refine ⟨σ, WExec.whsF (by simpa [wbit] using hz), ?_⟩
    have := Mv.refl I O R c f σ hO
    rw [hc, hf] at this
    simpa [cmap, cfin] using this
  | z + 1, cy, σ, hc, hf, hO, hT, hz => by
    obtain ⟨τ1, s1, m1⟩ := cellZ_spec cap I O R c f out nxt hIO hIR hOR hcf hcap cy σ hc hf hO
    obtain ⟨τ, s2, m2⟩ := loopZ_spec hcap z (nxt false cy) τ1 m1.vc m1.vf m1.hO
      (fun j hj => by rw [m1.sR, m1.hR, show σ.sh R + 1 + j = σ.sh R + (j + 1) by omega]; exact hT _ (by omega))
      (by rw [m1.sR, m1.hR, show σ.sh R + 1 + z = σ.sh R + (z + 1) by omega]; exact hz)
    have hw : wbit σ R = true := by simpa [wbit] using hT 0 (by omega)
    refine ⟨τ, WExec.mono (WExec.whsT hw s1 s2) (by rw [Nat.succ_mul]; omega), m1.trans_eq m2 ?_ ?_ ?_ rfl ?_⟩
    · rw [m1.hI]
    · simp [cmap, List.replicate_succ]
    · rw [m1.hR]; omega
    · simp [cfin, List.replicate_succ]

theorem loopB_spec (hcap : 1 ≤ cap) (rest : List Bool) : ∀ (bs : List Bool) (z : ℕ) (pre : List Bool) (cy : Bool)
    (σ : WState ns nr), σ.st I = pre ++ (frameP bs ++ rest) → σ.sh I = pre.length → σ.val c = bs.length →
    bs.length ≤ cap → σ.val f = cy.toNat → σ.sh O = (σ.st O).length →
    (∀ j < bs.length + z, readTapeBit (σ.st R) (σ.sh R + j) = true) →
    readTapeBit (σ.st R) (σ.sh R + (bs.length + z)) = false →
    ∃ τ, WExec cap (.whs R (cellW I O R c f out nxt)) σ τ ((bs.length + z) * 25 + 1) ∧
      Mv I O R c f σ τ (pre.length + 2 * bs.length) (frameP (cmap out nxt (bs ++ List.replicate z false) cy))
        (σ.sh R + (bs.length + z)) 0 (cfin nxt (bs ++ List.replicate z false) cy).toNat
  | [], z, pre, cy, σ, _, hIh, hc, _, hf, hO, hT, hz => by
    obtain ⟨τ, s, m⟩ := loopZ_spec cap I O R c f out nxt hIO hIR hOR hcf hcap z cy σ (by simpa using hc) hf hO
      (fun j hj => hT j (by simpa using hj)) (by simpa using hz)
    refine ⟨τ, by simpa using s, ?_⟩
    have := m
    rw [hIh] at this
    simpa using this
  | b :: bs, z, pre, cy, σ, hI, hIh, hc, hcb, hf, hO, hT, hz => by
    obtain ⟨τ1, s1, m1⟩ := cellB_spec cap I O R c f out nxt hIO hIR hOR hcf hcap pre rest b bs cy bs.length σ hI hIh
      (by simpa using hc) (by simpa using hcb) hf hO
    obtain ⟨τ, s2, m2⟩ := loopB_spec hcap rest bs z (pre ++ [true, b]) (nxt b cy) τ1
      (by rw [m1.sI, hI]; simp) (by rw [m1.hI]; simp) m1.vc (by simp at hcb; omega) m1.vf m1.hO
      (fun j hj => by
        rw [m1.sR, m1.hR, show σ.sh R + 1 + j = σ.sh R + (j + 1) by omega]; exact hT _ (by simp; omega))
      (by rw [m1.sR, m1.hR, show σ.sh R + 1 + (bs.length + z) = σ.sh R + ((b :: bs).length + z) by simp; omega]
          exact hz)
    have hw : wbit σ R = true := by simpa [wbit] using hT 0 (by simp)
    refine ⟨τ, WExec.mono (WExec.whsT hw s1 s2) (by simp; rw [Nat.add_right_comm, Nat.succ_mul]; omega),
      m1.trans_eq m2 ?_ ?_ ?_ rfl ?_⟩
    · simp; omega
    · simp [cmap]
    · rw [m1.hR]; simp; omega
    · simp [cfin]

/-- The closing steps of `wordW`: the word's end, the ruler back to its sentinel, the carry cleared. -/
theorem wordTail_spec (hcap : 1 ≤ cap) (h : ℕ) (cy : Bool) (σ : WState ns nr)
    (hR : σ.st R = false :: List.replicate h true) (hRh : σ.sh R = 1 + h) (hf : σ.val f = cy.toNat)
    (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (.seq (emitW O false) (.seq (.bwd R) (.seq (.whs R (.bwd R)) (WM.clear f)))) σ τ (3 * h + 14) ∧
      Mv I O R c f σ τ (σ.sh I) [false] 0 (σ.val c) 0 := by
  have hRO : R ≠ O := fun e => hOR e.symm
  have hRI : R ≠ I := fun e => hIR e.symm
  have s1 := emitW_spec cap O false σ hO
  set σ1 := (σ.sets O (σ.st O ++ [false])).seth O ((σ.st O).length + 1) with hσ1
  have s2 := WExec.bwd (cap := cap) R σ1
  set σ2 := σ1.seth R (σ1.sh R - 1) with hσ2
  have s3 := rewindR_spec cap R h σ2 (by simp [hσ2, hσ1, Function.update_of_ne hRO, hRh])
    (fun j h1 h2 => by
      simp only [hσ2, hσ1, WState.seth_st, WState.sets_st, Function.update_of_ne hRO, hR]
      have := ruler_read h (j - 1); rw [show 1 + (j - 1) = j by omega] at this; rw [this]; simp; omega)
    (by simp only [hσ2, hσ1, WState.seth_st, WState.sets_st, Function.update_of_ne hRO, hR]; rfl)
  have s4 := wclear_spec cap f cy.toNat (σ2.seth R 0) (by simp [hσ2, hσ1, hf])
    (by simp [hσ2, hσ1, hf]; cases cy <;> simp <;> omega)
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 (WExec.seq s3 s4))) (by cases cy <;> simp <;> omega), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hσ2, hσ1, Function.update_of_ne hIO]
  · simp [hσ2, hσ1, Function.update_of_ne hIO, Function.update_of_ne hIR]
  · simp [hσ2, hσ1, Function.update_of_ne hOR]
  · simp [hσ2, hσ1, Function.update_of_ne hOR]
  · simp [hσ2, hσ1, Function.update_of_ne hRO]
  · simp [hσ2, hσ1]
  · simp [hσ2, hσ1, Function.update_of_ne hcf]
  · simp [hσ2, hσ1]
  · refine ⟨fun i hi => ?_, fun r hr => ?_, ?_⟩
    · have h2 : i ≠ O := fun e => hi (Or.inr (Or.inl e))
      have h3 : i ≠ R := fun e => hi (Or.inr (Or.inr e))
      simp [hσ2, hσ1, Function.update_of_ne h2, Function.update_of_ne h3]
    · have h2 : r ≠ f := fun e => hr (Or.inr e)
      simp [hσ2, hσ1, Function.update_of_ne h2]
    · simp [hσ2, hσ1]

theorem wordB_spec (hcap : 1 ≤ cap) (h : ℕ) (pre bs rest : List Bool) (cy : Bool) (σ : WState ns nr)
    (hI : σ.st I = pre ++ (frameP bs ++ rest)) (hIh : σ.sh I = pre.length) (hc : σ.val c = bs.length)
    (hbh : bs.length ≤ h) (hbc : bs.length ≤ cap) (hf : σ.val f = cy.toNat) (hO : σ.sh O = (σ.st O).length)
    (hR : σ.st R = false :: List.replicate h true) (hRh : σ.sh R = 0) :
    ∃ τ, WExec cap (wordW I O R c f out nxt) σ τ (wordCost h) ∧
      Mv I O R c f σ τ (pre.length + 2 * bs.length)
        (frame (cmap out nxt (bs ++ List.replicate (h - bs.length) false) cy)) 0 0 0 := by
  have hRO : R ≠ O := fun e => hOR e.symm
  have hRI : R ≠ I := fun e => hIR e.symm
  have s1 := WExec.fwd (cap := cap) R σ
  set σ1 := σ.seth R (σ.sh R + 1) with hσ1
  obtain ⟨τ2, s2, m2⟩ := loopB_spec cap I O R c f out nxt hIO hIR hOR hcf hcap rest bs (h - bs.length) pre cy σ1
    (by simp [hσ1, Function.update_of_ne hIR, hI]) (by simp [hσ1, Function.update_of_ne hIR, hIh])
    (by simp [hσ1, hc]) hbc (by simp [hσ1, hf]) (by simp [hσ1, Function.update_of_ne hOR, hO])
    (fun j hj => by simp only [hσ1, WState.seth_st, WState.seth_sh, Function.update_self, hR, hRh]
                    rw [Nat.zero_add, ruler_read]; (try simp); (try omega))
    (by simp only [hσ1, WState.seth_st, WState.seth_sh, Function.update_self, hR, hRh]
        rw [Nat.zero_add, ruler_read]; (try simp); (try omega))
  obtain ⟨τ, s3, m3⟩ := wordTail_spec cap I O R c f hIO hIR hOR hcf hcap h
    (cfin nxt (bs ++ List.replicate (h - bs.length) false) cy) τ2
    (by rw [m2.sR]; simp [hσ1, hR]) (by rw [m2.hR]; simp [hσ1, hRh]; omega) m2.vf m2.hO
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) ?_, ?_⟩
  · unfold wordCost
    have : (bs.length + (h - bs.length)) * 25 = h * 25 := by rw [Nat.add_sub_cancel' hbh]
    omega
  · have m1 : Mv I O R c f σ σ1 (σ.sh I) [] (σ.sh R + 1) (σ.val c) (σ.val f) :=
      ⟨rfl, by simp [hσ1, Function.update_of_ne hIR], by simp [hσ1, Function.update_of_ne hOR],
        by simp [hσ1, Function.update_of_ne hOR, hO], by simp [hσ1], by simp [hσ1], rfl, rfl,
        frame_seth _ _ σ R _ (Or.inr (Or.inr rfl))⟩
    refine (m1.trans m2).trans_eq m3 ?_ ?_ rfl m2.vc rfl
    · exact m2.hI
    · simp [frame_eq_frameP]

/-- **The `h`-bit framed word of `0`**, when the count is `0`. -/
theorem wordZ_spec (hcap : 1 ≤ cap) (h : ℕ) (σ : WState ns nr) (hc : σ.val c = 0) (hf : σ.val f = 0)
    (hO : σ.sh O = (σ.st O).length) (hR : σ.st R = false :: List.replicate h true) (hRh : σ.sh R = 0) :
    ∃ τ, WExec cap (wordW I O R c f cpyOut cpyNxt) σ τ (wordCost h) ∧
      Mv I O R c f σ τ (σ.sh I) (frame (binary h 0)) 0 0 0 := by
  have hRO : R ≠ O := fun e => hOR e.symm
  have s1 := WExec.fwd (cap := cap) R σ
  set σ1 := σ.seth R (σ.sh R + 1) with hσ1
  obtain ⟨τ2, s2, m2⟩ := loopZ_spec cap I O R c f cpyOut cpyNxt hIO hIR hOR hcf hcap h false σ1
    (by simp [hσ1, hc]) (by simp [hσ1, hf]) (by simp [hσ1, Function.update_of_ne hOR, hO])
    (fun j hj => by simp only [hσ1, WState.seth_st, WState.seth_sh, Function.update_self, hR, hRh]
                    rw [Nat.zero_add, ruler_read]; (try simp); (try omega))
    (by simp only [hσ1, WState.seth_st, WState.seth_sh, Function.update_self, hR, hRh]
        rw [Nat.zero_add, ruler_read]; (try simp); (try omega))
  obtain ⟨τ, s3, m3⟩ := wordTail_spec cap I O R c f hIO hIR hOR hcf hcap h
    (cfin cpyNxt (List.replicate h false) false) τ2
    (by rw [m2.sR]; simp [hσ1, hR]) (by rw [m2.hR]; simp [hσ1, hRh]; try omega) m2.vf m2.hO
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by unfold wordCost; omega), ?_⟩
  have m1 : Mv I O R c f σ σ1 (σ.sh I) [] (σ.sh R + 1) (σ.val c) (σ.val f) :=
    ⟨rfl, by simp [hσ1, Function.update_of_ne hIR], by simp [hσ1, Function.update_of_ne hOR],
      by simp [hσ1, Function.update_of_ne hOR, hO], by simp [hσ1], by simp [hσ1], rfl, rfl,
      frame_seth _ _ σ R _ (Or.inr (Or.inr rfl))⟩
  refine (m1.trans m2).trans_eq m3 ?_ ?_ rfl m2.vc rfl
  · rw [m2.hI, m1.hI]
  · simp [frame_eq_frameP, cmap_cpy, CompilerMachine.Pool.binary_zero']

/-! ## Single moves -/

theorem fwdI_mv (σ : WState ns nr) (hO : σ.sh O = (σ.st O).length) :
    WExec cap (.fwd I) σ (σ.seth I (σ.sh I + 1)) 1 ∧
      Mv I O R c f σ (σ.seth I (σ.sh I + 1)) (σ.sh I + 1) [] (σ.sh R) (σ.val c) (σ.val f) := by
  have hOI : O ≠ I := fun e => hIO e.symm
  have hRI : R ≠ I := fun e => hIR e.symm
  refine ⟨WExec.fwd I σ, ⟨rfl, by simp, by simp, by simp [Function.update_of_ne hOI, hO], rfl,
    by simp [Function.update_of_ne hRI], rfl, rfl, frame_seth _ _ σ I _ (Or.inl rfl)⟩⟩

theorem incf_mv (σ : WState ns nr) (hO : σ.sh O = (σ.st O).length) (hf : σ.val f < cap) :
    WExec cap (.inc f) σ (σ.setv f (σ.val f + 1)) 3 ∧
      Mv I O R c f σ (σ.setv f (σ.val f + 1)) (σ.sh I) [] (σ.sh R) (σ.val c) (σ.val f + 1) := by
  have hfc : f ≠ c := fun e => hcf e.symm
  refine ⟨WExec.inc f σ hf, ⟨rfl, rfl, by simp, by simp [hO], rfl, rfl, by simp [Function.update_of_ne hcf], by simp,
    frame_setv _ _ σ f _ (Or.inr rfl)⟩⟩

/-! ## Native numbers -/

/-- **Count** the unary length of a framed `natWord`; the input head stops at the marker of its first bit. -/
theorem countW_spec (pre rest : List Bool) (v : ℕ) (σ : WState ns nr)
    (hI : σ.st I = pre ++ (frameP (natWord v) ++ rest)) (hIh : σ.sh I = pre.length) (hc : σ.val c = 0)
    (hk : natBitLength v ≤ cap) (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (countW I c) σ τ (countCost (natBitLength v)) ∧
      Mv I O R c f σ τ (pre.length + 2 * natBitLength v + 2) [] (σ.sh R) (natBitLength v) (σ.val f) := by
  have hOI : O ≠ I := fun e => hIO e.symm
  have hRI : R ≠ I := fun e => hIR e.symm
  have hfc : f ≠ c := fun e => hcf e.symm
  set k := natBitLength v with hkdef
  have hlen : (natWord v).length = 2 * k + 1 := natWord_length' v
  have s1 := WExec.fwd (cap := cap) I σ
  set σ1 := σ.seth I (σ.sh I + 1) with hσ1
  have s2 := countLoop_spec cap I c k σ1
    (fun i hi => by
      simp only [hσ1, WState.seth_st, WState.seth_sh, Function.update_self, hI, hIh]
      rw [show pre.length + 1 + 2 * i = pre.length + (2 * i + 1) by omega, rd_bit _ _ _ _ (by omega)]
      exact natWord_getD_lt v i hi)
    (by simp only [hσ1, WState.seth_st, WState.seth_sh, Function.update_self, hI, hIh]
        rw [show pre.length + 1 + 2 * k = pre.length + (2 * k + 1) by omega, rd_bit _ _ _ _ (by omega)]
        exact natWord_getD_k v)
    (by simp [hσ1, hc, hk])
  set σ2 := (σ1.seth I (σ1.sh I + 2 * k)).setv c (σ1.val c + k) with hσ2
  have s3 := WExec.fwd (cap := cap) I σ2
  refine ⟨_, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by unfold countCost; omega), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hσ2, hσ1]
  · simp [hσ2, hσ1, hIh]; omega
  · simp [hσ2, hσ1, Function.update_of_ne hOI]
  · simp [hσ2, hσ1, Function.update_of_ne hOI, hO]
  · simp [hσ2, hσ1, Function.update_of_ne hRI]
  · simp [hσ2, hσ1, Function.update_of_ne hRI]
  · simp [hσ2, hσ1, hc]
  · simp [hσ2, hσ1, Function.update_of_ne hfc]
  · refine ⟨fun i hi => ?_, fun r hr => ?_, ?_⟩
    · have h1 : i ≠ I := fun e => hi (Or.inl e)
      simp [hσ2, hσ1, Function.update_of_ne h1]
    · have h1 : r ≠ c := fun e => hr (Or.inl e)
      simp [hσ2, hσ1, Function.update_of_ne h1]
    · simp [hσ2, hσ1]

/-- **Skip** a framed `natWord`. -/
theorem skipNatW_spec (pre rest : List Bool) (v : ℕ) (σ : WState ns nr)
    (hI : σ.st I = pre ++ (frameP (natWord v) ++ rest)) (hIh : σ.sh I = pre.length) (hc : σ.val c = 0)
    (hk : natBitLength v ≤ cap) (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (skipNatW I c) σ τ (16 * natBitLength v + 7) ∧
      Mv I O R c f σ τ (pre.length + 2 * (natWord v).length) [] (σ.sh R) 0 (σ.val f) := by
  have hOI : O ≠ I := fun e => hIO e.symm
  have hRI : R ≠ I := fun e => hIR e.symm
  have hfc : f ≠ c := fun e => hcf e.symm
  obtain ⟨τ1, s1, m1⟩ := countW_spec cap I O R c f hIO hIR hOR hcf pre rest v σ hI hIh hc hk hO
  have s2 := skipLoop_spec cap I c (natBitLength v) τ1 m1.vc hk
  refine ⟨_, WExec.mono (WExec.seq s1 s2) (by unfold countCost; omega), ?_⟩
  have m2 : Mv I O R c f τ1 ((τ1.seth I (τ1.sh I + 2 * natBitLength v)).setv c 0)
      (τ1.sh I + 2 * natBitLength v) [] (τ1.sh R) 0 (τ1.val f) :=
    ⟨by simp, by simp, by simp, by simp [Function.update_of_ne hOI, m1.hO], by simp,
      by simp [Function.update_of_ne hRI], by simp, by simp [Function.update_of_ne hfc],
      (frame_seth _ _ τ1 I _ (Or.inl rfl)).trans (frame_setv _ _ _ c _ (Or.inl rfl))⟩
  refine m1.trans_eq m2 ?_ (by simp) m1.hR rfl m1.vf
  rw [m1.hI, natWord_length']; omega

/-- **A framed `natWord` as an `h`-bit framed word** through a carry map. -/
theorem convNatW_spec (hcap : 1 ≤ cap) (out nxt : Bool → Bool → Bool) (pre rest : List Bool) (v h : ℕ) (cy : Bool)
    (σ : WState ns nr) (hI : σ.st I = pre ++ (frameP (natWord v) ++ rest)) (hIh : σ.sh I = pre.length)
    (hc : σ.val c = 0) (hf : σ.val f = cy.toNat) (hkh : natBitLength v ≤ h) (hkc : natBitLength v ≤ cap)
    (hO : σ.sh O = (σ.st O).length) (hR : σ.st R = false :: List.replicate h true) (hRh : σ.sh R = 0) :
    ∃ τ, WExec cap (convNatW I O R c f out nxt) σ τ (countCost (natBitLength v) + 1 + wordCost h) ∧
      Mv I O R c f σ τ (pre.length + 2 * (natWord v).length) (frame (cmap out nxt (binary h v) cy)) 0 0 0 := by
  obtain ⟨τ1, s1, m1⟩ := countW_spec cap I O R c f hIO hIR hOR hcf pre rest v σ hI hIh hc hkc hO
  set k := natBitLength v with hk
  set pre' := pre ++ (frameP (List.replicate k true) ++ [true, false]) with hpre'
  have hI' : τ1.st I = pre' ++ (frameP (binary k v) ++ rest) := by
    rw [m1.sI, hI, frameP_natWord, hpre']; simp [hk]
  have hIh' : τ1.sh I = pre'.length := by rw [m1.hI, hpre']; simp; omega
  obtain ⟨τ, s2, m2⟩ := wordB_spec cap I O R c f out nxt hIO hIR hOR hcf hcap h pre' (binary k v) rest cy τ1 hI' hIh'
    (by rw [m1.vc, binary_length]) (by rw [binary_length]; exact hkh) (by rw [binary_length]; exact hkc)
    (by rw [m1.vf, hf]) m1.hO (by rw [m1.sR, hR]) (by rw [m1.hR, hRh])
  refine ⟨τ, WExec.seq s1 s2, m1.trans_eq m2 ?_ ?_ rfl rfl rfl⟩
  · rw [hpre', natWord_length']; simp; omega
  · rw [List.nil_append, binary_length, ← binary_pad' v h hkh]

/-- **A weight's pair**: from its framed `intWord`, the P/N pair `pairW h z`. -/
theorem convIntW_spec (hcap : 1 ≤ cap) (pre rest : List Bool) (z : ℤ) (h : ℕ) (σ : WState ns nr)
    (hI : σ.st I = pre ++ (frameP (intWord z) ++ rest)) (hIh : σ.sh I = pre.length) (hc : σ.val c = 0)
    (hf : σ.val f = 0) (hkh : natBitLength z.natAbs ≤ h) (hkc : natBitLength z.natAbs ≤ cap)
    (hO : σ.sh O = (σ.st O).length) (hR : σ.st R = false :: List.replicate h true) (hRh : σ.sh R = 0) :
    ∃ τ, WExec cap (convIntW I O R c f) σ τ (convIntCost (natBitLength z.natAbs) h) ∧
      Mv I O R c f σ τ (pre.length + 2 * (intWord z).length) (pairW h z) 0 0 0 := by
  obtain ⟨s1, m1⟩ := fwdI_mv cap I O R c f hIO hIR hOR hcf σ hO
  set σ1 := σ.seth I (σ.sh I + 1) with hσ1
  obtain ⟨s2, m2⟩ := fwdI_mv cap I O R c f hIO hIR hOR hcf σ1 m1.hO
  set σ2 := σ1.seth I (σ1.sh I + 1) with hσ2
  have hsign : wbit σ1 I = decide (z < 0) := by
    simp only [wbit, m1.sI, m1.hI, hI, hIh]
    have := rd_bit pre (intWord z) rest 0 (by simp [intWord])
    simpa [intWord] using this
  have hI2 : σ2.st I = (pre ++ [true, decide (z < 0)]) ++ (frameP (natWord z.natAbs) ++ rest) := by
    rw [m2.sI, m1.sI, hI, frameP_intWord]; simp
  have hIh2 : σ2.sh I = (pre ++ [true, decide (z < 0)]).length := by rw [m2.hI, m1.hI, hIh]; simp
  have hlen : (intWord z).length = (natWord z.natAbs).length + 1 := by simp [intWord]
  by_cases hz : z < 0
  · obtain ⟨σ3, s3, m3⟩ := wordZ_spec cap I O R c f hIO hIR hOR hcf hcap h σ2 (by rw [m2.vc, m1.vc, hc])
      (by rw [m2.vf, m1.vf, hf]) m2.hO (by rw [m2.sR, m1.sR, hR]) (by rw [m2.hR, m1.hR, hRh])
    obtain ⟨τ, s4, m4⟩ := convNatW_spec cap I O R c f hIO hIR hOR hcf hcap cpyOut cpyNxt (pre ++ [true, decide (z < 0)])
      rest z.natAbs h false σ3 (by rw [m3.sI, hI2]) (by rw [m3.hI, hIh2]) m3.vc (by rw [m3.vf]; rfl) hkh hkc m3.hO
      (by rw [m3.sR, m2.sR, m1.sR, hR]) m3.hR
    have run : WExec cap (convIntW I O R c f) σ τ _ :=
      WExec.seq s1 (WExec.ifsT (by rw [hsign]; simpa using hz) (WExec.seq s2 (WExec.seq s3 s4)))
    refine ⟨τ, WExec.mono run (by unfold convIntCost; omega), ?_⟩
    refine ((m1.trans m2).trans m3).trans_eq m4 ?_ ?_ rfl rfl rfl
    · rw [hlen]; simp; omega
    · rw [pairW_of_int, if_pos hz, cmap_cpy]; simp
  · obtain ⟨σ3, s3, m3⟩ := convNatW_spec cap I O R c f hIO hIR hOR hcf hcap cpyOut cpyNxt (pre ++ [true, decide (z < 0)])
      rest z.natAbs h false σ2 hI2 hIh2 (by rw [m2.vc, m1.vc, hc]) (by rw [m2.vf, m1.vf, hf]; rfl) hkh hkc m2.hO
      (by rw [m2.sR, m1.sR, hR]) (by rw [m2.hR, m1.hR, hRh])
    obtain ⟨τ, s4, m4⟩ := wordZ_spec cap I O R c f hIO hIR hOR hcf hcap h σ3 m3.vc m3.vf m3.hO
      (by rw [m3.sR, m2.sR, m1.sR, hR]) m3.hR
    have run : WExec cap (convIntW I O R c f) σ τ _ :=
      WExec.seq s1 (WExec.ifsF (by rw [hsign]; simpa using hz) (WExec.seq s2 (WExec.seq s3 s4)))
    refine ⟨τ, WExec.mono run (by unfold convIntCost; omega), ?_⟩
    refine ((m1.trans m2).trans m3).trans_eq m4 ?_ ?_ rfl rfl rfl
    · rw [m3.hI, hlen]; simp; omega
    · rw [pairW_of_int, if_neg hz, cmap_cpy]; simp

/-- **The pair of `−θ`** from the framed `intWord` of `t = θ − 1`. -/
theorem convThrW_spec (hcap : 2 ≤ cap) (pre rest : List Bool) (t : ℤ) (h : ℕ) (σ : WState ns nr)
    (hI : σ.st I = pre ++ (frameP (intWord t) ++ rest)) (hIh : σ.sh I = pre.length) (hc : σ.val c = 0)
    (hf : σ.val f = 0) (hkh : natBitLength t.natAbs + 1 ≤ h) (hkc : natBitLength t.natAbs ≤ cap)
    (hO : σ.sh O = (σ.st O).length) (hR : σ.st R = false :: List.replicate h true) (hRh : σ.sh R = 0) :
    ∃ τ, WExec cap (convThrW I O R c f) σ τ (convIntCost (natBitLength t.natAbs) h + 4) ∧
      Mv I O R c f σ τ (pre.length + 2 * (intWord t).length) (pairW h (-(t + 1))) 0 0 0 := by
  have hcap1 : 1 ≤ cap := by omega
  obtain ⟨s1, m1⟩ := fwdI_mv cap I O R c f hIO hIR hOR hcf σ hO
  set σ1 := σ.seth I (σ.sh I + 1) with hσ1
  obtain ⟨s2, m2⟩ := fwdI_mv cap I O R c f hIO hIR hOR hcf σ1 m1.hO
  set σ2 := σ1.seth I (σ1.sh I + 1) with hσ2
  have hsign : wbit σ1 I = decide (t < 0) := by
    simp only [wbit, m1.sI, m1.hI, hI, hIh]
    have := rd_bit pre (intWord t) rest 0 (by simp [intWord])
    simpa [intWord] using this
  have hI2 : σ2.st I = (pre ++ [true, decide (t < 0)]) ++ (frameP (natWord t.natAbs) ++ rest) := by
    rw [m2.sI, m1.sI, hI, frameP_intWord]; simp
  have hIh2 : σ2.sh I = (pre ++ [true, decide (t < 0)]).length := by rw [m2.hI, m1.hI, hIh]; simp
  have hlen : (intWord t).length = (natWord t.natAbs).length + 1 := by simp [intWord]
  have hlt : t.natAbs < 2 ^ natBitLength t.natAbs := CompilerMachine.Pool.lt_pow_natBitLength t.natAbs
  have hpow : 2 ^ (natBitLength t.natAbs + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by norm_num) hkh
  rw [pow_succ] at hpow
  by_cases ht : t < 0
  · obtain ⟨s3, m3⟩ := incf_mv cap I O R c f hIO hIR hOR hcf σ2 m2.hO (by rw [m2.vf, m1.vf, hf]; omega)
    set σ3 := σ2.setv f (σ2.val f + 1) with hσ3
    obtain ⟨σ4, s4, m4⟩ := convNatW_spec cap I O R c f hIO hIR hOR hcf hcap1 decOut decNxt
      (pre ++ [true, decide (t < 0)]) rest t.natAbs h true σ3 (by rw [m3.sI, hI2]) (by rw [m3.hI, hIh2])
      (by rw [m3.vc, m2.vc, m1.vc, hc]) (by rw [m3.vf, m2.vf, m1.vf, hf]; rfl) (by omega) hkc m3.hO
      (by rw [m3.sR, m2.sR, m1.sR, hR]) (by rw [m3.hR, m2.hR, m1.hR, hRh])
    obtain ⟨τ, s5, m5⟩ := wordZ_spec cap I O R c f hIO hIR hOR hcf hcap1 h σ4 m4.vc m4.vf m4.hO
      (by rw [m4.sR, m3.sR, m2.sR, m1.sR, hR]) m4.hR
    have run : WExec cap (convThrW I O R c f) σ τ _ :=
      WExec.seq s1 (WExec.ifsT (by rw [hsign]; simpa using ht) (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5))))
    refine ⟨τ, WExec.mono run (by unfold convIntCost; omega), ?_⟩
    refine (((m1.trans m2).trans m3).trans m4).trans_eq m5 ?_ ?_ rfl rfl rfl
    · rw [m4.hI, hlen]; simp; omega
    · rw [pairW_negThr, if_pos ht, cmap_dec h t.natAbs (by omega) (by omega)]; simp
  · obtain ⟨σ3, s3, m3⟩ := wordZ_spec cap I O R c f hIO hIR hOR hcf hcap1 h σ2 (by rw [m2.vc, m1.vc, hc])
      (by rw [m2.vf, m1.vf, hf]) m2.hO (by rw [m2.sR, m1.sR, hR]) (by rw [m2.hR, m1.hR, hRh])
    obtain ⟨s4, m4⟩ := incf_mv cap I O R c f hIO hIR hOR hcf σ3 m3.hO (by rw [m3.vf]; omega)
    set σ4 := σ3.setv f (σ3.val f + 1) with hσ4
    obtain ⟨τ, s5, m5⟩ := convNatW_spec cap I O R c f hIO hIR hOR hcf hcap1 incOut incNxt
      (pre ++ [true, decide (t < 0)]) rest t.natAbs h true σ4 (by rw [m4.sI, m3.sI, hI2])
      (by rw [m4.hI, m3.hI, hIh2]) (by rw [m4.vc, m3.vc]) (by rw [m4.vf, m3.vf]; rfl) (by omega) hkc m4.hO
      (by rw [m4.sR, m3.sR, m2.sR, m1.sR, hR]) (by rw [m4.hR, m3.hR])
    have run : WExec cap (convThrW I O R c f) σ τ _ :=
      WExec.seq s1 (WExec.ifsF (by rw [hsign]; simpa using ht) (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 s5))))
    refine ⟨τ, WExec.mono run (by unfold convIntCost; omega), ?_⟩
    refine (((m1.trans m2).trans m3).trans m4).trans_eq m5 ?_ ?_ rfl rfl rfl
    · rw [hlen]; simp; omega
    · rw [pairW_negThr, if_neg ht, cmap_inc h t.natAbs (by omega)]; simp

/-- **Skip** a framed `intWord`. -/
theorem skipIntW_spec (pre rest : List Bool) (z : ℤ) (σ : WState ns nr)
    (hI : σ.st I = pre ++ (frameP (intWord z) ++ rest)) (hIh : σ.sh I = pre.length) (hc : σ.val c = 0)
    (hk : natBitLength z.natAbs ≤ cap) (hO : σ.sh O = (σ.st O).length) :
    ∃ τ, WExec cap (skipIntW I c) σ τ (16 * natBitLength z.natAbs + 11) ∧
      Mv I O R c f σ τ (pre.length + 2 * (intWord z).length) [] (σ.sh R) 0 (σ.val f) := by
  obtain ⟨s1, m1⟩ := fwdI_mv cap I O R c f hIO hIR hOR hcf σ hO
  obtain ⟨s2, m2⟩ := fwdI_mv cap I O R c f hIO hIR hOR hcf _ m1.hO
  obtain ⟨τ, s3, m3⟩ := skipNatW_spec cap I O R c f hIO hIR hOR hcf (pre ++ [true, decide (z < 0)]) rest z.natAbs _
    (by rw [m2.sI, m1.sI, hI, frameP_intWord]; simp) (by rw [m2.hI, m1.hI, hIh]; simp)
    (by rw [m2.vc, m1.vc, hc]) hk m2.hO
  refine ⟨τ, WExec.mono (WExec.seq s1 (WExec.seq s2 s3)) (by omega), ?_⟩
  refine (m1.trans m2).trans_eq m3 ?_ (by simp) (by rw [m2.hR, m1.hR]) rfl (by rw [m2.vf, m1.vf])
  simp [intWord]; omega

end Cell

end Conv

end NearCubicWires.WireExponent3_5.PrimT
