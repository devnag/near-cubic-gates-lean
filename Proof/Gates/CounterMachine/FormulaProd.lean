import Proof.Gates.CounterMachine.FormulaState

/-! # RG machine, part 15: the Fermat product

**`tP_spec`**: from the formula state (`FState`), the printer emits `tToks d`, the tokens of
`∏_i (1 − (f_i − ρ_i)^{q−1})` over the digits `E_j^r` (role 0, then role 1 of a pair call) and the scores `X^r`
(lem:residue-count; table (a) of `sec:algorithm`), every head and scratch register restored. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_append)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp enc_length)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec
open NearCubicGates.Close.Interfaces.Formats (Tok tokWord toks)

variable {ns nr : ℕ} (cap : ℕ)

/-! ## Two generic steps -/

/-- A branch on a flag register: `P` when the flag is set, nothing otherwise. -/
theorem ifr_opt {P : WM ns nr} {r : Fin nr} {σ τ : WState ns nr} {c : ℕ} (b : Bool)
    (hv : σ.val r = if b then 1 else 0) (hP : b = true → WExec cap P σ τ c) (hτ : b = false → τ = σ) :
    WExec cap (.ifr r P .skip) σ τ (c + 1) := by
  cases b with
  | true => exact WExec.ifrT (by simp at hv; omega) (hP rfl)
  | false =>
    rw [hτ rfl]
    exact WExec.mono (WExec.ifrF (by simpa using hv) (WExec.skip σ)) (by omega)

section Lit
variable (S : Fin (ns + 1)) (F : Fin 24 ↪ Fin nr)

/-- `m` copies of a token, `m` in the counter `K` (cleared). -/
theorem litLoop_spec (K : Fin nr) (hK : ∀ i : Fin 24, F i ≠ K) (t : Tok) (m : ℕ) (σ : WState ns nr) (h : TRest S F σ)
    (hKv : σ.val K = m) (hcap : σ.val (F 7) + 2 * m * (tokWord t).length + 2 * (tokWord t).length ≤ cap)
    (hc : σ.val (F 16) + m < cap) :
    WExec cap (repLoop K (litC S F t)) σ ((emitT S F σ (List.replicate m t)).setv K 0)
      (m * (16 * (tokWord t).length + 4 + 4) + 1) := by
  let g : ℕ → WState ns nr := fun i => (emitT S F σ (List.replicate i t)).setv K (m - i)
  have hg0 : g 0 = σ := by
    simp only [g, List.replicate_zero, Nat.sub_zero]; rw [emitT_nil S F σ h.pr.out, ← hKv, wsetv_same]
  have hrl : ∀ i, ((List.replicate i t).flatMap tokWord).length = i * (tokWord t).length := by
    intro i; induction i with
    | zero => simp
    | succ i ih => rw [List.replicate_succ, List.flatMap_cons, List.length_append, ih]; ring
  have e := repLoop_spec cap K (litC S F t) m (16 * (tokWord t).length + 4) g (fun i _ => by simp [g])
    (by omega) (fun i hi => by
      simp only [g]
      rw [wsetv_setv, ← emitT_setv S F K (hK 7).symm (hK 16).symm, show m - (i + 1) = m - i - 1 by omega]
      have h1 : TRest S F (emitT S F (σ.setv K (m - i - 1)) (List.replicate i t)) :=
        (h.setv S F K hK _).emitT S F _
      have hmi : i * (tokWord t).length ≤ m * (tokWord t).length := Nat.mul_le_mul_right _ hi.le
      have e1 := litC_spec cap S F t _ h1
        (by rw [emitT_val7, hrl, WState.setv_val, Function.update_of_ne (hK 7)]
            have : 2 * m * (tokWord t).length = 2 * (m * (tokWord t).length) := by ring
            omega)
        (by rw [emitT_val16, WState.setv_val, Function.update_of_ne (hK 16), List.length_replicate]; omega)
      refine WExec.cast cap e1 ?_ le_rfl
      rw [emitT_append, ← List.replicate_succ', emitT_setv S F K (hK 7).symm (hK 16).symm])
  rw [hg0] at e
  simpa [g] using e

end Lit

/-! ## The product -/

/-- The Fermat factors of a request in printing order. -/
def tFacs (d : FData) : List (List Tok) :=
  digFacs 0 0 d.q d.J d.B0 d.L d.ρs ++ (if d.pair then digFacs d.G0 d.J d.q d.J d.B1 d.L d.ρs else []) ++
    [facToks (linToks 0 d.C0) (d.ρs.getD (d.rc * d.J) 0 : ℤ) d.q] ++
    (if d.pair then [facToks (linToks d.G0 d.C1) (d.ρs.getD (d.rc * d.J + 1) 0 : ℤ) d.q] else [])

def tToks (d : FData) : List Tok := prodToks (tFacs d)

theorem tFacs_length (d : FData) : (tFacs d).length = d.rc * (d.J + 1) := by
  unfold tFacs FData.rc digFacs; cases d.pair <;> simp <;> ring

section Prod
variable (Y : Fin 8 ↪ Fin (ns + 1)) (X : Fin 24 ↪ Fin nr) (F : Fin 24 ↪ Fin nr)

/-- The tail of the product printer: the empty product `1`, the `R` multiplications, rewinding the residues. -/
def tTail : WM ns nr :=
  .seq (litC (Y 0) F (.const 1))
  (.seq (copyR (X 11) (X 4) (F 8))
  (.seq (repLoop (X 4) (litC (Y 0) F .mul))
  (.seq (copyR (X 7) (F 19) (F 8)) (WM.rewind (Y 6) (F 19)))))

/-- The product printer. -/
def tP : WM ns nr :=
  .seq (roleDig (Y 0) F (Y 1) (Y 5) (Y 6) (X 14) (X 15) (X 16) (X 6) (X 2) (X 3) (X 5) (X 4) (X 1))
  (.seq (.ifr (X 0) (roleDig (Y 0) F (Y 3) (Y 5) (Y 6) (X 18) (X 19) (X 20) (X 6) (X 2) (X 3) (X 5) (X 4) (X 1)) .skip)
  (.seq (facP (Y 0) F (Y 6) (X 5) (stP (Y 0) (Y 2) F (X 14) (X 15) (X 17) (X 3)))
  (.seq (.ifr (X 0) (facP (Y 0) F (Y 6) (X 5) (stP (Y 0) (Y 4) F (X 18) (X 19) (X 21) (X 3))) .skip)
  (tTail Y X F))))

theorem encN_take_le (L : List ℕ) (a : ℕ) : (encN (L.take a)).length ≤ (encN L).length := by
  conv_rhs => rw [← List.take_append_drop a L]
  rw [encN_append, List.length_append]; omega

theorem nodupX (l : List (Fin 24)) (hl : l.Nodup) : (l.map X).Nodup := hl.map X.injective

/-- The facts of a state reached by printing and moving the residue head. -/
structure Shifted (σ τ : WState ns nr) (p : ℕ) : Prop where
  rest : TRest (Y 0) F τ
  st : ∀ i : Fin 8, i ≠ 0 → τ.st (Y i) = σ.st (Y i)
  sh : ∀ i : Fin 8, i ≠ 0 → i ≠ 6 → τ.sh (Y i) = σ.sh (Y i)
  shK : τ.sh (Y 6) = p
  val : ∀ j, τ.val (X j) = σ.val (X j)

theorem shifted_of (σ : WState ns nr) (hR : TRest (Y 0) F σ) (hFX : ∀ i j, F i ≠ X j) (ts : List Tok) (p : ℕ) :
    Shifted Y X F σ ((emitT (Y 0) F σ ts).seth (Y 6) p) p := by
  have hY : ∀ {i j : Fin 8}, i ≠ j → Y i ≠ Y j := fun h => Y.injective.ne h
  refine ⟨(hR.emitT (Y 0) F ts).seth (Y 0) F (Y 6) (hY (by decide)) p, fun i hi => ?_, fun i hi h6 => ?_, ?_, fun j => ?_⟩
  · simp only [WState.seth_st]; exact emitT_st_ne (Y 0) F (Y i) (hY hi) σ ts
  · simp only [WState.seth_sh, Function.update_of_ne (hY h6)]; exact emitT_sh_ne (Y 0) F (Y i) (hY hi) σ ts
  · simp
  · simp only [WState.seth_val]; exact emitT_val_ne (Y 0) F (X j) (hFX 7 j).symm (hFX 16 j).symm σ ts

theorem tToks_eq (d : FData) :
    tToks d = (digFacs 0 0 d.q d.J d.B0 d.L d.ρs).flatten ++
      ((if d.pair then (digFacs d.G0 d.J d.q d.J d.B1 d.L d.ρs).flatten else []) ++
      (facToks (linToks 0 d.C0) (d.ρs.getD (d.rc * d.J) 0 : ℤ) d.q ++
      ((if d.pair then facToks (linToks d.G0 d.C1) (d.ρs.getD (d.rc * d.J + 1) 0 : ℤ) d.q else []) ++
      ([Tok.const 1] ++ List.replicate (d.rc * (d.J + 1)) Tok.mul)))) := by
  unfold tToks prodToks
  rw [tFacs_length]
  unfold tFacs
  cases d.pair <;> simp [List.append_assoc]

/-- One score factor `1 − (X^r − σ_r)^{q−1}` after the tokens `ts`, the residue head at `m`. -/
theorem scoreFac_spec (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ)
    (SC : Fin 8) (hSC0 : SC ≠ 0) (hSC6 : SC ≠ 6) (iG io iL : Fin 24)
    (hi : [iG, io, iL, 3, 5].Nodup) (C : List ℤ) (G o : ℕ) (rC : List Bool) (hC : σ.st (Y SC) = encI C ++ rC)
    (hCl : C.length = G) (hGv : σ.val (X iG) = G) (hov : σ.val (X io) = o) (hLv : (encI C).length ≤ σ.val (X iL))
    (hLΛ : σ.val (X iL) ≤ Λ) (hoG : o + G ≤ Λ) (hz : ∀ z ∈ C, natBitLength z.natAbs ≤ Λ)
    (ts : List Tok) (m : ℕ) (hm : m < d.ρs.length) (rK : List Bool) (hK : σ.st (Y 6) = encN d.ρs ++ rK)
    (hcap : TCap cap F ((emitT (Y 0) F σ ts).seth (Y 6) (encN (d.ρs.take m)).length)
      (facToks (linToks o C) (d.ρs[m] : ℤ) d.q) Λ) :
    WExec cap (facP (Y 0) F (Y 6) (X 5) (stP (Y 0) (Y SC) F (X iG) (X io) (X iL) (X 3)))
      ((emitT (Y 0) F σ ts).seth (Y 6) (encN (d.ρs.take m)).length)
      ((emitT (Y 0) F σ (ts ++ facToks (linToks o C) (d.ρs[m] : ℤ) d.q)).seth (Y 6) (encN (d.ρs.take (m + 1))).length)
      (8000 * (Λ + 1) ^ 3) := by
  have hY : ∀ {i j : Fin 8}, i ≠ j → Y i ≠ Y j := fun h => Y.injective.ne h
  have hFX := hs.disj
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hi
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3⟩, ⟨c1, c2⟩, -⟩ := hi
  have hXX : ∀ {i j : Fin 24}, i ≠ j → X i ≠ X j := fun h => X.injective.ne h
  set τ := (emitT (Y 0) F σ ts).seth (Y 6) (encN (d.ρs.take m)).length with hτ
  have sh := shifted_of Y X F σ hs.rest hFX ts (encN (d.ρs.take m)).length
  rw [← hτ] at sh
  have hKS : Y 6 ≠ Y 0 := hY (by decide)
  have hSCS : Y 0 ≠ Y SC := hY (Ne.symm hSC0)
  rw [facToks_eq] at hcap
  have cP := TCap.left cap F (TCap.left cap F hcap)
  have cP' := TCap.right cap (Y 0) F cP
  set τ1 := emitT (Y 0) F τ [Tok.const 1] with hτ1
  have h1 : TRest (Y 0) F τ1 := sh.rest.emitT (Y 0) F _
  have v1 : ∀ j, τ1.val (X j) = σ.val (X j) := fun j => by
    rw [hτ1, emitT_val_ne (Y 0) F (X j) (hFX 7 j).symm (hFX 16 j).symm, sh.val]
  have hP := stP_run cap (Y 0) F (Y SC) hSCS (X iG) (X io) (X iL) (X 3) (fun i => hFX i iG) (fun i => hFX i io)
    (fun i => hFX i iL) (fun i => hFX i 3) G 0 o (σ.val (X iL)) Λ [C] (by simp [hCl]) (by simp) rC τ1 h1
    (by rw [hτ1, emitT_st_ne (Y 0) F _ hSCS.symm, sh.st SC hSC0, hC]; simp)
    (by rw [hτ1, emitT_sh_ne (Y 0) F _ hSCS.symm, sh.sh SC hSC0 hSC6]; exact hs.sh SC hSC0)
    (by rw [v1, hGv]) (by rw [v1, hov]) (by rw [v1]) (by rw [v1]; exact hs.zero 3 (by decide))
    (by simpa using hLv) (by omega) hoG hLΛ (by simpa using hz) (by simpa using cP')
  have hρm : natBitLength d.ρs[m] ≤ Λ := hb.zρ _ (List.getElem_mem hm)
  have e := facP_spec cap (Y 0) F (Y 6) hKS (X 5) (fun i => hFX i 5) _ (linToks o C) d.ρs[m] d.q Λ
    (4000 * (Λ + 1) ^ 3) (encN (d.ρs.take m)) (encN (d.ρs.drop (m + 1)) ++ rK) τ sh.rest
    (by rw [sh.st 6 (by decide), hK, encN_split d.ρs m hm]; simp [List.append_assoc]) sh.shK
    (by rw [sh.val]; exact hs.vQ) hb.q hρm (by rw [facToks_eq]; exact hcap) (by simpa using hP)
  refine WExec.cast cap e ?_ ?_
  · rw [hτ, emitT_seth (Y 0) F (Y 6) hKS, wseth_seth, emitT_append, encN_take_succ d.ρs m hm]
  · have : (Λ + 1) ^ 2 ≤ (Λ + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
    omega

def tD0 (d : FData) : List Tok := (digFacs 0 0 d.q d.J d.B0 d.L d.ρs).flatten
def tD1 (d : FData) : List Tok := if d.pair then (digFacs d.G0 d.J d.q d.J d.B1 d.L d.ρs).flatten else []
def tF0 (d : FData) : List Tok := facToks (linToks 0 d.C0) (d.ρs.getD (d.rc * d.J) 0 : ℤ) d.q
def tF1 (d : FData) : List Tok :=
  if d.pair then facToks (linToks d.G0 d.C1) (d.ρs.getD (d.rc * d.J + 1) 0 : ℤ) d.q else []

theorem tToks_eq' (d : FData) :
    tToks d = tD0 d ++ (tD1 d ++ (tF0 d ++ (tF1 d ++ ([Tok.const 1] ++ List.replicate (d.rc * (d.J + 1)) Tok.mul)))) := by
  rw [tToks_eq]; rfl

theorem rc_cases (d : FData) : (d.pair = true ∧ d.rc = 2) ∨ (d.pair = false ∧ d.rc = 1) := by
  unfold FData.rc; cases d.pair <;> simp

/-- Step 1: the digits of role 0. -/
theorem tP_A (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ) (hρ : d.rc * (d.J + 1) ≤ d.ρs.length)
    (hr : FBoundR X σ Λ) (hcap : TCap cap F σ (tD0 d) Λ) :
    WExec cap (roleDig (Y 0) F (Y 1) (Y 5) (Y 6) (X 14) (X 15) (X 16) (X 6) (X 2) (X 3) (X 5) (X 4) (X 1)) σ
      ((emitT (Y 0) F σ (tD0 d)).seth (Y 6) (encN (d.ρs.take d.J)).length) (20000 * (Λ + 1) ^ 4) := by
  have hY : ∀ {i j : Fin 8}, i ≠ j → Y i ≠ Y j := fun h => Y.injective.ne h
  have hFn : ∀ (l : List (Fin 24)) (i : Fin 24), F i ∉ l.map X := fun l i hm => by
    obtain ⟨j, -, hj⟩ := List.mem_map.1 hm; exact hs.disj i j hj.symm
  obtain ⟨rB0, hB0⟩ := hs.stB0
  obtain ⟨rL, hLs⟩ := hs.stL
  obtain ⟨rK, hKs⟩ := hs.stK
  have hJρ : d.J ≤ d.ρs.length := by
    rcases rc_cases d with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hρ <;> nlinarith
  have e := roleDig_spec cap (Y 0) F (Y 1) (Y 5) (Y 6) (hY (by decide)) (hY (by decide)) (hY (by decide))
    (hY (by decide)) (hY (by decide)) (X 14) (X 15) (X 16) (X 6) (X 2) (X 3) (X 5) (X 4) (X 1)
    (fun i => hFn [14, 15, 16, 6, 2, 3, 5, 4, 1] i) (nodupX X [14, 15, 16, 6, 2, 3, 5, 4, 1] (by decide))
    d.G0 d.J 0 0 d.q (σ.val (X 16)) (σ.val (X 6)) Λ d.B0 d.L d.ρs hb.b0 (by rw [hb.lB0]) hb.lL
    (by omega) rB0 rL rK σ hs.rest hB0 (hs.sh 1 (by decide))
    hLs (hs.sh 5 (by decide)) hKs (by simp [hs.sh 6 (by decide), encN]) hs.vG0 hs.vo0 rfl rfl
    (hs.zero 2 (by decide)) (hs.zero 3 (by decide)) hs.vQ (hs.zero 4 (by decide)) hs.vJ
    (by rw [List.take_of_length_le (by rw [hb.lB0])]; exact hs.vL0)
    (le_trans (encN_take_le _ _) hs.vLF)
    hb.J (by have := hb.G; omega) (hr 16 (by decide)) (hr 6 (by decide)) hb.q
    (fun b hb' z hz => hb.zB b (List.mem_append_left _ hb') z hz) hb.zL hb.zρ hcap
  rw [Nat.zero_add] at e
  exact e

/-- Step 2: the digits of role 1 (pair calls). -/
theorem tP_B (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ) (hρ : d.rc * (d.J + 1) ≤ d.ρs.length)
    (hr : FBoundR X σ Λ) (hcap : TCap cap F (emitT (Y 0) F σ (tD0 d)) (tD1 d) Λ) :
    WExec cap (.ifr (X 0) (roleDig (Y 0) F (Y 3) (Y 5) (Y 6) (X 18) (X 19) (X 20) (X 6) (X 2) (X 3) (X 5) (X 4) (X 1))
      .skip) ((emitT (Y 0) F σ (tD0 d)).seth (Y 6) (encN (d.ρs.take d.J)).length)
      ((emitT (Y 0) F σ (tD0 d ++ tD1 d)).seth (Y 6) (encN (d.ρs.take (d.rc * d.J))).length)
      (20000 * (Λ + 1) ^ 4 + 1) := by
  have hY : ∀ {i j : Fin 8}, i ≠ j → Y i ≠ Y j := fun h => Y.injective.ne h
  have hFX := hs.disj
  have hFn : ∀ (l : List (Fin 24)) (i : Fin 24), F i ∉ l.map X := fun l i hm => by
    obtain ⟨j, -, hj⟩ := List.mem_map.1 hm; exact hFX i j hj.symm
  obtain ⟨rB1, hB1⟩ := hs.stB1
  obtain ⟨rL, hLs⟩ := hs.stL
  obtain ⟨rK, hKs⟩ := hs.stK
  have hKS : Y 6 ≠ Y 0 := hY (by decide)
  set σ1 := (emitT (Y 0) F σ (tD0 d)).seth (Y 6) (encN (d.ρs.take d.J)).length with hσ1
  have sh1 := shifted_of Y X F σ hs.rest hFX (tD0 d) (encN (d.ρs.take d.J)).length
  rw [← hσ1] at sh1
  refine ifr_opt cap d.pair (by rw [sh1.val]; exact hs.vPr) (fun hp => ?_) (fun hp => ?_)
  · have hrc : d.rc = 2 := by unfold FData.rc; simp [hp]
    rw [hrc] at hρ
    have c2 : TCap cap F σ1 (digFacs d.G0 d.J d.q d.J d.B1 d.L d.ρs).flatten Λ := by
      have := hcap; unfold tD1 at this; rw [if_pos hp] at this; exact this.seth cap F (Y 6) _
    have e := roleDig_spec cap (Y 0) F (Y 3) (Y 5) (Y 6) (hY (by decide)) (hY (by decide)) hKS
      (hY (by decide)) (hY (by decide)) (X 18) (X 19) (X 20) (X 6) (X 2) (X 3) (X 5) (X 4) (X 1)
      (fun i => hFn [18, 19, 20, 6, 2, 3, 5, 4, 1] i) (nodupX X [18, 19, 20, 6, 2, 3, 5, 4, 1] (by decide))
      d.G1 d.J d.G0 d.J d.q (σ.val (X 20)) (σ.val (X 6)) Λ d.B1 d.L d.ρs hb.b1 (by rw [hb.lB1]) hb.lL (by omega)
      rB1 rL rK σ1 sh1.rest (by rw [sh1.st 3 (by decide)]; exact hB1)
      (by rw [sh1.sh 3 (by decide) (by decide)]; exact hs.sh 3 (by decide))
      (by rw [sh1.st 5 (by decide)]; exact hLs)
      (by rw [sh1.sh 5 (by decide) (by decide)]; exact hs.sh 5 (by decide))
      (by rw [sh1.st 6 (by decide)]; exact hKs) sh1.shK
      (by rw [sh1.val]; exact hs.vG1) (by rw [sh1.val]; exact hs.vo1) (sh1.val 20) (sh1.val 6)
      (by rw [sh1.val]; exact hs.zero 2 (by decide)) (by rw [sh1.val]; exact hs.zero 3 (by decide))
      (by rw [sh1.val]; exact hs.vQ) (by rw [sh1.val]; exact hs.zero 4 (by decide)) (by rw [sh1.val]; exact hs.vJ)
      (by rw [List.take_of_length_le (by rw [hb.lB1])]; exact hs.vL1)
      (le_trans (encN_take_le _ _) hs.vLF)
      hb.J (by have := hb.G; omega) (hr 20 (by decide)) (hr 6 (by decide)) hb.q
      (fun b hb' z hz => hb.zB b (List.mem_append_right _ hb') z hz) hb.zL hb.zρ c2
    refine WExec.cast cap e ?_ le_rfl
    rw [hσ1, emitT_seth (Y 0) F (Y 6) hKS, wseth_seth, emitT_append, hrc, show 2 * d.J = d.J + d.J by ring]
    unfold tD1; rw [if_pos hp]
  · have hrc : d.rc = 1 := by unfold FData.rc; simp [hp]
    rw [hσ1, hrc, Nat.one_mul]; unfold tD1; rw [if_neg (by simp [hp]), List.append_nil]

/-- Step 3: the score of role 0. -/
theorem tP_C (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ) (hρ : d.rc * (d.J + 1) ≤ d.ρs.length)
    (hr : FBoundR X σ Λ) (hcap : TCap cap F (emitT (Y 0) F σ (tD0 d ++ tD1 d)) (tF0 d) Λ) :
    WExec cap (facP (Y 0) F (Y 6) (X 5) (stP (Y 0) (Y 2) F (X 14) (X 15) (X 17) (X 3)))
      ((emitT (Y 0) F σ (tD0 d ++ tD1 d)).seth (Y 6) (encN (d.ρs.take (d.rc * d.J))).length)
      ((emitT (Y 0) F σ (tD0 d ++ tD1 d ++ tF0 d)).seth (Y 6) (encN (d.ρs.take (d.rc * d.J + 1))).length)
      (8000 * (Λ + 1) ^ 3) := by
  obtain ⟨rC0, hC0⟩ := hs.stC0
  obtain ⟨rK, hKs⟩ := hs.stK
  have hm0 : d.rc * d.J < d.ρs.length := by
    rcases rc_cases d with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at hρ ⊢ <;> nlinarith
  have hg0 : d.ρs.getD (d.rc * d.J) 0 = d.ρs[d.rc * d.J] := List.getD_eq_getElem _ _ hm0
  have e := scoreFac_spec cap Y X F d Λ σ hs hb 2 (by decide) (by decide) 14 15 17 (by decide) d.C0 d.G0 0 rC0 hC0
    hb.c0 hs.vG0 hs.vo0 hs.vS0 (hr 17 (by decide)) (by have := hb.G; omega)
    (fun z hz => hb.zC z (List.mem_append_left _ hz)) (tD0 d ++ tD1 d) (d.rc * d.J) hm0 rK hKs
    (by have := hcap.seth cap F (Y 6) (encN (d.ρs.take (d.rc * d.J))).length; unfold tF0 at this; rwa [hg0] at this)
  unfold tF0; rw [hg0]; exact e

/-- Step 4: the score of role 1 (pair calls). -/
theorem tP_D (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ) (hρ : d.rc * (d.J + 1) ≤ d.ρs.length)
    (hr : FBoundR X σ Λ) (hcap : TCap cap F (emitT (Y 0) F σ (tD0 d ++ tD1 d ++ tF0 d)) (tF1 d) Λ) :
    WExec cap (.ifr (X 0) (facP (Y 0) F (Y 6) (X 5) (stP (Y 0) (Y 4) F (X 18) (X 19) (X 21) (X 3))) .skip)
      ((emitT (Y 0) F σ (tD0 d ++ tD1 d ++ tF0 d)).seth (Y 6) (encN (d.ρs.take (d.rc * d.J + 1))).length)
      ((emitT (Y 0) F σ (tD0 d ++ tD1 d ++ tF0 d ++ tF1 d)).seth (Y 6) (encN (d.ρs.take (d.rc * (d.J + 1)))).length)
      (8000 * (Λ + 1) ^ 3 + 1) := by
  have hFX := hs.disj
  obtain ⟨rC1, hC1⟩ := hs.stC1
  obtain ⟨rK, hKs⟩ := hs.stK
  have hv : ((emitT (Y 0) F σ (tD0 d ++ tD1 d ++ tF0 d)).seth (Y 6)
      (encN (d.ρs.take (d.rc * d.J + 1))).length).val (X 0) = if d.pair then 1 else 0 := by
    rw [WState.seth_val, emitT_val_ne (Y 0) F (X 0) (hFX 7 0).symm (hFX 16 0).symm]; exact hs.vPr
  refine ifr_opt cap d.pair hv (fun hp => ?_) (fun hp => ?_)
  · have hrc : d.rc = 2 := by unfold FData.rc; simp [hp]
    have hm1 : d.rc * d.J + 1 < d.ρs.length := by rw [hrc] at hρ ⊢; nlinarith
    have hg1 : d.ρs.getD (d.rc * d.J + 1) 0 = d.ρs[d.rc * d.J + 1] := List.getD_eq_getElem _ _ hm1
    have e := scoreFac_spec cap Y X F d Λ σ hs hb 4 (by decide) (by decide) 18 19 21 (by decide) d.C1 d.G1 d.G0
      rC1 hC1 hb.c1 hs.vG1 hs.vo1 hs.vS1 (hr 21 (by decide)) (by have := hb.G; omega)
      (fun z hz => hb.zC z (List.mem_append_right _ hz)) (tD0 d ++ tD1 d ++ tF0 d) (d.rc * d.J + 1) hm1 rK hKs
      (by have := hcap.seth cap F (Y 6) (encN (d.ρs.take (d.rc * d.J + 1))).length
          unfold tF1 at this; rwa [if_pos hp, hg1] at this)
    unfold tF1; rw [if_pos hp, hg1, show d.rc * (d.J + 1) = d.rc * d.J + 1 + 1 by rw [hrc]; ring]; exact e
  · have hrc : d.rc = 1 := by unfold FData.rc; simp [hp]
    unfold tF1; rw [if_neg (by simp [hp]), List.append_nil, hrc]; simp

theorem replicate_words (t : Tok) (m : ℕ) :
    ((List.replicate m t).flatMap tokWord).length = m * (tokWord t).length := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, List.flatMap_cons, List.length_append, ih]; ring

/-- Step 5: the empty product, the multiplications, and the residue head back to `0`. -/
theorem tP_T (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ)
    (hr : FBoundR X σ Λ) (W : List Tok)
    (hcap : TCap cap F (emitT (Y 0) F σ W) ([Tok.const 1] ++ List.replicate (d.rc * (d.J + 1)) Tok.mul) Λ) :
    WExec cap (tTail Y X F) ((emitT (Y 0) F σ W).seth (Y 6) (encN (d.ρs.take (d.rc * (d.J + 1)))).length)
      (emitT (Y 0) F σ (W ++ ([Tok.const 1] ++ List.replicate (d.rc * (d.J + 1)) Tok.mul))) (1000 * (Λ + 1)) := by
  have hY : ∀ {i j : Fin 8}, i ≠ j → Y i ≠ Y j := fun h => Y.injective.ne h
  have hFF : ∀ {i j : Fin 24}, i ≠ j → F i ≠ F j := fun h => F.injective.ne h
  have hXX : ∀ {i j : Fin 24}, i ≠ j → X i ≠ X j := fun h => X.injective.ne h
  have hFX := hs.disj
  have hKS : Y 6 ≠ Y 0 := hY (by decide)
  set R := d.rc * (d.J + 1) with hR
  have hRΛ : R ≤ 2 * Λ + 2 := by
    have := hb.J; rcases rc_cases d with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [hR, h] <;> omega
  set p := (encN (d.ρs.take R)).length with hp
  set σ4 := (emitT (Y 0) F σ W).seth (Y 6) p with hσ4
  have sh := shifted_of Y X F σ hs.rest hFX W p
  rw [← hσ4] at sh
  have c1 := TCap.left cap F hcap
  have e1 := litC_spec cap (Y 0) F (.const 1) σ4 sh.rest
    (by rw [hσ4, WState.seth_val]; unfold TCap at c1; simp at c1; omega)
    (by rw [hσ4, WState.seth_val]; unfold TCap at c1; simp at c1; omega)
  set σ5 := emitT (Y 0) F σ4 [Tok.const 1] with hσ5
  have v5 : ∀ j, σ5.val (X j) = σ.val (X j) := fun j => by
    rw [hσ5, emitT_val_ne (Y 0) F _ (hFX 7 j).symm (hFX 16 j).symm, sh.val]
  have e2 := copyR_spec cap (v := X 11) (d := X 4) (t := F 8) (hXX (by decide)) (hFX 8 11).symm (hFX 8 4).symm σ5
    (by rw [hσ5, emitT_val_ne (Y 0) F _ (hFF (by decide)) (hFF (by decide)), hσ4, WState.seth_val,
          emitT_val_ne (Y 0) F _ (hFF (by decide)) (hFF (by decide))]; exact hs.rest.zero (Y 0) F 8 (by decide))
    (by rw [v5, v5, hs.zero 4 (by decide), hs.vR]; unfold TCap at hcap; simp at hcap; omega)
  rw [v5, v5, hs.zero 4 (by decide), hs.vR, Nat.zero_add] at e2
  set σ6 := σ5.setv (X 4) R with hσ6
  have h6 : TRest (Y 0) F σ6 := (sh.rest.emitT (Y 0) F _).setv (Y 0) F (X 4) (fun i => hFX i 4) R
  have c2 := TCap.right cap (Y 0) F hcap
  have e3 := litLoop_spec cap (Y 0) F (X 4) (fun i => hFX i 4) .mul R σ6 h6 (by simp [hσ6])
    (by rw [hσ6, WState.setv_val, Function.update_of_ne (hFX 7 4), hσ5, emitT_val7, hσ4, WState.seth_val]
        unfold TCap at c2; rw [emitT_val7] at c2
        rw [replicate_words] at c2
        rw [tokWord_mul_length] at c2 ⊢; simp at c2 ⊢; nlinarith)
    (by rw [hσ6, WState.setv_val, Function.update_of_ne (hFX 16 4), hσ5, emitT_val16, hσ4, WState.seth_val]
        unfold TCap at c2; rw [emitT_val16] at c2; simp at c2 ⊢; omega)
  set σ7 := (emitT (Y 0) F σ6 (List.replicate R Tok.mul)).setv (X 4) 0 with hσ7
  set E := emitT (Y 0) F σ (W ++ ([Tok.const 1] ++ List.replicate R Tok.mul)) with hE
  have hσ7' : σ7 = ((E.seth (Y 6) p).setv (X 4) R).setv (X 4) 0 := by
    rw [hσ7, hσ6, hσ5, hσ4, emitT_seth (Y 0) F (Y 6) hKS, emitT_append,
      emitT_setv (Y 0) F (X 4) (hFX 7 4).symm (hFX 16 4).symm, emitT_seth (Y 0) F (Y 6) hKS, emitT_append, hE,
      List.append_assoc]
  have hE4 : E.val (X 4) = 0 := by
    rw [hE, emitT_val_ne (Y 0) F _ (hFX 7 4).symm (hFX 16 4).symm]; exact hs.zero 4 (by decide)
  have hE19 : E.val (F 19) = 0 := by
    rw [hE, emitT_val_ne (Y 0) F _ (hFF (by decide)) (hFF (by decide))]; exact hs.rest.zero (Y 0) F 19 (by decide)
  have hE8 : E.val (F 8) = 0 := by
    rw [hE, emitT_val_ne (Y 0) F _ (hFF (by decide)) (hFF (by decide))]; exact hs.rest.zero (Y 0) F 8 (by decide)
  have hEK : E.sh (Y 6) = 0 := by rw [hE, emitT_sh_ne (Y 0) F _ hKS]; exact hs.sh 6 (by decide)
  have hE7 : E.val (X 7) = σ.val (X 7) := by rw [hE, emitT_val_ne (Y 0) F _ (hFX 7 7).symm (hFX 16 7).symm]
  have hplk : p ≤ σ.val (X 7) := le_trans (encN_take_le _ _) hs.vLK
  have hLK := hr 7 (by decide)
  rw [hσ7'] at e3
  generalize E = E' at hE4 hE19 hE8 hEK hE7 e3 ⊢
  have e4 := copyR_spec cap (v := X 7) (d := F 19) (t := F 8) (hFX 19 7).symm (hFX 8 7).symm (hFF (by decide))
    (((E'.seth (Y 6) p).setv (X 4) R).setv (X 4) 0)
    (by simp [Function.update_of_ne (hFX 8 4), hE8])
    (by simp [Function.update_of_ne (hFX 19 4), Function.update_of_ne (hXX (show (7 : Fin 24) ≠ 4 by decide)),
          hE19, hE7]
        unfold TCap at hcap; omega)
  simp only [WState.setv_val, WState.seth_val, Function.update_of_ne (hFX 19 4),
    Function.update_of_ne (hXX (show (7 : Fin 24) ≠ 4 by decide)), hE19, hE7, Nat.zero_add] at e4
  have e5 := wrewind_spec cap (Y 6) (F 19) (σ.val (X 7))
    ((((E'.seth (Y 6) p).setv (X 4) R).setv (X 4) 0).setv (F 19) (σ.val (X 7))) (by simp) (by simp; unfold TCap at hcap; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ ?_
  · apply WState.eq
    · funext j; by_cases hj : j = Y 6
      · subst hj; simp [hEK]; omega
      · simp [Function.update_of_ne hj]
    · simp
    · funext r; by_cases r19 : r = F 19
      · subst r19; simp [hE19]
      · by_cases r4 : r = X 4
        · subst r4; simp [Function.update_of_ne (hFX 19 4).symm, hE4]
        · simp [Function.update_of_ne r19, Function.update_of_ne r4]
    · simp
  · rw [tokWord_const1_length, tokWord_mul_length]; nlinarith

/-- **The Fermat product printer.** -/
theorem tP_spec (d : FData) (Λ : ℕ) (σ : WState ns nr) (hs : FState Y X F σ d) (hb : FBound d Λ) (hρ : d.rc * (d.J + 1) ≤ d.ρs.length)
    (hr : FBoundR X σ Λ) (hcap : TCap cap F σ (tToks d) Λ) :
    WExec cap (tP Y X F) σ (emitT (Y 0) F σ (tToks d)) (100000 * (Λ + 1) ^ 4) := by
  rw [tToks_eq'] at hcap ⊢
  have cA := TCap.left cap F hcap
  have r1 := TCap.right cap (Y 0) F hcap
  have cB := TCap.left cap F r1
  have r2 := TCap.right cap (Y 0) F r1
  rw [emitT_append] at r2
  have cC := TCap.left cap F r2
  have r3 := TCap.right cap (Y 0) F r2
  rw [emitT_append] at r3
  have cD := TCap.left cap F r3
  have r4 := TCap.right cap (Y 0) F r3
  rw [emitT_append] at r4
  have e1 := tP_A cap Y X F d Λ σ hs hb hρ hr cA
  have e2 := tP_B cap Y X F d Λ σ hs hb hρ hr cB
  have e3 := tP_C cap Y X F d Λ σ hs hb hρ hr cC
  have e4 := tP_D cap Y X F d Λ σ hs hb hρ hr cD
  have e5 := tP_T cap Y X F d Λ σ hs hb hr _ r4
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 e5)))) ?_ ?_
  · simp [List.append_assoc]
  · have h3 : (Λ + 1) ^ 3 ≤ (Λ + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : Λ + 1 ≤ (Λ + 1) ^ 3 := by nlinarith [Nat.one_le_pow 2 (Λ + 1) (by omega)]
    omega

end Prod

end NearCubicGates.Close.CounterMachine
