import Proof.Wire_3_5.FinalPassRegLib
import Proof.Wire_3_5.FinalPassListEvalRef

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.ListEval
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

/-! ## Registers and tactics -/

scoped notation "rMR" => (0 : Fin 15)
scoped notation "rS" => (1 : Fin 15)
scoped notation "rP" => (2 : Fin 15)
scoped notation "rC" => (3 : Fin 15)
scoped notation "rW" => (4 : Fin 15)
scoped notation "rV" => (5 : Fin 15)
scoped notation "rU" => (6 : Fin 15)
scoped notation "rT" => (7 : Fin 15)
scoped notation "rF" => (8 : Fin 15)
scoped notation "rR" => (9 : Fin 15)
scoped notation "rTP" => (10 : Fin 15)
scoped notation "rSP" => (11 : Fin 15)
scoped notation "rX" => (12 : Fin 15)
scoped notation "rT1" => (13 : Fin 15)
scoped notation "rT2" => (14 : Fin 15)

abbrev LState := RState 2 15
abbrev LProg := RM 2 15

/-- Close an equality of abstract states field by field. -/
syntax "rs_eq" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| rs_eq) => `(tactic| rs_eq [])
  | `(tactic| rs_eq [$ts,*]) => `(tactic| (refine RState.eq ?_ ?_ ?_ <;>
      first
        | (funext x; fin_cases x <;> (try simp [$ts,*]) <;> (try omega))
        | (try simp [$ts,*])))

variable (inp : Fin 3 → List Bool) (cap : ℕ)

theorem readTapeBit_drop (l : List Bool) (p k : ℕ) : readTapeBit l (p + k) = readTapeBit (l.drop p) k := by
  unfold readTapeBit
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem drop_succ_of_cons {l t : List Bool} {p : ℕ} {a : Bool} (h : l.drop p = a :: t) : l.drop (p + 1) = t := by
  have := congrArg List.tail h
  simpa [List.tail_drop] using this

theorem read_of_cons {l t : List Bool} {p : ℕ} {a : Bool} (h : l.drop p = a :: t) : readTapeBit l p = a := by
  have := readTapeBit_drop l p 0
  simp only [Nat.add_zero] at this
  rw [this, h]; rfl

theorem read_of_nil {l : List Bool} {p : ℕ} (h : l.drop p = []) : readTapeBit l p = false := by
  have := readTapeBit_drop l p 0
  simp only [Nat.add_zero] at this
  rw [this, h]; rfl

theorem drop_add_of_append {l a t : List Bool} {p : ℕ} (h : l.drop p = a ++ t) : l.drop (p + a.length) = t := by
  rw [← List.drop_drop, h, List.drop_left]

/-! ## The cyclic counter -/

/-- Add one to the residue. -/
def cycInc : LProg := .seq (.inc rV) (.seq (.dec rU) (.ifr rU .skip (RM.move rV rU)))

/-- Subtract one from the residue. -/
def cycDec : LProg := .seq (.ifr rV .skip (RM.move rU rV)) (.seq (.dec rV) (.inc rU))

/-- The counter holds residue `v` of modulus `P`. -/
def CycOk (P v : ℕ) (σ : LState) : Prop := σ.val rV = v ∧ σ.val rU = P - v ∧ v < P

/-- Set the counter to residue `v` of modulus `P`. -/
def setCyc (P v : ℕ) (σ : LState) : LState := (σ.setv rV v).setv rU (P - v)

@[simp] theorem setCyc_sh (P v : ℕ) (σ : LState) : (setCyc P v σ).sh = σ.sh := rfl
@[simp] theorem setCyc_cell (P v : ℕ) (σ : LState) : (setCyc P v σ).cell = σ.cell := rfl

theorem cycOk_set (P v : ℕ) (σ : LState) (hv : v < P) : CycOk P v (setCyc P v σ) := by
  refine ⟨?_, ?_, hv⟩ <;> simp [setCyc]

theorem cycInc_spec (P v : ℕ) (σ : LState) (hc : CycOk P v σ) (hP : P ≤ cap) :
    RExec inp cap cycInc σ (setCyc P ((v + 1) % P) σ) (7 * cap + 8) := by
  obtain ⟨hV, hU, hv⟩ := hc
  have h1 := RExec.inc (inp := inp) (cap := cap) rV σ (by omega)
  have h2 := RExec.dec (inp := inp) (cap := cap) rU (σ.setv rV (σ.val rV + 1)) (by simp; omega)
  set τ := (σ.setv rV (σ.val rV + 1)).setv rU ((σ.setv rV (σ.val rV + 1)).val rU - 1) with hτ
  have hτV : τ.val rV = v + 1 := by simp [τ, hV]
  have hτU : τ.val rU = P - v - 1 := by simp [τ, hU]
  by_cases hw : v + 1 < P
  · have h3 : RExec inp cap (.ifr rU .skip (RM.move rV rU)) τ τ 1 := RExec.ifrT (by omega) (RExec.skip τ)
    refine RExec.cast inp cap (RExec.seq h1 (RExec.seq h2 h3)) ?_ (by omega)
    have hmod : (v + 1) % P = v + 1 := Nat.mod_eq_of_lt hw
    rs_eq [τ, setCyc, hmod, hV, hU]
  · have hP' : v + 1 = P := by omega
    have h3 := move_spec inp cap rV rU (by decide) (v + 1) τ hτV (by omega) (by omega)
    have h3' : RExec inp cap (.ifr rU .skip (RM.move rV rU)) τ ((τ.setv rV 0).setv rU (τ.val rU + τ.val rV))
        (7 * (v + 1) + 2) := RExec.ifrF (by omega) h3
    refine RExec.cast inp cap (RExec.seq h1 (RExec.seq h2 h3')) ?_ (by omega)
    have hmod : (v + 1) % P = 0 := by rw [hP']; exact Nat.mod_self P
    rs_eq [τ, setCyc, hmod, hV, hU]

theorem cycDec_spec (P v : ℕ) (σ : LState) (hc : CycOk P v σ) (hP : P ≤ cap) :
    RExec inp cap cycDec σ (setCyc P ((v + P - 1) % P) σ) (7 * cap + 8) := by
  obtain ⟨hV, hU, hv⟩ := hc
  by_cases hv0 : v = 0
  · have h1 := move_spec inp cap rU rV (by decide) P σ (by omega) (by omega) (by omega)
    have h1' : RExec inp cap (.ifr rV .skip (RM.move rU rV)) σ ((σ.setv rU 0).setv rV (σ.val rV + σ.val rU))
        (7 * P + 2) := RExec.ifrF (by omega) h1
    set τ := (σ.setv rU 0).setv rV (σ.val rV + σ.val rU) with hτ
    have h2 := RExec.dec (inp := inp) (cap := cap) rV τ (by simp [τ]; omega)
    have h3 := RExec.inc (inp := inp) (cap := cap) rU (τ.setv rV (τ.val rV - 1)) (by simp [τ]; omega)
    refine RExec.cast inp cap (RExec.seq h1' (RExec.seq h2 h3)) ?_ (by omega)
    have hmod : (v + P - 1) % P = P - 1 := by rw [hv0, Nat.zero_add]; exact Nat.mod_eq_of_lt (by omega)
    rs_eq [τ, setCyc, hmod, hV, hU, hv0]
  · have h1 : RExec inp cap (.ifr rV .skip (RM.move rU rV)) σ σ 1 := RExec.ifrT (by omega) (RExec.skip σ)
    have h2 := RExec.dec (inp := inp) (cap := cap) rV σ (by omega)
    have h3 := RExec.inc (inp := inp) (cap := cap) rU (σ.setv rV (σ.val rV - 1)) (by simp; omega)
    refine RExec.cast inp cap (RExec.seq h1 (RExec.seq h2 h3)) ?_ (by omega)
    have hmod : (v + P - 1) % P = v - 1 := by
      rw [show v + P - 1 = (v - 1) + P by omega, Nat.add_mod_right]; exact Nat.mod_eq_of_lt (by omega)
    rs_eq [setCyc, hmod, hV, hU]

theorem mod_succ_add (P v n : ℕ) : ((v + 1) % P + n) % P = (v + (n + 1)) % P := by
  rw [Nat.mod_add_mod]; congr 1; omega

/-! ## Reading the window into the counter -/

/-- Forward on the table, counting its position. -/
def fwdT : LProg := RM.fwdC 1 rTP

/-- One unit of the window: forward, count it, add it to the residue. -/
def wStep : LProg := .seq fwdT (.seq (.inc rW) cycInc)

/-- Read the window `1^{W}0` into `W` and add it to the residue. -/
def readWcyc : LProg := .seq (.whs 1 wStep) fwdT

/-- The state after reading `n` window units. -/
def wState (P v n : ℕ) (σ : LState) : LState :=
  setCyc P ((v + n) % P) (((σ.seth 1 (σ.sh 1 + n)).setv rTP (σ.val rTP + n)).setv rW (σ.val rW + n))

theorem wLoop_spec (P : ℕ) (rest : List Bool) (hP1 : 1 ≤ P) (hP : P ≤ cap) :
    ∀ (n v : ℕ) (σ : LState), (inp 1).drop (σ.sh 1) = List.replicate n true ++ false :: rest → CycOk P v σ →
      σ.val rTP + n ≤ cap → σ.val rW + n ≤ cap →
      RExec inp cap (.whs 1 wStep) σ (wState P v n σ) (n * (7 * cap + 20) + 1)
  | 0, v, σ, hd, hc, _, _ => by
    have e : wState P v 0 σ = σ := by
      obtain ⟨hV, hU, hv⟩ := hc
      unfold wState
      rs_eq [setCyc, Nat.mod_eq_of_lt hv, hV, hU]
    rw [e]
    exact RExec.mono (RExec.whsF (by unfold sbit; exact read_of_cons (by simpa using hd))) (by omega)
  | n + 1, v, σ, hd, hc, ht, hw => by
    obtain ⟨hV, hU, hv⟩ := hc
    have h1 := fwdC_spec inp cap 1 rTP σ (by omega)
    set σ1 := (σ.seth 1 (σ.sh 1 + 1)).setv rTP (σ.val rTP + 1) with hσ1
    have h2 := RExec.inc (inp := inp) (cap := cap) rW σ1 (by simp [σ1]; omega)
    set σ2 := σ1.setv rW (σ1.val rW + 1) with hσ2
    have hc2 : CycOk P v σ2 := ⟨by simp [σ2, σ1, hV], by simp [σ2, σ1, hU], hv⟩
    have h3 := cycInc_spec inp cap P v σ2 hc2 hP
    set σ3 := setCyc P ((v + 1) % P) σ2 with hσ3
    have hd' : (inp 1).drop (σ3.sh 1) = List.replicate n true ++ false :: rest := by
      have : σ3.sh 1 = σ.sh 1 + 1 := by simp [σ3, σ2, σ1]
      rw [this]
      exact drop_succ_of_cons (by simpa [List.replicate_succ] using hd)
    have h4 := wLoop_spec P rest hP1 hP n ((v + 1) % P) σ3 hd' (cycOk_set P _ σ2 (Nat.mod_lt _ (by omega)))
      (by simp [σ3, σ2, σ1, setCyc]; omega) (by simp [σ3, σ2, σ1, setCyc]; omega)
    have hread : sbit inp σ 1 = true := by
      unfold sbit; exact read_of_cons (by simpa [List.replicate_succ] using hd)
    refine RExec.cast inp cap (RExec.whsT hread (RExec.seq h1 (RExec.seq h2 h3)) h4) ?_ (by nlinarith)
    unfold wState
    rw [mod_succ_add]
    rs_eq [σ3, σ2, σ1, setCyc]

theorem readWcyc_spec (P n v : ℕ) (rest : List Bool) (σ : LState) (hP1 : 1 ≤ P) (hP : P ≤ cap)
    (hd : (inp 1).drop (σ.sh 1) = List.replicate n true ++ false :: rest) (hc : CycOk P v σ)
    (ht : σ.val rTP + n + 1 ≤ cap) (hw : σ.val rW + n ≤ cap) :
    RExec inp cap readWcyc σ ((wState P v n σ).seth 1 (σ.sh 1 + n + 1) |>.setv rTP (σ.val rTP + n + 1))
      (n * (7 * cap + 20) + 7) := by
  have h1 := wLoop_spec inp cap P rest hP1 hP n v σ hd hc (by omega) hw
  have h2 := fwdC_spec inp cap 1 rTP (wState P v n σ) (by simp [wState, setCyc]; omega)
  refine RExec.cast inp cap (RExec.seq h1 h2) ?_ (by omega)
  unfold wState
  rs_eq [setCyc]

/-! ## Scanning a row against the framed point -/

/-- A hit: one more count in `C`, one more unit of the residue. -/
def hit : LProg := .seq (.inc rC) cycInc

/-- Hit when both the point bit and the row bit are set. -/
def hitOpt : LProg := .ifs 0 (.ifs 1 hit .skip) .skip

/-- One coordinate: to the point bit, test, to the next row bit and the next point marker. -/
def scanStep : LProg := .seq (.fwd 0) (.seq (.inc rR) (.seq hitOpt (.seq fwdT (.seq (.fwd 0) (.inc rR)))))

/-- Scan a row: count the coordinates set in both into `C` and the residue, then rewind the point. -/
def scanRow : LProg := .seq (.whs 0 scanStep) (RM.rewind 0 rR)

/-- The hit indicator of a row bit `b` and a point bit `z`, as in `hits`. -/
def hitN (b z : Bool) : ℕ := if b && z then 1 else 0

theorem hits_cons (b z : Bool) (bs zs : List Bool) : hits (b :: bs) (z :: zs) = hitN b z + hits bs zs := rfl

theorem hitN_le (b z : Bool) : hitN b z ≤ 1 := by unfold hitN; split <;> omega

theorem hits_le : ∀ (bs zs : List Bool), hits bs zs ≤ zs.length
  | [], _ => by simp [hits]
  | _ :: _, [] => by simp [hits]
  | b :: bs, z :: zs => by rw [hits_cons]; have := hitN_le b z; have := hits_le bs zs; simp; omega

/-- The state after `k` hits. -/
def hState (P v k : ℕ) (σ : LState) : LState := setCyc P ((v + k) % P) (σ.setv rC (σ.val rC + k))

theorem hitOpt_spec (P v : ℕ) (σ : LState) (z b : Bool) (hz : sbit inp σ 0 = z) (hb : sbit inp σ 1 = b)
    (hc : CycOk P v σ) (hP : P ≤ cap) (hC : σ.val rC < cap) :
    RExec inp cap hitOpt σ (hState P v (hitN b z) σ) (7 * cap + 15) := by
  obtain ⟨hV, hU, hv⟩ := hc
  have e0 : hState P v 0 σ = σ := by
    unfold hState
    rs_eq [setCyc, Nat.mod_eq_of_lt hv, hV, hU]
  cases z with
  | false =>
    have : hitN b false = 0 := by unfold hitN; simp
    rw [this, e0]
    exact RExec.mono (RExec.ifsF hz (RExec.skip σ)) (by omega)
  | true =>
    cases b with
    | false =>
      have : hitN false true = 0 := rfl
      rw [this, e0]
      exact RExec.mono (RExec.ifsT hz (RExec.ifsF hb (RExec.skip σ))) (by omega)
    | true =>
      have : hitN true true = 1 := rfl
      rw [this]
      have h1 := RExec.inc (inp := inp) (cap := cap) rC σ hC
      have hc1 : CycOk P v (σ.setv rC (σ.val rC + 1)) := ⟨by simp [hV], by simp [hU], hv⟩
      have h2 := cycInc_spec inp cap P v _ hc1 hP
      exact RExec.mono (RExec.ifsT hz (RExec.ifsT hb (RExec.seq h1 h2))) (by omega)

theorem frame_cons (z : Bool) (zs : List Bool) : frame (z :: zs) = true :: z :: frame zs := rfl

/-- The state after scanning `m` coordinates with `k` hits. -/
def sState (P v k m : ℕ) (σ : LState) : LState :=
  ((((hState P v k σ).seth 0 (σ.sh 0 + 2 * m)).setv rR (σ.val rR + 2 * m)).seth 1 (σ.sh 1 + m)).setv rTP
    (σ.val rTP + m)

theorem scanLoop_spec (P : ℕ) (rest : List Bool) (hP1 : 1 ≤ P) (hP : P ≤ cap) :
    ∀ (zs bs : List Bool) (v : ℕ) (σ : LState), bs.length = zs.length →
      (inp 0).drop (σ.sh 0) = frame zs → (inp 1).drop (σ.sh 1) = bs ++ rest → CycOk P v σ →
      σ.val rC + zs.length ≤ cap → σ.val rR + 2 * zs.length ≤ cap → σ.val rTP + zs.length ≤ cap →
      RExec inp cap (.whs 0 scanStep) σ (sState P v (hits bs zs) zs.length σ) (zs.length * (7 * cap + 40) + 1)
  | [], bs, v, σ, hl, h0, _, hc, _, _, _ => by
    obtain ⟨hV, hU, hv⟩ := hc
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hbs
    have e : sState P v (hits [] []) ([] : List Bool).length σ = σ := by
      unfold sState hState
      rs_eq [setCyc, hits, Nat.mod_eq_of_lt hv, hV, hU]
    rw [e]
    exact RExec.mono (RExec.whsF (by unfold sbit; exact read_of_cons (by simpa [frame] using h0))) (by simp)
  | z :: zs, bs, v, σ, hl, h0, h1, hc, hC, hR, hT => by
    obtain ⟨b, bs', rfl⟩ : ∃ b bs', bs = b :: bs' := by
      cases bs with
      | nil => simp at hl
      | cons b bs' => exact ⟨b, bs', rfl⟩
    have hl' : bs'.length = zs.length := by simpa using hl
    simp only [List.length_cons] at hC hR hT ⊢
    have hc0 := hc
    obtain ⟨hV, hU, hv⟩ := hc
    have hread0 : sbit inp σ 0 = true := by unfold sbit; exact read_of_cons (by rw [h0, frame_cons])
    -- fwd 0; inc R
    have s1 := RExec.fwd (inp := inp) (cap := cap) 0 σ
    set σ1 := σ.seth 0 (σ.sh 0 + 1) with hσ1
    have s2 := RExec.inc (inp := inp) (cap := cap) rR σ1 (by simp [σ1]; omega)
    set σ2 := σ1.setv rR (σ1.val rR + 1) with hσ2
    have hz : sbit inp σ2 0 = z := by
      unfold sbit
      have : σ2.sh 0 = σ.sh 0 + 1 := by simp [σ2, σ1]
      rw [this]; exact read_of_cons (drop_succ_of_cons (by rw [h0, frame_cons]))
    have hb : sbit inp σ2 1 = b := by
      unfold sbit
      have : σ2.sh 1 = σ.sh 1 := by simp [σ2, σ1]
      rw [this]; exact read_of_cons (by rw [h1]; rfl)
    have hc2 : CycOk P v σ2 := ⟨by simp [σ2, σ1, hV], by simp [σ2, σ1, hU], hv⟩
    have s3 := hitOpt_spec inp cap P v σ2 z b hz hb hc2 hP (by simp [σ2, σ1]; omega)
    set σ3 := hState P v (hitN b z) σ2 with hσ3
    have s4 := fwdC_spec inp cap 1 rTP σ3 (by simp [σ3, hState, setCyc, σ2, σ1]; omega)
    set σ4 := (σ3.seth 1 (σ3.sh 1 + 1)).setv rTP (σ3.val rTP + 1) with hσ4
    have s5 := RExec.fwd (inp := inp) (cap := cap) 0 σ4
    set σ5 := σ4.seth 0 (σ4.sh 0 + 1) with hσ5
    have s6 := RExec.inc (inp := inp) (cap := cap) rR σ5 (by simp [σ5, σ4, σ3, hState, setCyc, σ2, σ1]; omega)
    set σ6 := σ5.setv rR (σ5.val rR + 1) with hσ6
    have h6s0 : σ6.sh 0 = σ.sh 0 + 2 := by simp [σ6, σ5, σ4, σ3, hState, setCyc, σ2, σ1]
    have h6s1 : σ6.sh 1 = σ.sh 1 + 1 := by simp [σ6, σ5, σ4, σ3, hState, setCyc, σ2, σ1]
    have hc6 : CycOk P ((v + hitN b z) % P) σ6 := by
      refine ⟨?_, ?_, Nat.mod_lt _ (by omega)⟩ <;> simp [σ6, σ5, σ4, σ3, hState, setCyc]
    have h0' : (inp 0).drop (σ6.sh 0) = frame zs := by
      rw [h6s0]
      exact drop_succ_of_cons (drop_succ_of_cons (by rw [h0, frame_cons]))
    have h1' : (inp 1).drop (σ6.sh 1) = bs' ++ rest := by
      rw [h6s1]; exact drop_succ_of_cons (by rw [h1]; rfl)
    have hN := hitN_le b z
    have hH := hits_le bs' zs
    have ih := scanLoop_spec P rest hP1 hP zs bs' ((v + hitN b z) % P) σ6 hl' h0' h1' hc6
      (by simp [σ6, σ5, σ4, σ3, hState, setCyc, σ2, σ1]; omega)
      (by simp [σ6, σ5, σ4, σ3, hState, setCyc, σ2, σ1]; omega)
      (by simp [σ6, σ5, σ4, σ3, hState, setCyc, σ2, σ1]; omega)
    have body := RExec.seq s1 (RExec.seq s2 (RExec.seq s3 (RExec.seq s4 (RExec.seq s5 s6))))
    refine RExec.cast inp cap (RExec.whsT hread0 body ih) ?_ (by simp; nlinarith)
    have hmod : ((v + hitN b z) % P + hits bs' zs) % P = (v + hits (b :: bs') (z :: zs)) % P := by
      rw [hits_cons, Nat.mod_add_mod]; congr 1; omega
    unfold sState hState
    rw [hmod]
    rs_eq [σ6, σ5, σ4, σ3, σ2, σ1, hState, setCyc, hits_cons]

theorem scanRow_spec (P : ℕ) (rest bs Z : List Bool) (v : ℕ) (σ : LState) (hP1 : 1 ≤ P) (hP : P ≤ cap)
    (hl : bs.length = Z.length) (h0 : inp 0 = frame Z) (hs0 : σ.sh 0 = 0) (hR0 : σ.val rR = 0)
    (h1 : (inp 1).drop (σ.sh 1) = bs ++ rest) (hc : CycOk P v σ)
    (hC : σ.val rC + Z.length ≤ cap) (hR : 2 * Z.length ≤ cap) (hT : σ.val rTP + Z.length ≤ cap) :
    RExec inp cap scanRow σ
      (((hState P v (hits bs Z) σ).seth 1 (σ.sh 1 + Z.length)).setv rTP (σ.val rTP + Z.length))
      (Z.length * (7 * cap + 50) + 3) := by
  have h0' : (inp 0).drop (σ.sh 0) = frame Z := by rw [hs0, h0]; rfl
  have hl1 := scanLoop_spec inp cap P rest hP1 hP Z bs v σ hl h0' h1 hc hC (by omega) hT
  have hl2 := rewind_spec inp cap 0 rR (2 * Z.length) (sState P v (hits bs Z) Z.length σ)
    (by simp [sState, hState, setCyc, hR0]) (by simp [sState, hState, setCyc, hR0]; omega)
  refine RExec.cast inp cap (RExec.seq hl1 hl2) ?_ (by nlinarith)
  unfold sState hState
  rs_eq [setCyc, hs0, hR0]

/-! ## Subtracting twice the previous count -/

/-- `P` times: subtract two from the residue. -/
def sub2P : LProg := .whr rP (.seq (.dec rP) (.seq cycDec cycDec))

theorem sub2P_spec (P : ℕ) (hP1 : 1 ≤ P) (hPc : P ≤ cap) :
    ∀ (p v : ℕ) (σ : LState), σ.val rP = p → p ≤ cap → CycOk P v σ →
      RExec inp cap sub2P σ (setCyc P ((v + 2 * p * (P - 1)) % P) (σ.setv rP 0)) (p * (14 * cap + 22) + 1)
  | 0, v, σ, hp, _, hc => by
    obtain ⟨hV, hU, hv⟩ := hc
    have e : setCyc P ((v + 2 * 0 * (P - 1)) % P) (σ.setv rP 0) = σ := by
      rs_eq [setCyc, Nat.mod_eq_of_lt hv, hV, hU, hp]
    rw [e]
    exact RExec.mono (RExec.whrF hp) (by simp)
  | p + 1, v, σ, hp, hpc, hc => by
    have hc0 := hc
    obtain ⟨hV, hU, hv⟩ := hc
    have s1 := RExec.dec (inp := inp) (cap := cap) rP σ (by omega)
    have hc1 : CycOk P v (σ.setv rP (σ.val rP - 1)) := ⟨by simp [hV], by simp [hU], hv⟩
    have s2 := cycDec_spec inp cap P v _ hc1 hPc
    have hc2 := cycOk_set P ((v + P - 1) % P) (σ.setv rP (σ.val rP - 1)) (Nat.mod_lt _ (by omega))
    have s3 := cycDec_spec inp cap P _ _ hc2 hPc
    have hc3 := cycOk_set P (((v + P - 1) % P + P - 1) % P)
      (setCyc P ((v + P - 1) % P) (σ.setv rP (σ.val rP - 1))) (Nat.mod_lt _ (by omega))
    have ih := sub2P_spec P hP1 hPc p _ _ (by simp [setCyc, hp]) (by omega) hc3
    refine RExec.cast inp cap (RExec.whrT (by omega) (RExec.seq s1 (RExec.seq s2 s3)) ih) ?_ (by nlinarith)
    have hmod : ((((v + P - 1) % P + P - 1) % P) + 2 * p * (P - 1)) % P = (v + 2 * (p + 1) * (P - 1)) % P := by
      rw [Nat.mod_add_mod, show (v + P - 1) % P + P - 1 = (v + P - 1) % P + (P - 1) by omega, Nat.add_assoc,
        Nat.add_mod, Nat.mod_mod, ← Nat.add_mod, show v + P - 1 = v + (P - 1) by omega]
      congr 1
      ring
    rw [hmod]
    rs_eq [setCyc]

end NearCubicWires.WireExponent3_5.FinalPass.ListEval
