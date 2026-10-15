import Proof.Gates.Expand.Stack

set_option autoImplicit false

namespace NearCubicGates.Close.Expand

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.SignedSortKey (binary binary_length binary_value)
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close.WordPrograms
open NearCubicWires.WireExponent3_5.SelectionMachine.Sort (NumOn)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp readNatM readNatM_spec)
open NearCubicWires.WireExponent3_5.PrimAsm.CopyNat (enc_append)
open NearCubicGates.Close.Interfaces.Formats
open NearCubicGates.Close.WordPrograms.BinW (numOn_sets_ne numOn_sets_self numOn_setv)

/-! ## Tokens: tag and payload -/

def tagOf : Tok → ℕ
  | .const _ => 0
  | .var _ => 1
  | .add => 2
  | .neg => 3
  | .sub => 4
  | .mul => 5
  | .pow _ => 6

def payload : Tok → List Bool
  | .const a => Interfaces.intWord a
  | .var v => natWord v
  | .pow e => natWord e
  | _ => []

theorem tokWord_eq (tok : Tok) : tokWord tok = natWord (tagOf tok) ++ payload tok := by
  cases tok <;> simp [tokWord, tagOf, payload]

theorem tagOf_lt (tok : Tok) : tagOf tok < 7 := by cases tok <;> simp [tagOf]

variable {ns nr : ℕ}

/-! ## The evaluator at a position -/

section At
variable (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr)

/-- The evaluator at rest: input `inp` with head `hd`, stack `xs`. -/
structure EvAt (Wb m k t : ℕ) (inp : List Bool) (hd : ℕ) (xs : List ℕ) (σ : WState ns nr) : Prop where
  ev : Ev U R Wb m k t σ
  inp : σ.st (U 0) = inp
  hd : σ.sh (U 0) = hd
  stk : NumOn σ (U 1) Wb (senc m xs)

/-- The streams an evaluator program may change (the input only by its head). -/
def evS : List (Fin (ns + 1)) := [U 0, U 1, U 2, U 3, U 4, U 5]

/-- The registers an evaluator program may use (all back at `0`). -/
def evR : List (Fin nr) := [R 0, R 1, R 2, R 3, R 4, R 5, R 6, R 7, R 8, R 9, R 10]

/-- **A token program's specification** (one pass `A`, cost `c`). -/
def HSpec (cap Wb m k t : ℕ) (A : Alg) (P : WMX ns nr) (tok : Tok) (c : ℕ) : Prop :=
  ∀ (σ : WState ns nr) (pre rest : List Bool) (xs : List ℕ), (∀ x ∈ xs, x < m) → m ^ (xs.length + 2) ≤ 2 ^ Wb →
    EvAt U R Wb m k t (pre ++ enc true (payload tok) ++ rest) pre.length xs σ →
    Runs cap P σ c (fun τ => EvAt U R Wb m k t (pre ++ enc true (payload tok) ++ rest)
      (pre.length + 2 * (payload tok).length) (A.step xs tok) τ ∧ SameExcept σ τ (evS U) (evR R))

end At

/-! ## Dispatch on the tag -/

/-- Run program `j` of the list when register `T` holds `j` (`T` counted down to `0`). -/
def chain (T : Fin nr) : List (WMX ns nr) → WMX ns nr
  | [] => WMX.skip
  | h :: hs => .ifr T (.seq (WMX.dec T) (chain T hs)) h

theorem chain_spec (cap : ℕ) (T : Fin nr) (hcap : 7 ≤ cap) :
    ∀ (l : List (WMX ns nr)) (j : ℕ) (hj : j < l.length) (σ : WState ns nr) (c : ℕ) (Q : WState ns nr → Prop),
      σ.val T = j → j ≤ 7 → Runs cap l[j] (σ.setv T 0) c Q → Runs cap (chain T l) σ (c + 3 * j + 1) Q
  | [], j, hj, _, _, _, _, _, _ => absurd hj (by simp)
  | h :: hs, 0, _, σ, c, Q, hT, _, hr => by
    rw [wsetv_same' σ T hT] at hr
    exact Runs.ifrF hT hr
  | h :: hs, j + 1, hj, σ, c, Q, hT, hj7, hr => by
    have hd := WXExec.dec cap T σ (by omega)
    have e : (σ.setv T (σ.val T - 1)).setv T 0 = σ.setv T 0 := wsetv_setv σ T _ 0
    have ih := chain_spec cap T hcap hs j (by simpa using hj) (σ.setv T (σ.val T - 1)) c Q
      (by simp; omega) (by omega) (by rw [e]; simpa using hr)
    have := Runs.ifrT (r := T) (P' := h) (by omega : σ.val T ≠ 0) (Runs.seqE hd ih)
    exact this.cost (by omega)
where
  wsetv_same' (σ : WState ns nr) (T : Fin nr) (hT : σ.val T = 0) : σ.setv T 0 = σ := by
    rw [← hT]; exact wsetv_same σ T

/-! ## The token loop -/

section Loop
variable (U : Fin 10 ↪ Fin (ns + 1)) (R : Fin 12 ↪ Fin nr)

/-- Read one tag into `R 0`. -/
def readTag : WMX ns nr := .wm (readNatM true (U 0) (R 7) (R 8) (R 0) (R 9) (R 10))

/-- One token: read the tag, run its program. -/
def tokBody (hs : List (WMX ns nr)) : WMX ns nr := .seq (readTag U R) (chain (R 0) hs)

/-- All tokens (`R 11` counts them down). -/
def tokLoop (hs : List (WMX ns nr)) : WMX ns nr := .whr (R 11) (.seq (WMX.dec (R 11)) (tokBody U R hs))

def tagCost : ℕ := 5 * (40 * 2 ^ 3 + 40)

theorem readNat_tag_cost (x : ℕ) (hx : x < 7) :
    (natBitLength x + 2) * (40 * 2 ^ natBitLength x + 40) ≤ tagCost := by
  have : natBitLength x ≤ 3 := by
    unfold natBitLength
    have : Nat.log 2 x ≤ Nat.log 2 6 := Nat.log_mono_right (by omega)
    have h6 : Nat.log 2 6 = 2 := by decide
    omega
  have h2 : 2 ^ natBitLength x ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) this
  unfold tagCost
  nlinarith

variable {U R}

/-- **The token loop**: from the evaluator at the start of the token word with an empty stack and the counter at
the token count, every token is run; the stack ends as `toks.foldl A.step []`. -/
theorem tokLoop_spec (cap Wb m k t c : ℕ) (A : Alg) (hA : A.Closed m) (hs : List (WMX ns nr)) (hlen : hs.length = 7)
    (ts : List Tok) (hh : ∀ tok ∈ ts, HSpec U R cap Wb m k t A (hs.getD (tagOf tok) WMX.skip) tok c) (P0 rest : List Bool) (σ : WState ns nr)
    (h0 : EvAt U R Wb m k t (P0 ++ enc true (ts.flatMap tokWord) ++ rest) P0.length [] σ)
    (hN : σ.val (R 11) = ts.length) (hdepth : m ^ (ts.length + 2) ≤ 2 ^ Wb) (hcap : 2 ^ 4 + ts.length ≤ cap) :
    Runs cap (tokLoop U R hs) σ (ts.length * ((tagCost + 1 + (c + 3 * 7 + 1)) + 4) + 1)
      (fun τ => (EvAt U R Wb m k t (P0 ++ enc true (ts.flatMap tokWord) ++ rest)
        (P0.length + 2 * (ts.flatMap tokWord).length) (ts.foldl A.step []) τ ∧
        SameExcept σ τ (evS U) (evR R ++ [R 11])) ∧ τ.val (R 11) = 0) := by
  set inp := P0 ++ enc true (ts.flatMap tokWord) ++ rest with hinp
  let Inv : ℕ → WState ns nr → Prop := fun j τ =>
    EvAt U R Wb m k t inp (P0.length + 2 * ((ts.take j).flatMap tokWord).length) ((ts.take j).foldl A.step []) τ ∧
      SameExcept σ τ (evS U) (evR R ++ [R 11])
  have hI0 : Inv 0 σ := ⟨by simpa using h0, SameExcept.refl σ _ _⟩
  have key := Runs.count (cap := cap) (K := R 11) (body := tokBody U R hs) (tagCost + 1 + (c + 3 * 7 + 1))
    ts.length Inv (by omega) ?_ σ hI0 hN
  · refine key.post ?_
    rintro τ ⟨⟨hE, hF⟩, hK⟩
    rw [List.take_length] at hE
    exact ⟨⟨hE, hF⟩, hK⟩
  intro j hj τ ⟨hE, hF⟩ hK
  -- the input around token `j`
  set tok := ts[j] with htok
  have hsplit : ts.flatMap tokWord = (ts.take j).flatMap tokWord ++ (natWord (tagOf tok) ++ payload tok) ++
      (ts.drop (j + 1)).flatMap tokWord := by
    rw [← tokWord_eq]
    conv_lhs => rw [← List.take_append_drop j ts]
    rw [List.drop_eq_getElem_cons hj, List.flatMap_append, List.flatMap_cons, List.append_assoc]
  set pre1 := P0 ++ enc true ((ts.take j).flatMap tokWord) with hpre1
  have hinp1 : inp = pre1 ++ enc true (natWord (tagOf tok)) ++
      (enc true (payload tok) ++ enc true ((ts.drop (j + 1)).flatMap tokWord) ++ rest) := by
    rw [hinp, hsplit, hpre1]
    simp only [enc_append, List.append_assoc]
  have hlen1 : pre1.length = P0.length + 2 * ((ts.take j).flatMap tokWord).length := by
    rw [hpre1, List.length_append, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc_length]; rfl
  -- read the tag
  set τ0 := τ.setv (R 11) (ts.length - j - 1) with hτ0
  have hE0 : Ev U R Wb m k t τ0 := hE.ev.setv 11 rfl _
  have hrd := readNatM_spec (cap := cap) true (U 0) (R 7) (R 8) (R 0) (R 9) (R 10) (rN R (by decide))
    (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) (rN R (by decide))
    (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) (rN R (by decide)) (tagOf tok) pre1
    (enc true (payload tok) ++ enc true ((ts.drop (j + 1)).flatMap tokWord) ++ rest) τ0
    (by rw [hτ0]; simp only [WState.setv_st]; rw [hE.inp, hinp1])
    (by rw [hτ0]; simp only [WState.setv_sh]; rw [hE.hd, hlen1])
    (hE0.reg 7) (hE0.reg 8) (hE0.reg 9) (hE0.reg 10)
    (by
      rw [hE0.reg 0]
      have : natBitLength (tagOf tok) + 1 ≤ 4 := by
        have h7 := tagOf_lt tok
        unfold natBitLength
        have : Nat.log 2 (tagOf tok) ≤ Nat.log 2 6 := Nat.log_mono_right (by omega)
        have h6 : Nat.log 2 6 = 2 := by decide
        omega
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) this
      omega)
  set τ1 := (τ0.seth (U 0) (pre1.length + stp true * (natWord (tagOf tok)).length)).setv (R 0)
    (τ0.val (R 0) + tagOf tok) with hτ1
  have hT1 : τ1.val (R 0) = tagOf tok := by rw [hτ1]; simp [hE0.reg 0]
  -- the token program, after the dispatch
  set pre2 := pre1 ++ enc true (natWord (tagOf tok)) with hpre2
  have hlen2 : pre2.length = pre1.length + stp true * (natWord (tagOf tok)).length := by
    rw [hpre2, List.length_append, NearCubicWires.WireExponent3_5.PrimAsm.ParseNat.enc_length]
  have hσ2 : EvAt U R Wb m k t (pre2 ++ enc true (payload tok) ++
      (enc true ((ts.drop (j + 1)).flatMap tokWord) ++ rest)) pre2.length ((ts.take j).foldl A.step [])
      (τ1.setv (R 0) 0) := by
    have e1 : τ1.setv (R 0) 0 = τ0.seth (U 0) (pre1.length + stp true * (natWord (tagOf tok)).length) := by
      rw [hτ1, wsetv_setv]
      have : (τ0.seth (U 0) (pre1.length + stp true * (natWord (tagOf tok)).length)).val (R 0) = 0 := by
        simp [hE0.reg 0]
      rw [← this, wsetv_same]
    rw [e1]
    refine ⟨hE0.seth _, ?_, ?_, ?_⟩
    · simp only [WState.seth_st]
      rw [hτ0]; simp only [WState.setv_st]; rw [hE.inp, hinp1, hpre2]; simp only [List.append_assoc]
    · simp [hlen2]
    · have := hE.stk
      exact ⟨by simpa [hτ0] using this.1, by
        simp only [WState.seth_sh]
        rw [Function.update_of_ne (uN U (by decide))]
        simpa [hτ0] using this.2⟩
  have hbound : ∀ x ∈ (ts.take j).foldl A.step [], x < m := (A.foldl_lt hA (ts.take j)).1
  have hdep : m ^ (((ts.take j).foldl A.step []).length + 2) ≤ 2 ^ Wb := by
    have hl := (A.foldl_lt hA (ts.take j)).2
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · exfalso; subst h; exact absurd (hA.c 0) (by omega)
      · exact h
    refine le_trans (Nat.pow_le_pow_right hm ?_) hdepth
    have : (ts.take j).length ≤ ts.length := by rw [List.length_take]; omega
    omega
  have hprog := hh tok (List.getElem_mem hj) (τ1.setv (R 0) 0) pre2 (enc true ((ts.drop (j + 1)).flatMap tokWord) ++ rest) _
    hbound hdep hσ2
  have hdisp := chain_spec cap (R 0) (by omega) hs (tagOf tok) (by rw [hlen]; exact tagOf_lt tok) τ1 c _ hT1
    (by have := tagOf_lt tok; omega) (by rw [← List.getD_eq_getElem hs WMX.skip]; exact hprog)
  have hrun := Runs.seqE (WXExec.wm hrd) (hdisp.cost (show c + 3 * tagOf tok + 1 ≤ c + 3 * 7 + 1 by
    have := tagOf_lt tok; omega))
  refine (hrun.cost ?_).post ?_
  · have := readNat_tag_cost (tagOf tok) (tagOf_lt tok)
    omega
  rintro ρ ⟨hρ, hfr⟩
  have hfold : (ts.take (j + 1)).foldl A.step [] = A.step ((ts.take j).foldl A.step []) tok := by
    rw [List.take_succ_eq_append_getElem hj, List.foldl_append]; rfl
  have hpos : P0.length + 2 * ((ts.take (j + 1)).flatMap tokWord).length =
      pre2.length + 2 * (payload tok).length := by
    rw [hlen2, hlen1, List.take_succ_eq_append_getElem hj, List.flatMap_append, List.length_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, ← htok, tokWord_eq, List.length_append]
    simp [stp]
    ring
  have hfrK : SameExcept τ1 ρ (evS U) (evR R ++ [R 11]) := by
    have e1 : SameExcept τ1 (τ1.setv (R 0) 0) (evS U) (evR R ++ [R 11]) := sameExcept_setv τ1 (by simp [evR]) 0
    exact SameExcept.trans e1 (hfr.weaken (fun _ hx => hx) (fun _ hr => List.mem_append_left _ hr))
  have hK1 : ρ.val (R 11) = ts.length - j - 1 := by
    have : (R 11) ∉ evR R ++ [R 11] → False := fun hn => hn (by simp)
    have h1 : τ1.val (R 11) = ts.length - j - 1 := by
      rw [hτ1]
      simp only [WState.setv_val, WState.seth_val]
      rw [Function.update_of_ne (rN R (by decide)), hτ0]
      simp
    have h2 : ρ.val (R 11) = τ1.val (R 11) := by
      have := hfr.val (r := R 11) (by simp [evR, rN R])
      rw [this]
      simp
    rw [h2, h1]
  refine ⟨⟨⟨hρ.ev, ?_, ?_, ?_⟩, ?_⟩, hK1⟩
  · rw [hρ.inp, hinp, hsplit]
    rw [hpre2, hpre1]
    simp only [enc_append, List.append_assoc]
  · rw [hρ.hd, hpos]
  · rw [hfold]; exact hρ.stk
  · -- σ → τ → τ1 → ρ
    have hτ01 : SameExcept τ τ1 (evS U) (evR R ++ [R 11]) := by
      rw [hτ1, hτ0]
      refine SameExcept.trans (SameExcept.trans (sameExcept_setv τ (by simp) _) (sameExcept_seth _ (by simp [evS]) _))
        (sameExcept_setv _ (by simp [evR]) _)
    exact SameExcept.trans (SameExcept.trans hF hτ01) hfrK

end Loop

end NearCubicGates.Close.Expand
