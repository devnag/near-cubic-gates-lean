import Proof.Gates.CounterMachine.TabCallStageA

/-! # RK, part 9: every stream RK fills from its input is at most `LEN = 2|tabCallInput|` long -/

set_option autoImplicit false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.Counter

variable {B1 B2 cT : ℕ}

theorem encN_len (L : List ℕ) : (encN L).length = 2 * (L.flatMap natWord).length := by
  rw [encN_eq_marks]; simp [marks]; ring

theorem encN_sublist_le {L M : List ℕ} (h : L.Sublist M) : (encN L).length ≤ (encN M).length := by
  rw [encN_len, encN_len]
  have := (h.flatMap natWord).length_le
  omega

theorem encN_perm_len {L M : List ℕ} (h : L.Perm M) : (encN L).length = (encN M).length := by
  rw [encN_len, encN_len, (h.flatMap_right natWord).length_eq]

theorem len_eq (x : TabCallReq B1 B2 cT) :
    2 * (tabCallInput x).length = (encN (descN x.id ++ cellN x.r.c x.r.p x.r.wt)).length := by
  rw [encN_len, tabCallInput, cellInput, List.flatMap_append, cellN_word]

theorem W_le_wit (c : Call) (p : Params) (wt : Wit c.n) :
    (encN (W0 c wt p.J)).length + (encN (W1 c wt p.J)).length ≤ (encN (witN c p wt)).length := by
  have h1 := W_le_Bk c wt p.J
  rw [witN_blocks]
  have h2 := encN_le_mid ([(coordsOf wt.I).length] ++ coordsOf wt.I) ((List.range p.J).flatMap (wBlk c wt)) []
  simp only [List.append_nil] at h2
  omega

theorem L_le_params (p : Params) : (encN (p.factors ++ [p.M1, p.A])).length ≤ (encN (paramsN p)).length := by
  have hp : (p.factors ++ [p.M1, p.A]).Perm (p.M1 :: (p.factors ++ [p.A])) := List.perm_middle
  rw [encN_perm_len hp]
  apply encN_sublist_le
  have h1 : (p.M1 :: (p.factors ++ [p.A])).Sublist (p.M1 :: p.J :: p.factors.length :: (p.factors ++ [p.A, p.Lambda])) :=
    List.Sublist.cons_cons _ (List.Sublist.cons _ (List.Sublist.cons _
      (List.Sublist.append_left (List.sublist_append_left [p.A] [p.Lambda]) p.factors)))
  refine h1.trans ?_
  rw [show paramsN p = ([p.n, bitN p.pair, p.W] ++ ratN p.beta ++ [p.k, p.T, p.m, p.Dmax, p.P, p.e,
      (p.primes.sort (· ≤ ·)).length] ++ p.primes.sort (· ≤ ·) ++ [p.window, p.L2, p.Lw, p.hE, p.h, p.R0] ++
      ratN p.ell0) ++ (p.M1 :: p.J :: p.factors.length :: (p.factors ++ [p.A, p.Lambda])) by
    simp [paramsN, List.append_assoc]]
  exact List.sublist_append_right _ _

theorem dRho_le (id : ReqId) : (encN (dRho id)).length ≤ (encN (descN id)).length := by
  cases id with
  | residue part q κ σ =>
    have := encN_le_mid [0, partCode part, q, (κ ++ σ).length] (κ ++ σ) []
    simpa [dRho, descN, List.append_assoc] using this
  | digitMoment r j => simp [dRho, encN]
  | phiMoment r => simp [dRho, encN]

section
variable (x : TabCallReq B1 B2 cT)

/-- The whole input's encoding. -/
abbrev allN : List ℕ := descN x.id ++ cellN x.r.c x.r.p x.r.wt

theorem allN_split : allN x = descN x.id ++ callN x.r.c ++ paramsN x.r.p ++ witN x.r.c x.r.p x.r.wt := by
  simp [allN, cellN, List.append_assoc]

theorem call_le : (encN (callN x.r.c)).length ≤ (encN (allN x)).length := by
  have := encN_le_mid (descN x.id) (callN x.r.c) (paramsN x.r.p ++ witN x.r.c x.r.p x.r.wt)
  rw [allN_split]; simpa [List.append_assoc] using this

theorem params_le : (encN (paramsN x.r.p)).length ≤ (encN (allN x)).length := by
  have := encN_le_mid (descN x.id ++ callN x.r.c) (paramsN x.r.p) (witN x.r.c x.r.p x.r.wt)
  rw [allN_split]; simpa [List.append_assoc] using this

theorem wit_le : (encN (witN x.r.c x.r.p x.r.wt)).length ≤ (encN (allN x)).length := by
  have := encN_le_mid (descN x.id ++ callN x.r.c ++ paramsN x.r.p) (witN x.r.c x.r.p x.r.wt) []
  rw [allN_split]; simpa [List.append_assoc] using this

theorem desc_le : (encN (descN x.id)).length ≤ (encN (allN x)).length := by
  have := encN_le_mid [] (descN x.id) (cellN x.r.c x.r.p x.r.wt)
  simpa [allN] using this

theorem primes_le_all : (encN (x.r.p.primes.sort (· ≤ ·))).length ≤ (encN (allN x)).length := by
  refine le_trans ?_ (params_le x)
  have := encN_le_mid ([x.r.p.n, bitN x.r.p.pair, x.r.p.W] ++ ratN x.r.p.beta ++ [x.r.p.k, x.r.p.T, x.r.p.m,
    x.r.p.Dmax, x.r.p.P, x.r.p.e, (x.r.p.primes.sort (· ≤ ·)).length]) (x.r.p.primes.sort (· ≤ ·))
    ([x.r.p.window, x.r.p.L2, x.r.p.Lw, x.r.p.hE, x.r.p.h, x.r.p.R0] ++ ratN x.r.p.ell0 ++
      [x.r.p.M1, x.r.p.J, x.r.p.factors.length] ++ x.r.p.factors ++ [x.r.p.A, x.r.p.Lambda])
  simpa [paramsN, List.append_assoc] using this

theorem M1_le_all : (encN [x.r.p.M1]).length ≤ (encN (allN x)).length :=
  le_trans (TabCallProg.encN_single_le (by simp [paramsN])) (params_le x)

/-- **Every stream RK fills from its input is within `LEN`.** -/
theorem streams_le : (encN (W0 x.r.c x.r.wt x.r.p.J)).length ≤ (encN (allN x)).length ∧
    (encN (W1 x.r.c x.r.wt x.r.p.J)).length ≤ (encN (allN x)).length ∧
    (encN (x.r.c.first.coeffs.flatMap intN)).length ≤ (encN (allN x)).length ∧
    (encN (x.r.c.second.coeffs.flatMap intN)).length ≤ (encN (allN x)).length ∧
    (encN (x.r.p.factors ++ [x.r.p.M1, x.r.p.A])).length ≤ (encN (allN x)).length ∧
    (encN (dRho x.id)).length ≤ (encN (allN x)).length ∧
    (encN (x.r.c.first.gates.flatMap gateN)).length + (encN (x.r.c.second.gates.flatMap gateN)).length ≤
      (encN (allN x)).length := by
  have hw := W_le_wit x.r.c x.r.p x.r.wt
  have hwa := wit_le x
  have hc := callN_parts x.r.c
  have hca := call_le x
  have hl := L_le_params x.r.p
  have hpa := params_le x
  have hd := dRho_le x.id
  have hda := desc_le x
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

end

end NearCubicGates.Close.CounterMachine
