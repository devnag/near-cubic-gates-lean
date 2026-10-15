import Proof.Gates.CounterMachine.UnpackNats
import Proof.Gates.CounterMachine.FormulaBinom
import Proof.Gates.CounterMachine.CellIdx

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_append)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (enc stp enc_length readNatM readNatM_spec)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec
open NearCubicGates.Close.Interfaces
open NearCubicGates.Close.WordPrograms (SameExcept)

variable {ns nr : ℕ} (cap : ℕ)

theorem encI_eq_encN (zs : List ℤ) : encI zs = encN (zs.flatMap intN) := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    rw [show z :: zs = [z] ++ zs from rfl, encI_append, List.flatMap_append, encN_append, ih]
    congr 1
    simp [encI, encN, intN, Interfaces.intWord, WireExponent3_5.PrimAsm.ParseNat.enc, marksApp]

section Unpack
variable (IN GT SC : Fin (ns + 1)) (Q : Fin 16 ↪ Fin nr)

/-- `copyNat`'s register file inside `Q`: `Q 8 … Q 15` (`Q 15` the output position). -/
def Rq : Fin 8 ↪ Fin nr := ⟨fun i => Q ⟨8 + i.val, by omega⟩, fun a b h => by
  have := Q.injective h; simp [Fin.ext_iff] at this; exact Fin.ext this⟩

theorem Rq_apply (i : Fin 8) : Rq Q i = Q ⟨8 + i.val, by omega⟩ := rfl

/-- Unpack one circuit, part A: the gate count and the gate fields. -/
def unCircA (G N3 : Fin nr) : WM ns nr :=
  .seq (readNatM true IN (Q 0) (Q 1) G (Q 2) (Q 3))
  (.seq (copyR G (Q 4) (Q 3))
  (.seq (mulR N3 (Q 4) (Q 5) (Q 3))
  (listLoop (Q 5) (copyNat true IN GT (Rq Q)))))

/-- Part B: the top coefficients, then step over the table. -/
def unCircB : WM ns nr :=
  .seq (readNatM true IN (Q 0) (Q 1) (Q 6) (Q 2) (Q 3))
  (.seq (copyR (Q 6) (Q 4) (Q 3)) (.seq (copyR (Q 6) (Q 4) (Q 3)) (.seq (WM.clear (Q 6))
  (.seq (listLoop (Q 4) (copyNat true IN SC (Rq Q)))
  (.seq (readNatM true IN (Q 0) (Q 1) (Q 6) (Q 2) (Q 3))
  (listLoop (Q 6) (skipNat true IN (Q 0) (Q 1))))))))

/-- Unpack one circuit. -/
def unCirc (G N3 : Fin nr) : WM ns nr := .seq (unCircA IN GT Q G N3) (unCircB IN SC Q)

/-- The scratch registers of the unpacker at rest. -/
def QZero (σ : WState ns nr) : Prop := ∀ i : Fin 16, i ≠ 15 → σ.val (Q i) = 0

theorem circN_split {n : ℕ} (C : NCircuit n) :
    circN C = [C.gates.length] ++ C.gates.flatMap gateN ++ [C.coeffs.length] ++ C.coeffs.flatMap intN ++
      [C.table.length] ++ C.table.map bitN := rfl

theorem hRq_ne (j : Fin 8) (i : Fin 16) (hi : i.val < 8) : Rq Q j ≠ Q i := fun e => by
  rw [Rq_apply] at e; have := Q.injective e; simp [Fin.ext_iff] at this; omega

theorem fit_cap {L : List ℕ} {Λ : ℕ} (hfit : ∀ x ∈ L, natBitLength x + 2 ≤ Λ)
    (hΛ : Λ ≤ cap) : ∀ x ∈ L, natBitLength x + 1 ≤ cap := fun x hx => by have := hfit x hx; omega

theorem val_le_of_fit {x Λ : ℕ} (h : 2 ^ (natBitLength x + 1) ≤ Λ) : x ≤ Λ := by
  have := lt_two_pow_nbl x
  have : 2 ^ natBitLength x ≤ 2 ^ (natBitLength x + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- **Part A**: `G := g` (the gate count), the `g·(2n+3)` gate fields appended to `GT`. -/
theorem unCircA_spec (hIG : IN ≠ GT) (G N3 : Fin nr) (hQG : ∀ i, Q i ≠ G) (hQN : ∀ i, Q i ≠ N3) (hGN : G ≠ N3)
    (n g : ℕ) (A GW S : List ℕ) (hGWl : GW.length = g * (2 * n + 3)) (rest : List Bool) (σ : WState ns nr)
    (hσ : NatAt IN (A ++ [g] ++ GW ++ S) rest σ A.length) (hz : QZero Q σ) (hG0 : σ.val G = 0)
    (hN3 : σ.val N3 = 2 * n + 3) (hGT : σ.sh GT = (σ.st GT).length)
    (Λ : ℕ) (hfit : ∀ x ∈ A ++ [g] ++ GW ++ S, natBitLength x + 2 ≤ Λ) (hg : 2 ^ (natBitLength g + 1) ≤ Λ)
    (hlen : (A ++ [g] ++ GW ++ S).length ≤ Λ) (hn : 2 * n + 3 ≤ Λ)
    (hcapΛ : 20 * (Λ + 1) ^ 2 + σ.val (Q 15) ≤ cap) :
    WExec cap (unCircA IN GT Q G N3) σ
      (((appendO σ GT (Q 15) (encN GW)).seth IN (encN (A ++ [g] ++ GW)).length).setv G g) (500 * (Λ + 1) ^ 2) := by
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  have hz' : ∀ i : Fin 16, i ≠ 15 → σ.val (Q i) = 0 := hz
  have hΛcap : Λ + 1 ≤ cap := by nlinarith
  have hlen' := hlen
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen'
  have hgΛ : g ≤ Λ := val_le_of_fit hg
  have R7 : Rq Q 7 = Q 15 := rfl
  have nd : [Q 0, Q 1, G, Q 2, Q 3].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true]
    exact ⟨⟨hQ (by decide), (hQG 0), hQ (by decide), hQ (by decide)⟩, ⟨hQG 1, hQ (by decide), hQ (by decide)⟩,
      ⟨(hQG 2).symm, (hQG 3).symm⟩, hQ (by decide)⟩
  have D1 : A ++ [g] ++ GW ++ S = A ++ [g] ++ (GW ++ S) := by simp [List.append_assoc]
  -- 1. G := g
  have e1 := readN_spec cap IN (A ++ [g] ++ (GW ++ S)) rest (Q 0) (Q 1) G (Q 2) (Q 3) nd σ
    A.length (by rw [← D1]; exact hσ) (by simp) (hz' 0 (by decide)) (hz' 1 (by decide)) (hz' 2 (by decide))
    (hz' 3 (by decide)) (by rw [hG0, getElem_mid]; have := hg; omega)
  rw [getElem_mid, show A.length + 1 = A.length + [g].length by simp, take_mid A [g], hG0, Nat.zero_add] at e1
  set σ1 := (σ.seth IN (encN (A ++ [g])).length).setv G g with hσ1
  have v1 : ∀ i : Fin 16, σ1.val (Q i) = σ.val (Q i) := fun i => by simp [hσ1, Function.update_of_ne (hQG i)]
  -- 2. Q 4 := g
  have e2 := copyR_spec cap (v := G) (d := Q 4) (t := Q 3) (hQG 4).symm (hQG 3).symm (hQ (by decide)) σ1
    (by rw [v1]; exact hz' 3 (by decide)) (by rw [v1, hz' 4 (by decide)]; simp [hσ1]; omega)
  rw [v1, hz' 4 (by decide), Nat.zero_add, show σ1.val G = g by simp [hσ1]] at e2
  -- 3. Q 5 := g·(2n+3)
  have e3 := mulR_spec cap N3 (Q 4) (Q 5) (Q 3) (hQN 4).symm (hQN 5).symm (hQN 3).symm (hQ (by decide)) (hQ (by decide))
    (hQ (by decide)) (σ1.setv (Q 4) g) (2 * n + 3) g
    (by simp [Function.update_of_ne (hQN 4).symm, hσ1, Function.update_of_ne hGN.symm, hN3]) (by simp)
    (by simp [Function.update_of_ne (hQ (show (3 : Fin 16) ≠ 4 by decide)), v1, hz' 3 (by decide)])
    (by simp [Function.update_of_ne (hQ (show (5 : Fin 16) ≠ 4 by decide)), v1, hz' 5 (by decide)]
        rw [show g * (2 * n + 3) = GW.length by rw [hGWl]]; omega)
    (by omega)
  have hσ3 : ((σ1.setv (Q 4) g).setv (Q 5) ((σ1.setv (Q 4) g).val (Q 5) + g * (2 * n + 3))).setv (Q 4) 0 =
      σ1.setv (Q 5) GW.length := by
    apply WState.eq <;> try rfl
    funext r; by_cases r4 : r = Q 4
    · subst r4; simp [Function.update_of_ne (hQ (show (4 : Fin 16) ≠ 5 by decide)), v1, hz' 4 (by decide)]
    · by_cases r5 : r = Q 5
      · subst r5; simp [Function.update_of_ne (hQ (show (5 : Fin 16) ≠ 4 by decide)), v1, hz' 5 (by decide), hGWl]
      · simp [Function.update_of_ne r4, Function.update_of_ne r5]
  rw [hσ3] at e3
  set σ3 := σ1.setv (Q 5) GW.length with hσ3'
  have v3 : ∀ i : Fin 16, i ≠ 5 → σ3.val (Q i) = σ.val (Q i) := fun i hi => by
    simp [hσ3', Function.update_of_ne (hQ hi), v1]
  -- 4. the gate fields → GT
  have hLsum : ((A ++ [g] ++ GW ++ S).map fun x => (natWord x).length).sum ≤ Λ * (2 * Λ + 1) := by
    have := natWords_sum_le (A ++ [g] ++ GW ++ S) Λ (fun x hx => by have := hfit x hx; omega)
    nlinarith
  have hfull : (encN (A ++ [g] ++ GW ++ S)).length ≤ 2 * (Λ * (2 * Λ + 1)) := by rw [encN_length]; omega
  have e4 := copyNs_spec cap IN ((A ++ [g]) ++ GW ++ S) rest GT hIG (Rq Q) (Q 5) (fun j => hRq_ne Q j 5 (by decide)) σ3
    (A ++ [g]).length GW.length
    ⟨by simp only [hσ3', hσ1, WState.setv_st, WState.seth_st]; exact hσ.1,
     by simp only [hσ3', hσ1, WState.setv_sh, WState.seth_sh, Function.update_self]; rw [take_prefix]⟩
    (by simp [hσ3']) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [show Rq Q 1 = Q 9 from rfl, v3 9 (by decide)]; exact hz' 9 (by decide))
    (by rw [show Rq Q 2 = Q 10 from rfl, v3 10 (by decide)]; exact hz' 10 (by decide))
    (by simp only [hσ3', hσ1, WState.setv_sh, WState.seth_sh, WState.setv_st, WState.seth_st,
          Function.update_of_ne hIG.symm]; exact hGT) (σ.val (Q 15) + (encN GW).length)
    (by rw [R7, v3 15 (by decide), drop_take_mid])
    (by have := encN_le_mid (A ++ [g]) GW S
        rw [← encN_length]; nlinarith)
    (by omega)
  rw [drop_take_mid, take_mid] at e4
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 e4))) ?_ ?_
  · apply WState.eq
    · funext j; by_cases jI : j = IN
      · subst jI; simp
      · simp [hσ3', hσ1, appendO, Function.update_apply, jI, hIG, Ne.symm hIG]
    · simp [hσ3', hσ1, appendO]
    · funext r
      by_cases r5 : r = Q 5
      · subst r5; simp [Function.update_of_ne (hQG 5), R7, Function.update_of_ne (hQ (show (5 : Fin 16) ≠ 15 by decide))]
        exact (hz' 5 (by decide)).symm
      · by_cases r15 : r = Q 15
        · subst r15; simp [hσ3', hσ1, R7, Function.update_of_ne (hQG 15), Function.update_of_ne r5]
        · by_cases rG : r = G
          · subst rG; simp [hσ3', hσ1, R7, Function.update_of_ne (hQG 15).symm, Function.update_of_ne (hQG 5).symm]
          · simp [hσ3', hσ1, R7, Function.update_of_ne r5, Function.update_of_ne r15, Function.update_of_ne rG]
    · simp [hσ3', hσ1, appendO]
  · have r1 := readCost_le g Λ (hfit g (by simp)) hg
    have c1 := copySum_le GW Λ (fun x hx => by have := hfit x (by simp [hx]); omega)
    have m1' : g * (18 * (2 * n + 3) + 3 + 4) ≤ 18 * (Λ * Λ) + 7 * Λ := by nlinarith
    have l1' : GW.length * (120 * Λ + 124) ≤ 120 * (Λ * Λ) + 124 * Λ := by nlinarith
    have r1' : (natBitLength g + 2) * (40 * 2 ^ natBitLength g + 40) ≤ 40 * (Λ * Λ) + 40 * Λ := by nlinarith
    have hL2 : Λ * Λ + 2 * Λ + 1 = (Λ + 1) ^ 2 := by ring
    clear r1 hLsum hfull
    generalize Λ * Λ = P at *
    omega

/-- **Part B**: the `2 nc` coefficient fields appended to `SC`, then step over the `nt` table fields. -/
theorem unCircB_spec (hIS : IN ≠ SC) (P CW TB S : List ℕ) (nc nt : ℕ) (hCWl : CW.length = 2 * nc)
    (hTBl : TB.length = nt) (rest : List Bool) (σ : WState ns nr)
    (hσ : NatAt IN (P ++ [nc] ++ CW ++ [nt] ++ TB ++ S) rest σ P.length) (hz : QZero Q σ)
    (hSC : σ.sh SC = (σ.st SC).length)
    (Λ : ℕ) (hfit : ∀ x ∈ P ++ [nc] ++ CW ++ [nt] ++ TB ++ S, natBitLength x + 2 ≤ Λ)
    (hnc : 2 ^ (natBitLength nc + 1) ≤ Λ) (hnt : 2 ^ (natBitLength nt + 1) ≤ Λ)
    (hlen : (P ++ [nc] ++ CW ++ [nt] ++ TB ++ S).length ≤ Λ) (hcapΛ : 20 * (Λ + 1) ^ 2 + σ.val (Q 15) ≤ cap) :
    WExec cap (unCircB IN SC Q) σ
      ((appendO σ SC (Q 15) (encN CW)).seth IN (encN (P ++ [nc] ++ CW ++ [nt] ++ TB)).length) (1000 * (Λ + 1) ^ 2) := by
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  have hz' : ∀ i : Fin 16, i ≠ 15 → σ.val (Q i) = 0 := hz
  have hΛcap : Λ + 1 ≤ cap := by nlinarith
  have hlen' := hlen
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen'
  have hncΛ : nc ≤ Λ := val_le_of_fit hnc
  have R7 : Rq Q 7 = Q 15 := rfl
  have nd6 : [Q 0, Q 1, Q 6, Q 2, Q 3].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true]
    exact ⟨⟨hQ (by decide), hQ (by decide), hQ (by decide), hQ (by decide)⟩, ⟨hQ (by decide), hQ (by decide),
      hQ (by decide)⟩, ⟨hQ (by decide), hQ (by decide)⟩, hQ (by decide)⟩
  have D3 : P ++ [nc] ++ CW ++ [nt] ++ TB ++ S = P ++ [nc] ++ (CW ++ [nt] ++ TB ++ S) := by simp [List.append_assoc]
  have D4 : P ++ [nc] ++ CW ++ [nt] ++ TB ++ S = (P ++ [nc]) ++ CW ++ ([nt] ++ TB ++ S) := by simp [List.append_assoc]
  have D5 : P ++ [nc] ++ CW ++ [nt] ++ TB ++ S = (P ++ [nc] ++ CW) ++ [nt] ++ (TB ++ S) := by simp [List.append_assoc]
  have D6 : P ++ [nc] ++ CW ++ [nt] ++ TB ++ S = (P ++ [nc] ++ CW ++ [nt]) ++ TB ++ S := by simp [List.append_assoc]
  have hfit' := fit_cap cap hfit (by omega)
  have hLsum : ((P ++ [nc] ++ CW ++ [nt] ++ TB ++ S).map fun x => (natWord x).length).sum ≤ Λ * (2 * Λ + 1) := by
    have := natWords_sum_le (P ++ [nc] ++ CW ++ [nt] ++ TB ++ S) Λ (fun x hx => by have := hfit x hx; omega)
    nlinarith
  -- 5. Q 6 := nc
  have e5 := readN_spec cap IN (P ++ [nc] ++ (CW ++ [nt] ++ TB ++ S)) rest (Q 0) (Q 1) (Q 6) (Q 2) (Q 3)
    nd6 σ P.length (by rw [← D3]; exact hσ) (by simp)
    (hz' 0 (by decide)) (hz' 1 (by decide)) (hz' 2 (by decide)) (hz' 3 (by decide))
    (by rw [hz' 6 (by decide), getElem_mid]; have := hnc; omega)
  rw [getElem_mid, show P.length + 1 = P.length + [nc].length by simp, take_mid, hz' 6 (by decide),
    Nat.zero_add] at e5
  set σ5 := (σ.seth IN (encN (P ++ [nc])).length).setv (Q 6) nc with hσ5
  have v5 : ∀ i : Fin 16, i ≠ 15 → i ≠ 6 → σ5.val (Q i) = σ.val (Q i) := fun i hi h6 => by
    simp [hσ5, Function.update_of_ne (hQ h6)]
  -- 6.–8. Q 4 := 2 nc, Q 6 := 0
  have e6 := copyR_spec cap (v := Q 6) (d := Q 4) (t := Q 3) (hQ (by decide)) (hQ (by decide)) (hQ (by decide)) σ5
    (by rw [v5 3 (by decide) (by decide)]; exact hz' 3 (by decide))
    (by rw [v5 4 (by decide) (by decide), hz' 4 (by decide)]; simp [hσ5]; omega)
  rw [v5 4 (by decide) (by decide), hz' 4 (by decide), Nat.zero_add, show σ5.val (Q 6) = nc by simp [hσ5]] at e6
  have e7 := copyR_spec cap (v := Q 6) (d := Q 4) (t := Q 3) (hQ (by decide)) (hQ (by decide)) (hQ (by decide))
    (σ5.setv (Q 4) nc) (by simp [Function.update_of_ne (hQ (show (3 : Fin 16) ≠ 4 by decide))]
                           rw [v5 3 (by decide) (by decide)]; exact hz' 3 (by decide))
    (by simp [Function.update_of_ne (hQ (show (6 : Fin 16) ≠ 4 by decide)), hσ5]; omega)
  simp only [WState.setv_val, Function.update_self, Function.update_of_ne (hQ (show (6 : Fin 16) ≠ 4 by decide)),
    wsetv_setv] at e7
  rw [show σ5.val (Q 6) = nc by simp [hσ5]] at e7
  have e8 := wclear_spec cap (Q 6) nc ((σ5.setv (Q 4) (nc + nc)))
    (by simp [Function.update_of_ne (hQ (show (6 : Fin 16) ≠ 4 by decide)), hσ5])
    (by simp [Function.update_of_ne (hQ (show (6 : Fin 16) ≠ 4 by decide)), hσ5]; omega)
  set σ8 := (σ5.setv (Q 4) (nc + nc)).setv (Q 6) 0 with hσ8
  have v8 : ∀ i : Fin 16, i ≠ 15 → i ≠ 4 → σ8.val (Q i) = σ.val (Q i) := fun i hi h4 => by
    by_cases h6 : i = 6
    · subst h6; simp [hσ8]; exact (hz' 6 (by decide)).symm
    · simp [hσ8, Function.update_of_ne (hQ h6), Function.update_of_ne (hQ h4)]; exact v5 i hi h6
  have hst8 : σ8.st IN = σ.st IN := by simp [hσ8, hσ5]
  have h15_8 : σ8.val (Q 15) = σ.val (Q 15) := by
    simp [hσ8, hσ5, Function.update_of_ne (hQ (show (15 : Fin 16) ≠ 6 by decide)),
      Function.update_of_ne (hQ (show (15 : Fin 16) ≠ 4 by decide))]
  -- 9. the top coefficients → SC
  have e9 := copyNs_spec cap IN ((P ++ [nc]) ++ CW ++ ([nt] ++ TB ++ S)) rest SC hIS (Rq Q) (Q 4)
    (fun j => hRq_ne Q j 4 (by decide)) σ8 (P ++ [nc]).length CW.length
    ⟨by rw [hst8, hσ.1, D4], by simp only [hσ8, hσ5, WState.setv_sh, WState.seth_sh, Function.update_self]
                                rw [take_prefix]⟩
    (by simp [hσ8, Function.update_of_ne (hQ (show (4 : Fin 16) ≠ 6 by decide)), hCWl]; ring)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by rw [show Rq Q 1 = Q 9 from rfl, v8 9 (by decide) (by decide)]; exact hz' 9 (by decide))
    (by rw [show Rq Q 2 = Q 10 from rfl, v8 10 (by decide) (by decide)]; exact hz' 10 (by decide))
    (by simp only [hσ8, hσ5, WState.setv_sh, WState.seth_sh, WState.setv_st, WState.seth_st,
          Function.update_of_ne hIS.symm]; exact hSC) (σ.val (Q 15) + (encN CW).length)
    (by rw [R7, h15_8, drop_take_mid])
    (by have := encN_le_mid (P ++ [nc]) CW ([nt] ++ TB ++ S)
        rw [← D4] at this; rw [← D4, ← encN_length]
        have : (encN (P ++ [nc] ++ CW ++ [nt] ++ TB ++ S)).length ≤ 2 * (Λ * (2 * Λ + 1)) := by
          rw [encN_length]; omega
        nlinarith)
    (by omega)
  rw [drop_take_mid, take_mid] at e9
  set σ9 := ((appendO σ8 SC (Rq Q 7) (encN CW)).setv (Q 4) 0).seth IN (encN (P ++ [nc] ++ CW)).length with hσ9
  have v9 : ∀ i : Fin 16, i ≠ 15 → σ9.val (Q i) = σ.val (Q i) := fun i hi => by
    by_cases h4 : i = 4
    · subst h4; simp [hσ9]; exact (hz' 4 (by decide)).symm
    · simp [hσ9, appendO, R7, Function.update_of_ne (hQ h4), Function.update_of_ne (hQ hi)]; exact v8 i hi h4
  have hst9 : σ9.st IN = σ.st IN := by simp [hσ9, appendO, Function.update_of_ne hIS, hst8]
  -- 10. Q 6 := nt
  have e10 := readN_spec cap IN ((P ++ [nc] ++ CW) ++ [nt] ++ (TB ++ S)) rest (Q 0) (Q 1) (Q 6) (Q 2) (Q 3)
    nd6 σ9 (P ++ [nc] ++ CW).length
    ⟨by rw [hst9, hσ.1, D5], by simp only [hσ9, WState.seth_sh, Function.update_self]; rw [take_prefix]⟩ (by simp)
    (by rw [v9 0 (by decide)]; exact hz' 0 (by decide)) (by rw [v9 1 (by decide)]; exact hz' 1 (by decide))
    (by rw [v9 2 (by decide)]; exact hz' 2 (by decide)) (by rw [v9 3 (by decide)]; exact hz' 3 (by decide))
    (by rw [v9 6 (by decide), hz' 6 (by decide), getElem_mid]; have := hnt; omega)
  rw [getElem_mid, show (P ++ [nc] ++ CW).length + 1 = (P ++ [nc] ++ CW).length + [nt].length by simp, take_mid,
    v9 6 (by decide), hz' 6 (by decide), Nat.zero_add] at e10
  set σ10 := (σ9.seth IN (encN (P ++ [nc] ++ CW ++ [nt])).length).setv (Q 6) nt with hσ10
  -- 11. skip the table
  have e11 := skipNs_spec cap IN ((P ++ [nc] ++ CW ++ [nt]) ++ TB ++ S) rest (Q 6) (Q 0) (Q 1)
    (hQ (by decide)) (hQ (by decide)) (hQ (by decide)) σ10 (P ++ [nc] ++ CW ++ [nt]).length TB.length
    ⟨by simp only [hσ10, WState.setv_st, WState.seth_st]; rw [hst9, hσ.1, D6],
     by simp only [hσ10, WState.setv_sh, WState.seth_sh, Function.update_self]; rw [take_prefix]⟩
    (by simp [hσ10, hTBl]) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
    (by simp [hσ10, Function.update_of_ne (hQ (show (0 : Fin 16) ≠ 6 by decide))]; rw [v9 0 (by decide)]
        exact hz' 0 (by decide))
    (by simp [hσ10, Function.update_of_ne (hQ (show (1 : Fin 16) ≠ 6 by decide))]; rw [v9 1 (by decide)]
        exact hz' 1 (by decide))
    (fun x hx => by rw [← D6] at hx; exact hfit' x hx) (by omega)
  rw [take_mid, drop_take_mid] at e11
  refine WExec.cast cap (WExec.seq e5 (WExec.seq e6 (WExec.seq e7 (WExec.seq e8 (WExec.seq e9
    (WExec.seq e10 e11)))))) ?_ ?_
  · apply WState.eq
    · funext j
      by_cases jI : j = IN
      · subst jI; simp
      · simp [hσ10, hσ9, hσ8, hσ5, appendO, Function.update_apply, jI, hIS, Ne.symm hIS]
    · simp [hσ10, hσ9, hσ8, hσ5, appendO]
    · funext r
      by_cases hq : ∃ i, Q i = r
      · obtain ⟨i, rfl⟩ := hq
        by_cases i15 : i = 15
        · subst i15
          simp [hσ10, hσ9, hσ8, hσ5, appendO, R7, Function.update_of_ne (hQ (show (15 : Fin 16) ≠ 6 by decide)),
            Function.update_of_ne (hQ (show (15 : Fin 16) ≠ 4 by decide))]
        · have hfin : ((σ10.setv (Q 6) 0).seth IN (encN (P ++ [nc] ++ CW ++ [nt] ++ TB)).length).val (Q i) = 0 := by
            by_cases i6 : i = 6
            · subst i6; simp
            · simp [hσ10, Function.update_of_ne (hQ i6)]; rw [v9 i i15]; exact hz' i i15
          rw [hfin]
          simp [appendO, Function.update_of_ne (hQ i15)]
          exact (hz' i i15).symm
      · have hr : ∀ i, r ≠ Q i := fun i e => hq ⟨i, e.symm⟩
        simp [hσ10, hσ9, hσ8, hσ5, appendO, R7, hr]
    · simp [hσ10, hσ9, hσ8, hσ5, appendO]
  · have r2 := readCost_le nc Λ (hfit nc (by simp)) hnc
    have r3 := readCost_le nt Λ (hfit nt (by simp)) hnt
    have c2 := copySum_le CW Λ (fun x hx => by have := hfit x (by simp [hx]); omega)
    have c3 := skipSum_le TB Λ (fun x hx => by have := hfit x (by simp [hx]); omega)
    have r2' : (natBitLength nc + 2) * (40 * 2 ^ natBitLength nc + 40) ≤ 40 * (Λ * Λ) + 40 * Λ := by nlinarith
    have r3' : (natBitLength nt + 2) * (40 * 2 ^ natBitLength nt + 40) ≤ 40 * (Λ * Λ) + 40 * Λ := by nlinarith
    have l2' : CW.length * (120 * Λ + 124) ≤ 120 * (Λ * Λ) + 124 * Λ := by nlinarith
    have l3' : TB.length * (20 * Λ + 24) ≤ 20 * (Λ * Λ) + 24 * Λ := by nlinarith
    have hL2 : Λ * Λ + 2 * Λ + 1 = (Λ + 1) ^ 2 := by ring
    clear r2 r3 hLsum
    generalize Λ * Λ = P' at *
    omega

/-- **One circuit unpacked.** -/
theorem unCirc_spec (hIG : IN ≠ GT) (hIS : IN ≠ SC) (hGS : GT ≠ SC) (G N3 : Fin nr) (hQG : ∀ i, Q i ≠ G)
    (hQN : ∀ i, Q i ≠ N3) (hGN : G ≠ N3) {n : ℕ} (C : NCircuit n) (A B : List ℕ) (rest : List Bool)
    (σ : WState ns nr) (hσ : NatAt IN (A ++ circN C ++ B) rest σ A.length) (hz : QZero Q σ) (hG0 : σ.val G = 0)
    (hN3 : σ.val N3 = 2 * n + 3) (hGT : σ.sh GT = (σ.st GT).length) (hSC : σ.sh SC = (σ.st SC).length)
    (Λ : ℕ) (hfit : ∀ x ∈ A ++ circN C ++ B, natBitLength x + 2 ≤ Λ)
    (hRd : 2 ^ (natBitLength C.gates.length + 1) ≤ Λ ∧ 2 ^ (natBitLength C.coeffs.length + 1) ≤ Λ ∧
      2 ^ (natBitLength C.table.length + 1) ≤ Λ)
    (hlen : (A ++ circN C ++ B).length ≤ Λ) (hn : 2 * n + 3 ≤ Λ)
    (hcapΛ : 20 * (Λ + 1) ^ 2 + 2 * (encN (A ++ circN C ++ B)).length + σ.val (Q 15) ≤ cap) :
    WExec cap (unCirc IN GT SC Q G N3) σ
      (((appendO (appendO σ GT (Q 15) (encN (C.gates.flatMap gateN))) SC (Q 15) (encN (C.coeffs.flatMap intN))).seth
        IN (encN (A ++ circN C)).length).setv G C.gates.length) (2000 * (Λ + 1) ^ 2) := by
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  have hc := circN_split C
  have hGWl : (C.gates.flatMap gateN).length = C.gates.length * (2 * n + 3) := flatMap_gateN_length _
  have hCWl : (C.coeffs.flatMap intN).length = 2 * C.coeffs.length := flatMap_intN_length _
  have hTBl : (C.table.map bitN).length = C.table.length := by simp
  generalize C.gates.flatMap gateN = GW at hc hGWl ⊢
  generalize C.coeffs.flatMap intN = CW at hc hCWl ⊢
  generalize C.table.map bitN = TB at hc hTBl
  rw [hc] at hσ hfit hlen hcapΛ ⊢
  have DA : A ++ ([C.gates.length] ++ GW ++ [C.coeffs.length] ++ CW ++ [C.table.length] ++ TB) ++ B =
      A ++ [C.gates.length] ++ GW ++ ([C.coeffs.length] ++ CW ++ [C.table.length] ++ TB ++ B) := by
    simp [List.append_assoc]
  have DB : A ++ ([C.gates.length] ++ GW ++ [C.coeffs.length] ++ CW ++ [C.table.length] ++ TB) ++ B =
      (A ++ [C.gates.length] ++ GW) ++ [C.coeffs.length] ++ CW ++ [C.table.length] ++ TB ++ B := by
    simp [List.append_assoc]
  have hencB : (encN (A ++ ([C.gates.length] ++ GW ++ [C.coeffs.length] ++ CW ++ [C.table.length] ++ TB) ++
      B)).length = (encN (A ++ [C.gates.length] ++ GW ++ ([C.coeffs.length] ++ CW ++ [C.table.length] ++ TB ++
      B))).length := by rw [DA]
  have eA := unCircA_spec cap IN GT Q hIG G N3 hQG hQN hGN n C.gates.length A GW
    ([C.coeffs.length] ++ CW ++ [C.table.length] ++ TB ++ B) hGWl rest σ (by rw [← DA]; exact hσ) hz hG0 hN3 hGT Λ
    (by rw [← DA]; exact hfit) hRd.1 (by rw [← DA]; exact hlen) hn (by nlinarith)
  set τ := ((appendO σ GT (Q 15) (encN GW)).seth IN (encN (A ++ [C.gates.length] ++ GW)).length).setv G
    C.gates.length with hτ
  have eB := unCircB_spec cap IN SC Q hIS (A ++ [C.gates.length] ++ GW) CW TB B C.coeffs.length C.table.length hCWl
    hTBl rest τ
    ⟨by simp only [hτ, WState.setv_st, WState.seth_st]
        simp only [appendO, WState.setv_st, WState.seth_st, WState.sets_st, Function.update_of_ne hIG]; rw [hσ.1, DB],
     by simp only [hτ, WState.setv_sh, WState.seth_sh, Function.update_self]
        rw [show A ++ [C.gates.length] ++ GW ++ [C.coeffs.length] ++ CW ++ [C.table.length] ++ TB ++ B =
          (A ++ [C.gates.length] ++ GW) ++ ([C.coeffs.length] ++ CW ++ [C.table.length] ++ TB ++ B) by
          simp [List.append_assoc], List.take_left]⟩
    (fun i hi => by simp [hτ, appendO, Function.update_of_ne (hQG i), Function.update_of_ne (hQ hi)]; exact hz i hi)
    (by simp [hτ, appendO, Function.update_of_ne hIS.symm, Function.update_of_ne hGS.symm]; exact hSC) Λ
    (by rw [← DB]; exact hfit) hRd.2.1 hRd.2.2 (by rw [← DB]; exact hlen)
    (by have : τ.val (Q 15) = σ.val (Q 15) + (encN GW).length := by
          simp [hτ, appendO, Function.update_of_ne (hQG 15)]
        rw [this]
        have := encN_le_mid (A ++ [C.gates.length]) GW ([C.coeffs.length] ++ CW ++ [C.table.length] ++ TB ++ B)
        rw [← DA] at this; omega)
  refine WExec.cast cap (WExec.seq eA eB) ?_ ?_
  · apply WState.eq
    · funext j; by_cases jI : j = IN
      · subst jI; simp [List.append_assoc]
      · simp [hτ, appendO, Function.update_apply, jI, hIS, hIG, hGS, Ne.symm hIS, Ne.symm hIG, Ne.symm hGS]
    · funext j; by_cases jS : j = SC
      · subst jS; simp [hτ, appendO, Function.update_of_ne hGS.symm]
      · simp [hτ, appendO, Function.update_of_ne jS]
    · funext r; by_cases r15 : r = Q 15
      · subst r15; simp [hτ, appendO, Function.update_of_ne (hQG 15)]
      · by_cases rG : r = G
        · subst rG; simp [hτ, appendO, Function.update_of_ne (hQG 15).symm]
        · simp [hτ, appendO, Function.update_of_ne r15, Function.update_of_ne rG]
    · simp [hτ, appendO]
  · have : (Λ + 1) ^ 2 ≥ 1 := Nat.one_le_pow _ _ (by omega)
    omega

/-! ## The call -/

def unCall1 (Rn Rk N3 : Fin nr) : WM ns nr :=
  .seq (readNatM true IN (Q 0) (Q 1) Rn (Q 2) (Q 3))
  (.seq (readNatM true IN (Q 0) (Q 1) Rk (Q 2) (Q 3))
  (.seq (copyR Rn N3 (Q 3)) (.seq (copyR Rn N3 (Q 3)) (.seq (.inc N3) (.seq (.inc N3) (.inc N3))))))

/-- Step over the parity list and the radius. -/
def unCall3 : WM ns nr :=
  .seq (readNatM true IN (Q 0) (Q 1) (Q 6) (Q 2) (Q 3))
  (.seq (listLoop (Q 6) (skipNat true IN (Q 0) (Q 1)))
  (.seq (.inc (Q 6)) (.seq (.inc (Q 6)) (.seq (.inc (Q 6))
  (listLoop (Q 6) (skipNat true IN (Q 0) (Q 1)))))))

def unCall (GJ S0 S1 : Fin (ns + 1)) (Rn Rk N3 G0 G1 : Fin nr) : WM ns nr :=
  .seq (unCall1 IN Q Rn Rk N3) (.seq (unCirc IN GJ S0 Q G0 N3) (.seq (unCirc IN GJ S1 Q G1 N3) (unCall3 IN Q)))

theorem unCall1_spec (Rn Rk N3 : Fin nr) (hd : [Rn, Rk, N3].Nodup) (hQ' : ∀ i, Q i ∉ [Rn, Rk, N3])
    (n kt : ℕ) (A B : List ℕ) (rest : List Bool) (σ : WState ns nr)
    (hσ : NatAt IN (A ++ [n, kt] ++ B) rest σ A.length) (hz : QZero Q σ)
    (h0 : σ.val Rn = 0 ∧ σ.val Rk = 0 ∧ σ.val N3 = 0) (Λ : ℕ)
    (hfit : 2 ^ (natBitLength n + 1) ≤ Λ ∧ 2 ^ (natBitLength kt + 1) ≤ Λ) (hcap : 4 * Λ + 4 ≤ cap) :
    WExec cap (unCall1 IN Q Rn Rk N3) σ
      ((((σ.seth IN (encN (A ++ [n, kt])).length).setv Rn n).setv Rk kt).setv N3 (2 * n + 3)) (200 * (Λ + 1) ^ 2) := by
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hd
  obtain ⟨⟨nk, nN⟩, kN⟩ := hd
  have qn : ∀ i, Q i ≠ Rn := fun i h => hQ' i (by simp [h])
  have qk : ∀ i, Q i ≠ Rk := fun i h => hQ' i (by simp [h])
  have qN : ∀ i, Q i ≠ N3 := fun i h => hQ' i (by simp [h])
  have hz' : ∀ i : Fin 16, i ≠ 15 → σ.val (Q i) = 0 := hz
  have hn := val_le_of_fit hfit.1
  have hk := val_le_of_fit hfit.2
  have nd1 : [Q 0, Q 1, Rn, Q 2, Q 3].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true]
    exact ⟨⟨hQ (by decide), qn 0, hQ (by decide), hQ (by decide)⟩, ⟨qn 1, hQ (by decide), hQ (by decide)⟩,
      ⟨(qn 2).symm, (qn 3).symm⟩, hQ (by decide)⟩
  have nd2 : [Q 0, Q 1, Rk, Q 2, Q 3].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true]
    exact ⟨⟨hQ (by decide), qk 0, hQ (by decide), hQ (by decide)⟩, ⟨qk 1, hQ (by decide), hQ (by decide)⟩,
      ⟨(qk 2).symm, (qk 3).symm⟩, hQ (by decide)⟩
  have e1 := readF_spec cap IN rest (Q 0) (Q 1) Rn (Q 2) (Q 3) nd1 A ([kt] ++ B) n σ
    (natAt_congr IN rest (by simp [List.append_assoc]) hσ) (hz' 0 (by decide)) (hz' 1 (by decide))
    (hz' 2 (by decide)) (hz' 3 (by decide)) (by rw [h0.1]; omega)
  rw [h0.1, Nat.zero_add] at e1
  set σ1 := (σ.seth IN (encN (A ++ [n])).length).setv Rn n with hσ1
  have v1 : ∀ i : Fin 16, σ1.val (Q i) = σ.val (Q i) := fun i => by simp [hσ1, Function.update_of_ne (qn i)]
  have e2 := readF_spec cap IN rest (Q 0) (Q 1) Rk (Q 2) (Q 3) nd2 (A ++ [n]) B kt σ1
    ⟨by simp only [hσ1, WState.setv_st, WState.seth_st]; rw [hσ.1]; simp [List.append_assoc],
     by simp only [hσ1, WState.setv_sh, WState.seth_sh, Function.update_self]; rw [take_prefix]⟩
    (by rw [v1]; exact hz' 0 (by decide)) (by rw [v1]; exact hz' 1 (by decide))
    (by rw [v1]; exact hz' 2 (by decide)) (by rw [v1]; exact hz' 3 (by decide))
    (by simp [hσ1, Function.update_of_ne (Ne.symm nk), h0.2.1]; omega)
  rw [show σ1.val Rk = 0 by simp [hσ1, Function.update_of_ne (Ne.symm nk), h0.2.1], Nat.zero_add] at e2
  set σ2 := (σ1.seth IN (encN (A ++ [n] ++ [kt])).length).setv Rk kt with hσ2
  have v2 : ∀ i : Fin 16, σ2.val (Q i) = σ.val (Q i) := fun i => by
    simp [hσ2, Function.update_of_ne (qk i)]; exact v1 i
  have vn2 : σ2.val Rn = n := by simp [hσ2, hσ1, Function.update_of_ne nk]
  have vN2 : σ2.val N3 = 0 := by
    simp [hσ2, hσ1, Function.update_of_ne (Ne.symm kN), Function.update_of_ne (Ne.symm nN), h0.2.2]
  have e3 := copyR_spec cap (v := Rn) (d := N3) (t := Q 3) nN (qn 3).symm (qN 3).symm σ2
    (by rw [v2]; exact hz' 3 (by decide)) (by rw [vn2, vN2]; omega)
  rw [vn2, vN2, Nat.zero_add] at e3
  have e4 := copyR_spec cap (v := Rn) (d := N3) (t := Q 3) nN (qn 3).symm (qN 3).symm (σ2.setv N3 n)
    (by simp [Function.update_of_ne (qN 3)]; rw [v2]; exact hz' 3 (by decide))
    (by simp [Function.update_of_ne nN, vn2]; omega)
  simp only [WState.setv_val, Function.update_self, Function.update_of_ne nN, vn2, wsetv_setv] at e4
  have e5 := WExec.inc (cap := cap) N3 (σ2.setv N3 (n + n)) (by simp; omega)
  have e6 := WExec.inc (cap := cap) N3 ((σ2.setv N3 (n + n)).setv N3 ((σ2.setv N3 (n + n)).val N3 + 1))
    (by simp; omega)
  have e7 := WExec.inc (cap := cap) N3 (((σ2.setv N3 (n + n)).setv N3 ((σ2.setv N3 (n + n)).val N3 + 1)).setv N3
    (((σ2.setv N3 (n + n)).setv N3 ((σ2.setv N3 (n + n)).val N3 + 1)).val N3 + 1)) (by simp; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))))
    ?_ ?_
  · simp only [hσ2, hσ1, wsetv_setv, WState.setv_val, Function.update_self]
    apply WState.eq
    · funext j; by_cases jI : j = IN
      · subst jI; simp [List.append_assoc]
      · simp [Function.update_of_ne jI]
    · simp
    · funext r; by_cases rN : r = N3
      · subst rN; simp; ring
      · by_cases rk : r = Rk
        · subst rk; simp [Function.update_of_ne kN]
        · by_cases rn : r = Rn
          · subst rn; simp [Function.update_of_ne nN, Function.update_of_ne nk]
          · simp [Function.update_of_ne rN, Function.update_of_ne rk, Function.update_of_ne rn]
    · simp
  · have r1 := readCost_le n Λ (by have := Nat.lt_two_pow_self (n := natBitLength n + 1); omega) hfit.1
    have r2 := readCost_le kt Λ (by have := Nat.lt_two_pow_self (n := natBitLength kt + 1); omega) hfit.2
    have r1' : (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) ≤ 40 * (Λ * Λ) + 40 * Λ := by nlinarith
    have r2' : (natBitLength kt + 2) * (40 * 2 ^ natBitLength kt + 40) ≤ 40 * (Λ * Λ) + 40 * Λ := by nlinarith
    have hL2 : Λ * Λ + 2 * Λ + 1 = (Λ + 1) ^ 2 := by ring
    clear r1 r2
    generalize Λ * Λ = P' at *
    omega

theorem unCall3_spec (A par R3 B : List ℕ) (hR3 : R3.length = 3) (rest : List Bool) (σ : WState ns nr)
    (hσ : NatAt IN (A ++ [par.length] ++ par ++ R3 ++ B) rest σ A.length) (hz : QZero Q σ) (Λ : ℕ)
    (hfit : ∀ x ∈ A ++ [par.length] ++ par ++ R3 ++ B, natBitLength x + 2 ≤ Λ) (hpar : 2 ^ (natBitLength par.length + 1) ≤ Λ)
    (hlen : (A ++ [par.length] ++ par ++ R3 ++ B).length ≤ Λ) (hcap : 4 * Λ + 4 ≤ cap) :
    WExec cap (unCall3 IN Q) σ (σ.seth IN (encN (A ++ [par.length] ++ par ++ R3)).length) (200 * (Λ + 1) ^ 2) := by
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  have hz' : ∀ i : Fin 16, i ≠ 15 → σ.val (Q i) = 0 := hz
  have hlen' := hlen
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen'
  have hfit' := fit_cap cap hfit (by omega)
  have nd6 : [Q 0, Q 1, Q 6, Q 2, Q 3].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true]
    exact ⟨⟨hQ (by decide), hQ (by decide), hQ (by decide), hQ (by decide)⟩, ⟨hQ (by decide), hQ (by decide),
      hQ (by decide)⟩, ⟨hQ (by decide), hQ (by decide)⟩, hQ (by decide)⟩
  have e1 := readF_spec cap IN rest (Q 0) (Q 1) (Q 6) (Q 2) (Q 3) nd6 A (par ++ R3 ++ B) par.length σ
    (natAt_congr IN rest (by simp [List.append_assoc]) hσ) (hz' 0 (by decide)) (hz' 1 (by decide))
    (hz' 2 (by decide)) (hz' 3 (by decide))
    (by rw [hz' 6 (by decide)]; have := hpar; omega)
  rw [hz' 6 (by decide), Nat.zero_add] at e1
  set σ1 := (σ.seth IN (encN (A ++ [par.length])).length).setv (Q 6) par.length with hσ1
  have e2 := skipF_spec cap IN rest (Q 6) (Q 0) (Q 1) (hQ (by decide)) (hQ (by decide)) (hQ (by decide))
    (A ++ [par.length]) par (R3 ++ B) σ1
    ⟨by simp only [hσ1, WState.setv_st, WState.seth_st]; rw [hσ.1]; simp [List.append_assoc],
     by simp only [hσ1, WState.setv_sh, WState.seth_sh, Function.update_self]; rw [take_prefix]⟩
    (by simp [hσ1]) (by simp [hσ1, Function.update_of_ne (hQ (show (0 : Fin 16) ≠ 6 by decide))]; exact hz' 0 (by decide))
    (by simp [hσ1, Function.update_of_ne (hQ (show (1 : Fin 16) ≠ 6 by decide))]; exact hz' 1 (by decide))
    (fun x hx => hfit' x (by simp only [List.mem_append] at hx ⊢; tauto)) (by omega)
  set σ2 := (σ1.setv (Q 6) 0).seth IN (encN (A ++ [par.length] ++ par)).length with hσ2
  have v2 : σ2 = σ.seth IN (encN (A ++ [par.length] ++ par)).length := by
    rw [hσ2, hσ1, wsetv_setv, wseth_setv, wseth_seth, show (0 : ℕ) = σ.val (Q 6) from (hz' 6 (by decide)).symm,
      wsetv_same]
  rw [v2] at e2
  set τ0 := σ.seth IN (encN (A ++ [par.length] ++ par)).length with hτ0
  have hτ06 : τ0.val (Q 6) = 0 := by simp [hτ0]; exact hz' 6 (by decide)
  have e3 : WExec cap (WM.inc (Q 6)) τ0 (τ0.setv (Q 6) 1) 3 := by
    have := WExec.inc (cap := cap) (Q 6) τ0 (by rw [hτ06]; omega); rwa [hτ06] at this
  have e4 : WExec cap (WM.inc (Q 6)) (τ0.setv (Q 6) 1) (τ0.setv (Q 6) 2) 3 := by
    have := WExec.inc (cap := cap) (Q 6) (τ0.setv (Q 6) 1) (by simp; omega); simpa [wsetv_setv] using this
  have e5 : WExec cap (WM.inc (Q 6)) (τ0.setv (Q 6) 2) (τ0.setv (Q 6) 3) 3 := by
    have := WExec.inc (cap := cap) (Q 6) (τ0.setv (Q 6) 2) (by simp; omega); simpa [wsetv_setv] using this
  have e6 := skipF_spec cap IN rest (Q 6) (Q 0) (Q 1) (hQ (by decide)) (hQ (by decide)) (hQ (by decide))
    (A ++ [par.length] ++ par) R3 B (τ0.setv (Q 6) 3)
    ⟨by simp only [hτ0, WState.setv_st, WState.seth_st]; rw [hσ.1],
     by simp only [hτ0, WState.setv_sh, WState.seth_sh, Function.update_self]; rw [take_prefix]⟩
    (by simp [hR3]) (by simp [hτ0, Function.update_of_ne (hQ (show (0 : Fin 16) ≠ 6 by decide))]; exact hz' 0 (by decide))
    (by simp [hτ0, Function.update_of_ne (hQ (show (1 : Fin 16) ≠ 6 by decide))]; exact hz' 1 (by decide))
    hfit' (by omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))) ?_ ?_
  · rw [hτ0, wsetv_setv, wseth_setv, wseth_seth, show (0 : ℕ) = σ.val (Q 6) from (hz' 6 (by decide)).symm,
      wsetv_same]
  · have r1 := readCost_le par.length Λ (hfit _ (by simp)) hpar
    have s1 := skipSum_le par Λ (fun x hx => by have := hfit x (by simp [hx]); omega)
    have s2 := skipSum_le R3 Λ (fun x hx => by have := hfit x (by simp [hx]); omega)
    have r1' : (natBitLength par.length + 2) * (40 * 2 ^ natBitLength par.length + 40) ≤ 40 * (Λ * Λ) + 40 * Λ := by
      nlinarith
    have l1 : par.length * (20 * Λ + 24) ≤ 20 * (Λ * Λ) + 24 * Λ := by nlinarith
    have l2 : R3.length * (20 * Λ + 24) ≤ 20 * (Λ * Λ) + 24 * Λ := by nlinarith
    have hL2 : Λ * Λ + 2 * Λ + 1 = (Λ + 1) ^ 2 := by ring
    clear r1
    generalize Λ * Λ = P' at *
    omega

theorem callN_split (c : Call) : callN c = [c.n, kindTag c.kind] ++ circN c.first ++ circN c.second ++
    [c.parity.length] ++ c.parity ++ ratN c.radius := rfl

/-- The second circuit, the parity list, the radius. -/
theorem unCallTail_spec (GJ S1 : Fin (ns + 1)) (iG : IN ≠ GJ) (i1 : IN ≠ S1) (g1 : GJ ≠ S1) (G1 N3 : Fin nr)
    (hQG : ∀ i, Q i ≠ G1) (hQN : ∀ i, Q i ≠ N3) (hGN : G1 ≠ N3) {n : ℕ} (C : NCircuit n) (par R3 : List ℕ)
    (hR3 : R3.length = 3) (A B : List ℕ) (rest : List Bool) (σ : WState ns nr)
    (hσ : NatAt IN (A ++ circN C ++ [par.length] ++ par ++ R3 ++ B) rest σ A.length) (hz : QZero Q σ)
    (hG0 : σ.val G1 = 0) (hN3 : σ.val N3 = 2 * n + 3) (hGJ : σ.sh GJ = (σ.st GJ).length)
    (hS1 : σ.sh S1 = (σ.st S1).length) (Λ : ℕ)
    (hfit : ∀ x ∈ A ++ circN C ++ [par.length] ++ par ++ R3 ++ B, natBitLength x + 2 ≤ Λ)
    (hRd : 2 ^ (natBitLength C.gates.length + 1) ≤ Λ ∧ 2 ^ (natBitLength C.coeffs.length + 1) ≤ Λ ∧
      2 ^ (natBitLength C.table.length + 1) ≤ Λ) (hpar : 2 ^ (natBitLength par.length + 1) ≤ Λ)
    (hlen : (A ++ circN C ++ [par.length] ++ par ++ R3 ++ B).length ≤ Λ) (hn : 2 * n + 3 ≤ Λ)
    (hcapΛ : 20 * (Λ + 1) ^ 2 + 2 * (encN (A ++ circN C ++ [par.length] ++ par ++ R3 ++ B)).length + σ.val (Q 15) ≤ cap) :
    WExec cap (.seq (unCirc IN GJ S1 Q G1 N3) (unCall3 IN Q)) σ
      ((((appendO (appendO σ GJ (Q 15) (encN (C.gates.flatMap gateN))) S1 (Q 15) (encN (C.coeffs.flatMap intN))).seth
        IN (encN (A ++ circN C)).length).setv G1 C.gates.length).seth IN
        (encN (A ++ circN C ++ [par.length] ++ par ++ R3)).length) (3000 * (Λ + 1) ^ 2) := by
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  have e1 := unCirc_spec cap IN GJ S1 Q iG i1 g1 G1 N3 hQG hQN hGN C A ([par.length] ++ par ++ R3 ++ B) rest σ
    (natAt_congr IN rest (by simp [List.append_assoc]) hσ) hz hG0 hN3 hGJ hS1 Λ
    (fun x hx => hfit x (by simp only [List.mem_append] at hx ⊢; tauto)) hRd
    (by simp only [List.length_append] at hlen ⊢; omega) hn
    (by have : (encN (A ++ circN C ++ ([par.length] ++ par ++ R3 ++ B))).length =
          (encN (A ++ circN C ++ [par.length] ++ par ++ R3 ++ B)).length := by simp [List.append_assoc]
        rw [this]; exact hcapΛ)
  set τ := ((appendO (appendO σ GJ (Q 15) (encN (C.gates.flatMap gateN))) S1 (Q 15) (encN (C.coeffs.flatMap intN))).seth
    IN (encN (A ++ circN C)).length).setv G1 C.gates.length with hτ
  have e2 := unCall3_spec cap IN Q (A ++ circN C) par R3 B hR3 rest τ
    ⟨by simp [hτ, appendO, Function.update_of_ne iG, Function.update_of_ne i1]; rw [hσ.1]; simp [List.append_assoc],
     by simp only [hτ, WState.setv_sh, WState.seth_sh, Function.update_self]
        rw [show A ++ circN C ++ [par.length] ++ par ++ R3 ++ B = (A ++ circN C) ++ ([par.length] ++ par ++ R3 ++ B) by
          simp [List.append_assoc], List.take_left]⟩
    (fun i hi => by
      simp [hτ, appendO, Function.update_of_ne (hQG i), Function.update_of_ne (hQ hi)]; exact hz i hi) Λ
    hfit hpar hlen (by nlinarith)
  refine WExec.mono (WExec.seq e1 e2) ?_
  have : (1 : ℕ) ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  omega

/-- The state after unpacking the call (explicit). -/
def unCallFinal (GJ S0 S1 : Fin (ns + 1)) (Rn Rk N3 G0 G1 : Fin nr) (c : Call) (A : List ℕ) (σ : WState ns nr) :
    WState ns nr :=
  (((appendO (appendO (((appendO (appendO ((((σ.seth IN (encN (A ++ [c.n, kindTag c.kind])).length).setv Rn c.n).setv
    Rk (kindTag c.kind)).setv N3 (2 * c.n + 3)) GJ (Q 15) (encN (c.first.gates.flatMap gateN))) S0 (Q 15)
    (encN (c.first.coeffs.flatMap intN))).seth IN (encN (A ++ [c.n, kindTag c.kind] ++ circN c.first)).length).setv G0
    c.first.gates.length) GJ (Q 15) (encN (c.second.gates.flatMap gateN))) S1 (Q 15)
    (encN (c.second.coeffs.flatMap intN))).seth IN
    (encN (A ++ [c.n, kindTag c.kind] ++ circN c.first ++ circN c.second)).length).setv G1
    c.second.gates.length).seth IN (encN (A ++ [c.n, kindTag c.kind] ++ circN c.first ++ circN c.second ++
    [c.parity.length] ++ c.parity ++ ratN c.radius)).length

/-- The call unpacker's run (explicit end state). -/
theorem unCall_run (GJ S0 S1 : Fin (ns + 1)) (hd5 : [IN, GJ, S0, S1].Nodup) (Rn Rk N3 G0 G1 : Fin nr)
    (hdr : [Rn, Rk, N3, G0, G1].Nodup) (hQ' : ∀ i, Q i ∉ [Rn, Rk, N3, G0, G1]) (c : Call) (A B : List ℕ)
    (rest : List Bool) (σ : WState ns nr) (hσ : NatAt IN (A ++ callN c ++ B) rest σ A.length) (hz : QZero Q σ)
    (h0 : ∀ r ∈ [Rn, Rk, N3, G0, G1], σ.val r = 0) (hGJ : σ.sh GJ = (σ.st GJ).length)
    (hS0 : σ.sh S0 = (σ.st S0).length) (hS1 : σ.sh S1 = (σ.st S1).length) (Λ : ℕ)
    (hfit : ∀ x ∈ A ++ callN c ++ B, natBitLength x + 2 ≤ Λ)
    (hRd : ∀ v ∈ [c.n, kindTag c.kind, c.first.gates.length, c.first.coeffs.length, c.first.table.length,
      c.second.gates.length, c.second.coeffs.length, c.second.table.length, c.parity.length],
      2 ^ (natBitLength v + 1) ≤ Λ)
    (hlen : (A ++ callN c ++ B).length ≤ Λ) (hn : 2 * c.n + 3 ≤ Λ)
    (hcapΛ : 20 * (Λ + 1) ^ 2 + 4 * (encN (A ++ callN c ++ B)).length + σ.val (Q 15) ≤ cap) :
    WExec cap (unCall IN Q GJ S0 S1 Rn Rk N3 G0 G1) σ (unCallFinal IN Q GJ S0 S1 Rn Rk N3 G0 G1 c A σ)
      (6000 * (Λ + 1) ^ 2) := by
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
    not_false_eq_true] at hd5 hdr
  obtain ⟨⟨iG, i0, i1⟩, ⟨g0, g1⟩, s01⟩ := hd5
  obtain ⟨⟨nk, nN, nG0, nG1⟩, ⟨kN, kG0, kG1⟩, ⟨NG0, NG1⟩, G01⟩ := hdr
  have qr : ∀ i r, r ∈ [Rn, Rk, N3, G0, G1] → Q i ≠ r := fun i r hr h => hQ' i (h ▸ hr)
  have hz' : ∀ i : Fin 16, i ≠ 15 → σ.val (Q i) = 0 := hz
  have hlen' := hlen
  simp only [callN_split, List.length_append, List.length_cons, List.length_nil] at hlen'
  rw [callN_split] at hσ hfit hcapΛ
  have hRR : (ratN c.radius).length = 3 := by simp [ratN, intN]
  -- 1. header
  have e1 := unCall1_spec cap IN Q Rn Rk N3 (by simp [nk, nN, kN]) (fun i h => hQ' i (by simp at h ⊢; tauto))
    c.n (kindTag c.kind) A (circN c.first ++ circN c.second ++ [c.parity.length] ++ c.parity ++ ratN c.radius ++ B) rest σ
    (natAt_congr IN rest (by simp [List.append_assoc]) hσ) hz ⟨h0 Rn (by simp), h0 Rk (by simp), h0 N3 (by simp)⟩ Λ
    ⟨hRd c.n (by simp), hRd (kindTag c.kind) (by simp)⟩ (by nlinarith)
  set σ1 := (((σ.seth IN (encN (A ++ [c.n, kindTag c.kind])).length).setv Rn c.n).setv Rk (kindTag c.kind)).setv N3
    (2 * c.n + 3) with hσ1
  have v1 : ∀ r, r ∉ [Rn, Rk, N3] → σ1.val r = σ.val r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hσ1, Function.update_of_ne hr.1, Function.update_of_ne hr.2.1, Function.update_of_ne hr.2.2]
  have z1 : QZero Q σ1 := fun i hi => by rw [v1 _ (fun h => hQ' i (by simp at h ⊢; tauto))]; exact hz i hi
  -- 2. the first circuit
  have e2 := unCirc_spec cap IN GJ S0 Q iG i0 g0 G0 N3 (fun i => qr i G0 (by simp)) (fun i => qr i N3 (by simp))
    (Ne.symm NG0) c.first (A ++ [c.n, kindTag c.kind]) (circN c.second ++ [c.parity.length] ++ c.parity ++ ratN c.radius ++ B) rest σ1
    ⟨by simp only [hσ1, WState.setv_st, WState.seth_st]; rw [hσ.1]; simp [List.append_assoc],
     by simp only [hσ1, WState.setv_sh, WState.seth_sh, Function.update_self]
        rw [show A ++ [c.n, kindTag c.kind] ++ circN c.first ++ (circN c.second ++ [c.parity.length] ++ c.parity ++ ratN c.radius ++ B) =
          (A ++ [c.n, kindTag c.kind]) ++ (circN c.first ++ (circN c.second ++ [c.parity.length] ++ c.parity ++ ratN c.radius ++ B)) by
          simp [List.append_assoc], List.take_left]⟩
    z1 (by rw [v1 _ (by simp [Ne.symm nG0, Ne.symm kG0, Ne.symm NG0])]; exact h0 G0 (by simp))
    (by simp [hσ1])
    (by simp [hσ1, Function.update_of_ne (Ne.symm iG)]; exact hGJ)
    (by simp [hσ1, Function.update_of_ne (Ne.symm i0)]; exact hS0) Λ
    (fun x hx => hfit x (by simp only [List.mem_append] at hx ⊢; tauto))
    ⟨hRd _ (by simp), hRd _ (by simp), hRd _ (by simp)⟩
    (by simp only [List.length_append, List.length_cons, List.length_nil] at hlen' ⊢; omega) hn
    (by have : (encN (A ++ [c.n, kindTag c.kind] ++ circN c.first ++ (circN c.second ++ [c.parity.length] ++ c.parity ++ ratN c.radius ++ B))).length =
          (encN (A ++ ([c.n, kindTag c.kind] ++ circN c.first ++ circN c.second ++ [c.parity.length] ++ c.parity ++ ratN c.radius) ++ B)).length := by
          simp [List.append_assoc]
        rw [this, show σ1.val (Q 15) = σ.val (Q 15) from v1 _ (fun h => hQ' 15 (by simp at h ⊢; tauto))]; omega)
  set σ2 := ((appendO (appendO σ1 GJ (Q 15) (encN (c.first.gates.flatMap gateN))) S0 (Q 15)
    (encN (c.first.coeffs.flatMap intN))).seth IN (encN (A ++ [c.n, kindTag c.kind] ++ circN c.first)).length).setv G0
    c.first.gates.length with hσ2
  have v2 : ∀ r, r ∉ [Rn, Rk, N3, G0, Q 15] → σ2.val r = σ.val r := fun r hr => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [hσ2, appendO, Function.update_of_ne hr.2.2.2.1, Function.update_of_ne hr.2.2.2.2]
    exact v1 r (by simp [hr.1, hr.2.1, hr.2.2.1])
  have h15_2 : σ2.val (Q 15) = σ.val (Q 15) + (encN (c.first.gates.flatMap gateN)).length +
      (encN (c.first.coeffs.flatMap intN)).length := by
    simp [hσ2, appendO, Function.update_of_ne (qr 15 G0 (by simp))]
    rw [v1 _ (fun h => hQ' 15 (by simp at h ⊢; tauto))]
  have z2 : QZero Q σ2 := fun i hi => by
    rw [v2 _ (fun h => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h | h | h | h
      · exact qr i Rn (by simp) h
      · exact qr i Rk (by simp) h
      · exact qr i N3 (by simp) h
      · exact qr i G0 (by simp) h
      · exact hi (Q.injective h))]
    exact hz i hi
  have hst2 : σ2.st IN = σ.st IN := by
    simp [hσ2, appendO, Function.update_of_ne iG, Function.update_of_ne i0, hσ1]
  have e3 := unCallTail_spec cap IN Q GJ S1 iG i1 g1 G1 N3 (fun i => qr i G1 (by simp)) (fun i => qr i N3 (by simp))
    (Ne.symm NG1) c.second c.parity (ratN c.radius) hRR (A ++ [c.n, kindTag c.kind] ++ circN c.first) B rest σ2
    ⟨by rw [hst2, hσ.1]; simp [List.append_assoc],
     by simp only [hσ2, WState.setv_sh, WState.seth_sh, Function.update_self]
        rw [show A ++ [c.n, kindTag c.kind] ++ circN c.first ++ circN c.second ++ [c.parity.length] ++ c.parity ++
          ratN c.radius ++ B = (A ++ [c.n, kindTag c.kind] ++ circN c.first) ++ (circN c.second ++
          [c.parity.length] ++ c.parity ++ ratN c.radius ++ B) by simp [List.append_assoc], List.take_left]⟩
    z2 (by rw [v2 _ (by simp [Ne.symm nG1, Ne.symm kG1, Ne.symm NG1, Ne.symm G01, Ne.symm (qr 15 G1 (by simp))])]
           exact h0 G1 (by simp))
    (by simp [hσ2, appendO, Function.update_of_ne NG0, Function.update_of_ne (Ne.symm (qr 15 N3 (by simp))), hσ1])
    (by simp [hσ2, appendO, Function.update_of_ne g0, Function.update_of_ne (Ne.symm iG), hσ1, hGJ])
    (by simp [hσ2, appendO, Function.update_of_ne (Ne.symm g1), Function.update_of_ne (Ne.symm s01),
          Function.update_of_ne (Ne.symm i1), hσ1]; exact hS1) Λ
    (fun x hx => hfit x (by simp only [List.mem_append] at hx ⊢; tauto))
    ⟨hRd _ (by simp), hRd _ (by simp), hRd _ (by simp)⟩ (hRd _ (by simp))
    (by simp only [List.length_append, List.length_cons, List.length_nil] at hlen' ⊢; omega) hn
    (by have hl : (encN (A ++ [c.n, kindTag c.kind] ++ circN c.first ++ circN c.second ++ [c.parity.length] ++
          c.parity ++ ratN c.radius ++ B)).length = (encN (A ++ ([c.n, kindTag c.kind] ++ circN c.first ++
          circN c.second ++ [c.parity.length] ++ c.parity ++ ratN c.radius) ++ B)).length := by
          simp [List.append_assoc]
        have hA := encN_le_mid (A ++ [c.n, kindTag c.kind] ++ [c.first.gates.length]) (c.first.gates.flatMap gateN)
          ([c.first.coeffs.length] ++ c.first.coeffs.flatMap intN ++ [c.first.table.length] ++
            c.first.table.map bitN ++ circN c.second ++ [c.parity.length] ++ c.parity ++ ratN c.radius ++ B)
        have hB := encN_le_mid (A ++ [c.n, kindTag c.kind] ++ [c.first.gates.length] ++ c.first.gates.flatMap gateN ++
          [c.first.coeffs.length]) (c.first.coeffs.flatMap intN) ([c.first.table.length] ++
            c.first.table.map bitN ++ circN c.second ++ [c.parity.length] ++ c.parity ++ ratN c.radius ++ B)
        have eA : A ++ [c.n, kindTag c.kind] ++ [c.first.gates.length] ++ c.first.gates.flatMap gateN ++
            ([c.first.coeffs.length] ++ c.first.coeffs.flatMap intN ++ [c.first.table.length] ++
            c.first.table.map bitN ++ circN c.second ++ [c.parity.length] ++ c.parity ++ ratN c.radius ++ B) =
            A ++ ([c.n, kindTag c.kind] ++ circN c.first ++ circN c.second ++ [c.parity.length] ++ c.parity ++
            ratN c.radius) ++ B := by simp [circN, List.append_assoc]
        have eB : A ++ [c.n, kindTag c.kind] ++ [c.first.gates.length] ++ c.first.gates.flatMap gateN ++
            [c.first.coeffs.length] ++ c.first.coeffs.flatMap intN ++ ([c.first.table.length] ++
            c.first.table.map bitN ++ circN c.second ++ [c.parity.length] ++ c.parity ++ ratN c.radius ++ B) =
            A ++ ([c.n, kindTag c.kind] ++ circN c.first ++ circN c.second ++ [c.parity.length] ++ c.parity ++
            ratN c.radius) ++ B := by simp [circN, List.append_assoc]
        rw [eA] at hA; rw [eB] at hB
        rw [hl, h15_2]; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) ?_ ?_
  · rw [hσ2, hσ1]; unfold unCallFinal; simp only [List.append_assoc]
  · have : (1 : ℕ) ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega

end Unpack

end NearCubicGates.Close.CounterMachine
