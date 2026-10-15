import Proof.Gates.CounterMachine.UnpackAll
import Proof.Gates.CounterMachine.TabCallSpec

/-! # RK, part 2: reading the request descriptor

`descN id` (RKSpec): three header fields (tag, then part/q or role/digit), and for a residue request the residue
vector `κ ++ σ` with its length. **`rdDesc_spec`**: registers `T 0, T 1, T 2` get the header, the residue vector is
appended to the stream `KV` (`encN`, RG's `Y 6`), the input head moves past the descriptor. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NearCubicGates.Close.CounterMachine

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm.WriteNat (appendO appendO_append)
open NearCubicWires.WireExponent3_5.PrimAsm.ParseNat (readNatM)
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Codec NearCubicGates.Close.Counter NearCubicGates.Close.Interfaces
open NearCubicGates.Close.Interfaces.Formats

variable {ns nr : ℕ} (cap : ℕ)

/-- The header fields and the residue vector of a descriptor. -/
def dTag : ReqId → ℕ
  | .residue .. => 0
  | .digitMoment .. => 1
  | .phiMoment _ => 2

def dF1 : ReqId → ℕ
  | .residue part _ _ _ => partCode part
  | .digitMoment r _ => r
  | .phiMoment r => r

def dF2 : ReqId → ℕ
  | .residue _ q _ _ => q
  | .digitMoment _ j => j
  | .phiMoment _ => 0

def dRho : ReqId → List ℕ
  | .residue _ _ κ σ => κ ++ σ
  | _ => []

theorem descN_split (id : ReqId) : descN id = [dTag id, dF1 id, dF2 id] ++
    (if dTag id = 0 then [(dRho id).length] ++ dRho id else []) := by
  cases id <;> simp [descN, dTag, dF1, dF2, dRho]

section Desc
variable (IN KV : Fin (ns + 1)) (Q : Fin 16 ↪ Fin nr) (T : Fin 4 ↪ Fin nr)

def rdF (v : Fin nr) : WM ns nr := readNatM true IN (Q 0) (Q 1) v (Q 2) (Q 3)

/-- Read the descriptor. -/
def rdDesc : WM ns nr :=
  .seq (rdF IN Q (T 0)) (.seq (rdF IN Q (T 1)) (.seq (rdF IN Q (T 2))
    (.ifr (T 0) .skip (.seq (rdF IN Q (T 3)) (listLoop (T 3) (copyNat true IN KV (Rq Q)))))))

theorem rdF_step (hTQ : ∀ i j, T i ≠ Q j) (i : Fin 4) (A B : List ℕ) (x : ℕ) (rest : List Bool) (σ : WState ns nr)
    (hσ : NatAt IN (A ++ [x] ++ B) rest σ A.length) (hz : QZero Q σ) (hv : σ.val (T i) = 0) (Λ : ℕ)
    (h1 : natBitLength x + 2 ≤ Λ) (h2 : 2 ^ (natBitLength x + 1) ≤ Λ) (hc : Λ ≤ cap) :
    WExec cap (rdF IN Q (T i)) σ ((σ.seth IN (encN (A ++ [x])).length).setv (T i) x) (Λ * (40 * Λ + 40)) := by
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  have hd : [Q 0, Q 1, T i, Q 2, Q 3].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true,
      not_false_eq_true]
    exact ⟨⟨hQ (by decide), (hTQ i 0).symm, hQ (by decide), hQ (by decide)⟩, ⟨(hTQ i 1).symm, hQ (by decide),
      hQ (by decide)⟩, ⟨hTQ i 2, hTQ i 3⟩, hQ (by decide)⟩
  have e := readF_spec cap IN rest (Q 0) (Q 1) (T i) (Q 2) (Q 3) hd A B x σ hσ (hz 0 (by decide)) (hz 1 (by decide))
    (hz 2 (by decide)) (hz 3 (by decide)) (by rw [hv]; omega)
  rw [hv, Nat.zero_add] at e
  exact WExec.mono e (readCost_le x Λ h1 h2)

theorem rdDesc_spec (hTQ : ∀ i j, T i ≠ Q j) (hIK : IN ≠ KV) (id : ReqId) (L : List ℕ) (rest : List Bool)
    (σ : WState ns nr) (hσ : NatAt IN (descN id ++ L) rest σ 0) (hz : QZero Q σ) (hT : ∀ i, σ.val (T i) = 0)
    (hKV : σ.sh KV = (σ.st KV).length) (Λ : ℕ)
    (hbits : ∀ x ∈ descN id, natBitLength x + 2 ≤ Λ ∧ 2 ^ (natBitLength x + 1) ≤ Λ) (hlen : (descN id).length ≤ Λ)
    (hcap : Λ + σ.val (Q 15) + 3 * (encN (descN id ++ L)).length + 4 ≤ cap) :
    ∃ τ, WExec cap (rdDesc IN KV Q T) σ τ (400 * (Λ + 1) ^ 3) ∧
      NatAt IN (descN id ++ L) rest τ (descN id).length ∧ QZero Q τ ∧
      τ.val (T 0) = dTag id ∧ τ.val (T 1) = dF1 id ∧ τ.val (T 2) = dF2 id ∧ τ.val (T 3) = 0 ∧
      τ.st KV = σ.st KV ++ encN (dRho id) ∧ τ.sh KV = (τ.st KV).length ∧
      τ.val (Q 15) = σ.val (Q 15) + (encN (dRho id)).length ∧
      (∀ X, X ≠ IN → X ≠ KV → τ.st X = σ.st X ∧ τ.sh X = σ.sh X) ∧
      (∀ r, (∀ i, r ≠ T i) → r ≠ Q 15 → τ.val r = σ.val r) := by
  have hT' : ∀ {a b : Fin 4}, a ≠ b → T a ≠ T b := fun h => T.injective.ne h
  have hQ : ∀ {a b : Fin 16}, a ≠ b → Q a ≠ Q b := fun h => Q.injective.ne h
  set R' := (if dTag id = 0 then [(dRho id).length] ++ dRho id else []) with hR'
  have hsp := descN_split id
  rw [← hR'] at hsp
  have hb : ∀ x ∈ [dTag id, dF1 id, dF2 id], natBitLength x + 2 ≤ Λ ∧ 2 ^ (natBitLength x + 1) ≤ Λ :=
    fun x hx => hbits x (by rw [hsp]; exact List.mem_append_left _ hx)
  have hΛc : Λ ≤ cap := by omega
  have hencL := encN_le_mid [] (descN id) L
  simp only [List.nil_append] at hencL
  -- the three header fields
  have e1 := rdF_step cap IN Q T hTQ 0 [] ([dF1 id, dF2 id] ++ R' ++ L) (dTag id) rest σ
    (natAt_congr IN rest (by rw [hsp]; simp) hσ) hz (hT 0) Λ (hb _ (by simp)).1 (hb _ (by simp)).2 hΛc
  set σ1 := (σ.seth IN (encN ([] ++ [dTag id])).length).setv (T 0) (dTag id) with hσ1
  have e2 := rdF_step cap IN Q T hTQ 1 [dTag id] ([dF2 id] ++ R' ++ L) (dF1 id) rest σ1
    ⟨by simp only [hσ1, WState.setv_st, WState.seth_st]; rw [hσ.1, hsp]; simp,
     by simp [hσ1]⟩
    (fun i hi => by simp [hσ1, Function.update_of_ne (hTQ 0 i).symm]; exact hz i hi)
    (by simp [hσ1, Function.update_of_ne (hT' (show (1 : Fin 4) ≠ 0 by decide)), hT 1]) Λ
    (hb _ (by simp)).1 (hb _ (by simp)).2 hΛc
  set σ2 := (σ1.seth IN (encN ([dTag id] ++ [dF1 id])).length).setv (T 1) (dF1 id) with hσ2
  have e3 := rdF_step cap IN Q T hTQ 2 [dTag id, dF1 id] (R' ++ L) (dF2 id) rest σ2
    ⟨by simp only [hσ2, hσ1, WState.setv_st, WState.seth_st]; rw [hσ.1, hsp]; simp,
     by simp [hσ2]⟩
    (fun i hi => by
      simp [hσ2, hσ1, Function.update_of_ne (hTQ 0 i).symm, Function.update_of_ne (hTQ 1 i).symm]; exact hz i hi)
    (by simp [hσ2, hσ1, Function.update_of_ne (hT' (show (2 : Fin 4) ≠ 0 by decide)),
      Function.update_of_ne (hT' (show (2 : Fin 4) ≠ 1 by decide)), hT 2]) Λ
    (hb _ (by simp)).1 (hb _ (by simp)).2 hΛc
  set σ3 := (σ2.seth IN (encN ([dTag id, dF1 id] ++ [dF2 id])).length).setv (T 2) (dF2 id) with hσ3
  have z3 : QZero Q σ3 := fun i hi => by
    simp [hσ3, hσ2, hσ1, Function.update_of_ne (hTQ 0 i).symm, Function.update_of_ne (hTQ 1 i).symm,
      Function.update_of_ne (hTQ 2 i).symm]; exact hz i hi
  have st3 : σ3.st = σ.st := by simp [hσ3, hσ2, hσ1]
  have sh3 : σ3.sh = Function.update σ.sh IN (encN [dTag id, dF1 id, dF2 id]).length := by
    simp [hσ3, hσ2, hσ1]
  have v3 : ∀ r, (∀ i, r ≠ T i) → σ3.val r = σ.val r := fun r hr => by
    simp [hσ3, hσ2, hσ1, Function.update_of_ne (hr 0), Function.update_of_ne (hr 1), Function.update_of_ne (hr 2)]
  have t3 : σ3.val (T 0) = dTag id ∧ σ3.val (T 1) = dF1 id ∧ σ3.val (T 2) = dF2 id ∧ σ3.val (T 3) = 0 := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [hσ3, hσ2, hσ1, Function.update_of_ne (hT' (show (0 : Fin 4) ≠ 2 by decide)),
        Function.update_of_ne (hT' (show (0 : Fin 4) ≠ 1 by decide))]
    · simp [hσ3, hσ2, hσ1, Function.update_of_ne (hT' (show (1 : Fin 4) ≠ 2 by decide))]
    · simp [hσ3]
    · simp [hσ3, hσ2, hσ1, Function.update_of_ne (hT' (show (3 : Fin 4) ≠ 2 by decide)),
        Function.update_of_ne (hT' (show (3 : Fin 4) ≠ 1 by decide)),
        Function.update_of_ne (hT' (show (3 : Fin 4) ≠ 0 by decide)), hT 3]
  have h1Λ : 1 ≤ (Λ + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hc3 : Λ * (40 * Λ + 40) ≤ 40 * (Λ + 1) ^ 2 := by nlinarith
  have h23 : (Λ + 1) ^ 2 ≤ (Λ + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  by_cases htag : dTag id = 0
  · -- a residue request: the length, then the vector
    have hR'e : R' = [(dRho id).length] ++ dRho id := by rw [hR', if_pos htag]
    have hbl := hbits (dRho id).length (by rw [hsp, hR'e]; simp)
    have e4 := rdF_step cap IN Q T hTQ 3 [dTag id, dF1 id, dF2 id] (dRho id ++ L) (dRho id).length rest σ3
      ⟨by rw [st3, hσ.1, hsp, hR'e]; simp, by rw [sh3]; simp⟩ z3 t3.2.2.2 Λ hbl.1 hbl.2 hΛc
    set σ4 := (σ3.seth IN (encN ([dTag id, dF1 id, dF2 id] ++ [(dRho id).length])).length).setv (T 3)
      (dRho id).length with hσ4
    have hKR : ∀ j, Rq Q j ≠ T 3 := fun j h => hTQ 3 _ (by rw [Rq_apply] at h; exact h.symm)
    have e5 := copyF_spec cap IN rest KV hIK (Rq Q) (T 3) hKR ([dTag id, dF1 id, dF2 id] ++ [(dRho id).length])
      (dRho id) L σ4 ⟨by simp [hσ4, st3, hσ.1, hsp, hR'e], by simp [hσ4]⟩ (by simp [hσ4])
      (by simp only [hσ4, WState.setv_val, WState.seth_val, Rq_apply]
          rw [Function.update_of_ne (hTQ 3 _).symm]; exact z3 _ (by decide))
      (by simp only [hσ4, WState.setv_val, WState.seth_val, Rq_apply]
          rw [Function.update_of_ne (hTQ 3 _).symm]; exact z3 _ (by decide))
      (by simp [hσ4, st3, sh3, Function.update_of_ne (Ne.symm hIK), hKV])
      (by simp only [hσ4, WState.setv_val, WState.seth_val, Rq_apply]
          rw [Function.update_of_ne (hTQ 3 _).symm]
          have : σ3.val (Q ⟨8 + (7 : Fin 8).val, by omega⟩) = σ.val (Q 15) := v3 _ (fun i => (hTQ i 15).symm)
          rw [this]
          rw [show [dTag id, dF1 id, dF2 id] ++ [(dRho id).length] ++ dRho id ++ L = descN id ++ L by
            rw [hsp, hR'e]; simp]
          omega)
      (by have := hlen; rw [hsp, hR'e] at this; simp at this; omega)
    have hρb : ∀ x ∈ dRho id, natBitLength x ≤ Λ := fun x hx => by
      have := (hbits x (by rw [hsp, hR'e]; simp [hx])).1; omega
    have hρl : (dRho id).length ≤ Λ := by have := hlen; rw [hsp, hR'e] at this; simp at this; omega
    have hcs := copySum_le (dRho id) Λ hρb
    have hcs2 : (dRho id).length * (120 * Λ + 124) ≤ 124 * (Λ + 1) ^ 2 := by nlinarith
    set σ5 := ((appendO σ4 KV (Rq Q 7) (encN (dRho id))).setv (T 3) 0).seth IN
      (encN ([dTag id, dF1 id, dF2 id] ++ [(dRho id).length] ++ dRho id)).length with hσ5
    have q4 : σ4.val (Rq Q 7) = σ.val (Q 15) := by
      simp only [hσ4, WState.setv_val, WState.seth_val, Rq_apply]
      rw [Function.update_of_ne (hTQ 3 _).symm]; exact v3 _ (fun i => (hTQ i 15).symm)
    have hR7 : Rq Q 7 = Q 15 := rfl
    refine ⟨σ5, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.ifrF (by rw [t3.1, htag])
      (WExec.seq e4 e5))))) (by nlinarith), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨by simp [hσ5, hσ4, st3, Function.update_of_ne hIK, hσ.1], ?_⟩
      simp only [hσ5, WState.seth_sh, Function.update_self]
      rw [hsp, hR'e]; simp
    · intro i hi
      simp only [hσ5, hσ4, WState.seth_val, WState.setv_val, appendO, WState.sets_val, hR7]
      rw [Function.update_of_ne (hTQ 3 i).symm, Function.update_of_ne (fun h => hi (Q.injective h)),
        Function.update_of_ne (hTQ 3 i).symm]
      exact z3 i hi
    · simp [hσ5, hσ4, appendO, hR7, Function.update_of_ne (hT' (show (0 : Fin 4) ≠ 3 by decide)),
        Function.update_of_ne (hTQ 0 _)]; exact t3.1
    · simp [hσ5, hσ4, appendO, hR7, Function.update_of_ne (hT' (show (1 : Fin 4) ≠ 3 by decide)),
        Function.update_of_ne (hTQ 1 _)]; exact t3.2.1
    · simp [hσ5, hσ4, appendO, hR7, Function.update_of_ne (hT' (show (2 : Fin 4) ≠ 3 by decide)),
        Function.update_of_ne (hTQ 2 _)]; exact t3.2.2.1
    · simp [hσ5]
    · simp [hσ5, hσ4, appendO, Function.update_of_ne (Ne.symm hIK), st3]
    · simp [hσ5, hσ4, appendO, Function.update_of_ne (Ne.symm hIK), st3, sh3, hKV]
    · simp only [hσ5, hσ4, WState.seth_val, WState.setv_val, appendO, WState.sets_val, hR7]
      rw [Function.update_of_ne (hTQ 3 _).symm, Function.update_self]
      rw [Function.update_of_ne (hTQ 3 _).symm]
      rw [v3 _ (fun i => (hTQ i 15).symm)]
    · intro X hX1 hX2
      simp [hσ5, hσ4, appendO, Function.update_of_ne hX1, Function.update_of_ne hX2, st3, sh3]
    · intro r hr h15
      simp only [hσ5, hσ4, WState.seth_val, WState.setv_val, appendO, WState.sets_val, hR7]
      rw [Function.update_of_ne (hr 3), Function.update_of_ne h15, Function.update_of_ne (hr 3)]
      exact v3 r hr
  · -- a moment request: nothing more
    have hR'e : R' = [] := by rw [hR', if_neg htag]
    have hρ : dRho id = [] := by cases id <;> simp_all [dTag, dRho]
    refine ⟨σ3, WExec.mono (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.ifrT (by rw [t3.1]; exact htag)
      (WExec.skip σ3))))) (by nlinarith), ?_, z3, t3.1, t3.2.1, t3.2.2.1, t3.2.2.2, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨by rw [st3, hσ.1], ?_⟩
      rw [sh3, Function.update_self, hsp, hR'e]; simp
    · rw [st3, hρ]; simp [encN]
    · rw [st3, sh3, Function.update_of_ne (Ne.symm hIK)]; exact hKV
    · rw [v3 _ (fun i => (hTQ i 15).symm), hρ]; simp [encN]
    · intro X hX1 _
      rw [st3, sh3, Function.update_of_ne hX1]; exact ⟨rfl, rfl⟩
    · intro r hr _
      exact v3 r hr

end Desc

end NearCubicGates.Close.CounterMachine
