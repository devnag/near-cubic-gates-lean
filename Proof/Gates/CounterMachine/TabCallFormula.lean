import Proof.Gates.CounterMachine.TabCallVal

/-! # RK, part 12: RG's top branch

**`formulaTop_spec`**: on RG's formula state of a request, the branch on the descriptor tag (residue: `ampP`; digit
moment: `momDP r`; `Φ` moment: `momPP r`, `r` the role) prints exactly `formulaToks x` (= `toks (tabCallTab x).F`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicGates.Close.CounterMachine.TabCallProg

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Counter

variable (tP tK : ℕ) {B1 B2 cT : ℕ}

/-- The branch on the descriptor (`Td 0` the tag, `Td 1` the role). -/
def formulaTop : WM (NS tP tK) NR :=
  .ifr (Td 0)
    (.seq (.dec (Td 0)) (.ifr (Td 0)
      (.seq (.inc (Td 0)) (.ifr (Td 1) (momPP (Y tP tK) X F 1) (momPP (Y tP tK) X F 0)))
      (.seq (.inc (Td 0)) (.ifr (Td 1) (momDP (Y tP tK) X F 1) (momDP (Y tP tK) X F 0)))))
    (ampP (Y tP tK) X F)

theorem decInc (σ : WState (NS tP tK) NR) (cap : ℕ) (r : Fin NR) (v : ℕ) (hv : σ.val r = v + 1) (hc : v + 1 < cap)
    (P Q : WM (NS tP tK) NR) (τ : WState (NS tP tK) NR) (n : ℕ) (hP : WExec cap P σ τ n) :
    WExec cap (.seq (.dec r) (.ifr r (.seq (.inc r) P) (.seq (.inc r) Q))) σ τ (n + 7) ∨ v = 0 := by
  rcases Nat.eq_zero_or_pos v with h | h
  · exact Or.inr h
  · left
    have e1 := WExec.dec (cap := cap) r σ (by omega)
    have e2 := WExec.inc (cap := cap) r (σ.setv r (σ.val r - 1)) (by simp; omega)
    have hs : (σ.setv r (σ.val r - 1)).setv r ((σ.setv r (σ.val r - 1)).val r + 1) = σ := by
      rw [wsetv_setv]; simp [hv]; rw [← hv]; exact wsetv_same σ r
    rw [hs] at e2
    exact WExec.mono (WExec.seq e1 (WExec.ifrT (by simp; omega) (WExec.seq e2 hP))) (by omega)

theorem decInc' (σ : WState (NS tP tK) NR) (cap : ℕ) (r : Fin NR) (hv : σ.val r = 1) (hc : 1 < cap)
    (P Q : WM (NS tP tK) NR) (τ : WState (NS tP tK) NR) (n : ℕ) (hQ : WExec cap Q σ τ n) :
    WExec cap (.seq (.dec r) (.ifr r (.seq (.inc r) P) (.seq (.inc r) Q))) σ τ (n + 7) := by
  have e1 := WExec.dec (cap := cap) r σ (by omega)
  have e2 := WExec.inc (cap := cap) r (σ.setv r (σ.val r - 1)) (by simp; omega)
  have hs : (σ.setv r (σ.val r - 1)).setv r ((σ.setv r (σ.val r - 1)).val r + 1) = σ := by
    rw [wsetv_setv]; simp [hv]; rw [← hv]; exact wsetv_same σ r
  rw [hs] at e2
  exact WExec.mono (WExec.seq e1 (WExec.ifrF (by simp [hv]) (WExec.seq e2 hQ))) (by omega)

/-- The common hypotheses of RG's top branch. -/
structure FormulaPre (x : TabCallReq B1 B2 cT) (Λ cap : ℕ) (σ : WState (NS tP tK) NR) : Prop where
  hs : FState (Y tP tK) X F σ (fdataOf x)
  hb : FBound (fdataOf x) Λ
  hr : FBoundR X σ Λ
  hf : dTag x.id = 0 → AmpFree X σ
  hbin : ∀ j < x.r.p.e, binom x.r.p.e j * (x.r.p.e + j) ≤ Λ
  h2e : 2 * x.r.p.e ≤ Λ
  h2G : 2 * (x.r.c.first.gates.length + x.r.c.second.gates.length) ≤ Λ
  h0 : σ.val (Td 0) = dTag x.id
  h1 : σ.val (Td 1) = dF1 x.id
  h10 : dTag x.id = 1 → σ.val (X 10) = dF2 x.id
  hc3 : 3 ≤ cap
  hcap : TCap cap F σ (formulaToks x) Λ

theorem fdataOf_e (x : TabCallReq B1 B2 cT) : (fdataOf x).e = x.r.p.e := rfl

theorem hGr_of (x : TabCallReq B1 B2 cT) (Λ : ℕ) (h2G : 2 * (x.r.c.first.gates.length + x.r.c.second.gates.length) ≤ Λ) :
    ∀ r < 2, 2 * (fdataOf x).Gr r ≤ Λ := fun r hr' => by
  unfold fdataOf; rw [fdata_Gr _ _ _ _ _ r hr']; unfold circ; split_ifs <;> omega

theorem formulaTop_res (x : TabCallReq B1 B2 cT) (Λ cap : ℕ) (σ : WState (NS tP tK) NR) (h : FormulaPre tP tK x Λ cap σ)
    (part : Option Bool) (q : ℕ) (κ σ' : List ℕ) (hid : x.id = .residue part q κ σ') :
    WExec cap (formulaTop tP tK) σ (emitT (Y tP tK 0) F σ (formulaToks x)) (300000 * (Λ + 1) ^ 5 + 20) := by
  have hm := x.mem; rw [hid] at hm
  have hl := mem_residue_len hm
  have hρ : (fdataOf x).rc * ((fdataOf x).J + 1) ≤ (fdataOf x).ρs.length := by
    have h1 : (fdataOf x).rc = roleCount x.r.c.kind := fdata_rc _ _ _ _ _
    have h2 : (fdataOf x).ρs = κ ++ σ' := by show dRho x.id = _; rw [hid]; rfl
    have h3 : (fdataOf x).J = x.r.p.J := rfl
    rw [h1, h2, h3, List.length_append, hl.1, hl.2]; ring_nf; omega
  have hrt : formulaToks x = ampToks (fdataOf x).e (tToks (fdataOf x)) := by
    unfold formulaToks; rw [hid]; rfl
  have hcap' := h.hcap; rw [hrt] at hcap'
  have e := ampP_spec cap (Y tP tK) X F (fdataOf x) Λ σ h.hs h.hb hρ h.hr (h.hf (by rw [hid]; rfl))
    (by rw [fdataOf_e]; exact h.hbin) (by rw [fdataOf_e]; exact h.h2e) hcap'
  rw [hrt]
  exact WExec.mono (WExec.ifrF (by rw [h.h0, hid]; rfl) e) (by omega)

theorem formulaTop_dig (x : TabCallReq B1 B2 cT) (Λ cap : ℕ) (σ : WState (NS tP tK) NR) (h : FormulaPre tP tK x Λ cap σ)
    (r j : ℕ) (hid : x.id = .digitMoment r j) :
    WExec cap (formulaTop tP tK) σ (emitT (Y tP tK 0) F σ (formulaToks x)) (300000 * (Λ + 1) ^ 5 + 20) := by
  have hm := x.mem; rw [hid] at hm
  have hrj := mem_moment hm
  have hr2 : r < 2 := by have := roleCount_le_two x.r.c; omega
  have hrt : formulaToks x = mdToks (fdataOf x) r j := by unfold formulaToks; rw [hid]
  have hT1 : σ.val (Td 1) = r := by rw [h.h1, hid]; rfl
  have hX10 : σ.val (X 10) = j := by rw [h.h10 (by rw [hid]; rfl), hid]; rfl
  have hJ : j < (fdataOf x).J := hrj.2
  have hGr := hGr_of x Λ h.h2G
  have hcap' := h.hcap; rw [hrt] at hcap'
  have h3 : (Λ + 1) ^ 3 ≤ (Λ + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have e0 : ∀ r' : ℕ, r' < 2 → r' = r → WExec cap (momDP (Y tP tK) X F r') σ
      (emitT (Y tP tK 0) F σ (mdToks (fdataOf x) r j)) (25000 * (Λ + 1) ^ 3) := by
    intro r' hr' hre
    subst hre
    exact momDP_spec cap (Y tP tK) X F (fdataOf x) Λ σ h.hs h.hb h.hr r' j hr' hJ hX10 (hGr r' hr') hcap'
  have eb : WExec cap (.ifr (Td 1) (momDP (Y tP tK) X F 1) (momDP (Y tP tK) X F 0)) σ
      (emitT (Y tP tK 0) F σ (mdToks (fdataOf x) r j)) (25000 * (Λ + 1) ^ 3 + 1) := by
    rcases (show r = 0 ∨ r = 1 by omega) with h' | h'
    · exact WExec.ifrF (by rw [hT1, h']) (WExec.mono (e0 0 (by decide) h'.symm) (by omega))
    · exact WExec.ifrT (by rw [hT1, h']; decide) (e0 1 (by decide) h'.symm)
  have e2 := decInc' tP tK σ cap (Td 0) (by rw [h.h0, hid]; rfl) (by have := h.hc3; omega)
    (.ifr (Td 1) (momPP (Y tP tK) X F 1) (momPP (Y tP tK) X F 0)) _ _ _ eb
  rw [hrt]
  exact WExec.mono (WExec.ifrT (by rw [h.h0, hid]; simp [dTag]) e2) (by omega)

theorem formulaTop_phi (x : TabCallReq B1 B2 cT) (Λ cap : ℕ) (σ : WState (NS tP tK) NR) (h : FormulaPre tP tK x Λ cap σ)
    (r : ℕ) (hid : x.id = .phiMoment r) :
    WExec cap (formulaTop tP tK) σ (emitT (Y tP tK 0) F σ (formulaToks x)) (300000 * (Λ + 1) ^ 5 + 20) := by
  have hm := x.mem; rw [hid] at hm
  have hr' := mem_phi hm
  have hr2 : r < 2 := by have := roleCount_le_two x.r.c; omega
  have hspec := cellReq_spec x.r
  have hL := factors_length hspec
  have hJ1 : 1 ≤ x.r.p.J := hspec.J_pos
  have hrt : formulaToks x = mpToks (fdataOf x) r := by unfold formulaToks; rw [hid]
  have hT1 : σ.val (Td 1) = r := by rw [h.h1, hid]; rfl
  have hLJ : (fdataOf x).J < (fdataOf x).L.length := by
    show x.r.p.J < (x.r.p.factors ++ [x.r.p.M1, x.r.p.A]).length; simp [hL]; omega
  have hGr := hGr_of x Λ h.h2G
  have hcap' := h.hcap; rw [hrt] at hcap'
  have h3 : (Λ + 1) ^ 3 ≤ (Λ + 1) ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  have e0 : ∀ r' : ℕ, r' < 2 → r' = r → WExec cap (momPP (Y tP tK) X F r') σ
      (emitT (Y tP tK 0) F σ (mpToks (fdataOf x) r)) (30000 * (Λ + 1) ^ 3) := by
    intro r' hlt hre
    subst hre
    exact momPP_spec cap (Y tP tK) X F (fdataOf x) Λ σ h.hs h.hb h.hr r' hlt hJ1 hLJ (hGr r' hlt) hcap'
  have eb : WExec cap (.ifr (Td 1) (momPP (Y tP tK) X F 1) (momPP (Y tP tK) X F 0)) σ
      (emitT (Y tP tK 0) F σ (mpToks (fdataOf x) r)) (30000 * (Λ + 1) ^ 3 + 1) := by
    rcases (show r = 0 ∨ r = 1 by omega) with h' | h'
    · exact WExec.ifrF (by rw [hT1, h']) (WExec.mono (e0 0 (by decide) h'.symm) (by omega))
    · exact WExec.ifrT (by rw [hT1, h']; decide) (e0 1 (by decide) h'.symm)
  have e2 := decInc tP tK σ cap (Td 0) 1 (by rw [h.h0, hid]; rfl) (by have := h.hc3; omega)
    (.ifr (Td 1) (momPP (Y tP tK) X F 1) (momPP (Y tP tK) X F 0))
    (.ifr (Td 1) (momDP (Y tP tK) X F 1) (momDP (Y tP tK) X F 0)) _ _ eb
  rw [hrt]
  rcases e2 with e2 | e2
  · exact WExec.mono (WExec.ifrT (by rw [h.h0, hid]; simp [dTag]) e2) (by omega)
  · omega

/-- **RG's top branch.** -/
theorem formulaTop_spec (x : TabCallReq B1 B2 cT) (Λ cap : ℕ) (σ : WState (NS tP tK) NR) (h : FormulaPre tP tK x Λ cap σ) :
    WExec cap (formulaTop tP tK) σ (emitT (Y tP tK 0) F σ (formulaToks x)) (300000 * (Λ + 1) ^ 5 + 20) := by
  cases hid : x.id with
  | residue part q κ σ' => exact formulaTop_res tP tK x Λ cap σ h part q κ σ' hid
  | digitMoment r j => exact formulaTop_dig tP tK x Λ cap σ h r j hid
  | phiMoment r => exact formulaTop_phi tP tK x Λ cap σ h r hid

end NearCubicGates.Close.CounterMachine.TabCallProg
