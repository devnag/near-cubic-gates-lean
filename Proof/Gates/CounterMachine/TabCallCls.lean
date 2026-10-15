import Proof.Gates.CounterMachine.TabCallMach
import Proof.Gates.Cells.OutLen

/-! # RK, part 20: RK's cost class, ONE exponent for every `c_T` (**`tabCallBud_cls`**), and **`tabCallMachineOf`**, **`tabCallMachine`**

`tabCallBud ≤ M·U` with `M = (Cl+1)(CP+1)²(CK+1)` (constants of this `c_T`'s prefix machine and of PolyTab) and `U` in the
uniform class `TB` (`tb_U`): stage A (`costA ≤ (Cl+1)·UA`), the prefix machine (`CP·2^k·W`), PolyTab (`CK·2^s·tabSize^{eK}`),
stage B (RG's `(Λ+1)^5`, the request word `(|prefix| + |tokens| + 1)² ≤ (CP+1)²·4^k·(W + 2 + 2·tabSize)²`). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicGates.Close.CounterMachine.TabCallProg

open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation (natWord)
open NearCubicGates.Close.Interfaces NearCubicGates.Close.Interfaces.Formats NearCubicGates.Close.CounterMachine
open NearCubicGates.Close.Counter NearCubicGates.Close.CheckedPCPP

/-! ## The uniform envelope -/

section Env
variable {B1 B2 : ℕ}

noncomputable def PAf (i : TabCallIndex B1 B2) : ℕ := 1000 * (tabCallInput i.2).length + 2000 * (nI i + 1) ^ 4 + 3000
noncomputable def LAf (El : ℕ) (i : TabCallIndex B1 B2) : ℕ := 200 * (El + nI i + 1) * (2 ^ sI i * (nI i + 1) ^ (El + 1) + 1)
noncomputable def Λ5 (i : TabCallIndex B1 B2) : ℕ := (Λf i.2 + 1) ^ 5
noncomputable def UAf (El : ℕ) (i : TabCallIndex B1 B2) : ℕ := PAf i + 32500 * Λ5 i + LAf El i
noncomputable def Wf (eP : ℕ) (i : TabCallIndex B1 B2) : ℕ := ((cellInput i.2.r).length + 1) ^ eP
noncomputable def PWf (eP : ℕ) (i : TabCallIndex B1 B2) : ℕ := 2 ^ i.2.r.p.k * Wf eP i
noncomputable def KBf (eK : ℕ) (i : TabCallIndex B1 B2) : ℕ := 2 ^ sI i * tabSize (tabCallTab i.2) ^ eK
noncomputable def PBf (eP : ℕ) (i : TabCallIndex B1 B2) : ℕ := 4 ^ i.2.r.p.k * (Wf eP i + 2 + 2 * tabSize (tabCallTab i.2)) ^ 2

/-- The uniform envelope of RK's budget. -/
noncomputable def Uf (El eP eK : ℕ) (i : TabCallIndex B1 B2) : ℕ :=
  265 * UAf El i + 102 * PWf eP i + 2 * KBf eK i + 300021 * Λ5 i + 5000 * PBf eP i +
    240 * (tabCallInput i.2).length + 500

theorem tb_U (El eP eK : ℕ) : TB (Uf (B1 := B1) (B2 := B2) El eP eK) := by
  have hn : PolyB (nI (B1 := B1) (B2 := B2)) nI := PolyB.size
  have hPA : TB (PAf (B1 := B1) (B2 := B2)) := TB.ofPoly
    (PolyB.add (PolyB.add (PolyB.mul (PolyB.const 1000) polyL)
      (PolyB.mul (PolyB.const 2000) (PolyB.pow (PolyB.add hn (PolyB.const 1)) 4))) (PolyB.const 3000))
  have hLA : TB (LAf (B1 := B1) (B2 := B2) El) := by
    refine TB.of_le (g := fun i => 200 * (El + nI i + 1) * ((nI i + 1) ^ (El + 1) + 1))
      (PolyB.mul (PolyB.mul (PolyB.const 200) (PolyB.add (PolyB.add (PolyB.const El) hn) (PolyB.const 1)))
        (PolyB.add (PolyB.pow (PolyB.add hn (PolyB.const 1)) (El + 1)) (PolyB.const 1))) fun i => ?_
    have h1 := Nat.one_le_two_pow (n := sI i)
    have h2 : 2 ^ sI i * (nI i + 1) ^ (El + 1) + 1 ≤ 2 ^ sI i * ((nI i + 1) ^ (El + 1) + 1) := by
      rw [Nat.mul_add, mul_one]; omega
    calc LAf El i ≤ 200 * (El + nI i + 1) * (2 ^ sI i * ((nI i + 1) ^ (El + 1) + 1)) := by
          unfold LAf; exact Nat.mul_le_mul_left _ h2
      _ = 2 ^ sI i * (200 * (El + nI i + 1) * ((nI i + 1) ^ (El + 1) + 1)) := by ring
  have hΛ : TB (Λ5 (B1 := B1) (B2 := B2)) := tb_Λ5
  have hUA : TB (UAf (B1 := B1) (B2 := B2) El) := TB.add (TB.add hPA (TB.cmul 32500 hΛ)) hLA
  have hW : PolyB (nI (B1 := B1) (B2 := B2)) (Wf eP) := PolyB.pow (PolyB.add polyCin (PolyB.const 1)) eP
  have hPW : TB (PWf (B1 := B1) (B2 := B2) eP) := tb_two_k hW
  have hKB : TB (KBf (B1 := B1) (B2 := B2) eK) := TB.of_le (PolyB.pow polyTab eK) fun i => le_refl _
  have hPB : TB (PBf (B1 := B1) (B2 := B2) eP) :=
    tb_four_k (PolyB.pow (PolyB.add (PolyB.add hW (PolyB.const 2)) (PolyB.mul (PolyB.const 2) polyTab)) 2)
  have hL : TB (fun i : TabCallIndex B1 B2 => (tabCallInput i.2).length) := TB.ofPoly polyL
  exact TB.add (TB.add (TB.add (TB.add (TB.add (TB.add (TB.cmul 265 hUA) (TB.cmul 102 hPW)) (TB.cmul 2 hKB))
    (TB.cmul 300021 hΛ)) (TB.cmul 5000 hPB)) (TB.cmul 240 hL)) (TB.ofPoly (PolyB.const 500))

end Env

/-! ## The pointwise bound -/

section Point
variable {B1 B2 cT : ℕ} (PolyTab : TabMachine) (PM : PrefixMachine B1 B2 cT) (CP eP : ℕ)
  (hPM : ∀ r, PM.budget r ≤ CP * 2 ^ r.p.k * ((cellInput r).length + 1) ^ eP)

theorem costA_le (x : TabCallReq B1 B2 cT) (Cl El : ℕ) :
    costA x (Λf x) Cl El ≤ (Cl + 1) * UAf El ⟨cT, x⟩ := by
  have hci := cellInput_le_L x
  have hsl := streams_le x
  simp only [allN] at hsl
  have hle := len_eq x
  have hdf := dF_le x
  have hkt : kindTag x.r.c.kind ≤ 2 := by cases x.r.c.kind <;> decide
  have hJ := J_le x
  have hk := k_le x
  have hc := circ_counts x
  have hn4 := n4_ge x.r.c.n
  have hp4 := pow4_ge x.r.c.n
  have h3 : (Λf x + 1) ^ 3 ≤ Λ5 ⟨cT, x⟩ := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h2 : (Λf x + 1) ^ 2 ≤ Λ5 ⟨cT, x⟩ := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hlog : 200 * (El + x.r.c.n + 1) * (lcap Cl El x.r.c.n x.r.p.k * (x.r.c.n + 1) + 1) ≤
      (Cl + 1) * LAf El ⟨cT, x⟩ := by
    unfold LAf nI sI lcap
    have e : Cl * 2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ El * (x.r.c.n + 1) + 1 ≤
        (Cl + 1) * (2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ (El + 1) + 1) := by
      rw [pow_succ]
      nlinarith [Nat.zero_le (2 ^ (x.r.c.n - x.r.p.k) * ((x.r.c.n + 1) ^ El * (x.r.c.n + 1)))]
    calc 200 * (El + x.r.c.n + 1) * (Cl * 2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ El * (x.r.c.n + 1) + 1)
        ≤ 200 * (El + x.r.c.n + 1) * ((Cl + 1) * (2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ (El + 1) + 1)) :=
          Nat.mul_le_mul_left _ e
      _ = (Cl + 1) * (200 * (El + x.r.c.n + 1) * (2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ (El + 1) + 1)) := by
          ring
  have hA : costA x (Λf x) Cl El ≤ PAf ⟨cT, x⟩ + 32500 * Λ5 ⟨cT, x⟩ + (Cl + 1) * LAf El ⟨cT, x⟩ := by
    unfold costA
    dsimp only [PAf, nI]
    simp only [List.append_nil]
    have := hsl.2.2.2.2.2.1
    rw [← hle] at this ⊢
    omega
  have e : (Cl + 1) * UAf El ⟨cT, x⟩ = (Cl + 1) * PAf ⟨cT, x⟩ + (Cl + 1) * (32500 * Λ5 ⟨cT, x⟩) +
      (Cl + 1) * LAf El ⟨cT, x⟩ := by unfold UAf; ring
  have a1 : PAf ⟨cT, x⟩ ≤ (Cl + 1) * PAf ⟨cT, x⟩ := Nat.le_mul_of_pos_left _ (by omega)
  have a2 : 32500 * Λ5 ⟨cT, x⟩ ≤ (Cl + 1) * (32500 * Λ5 ⟨cT, x⟩) := Nat.le_mul_of_pos_left _ (by omega)
  omega

include hPM in
theorem tabCallBud_le (x : TabCallReq B1 B2 cT) :
    tabCallBud PolyTab PM CP eP x ≤ ((ClOf B1 B2 PolyTab CP eP + 1) * ((CP + 1) ^ 2 * (CK PolyTab + 1))) *
      Uf (ElOf B1 B2 PolyTab eP) eP (eK PolyTab) ⟨cT, x⟩ := by
  unfold tabCallBud tabCallCost costB
  have hA := costA_le x (ClOf B1 B2 PolyTab CP eP) (ElOf B1 B2 PolyTab eP)
  set Cl := ClOf B1 B2 PolyTab CP eP
  set El := ElOf B1 B2 PolyTab eP
  set i : TabCallIndex B1 B2 := ⟨cT, x⟩ with hi
  set M := (Cl + 1) * ((CP + 1) ^ 2 * (CK PolyTab + 1)) with hM
  have hP : PM.budget x.r ≤ CP * PWf eP i := by
    have := hPM x.r; unfold PWf Wf; rw [← Nat.mul_assoc]; exact this
  have hK : PolyTab.budget (tabCallTab x) ≤ CK PolyTab * KBf (eK PolyTab) i := by
    have := polyTab_le PolyTab (tabCallTab x); rw [tabCallTab_s] at this; unfold KBf sI; rw [← Nat.mul_assoc]; exact this
  have hpw : (prefixesWord x.r).length ≤ PM.budget x.r + 1 := NearCubicGates.Close.Cells.wf_out_len PM.wf x.r
  have hpf := pfx_le x
  have htk := toks_le x
  have hsq : ((pfxOf x).length + ((formulaToks x).flatMap tokWord).length + (formulaToks x).length + 1) ^ 2 ≤
      (CP + 1) ^ 2 * PBf eP i := by
    have h2k := Nat.one_le_two_pow (n := x.r.p.k)
    have hb : (pfxOf x).length + ((formulaToks x).flatMap tokWord).length + (formulaToks x).length + 1 ≤
        (CP + 1) * 2 ^ x.r.p.k * (Wf eP i + 2 + 2 * tabSize (tabCallTab x)) := by
      have h1 : PM.budget x.r ≤ CP * 2 ^ x.r.p.k * Wf eP i := hPM x.r
      have e : (CP + 1) * 2 ^ x.r.p.k * (Wf eP i + 2 + 2 * tabSize (tabCallTab x)) =
          CP * 2 ^ x.r.p.k * Wf eP i + (2 ^ x.r.p.k * Wf eP i + (CP + 1) * 2 ^ x.r.p.k * (2 + 2 * tabSize (tabCallTab x))) := by
        ring
      have h3 : 2 + 2 * tabSize (tabCallTab x) ≤ (CP + 1) * 2 ^ x.r.p.k * (2 + 2 * tabSize (tabCallTab x)) :=
        Nat.le_mul_of_pos_left _ (Nat.mul_pos (by omega) h2k)
      omega
    calc _ ≤ ((CP + 1) * 2 ^ x.r.p.k * (Wf eP i + 2 + 2 * tabSize (tabCallTab x))) ^ 2 := Nat.pow_le_pow_left hb 2
      _ = (CP + 1) ^ 2 * PBf eP i := by
          unfold PBf; rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]; ring
  -- the multipliers
  have hM1 : 1 ≤ (CP + 1) ^ 2 * (CK PolyTab + 1) := Nat.mul_pos (Nat.pow_pos (by omega)) (by omega)
  have m1 : (Cl + 1) * UAf El i ≤ M * UAf El i := Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ hM1)
  have hCP : CP ≤ M := by
    have : CP + 1 ≤ (CP + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
    have : (CP + 1) ^ 2 ≤ (CP + 1) ^ 2 * (CK PolyTab + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have : (CP + 1) ^ 2 * (CK PolyTab + 1) ≤ M := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hCK : CK PolyTab ≤ M := by
    have : CK PolyTab + 1 ≤ (CP + 1) ^ 2 * (CK PolyTab + 1) := Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega))
    have : (CP + 1) ^ 2 * (CK PolyTab + 1) ≤ M := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hCP2 : (CP + 1) ^ 2 ≤ M := by
    have : (CP + 1) ^ 2 ≤ (CP + 1) ^ 2 * (CK PolyTab + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have : (CP + 1) ^ 2 * (CK PolyTab + 1) ≤ M := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hM0 : 1 ≤ M := Nat.mul_pos (by omega) hM1
  have m2 : CP * PWf eP i ≤ M * PWf eP i := Nat.mul_le_mul_right _ hCP
  have m3 : CK PolyTab * KBf (eK PolyTab) i ≤ M * KBf (eK PolyTab) i := Nat.mul_le_mul_right _ hCK
  have m4 : (CP + 1) ^ 2 * PBf eP i ≤ M * PBf eP i := Nat.mul_le_mul_right _ hCP2
  have m5 : Λ5 i ≤ M * Λ5 i := Nat.le_mul_of_pos_left _ hM0
  have m6 : (tabCallInput x).length ≤ M * (tabCallInput x).length := Nat.le_mul_of_pos_left _ hM0
  have eU : M * Uf El eP (eK PolyTab) i = 265 * (M * UAf El i) + 102 * (M * PWf eP i) + 2 * (M * KBf (eK PolyTab) i) +
      300021 * (M * Λ5 i) + 5000 * (M * PBf eP i) + 240 * (M * (tabCallInput x).length) + 500 * M := by
    unfold Uf; ring
  have hΛ5 : (Λf x + 1) ^ 5 = Λ5 i := rfl
  rw [hΛ5]
  omega

end Point

/-! ## The class and the machines -/

/-- **RK's class, one exponent for every `c_T`.** -/
theorem tabCallBud_cls (B1 B2 : ℕ) (PolyTab : TabMachine) (eP : ℕ) : ∃ e : ℕ, ∀ (cT : ℕ) (PM : PrefixMachine B1 B2 cT)
    (CP : ℕ), (∀ r, PM.budget r ≤ CP * 2 ^ r.p.k * ((cellInput r).length + 1) ^ eP) →
    ∃ C : ℕ, ∀ x : TabCallReq B1 B2 cT, tabCallBud PolyTab PM CP eP x ≤ C * 2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ e := by
  obtain ⟨CU, eU, hU⟩ := tb_U (B1 := B1) (B2 := B2) (ElOf B1 B2 PolyTab eP) eP (eK PolyTab)
  refine ⟨eU, fun cT PM CP hPM => ⟨((ClOf B1 B2 PolyTab CP eP + 1) * ((CP + 1) ^ 2 * (CK PolyTab + 1))) * CU, fun x => ?_⟩⟩
  have h1 := tabCallBud_le PolyTab PM CP eP hPM x
  have h2 := hU ⟨cT, x⟩
  unfold sI nI at h2
  calc tabCallBud PolyTab PM CP eP x ≤ _ := h1
    _ ≤ ((ClOf B1 B2 PolyTab CP eP + 1) * ((CP + 1) ^ 2 * (CK PolyTab + 1))) *
        (CU * 2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ eU) := Nat.mul_le_mul_left _ h2
    _ = _ := by ring

/-- **RK** (STATEMENT RK) for a prefix machine with an explicit class `CP·2^k·(|cellInput|+1)^{eP}`. -/
noncomputable def tabCallMachineOf {B1 B2 cT : ℕ} (PolyTab : TabMachine) (hord : ∀ R, PolyTab.order R = printerOrder R.s)
    (PM : PrefixMachine B1 B2 cT) (CP eP : ℕ)
    (hPM : ∀ r, PM.budget r ≤ CP * 2 ^ r.p.k * ((cellInput r).length + 1) ^ eP) : TabCallMachine B1 B2 cT PolyTab where
  budget := tabCallBud PolyTab PM CP eP
  wf := tabCallWF PolyTab hord PM CP eP hPM
  cls := by
    obtain ⟨e, he⟩ := tabCallBud_cls B1 B2 PolyTab eP
    obtain ⟨C, hC⟩ := he cT PM CP hPM
    exact ⟨C, e, hC⟩

theorem tabCallMachineOf_budget {B1 B2 cT : ℕ} (PolyTab : TabMachine) (hord : ∀ R, PolyTab.order R = printerOrder R.s)
    (PM : PrefixMachine B1 B2 cT) (CP eP : ℕ)
    (hPM : ∀ r, PM.budget r ≤ CP * 2 ^ r.p.k * ((cellInput r).length + 1) ^ eP) :
    (tabCallMachineOf PolyTab hord PM CP eP hPM).budget = tabCallBud PolyTab PM CP eP := rfl

/-- **RK** (STATEMENT RK), constants taken from the prefix machine's class. -/
noncomputable def tabCallMachine {B1 B2 cT : ℕ} (PolyTab : TabMachine) (hord : ∀ R, PolyTab.order R = printerOrder R.s)
    (PM : PrefixMachine B1 B2 cT) : TabCallMachine B1 B2 cT PolyTab :=
  tabCallMachineOf PolyTab hord PM (Classical.choose PM.cls) (Classical.choose (Classical.choose_spec PM.cls))
    (Classical.choose_spec (Classical.choose_spec PM.cls))

/-- **RK, uniform in `c_T`.** For a prefix-machine family with ONE class exponent (`∃ e, ∀ cT, ∃ C, …`), the RK
machines `tabCallMachineOf … (PM cT) (C cT) e …` have ONE class exponent. -/
theorem tabCallMachine_uniform (B1 B2 : ℕ) (PolyTab : TabMachine) (hord : ∀ R, PolyTab.order R = printerOrder R.s)
    (PM : ∀ cT, PrefixMachine B1 B2 cT)
    (hPM : ∃ eP, ∀ cT, ∃ CP, ∀ r : CellReq B1 B2 cT, (PM cT).budget r ≤ CP * 2 ^ r.p.k * ((cellInput r).length + 1) ^ eP) :
    ∃ (RK : ∀ cT, TabCallMachine B1 B2 cT PolyTab) (e : ℕ), ∀ cT, ∃ C, ∀ x : TabCallReq B1 B2 cT,
      (RK cT).budget x ≤ C * 2 ^ (x.r.c.n - x.r.p.k) * (x.r.c.n + 1) ^ e := by
  obtain ⟨eP, hP⟩ := hPM
  obtain ⟨e, he⟩ := tabCallBud_cls B1 B2 PolyTab eP
  refine ⟨fun cT => tabCallMachineOf PolyTab hord (PM cT) (Classical.choose (hP cT)) eP (Classical.choose_spec (hP cT)), e,
    fun cT => ?_⟩
  exact he cT (PM cT) _ (Classical.choose_spec (hP cT))

end NearCubicGates.Close.CounterMachine.TabCallProg
