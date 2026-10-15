import Proof.Wire_3_5.UnionMachineThrUnitIface3

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimThrW.RadSetup

/-! ## A tape grows only under its head -/

theorem wtb_le : ∀ (l : List Bool) (p K : ℕ) (v : Bool), l.length ≤ K → p + 1 ≤ K → (writeTapeBit l p v).length ≤ K
  | [], 0, K, v, _, h => by simp only [writeTapeBit, List.length_cons, List.length_nil]; omega
  | [], p + 1, K, v, _, h => by
    have := wtb_le [] p (K - 1) v (by simp) (by omega)
    simp only [writeTapeBit, List.length_cons]
    omega
  | a :: t, 0, K, v, h, _ => by
    simp only [writeTapeBit, List.length_cons] at h ⊢
    omega
  | a :: t, p + 1, K, v, h, hp => by
    simp only [List.length_cons] at h
    have := wtb_le t p (K - 1) v (by omega) (by omega)
    simp only [writeTapeBit, List.length_cons]
    omega

theorem step_len {t s : ℕ} (p : Machine t s) (c d : Configuration t s) (i : Fin t) (hs : step p c = some d) (K : ℕ)
    (h1 : (c.tapes i).length ≤ K) (h2 : c.heads i + 1 ≤ K) : (d.tapes i).length ≤ K := by
  cases hr : p.rule c.control c.scanned with
  | none => simp [step, hr] at hs
  | some action =>
    have hd : applyAction c action = d := by simpa [step, hr] using hs
    subst d
    change (match action.write i with
      | none => c.tapes i
      | some value => writeTapeBit (c.tapes i) (c.heads i) value).length ≤ K
    split
    · exact h1
    · exact wtb_le _ _ _ _ h1 h2

theorem prefix_len {t s space n : ℕ} {p : Machine t s} {c e : Configuration t s} (hp : Prefix p space n c e)
    (i : Fin t) : ∀ K, (c.tapes i).length ≤ K → c.heads i + n ≤ K → (e.tapes i).length ≤ K := by
  induction hp with
  | refl => intro K h1 _; exact h1
  | step _ _ hs _ ih =>
    intro K h1 h2
    have hh := SelectiveReset.step_head p _ _ i hs
    exact ih K (step_len p _ _ i hs K h1 (by omega)) (by omega)

/-- **A run of `n` steps leaves every tape within its old length or its head's reach.** -/
theorem Step_len {t s n : ℕ} {M : Machine t s} {H H' : Fin t → ℕ} {A A' : Fin t → List Bool}
    (h : Step M n H A H' A') (i : Fin t) (K : ℕ) (h1 : (A i).length ≤ K) (h2 : H i + n ≤ K) : (A' i).length ≤ K := by
  obtain ⟨r, hr, -, ht, hs⟩ := h
  have hp := (prefix_of_run M n ⟨M.start, H, A⟩ r hr).1
  rw [← ht]
  exact prefix_len hp i K h1 (by show H i + r.steps ≤ K; omega)

/-- **A unit that meets `UnitOK` runs at least `j + 1` steps** (its counter grows to `1^(j+1)` from head `0`). -/
theorem unitOK_ctr {cap x sU : ℕ} {U : Machine (PrimAsm.CellLoop.TT x) sU} {nU : ℕ} {w u : List Bool}
    {emit : ℕ → List Bool} {j : ℕ} {out : List Bool} (h : PrimThrW.Shell.UnitOK cap x U nU w u emit j out) :
    j + 1 ≤ nU := by
  obtain ⟨σE, mU, hS, -, -, -, h2, hn⟩ := h
  by_contra hlt
  have n20 : sk x 2 ≠ sk x 0 := fun e => absurd (sk_inj x e) (by decide)
  have n21 : sk x 2 ≠ sk x 1 := fun e => absurd (sk_inj x e) (by decide)
  have n213 : sk x 2 ≠ sk x 113 := fun e => absurd (sk_inj x e) (by decide)
  have hl := Step_len hS (sTape (sk x 2)) j
    (by rw [wenc_A_s]; simp [CellLoopD.blankCellD, CellState.blankCell, n20, n21, n213])
    (by rw [wenc_H_s]; simp [CellLoopD.blankCellD, CellState.blankCell, n21]; omega)
  rw [wenc_A_s, h2, List.length_replicate] at hl
  omega

/-- **THRU2 is `False` at a THR call**: its `ok` at the unit `j := nU (meas)` and the capacity `need (meas) + j`
contradicts `unitOK_ctr`. -/
theorem ThrUnitSpec2.ok_false {l : Literals} {F : GateFree l} (U : ThrUnitSpec2 l F) (kclk coef A a : ℕ)
    (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n) (a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hc : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation)) : False := by
  have h := U.ok kclk coef A a ha n hs a' ha' Cs carriers translation hc []
    (U.nU (U.meas kclk coef A a ha n hs a' ha' Cs carriers translation))
    (U.need (U.meas kclk coef A a ha n hs a' ha' Cs carriers translation) +
      U.nU (U.meas kclk coef A a ha n hs a' ha' Cs carriers translation)) le_rfl
  have := unitOK_ctr h
  omega

/-! ## THRU3 -/

/-- **The THR unit machine at a gate, v3**: `need` polynomial in the per-call measure `meas` (which the THR load
absorbs, `meas_le`), and `UnitOK` at every capacity `cap ≥ need (meas) + j` within `nU (meas + cap)`. -/
structure ThrUnitSpec3 (l : Literals) (F : GateFree l) where
  x : ℕ
  sU : ℕ
  U : Machine (PrimAsm.CellLoop.TT x) sU
  meas : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ), ℕ
  need : ℕ → ℕ
  nU : ℕ → ℕ
  Kn : ℕ
  Dn : ℕ
  need_le : ∀ X, need X ≤ Kn * (X + 1) ^ Dn
  Ku : ℕ
  Du : ℕ
  nU_le : ∀ X, nU X ≤ Ku * (X + 1) ^ Du
  Km : ℕ
  Dm : ℕ
  meas_le : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    meas kclk coef A a ha n hs a' ha' Cs carriers translation ≤
      Km * (n + 2) ^ Dm * 2 ^ (Km * ((gate0 l F).budget kclk coef A a ha).psiOf n)
  ok : ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (n : ℕ) (hs : (callInputs l F kclk coef A a ha).StarAt n)
    (a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (translation : List ℕ),
    (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation) →
    ∀ (out : List Bool) (j cap : ℕ), need (meas kclk coef A a ha n hs a' ha' Cs carriers translation) + j ≤ cap →
    PrimThrW.Shell.UnitOK cap x U (nU (meas kclk coef A a ha n hs a' ha' Cs carriers translation + cap))
      (ThrDec.thrCallW l F kclk coef A a ha hs ha' Cs carriers translation)
      (ThrDec.thrCallU l F kclk coef A a ha hs Cs carriers)
      (SymDec.unitE (ThrDec.thrTOT l F kclk coef A a ha hs Cs carriers) (carriers.length + 1) 0
        (ThrDec.thrCallUnit l F kclk coef A a ha hs Cs carriers translation)) j out

/-- The unit's exponents (with the envelope: from `(l, fe)` only). -/
def ThrUnitSpec3.deg3 {l : Literals} {F : GateFree l} (U : ThrUnitSpec3 l F) : ℕ :=
  max (max U.Dn U.Du) (max U.Dm U.Km)

/-- The unit's coefficients (after `F`). -/
def ThrUnitSpec3.cf3 {l : Literals} {F : GateFree l} (U : ThrUnitSpec3 l F) : ℕ := U.Kn + U.Ku

/-- **The unit machines v3 in `ThrLeafJ2`'s order of choice** (`Seams.StageU`). -/
abbrev ThrUnitU3 (l : Literals) : Type :=
  FinalPass.Seams.StageU l (fun F _ _ _ _ _ => ThrUnitSpec3 l F) (fun U => U.deg3) (fun U => U.cf3)

abbrev ThrLeafOfU3 (l : Literals) : Type :=
  ThrData.ThrStage4U l → ThrUnitU3 l → WritersJoin.ThrLeafJ2 l

/-- **C6b's producer statement, v4**: the uniform decode fronts and RADIX setups (v5) on the unit cells `xF F`, the
FILTER setup and its pipe bound give the unit machines v3. -/
abbrev ThrUnitOf4 (l : Literals) : Type :=
  ∀ (W : PrimT.WalkBank.WalkBankProducer) (xF : GateFree l → ℕ), (∀ F, W.x ≤ xF F) →
    FiltSetup.FiltSetupSpec5 W → BudgetIface.FiltPipeLe2 →
    FinalPass.Seams.StageU l (fun F _ _ _ _ _ => ThrDec.ThrDecFront (xF F) l F) (fun D => decDeg D)
      (fun D => decCf D) →
    FinalPass.Seams.StageU l (fun F _ _ _ _ _ => RadSetupB5.RadSetupSpecB5 (xF F) l F) (fun R => radDeg5 R)
      (fun R => radCf5 R) →
    ThrUnitU3 l

/-- **The tail's budget**: at the capacity `need X + b` (`b` the shell's loop bound), the unit budget is polynomial
in the measure and `b`. -/
theorem ThrUnitSpec3.nU_tail {l : Literals} {F : GateFree l} (U : ThrUnitSpec3 l F) (X b : ℕ) :
    U.nU (X + (U.need X + b)) ≤ U.Ku * (X + U.need X + b + 1) ^ U.Du := by
  have h := U.nU_le (X + (U.need X + b))
  rw [show X + (U.need X + b) + 1 = X + U.need X + b + 1 by omega] at h
  exact h

end NearCubicWires.WireExponent3_5.UnionMachine.ThrUnit
