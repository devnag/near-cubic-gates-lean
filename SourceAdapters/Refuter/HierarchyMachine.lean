import SourceAdapters.Refuter.CappedDock
import Proof.Gates.Succinct.VerifierRun

/-!
# The hierarchy verifier `𝒟` (input 7, the paper Step 1 and proof of `cor:framed-refuter`)

proof of `lem:multitape-refuter` (Step 1): "First `𝒟` computes `T(N)` and prepares its clock … The clock rejects every branch
whose steps after clock preparation exceed `(c_0+2)(T(N)+1)` … Hence every branch halts within
`O(T(N)+1)` steps on every input": "A deterministic verifier reads those choices from a framed
witness … Taking a sufficiently large fixed integer `c` gives both the step bound and the witness length
`c(T(N)+1)`".

`hverifier` = (tapes 1, 2 swapped) `prep ; dock(capped(bodyFull))`: the clock preparation (`ClockPrep.lean`),
then the capped machine of the join `CappedMachineRun` running `bodyFull` on the input, the witness and `63`
blank streams with the clock stream `1^{1024(T(N)+1)}`. It accepts in the control of `bodyFull`'s accepting
verdict. `hverifier_run`: on every input and witness it halts within `prepBound + clockLen + 2` steps, and it
accepts iff `bodyFull` reaches its accepting verdict within the clock (`BodyAcc`).
-/

namespace NearCubicGates.Adapters.Refuter.Clock

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicGates.Close.WordPrograms
open NearCubicGates.Adapters.Refuter NearCubicGates.Adapters.Refuter.Mach
open NearCubicGates.Close.CheckedPCPP (coldBank coldBank_s coldBank_c coldBank_r)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_val cTape_val rTape_val sTape_inj)
open NearCubicGates.Close.Succinct (swap12 swap12_swap12 swap12_inj pick_swap12)
open NearCubicGates.Adapters.Joins

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! ## The body's cold tapes -/

theorem coldBody_val (x w : List Bool) (j : Fin (NS + 2 + NR)) :
    coldBank (coldSt x w) j = if j.val = 0 then RepairOrdinary.frame x else if j.val = 2 then RepairOrdinary.frame w
      else [] := by
  rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
  · rw [coldBank_s, sTape_val]
    by_cases h0 : i.val = 0
    · have : i = sIN := Fin.ext h0
      subst this; simp [coldSt]
    · by_cases h1 : i.val = 1
      · have : i = sWIT := Fin.ext h1
        subst this; simp [coldSt]
      · have a1 : i ≠ sIN := fun e => h0 (by rw [e]; rfl)
        have a2 : i ≠ sWIT := fun e => h1 (by rw [e]; rfl)
        simp [coldSt, a1, a2, h0]; omega
  · rw [coldBank_c, cTape_val]; simp
  · rw [coldBank_r, rTape_val]; simp only [NS]; simp; omega

/-- The outer cold tapes. -/
theorem coldOuter_val (p : Program) (x w : List Bool) (j : Fin (ONS p.tapeCount + 2 + ONR)) :
    coldBank (ocold p x w) j = if j.val = 0 then RepairOrdinary.frame x else if j.val = 2 then RepairOrdinary.frame w
      else [] := by
  rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, rfl⟩
  · rw [coldBank_s, sTape_val]
    by_cases h0 : i.val = 0
    · have : i = Sx p.tapeCount := Fin.ext h0
      subst this; simp
    · by_cases h1 : i.val = 1
      · have : i = Sw p.tapeCount := Fin.ext h1
        subst this; simp
      · rw [ocold_other p x w i (by omega)]; simp [h0]; omega
  · rw [coldBank_c, cTape_val]; simp
  · rw [coldBank_r, rTape_val]; simp only [ONS]; simp; omega

/-! ## Where the capped body's tapes live -/

section Map
variable (tP : ℕ)

/-- The outer stream of each tape of the capped body: input, cell, witness, …, clock. -/
def smap (j : Fin (NS + 2 + NR + 1)) : Fin (ONS tP + 1) :=
  if j.val = 0 then Sx tP else if j.val = 2 then Sw tP else if h65 : j.val = 65 then Scl tP
  else Sfr tP ⟨if j.val = 1 then 0 else j.val - 2, by have := j.isLt; simp only [NS, NR] at this; split <;> omega⟩

theorem smap_val (j : Fin (NS + 2 + NR + 1)) :
    (smap tP j).val = if j.val = 0 then 0 else if j.val = 2 then 1 else if j.val = 65 then 2
      else 4 + tP + (if j.val = 1 then 0 else j.val - 2) := by
  unfold smap; split_ifs <;> simp

theorem smap_inj : Function.Injective (smap tP) := by
  intro a b h
  have := congrArg Fin.val h
  rw [smap_val, smap_val] at this
  have ha := a.isLt; have hb := b.isLt
  simp only [NS, NR] at ha hb
  apply Fin.ext
  split_ifs at this <;> omega

def bmap (j : Fin (NS + 2 + NR + 1)) : Fin (ONS tP + 2 + ONR) := sTape (smap tP j)

theorem bmap_inj : Function.Injective (bmap tP) := fun _ _ h => smap_inj tP (sTape_inj h)

end Map

/-! ## The machine -/

section Machine
variable (hcr : CappedMachineRun) (p : Program)

/-- The capped body (the join's transform of `bodyFull`). -/
noncomputable def bnd : Machine (NS + 2 + NR + 1) (body.size + 3 + 1) :=
  Classical.choose (hcr (NS + 2 + NR) (body.size + 3) bodyFull)

theorem bnd_spec (cap : ℕ) (input : Fin (NS + 2 + NR) → List Bool) :
    ∃ receipt, run (bnd hcr) (cap + 1) (cappedInputTapes cap input) = some receipt ∧
      CappedResultAgreement (run bodyFull cap input) receipt :=
  (Classical.choose_spec (hcr (NS + 2 + NR) (body.size + 3) bodyFull)).2 cap input

/-- The clock preparation, then the docked capped body. -/
noncomputable def innerM : Machine (ONS p.tapeCount + 2 + ONR) ((prep p).size + (body.size + 3 + 1)) :=
  Composition.machine (prep p).compile (RecoveryFocus.machine (bmap p.tapeCount) (bnd hcr))

theorem three_le (tP : ℕ) : 3 ≤ ONS tP + 2 + ONR := by unfold ONS; omega

/-- **The hierarchy verifier `𝒟`.** -/
noncomputable def hverifier : OrdinaryVerifier where
  tapeCount := ONS p.tapeCount + 2 + ONR
  stateCount := (prep p).size + (body.size + 3 + 1)
  twoTapes := by have := three_le p.tapeCount; omega
  machine := RecoveryFocus.machine (swap12 _ (three_le p.tapeCount)) (innerM hcr p)
  accepting := fun q => decide (q.val = (prep p).size + body.size + 1)

/-- The body reached its accepting verdict within the clock. -/
def BodyAcc (cap : ℕ) (x w : List Bool) : Prop :=
  ∃ rB, run bodyFull cap (coldBank (coldSt x w)) = some rB ∧ rB.final.control.val = body.size + 1

theorem bank_swap' (x w : List Bool) (i : Fin (ONS p.tapeCount + 2 + ONR)) :
    coldBank (ocold p x w) (swap12 _ (three_le p.tapeCount) i) = (hverifier hcr p).inputTapes x w i := by
  rw [coldOuter_val]
  show _ = if i.val = 0 then RepairOrdinary.frame x else if i.val = 1 then RepairOrdinary.frame w else []
  have hs : (swap12 _ (three_le p.tapeCount) i).val = if i.val = 1 then 2 else if i.val = 2 then 1 else i.val := by
    unfold swap12; split_ifs <;> simp_all
  rw [hs]
  by_cases h1 : i.val = 1
  · simp [h1]
  · by_cases h2 : i.val = 2
    · simp [h2]
    · simp [h1, h2]

end Machine

/-! ## The run of `𝒟` -/

theorem smap_cases (tP : ℕ) (j : Fin (NS + 2 + NR + 1)) :
    (smap tP j = Sx tP ∧ j.val = 0) ∨ (smap tP j = Sw tP ∧ j.val = 2) ∨ (smap tP j = Scl tP ∧ j.val = 65) ∨
      (∃ k, smap tP j = Sfr tP k ∧ j.val ≠ 0 ∧ j.val ≠ 2 ∧ j.val ≠ 65) := by
  unfold smap
  by_cases h0 : j.val = 0
  · left; simp [h0]
  · by_cases h2 : j.val = 2
    · right; left; simp [h2]
    · by_cases h65 : j.val = 65
      · right; right; left; simp [h65]
      · right; right; right; simp only [h0, h2, h65, if_false, dite_false]; exact ⟨_, rfl, h0, h2, h65⟩

set_option maxHeartbeats 400000 in
/-- **Every run of `𝒟` halts within `prepBound + clockLen + 2` steps** (proof of `lem:multitape-refuter`), and it accepts iff the
body reaches its accepting verdict within the clock. -/
theorem hverifier_run (hcr : CappedMachineRun) (T : ℕ → ℕ) (C : ℕ)
    (wf : RepairOrdinary.WordFunction ℕ (fun n => List.replicate n true) (fun n => (T n).bits) (fun n => C * (T n + 1)))
    (x w : List Bool) :
    ∃ rH, run (hverifier hcr wf.program).machine
        (prepBound C x.length (T x.length) + 1 + (clockLen (T x.length) + 1))
        ((hverifier hcr wf.program).inputTapes x w) = some rH ∧
      ((hverifier hcr wf.program).accepting rH.final.control = true ↔ BodyAcc (clockLen (T x.length)) x w) := by
  -- the clock preparation
  obtain ⟨τ, c, eP, hX, hXh, hW, hWh, hC, hCh, hF, hc⟩ :=
    prep_spec wf.program (2 * x.length + 2 * C * (T x.length + 1) + 4096 * (T x.length + 1) + 8) T C wf rfl x w le_rfl
  obtain ⟨r1, hr1, hh1, ht1, _, _⟩ := cold_run' eP (fun _ => rfl) (fun _ => rfl) rfl
  -- the capped body
  obtain ⟨rb, hrb, hag⟩ := bnd_spec hcr (clockLen (T x.length)) (coldBank (coldSt x w))
  have hcfg : initialConfiguration (bnd hcr) (cappedInputTapes (clockLen (T x.length)) (coldBank (coldSt x w))) =
      (⟨(bnd hcr).start, fun j => r1.final.heads (bmap wf.program.tapeCount j),
        fun j => r1.final.tapes (bmap wf.program.tapeCount j)⟩ :
        Configuration (NS + 2 + NR + 1) (body.size + 3 + 1)) := by
    apply configuration_ext
    · rfl
    · funext j
      simp only [initialConfiguration, bmap, hh1, NearCubicWires.WireExponent3_5.FinalPass.Tm.wenc_H_s]
      rcases smap_cases wf.program.tapeCount j with ⟨e, _⟩ | ⟨e, _⟩ | ⟨e, _⟩ | ⟨k, e, _⟩ <;> rw [e]
      · rw [hXh]
      · rw [hWh]
      · rw [hCh]
      · rw [(hF k).2]
    · funext j
      simp only [initialConfiguration, bmap, ht1, cappedInputTapes]
      have hj := j.isLt
      simp only [NS, NR] at hj
      rcases smap_cases wf.program.tapeCount j with ⟨e, h0⟩ | ⟨e, h2⟩ | ⟨e, h65⟩ | ⟨k, e, h0, h2, h65⟩ <;> rw [e]
      · rw [hX, dif_pos (by simp only [NS, NR]; omega), coldBody_val]; simp [h0]
      · rw [hW, dif_pos (by simp only [NS, NR]; omega), coldBody_val]; simp [h2]
      · rw [hC, dif_neg (by simp only [NS, NR]; omega)]
      · rw [(hF k).1, dif_pos (by simp only [NS, NR]; omega), coldBody_val]; simp [h0, h2]
  have hrb' : runFrom (bnd hcr) (clockLen (T x.length) + 1)
      (⟨(bnd hcr).start, fun j => r1.final.heads (bmap wf.program.tapeCount j),
        fun j => r1.final.tapes (bmap wf.program.tapeCount j)⟩ :
        Configuration (NS + 2 + NR + 1) (body.size + 3 + 1)) = some rb := by
    rw [← hcfg]; exact hrb
  obtain ⟨res, hres, hresf, _⟩ := RecoveryFocus.run_config (bmap wf.program.tapeCount) (bmap_inj wf.program.tapeCount)
    (bnd hcr) r1.final.heads r1.final.tapes (clockLen (T x.length) + 1) _ rb hrb'
  rw [config_self] at hres
  have hrestart : Composition.restart r1.final (RecoveryFocus.machine (bmap wf.program.tapeCount) (bnd hcr)).start =
      (⟨(bnd hcr).start, r1.final.heads, r1.final.tapes⟩ :
        Configuration (ONS wf.program.tapeCount + 2 + ONR) (body.size + 3 + 1)) := rfl
  rw [← hrestart] at hres
  have hjoin := Composition.run_join (prep wf.program).compile (RecoveryFocus.machine (bmap wf.program.tapeCount) (bnd hcr))
    c (clockLen (T x.length) + 1) _ r1 res hr1 hres
  replace hjoin : runFrom (innerM hcr wf.program) (c + 1 + (clockLen (T x.length) + 1))
      (initialConfiguration (innerM hcr wf.program) (coldBank (ocold wf.program x w))) =
        some (Composition.joinedReceipt r1 res) := hjoin
  -- the renamed tapes
  have hinit : initialConfiguration (hverifier hcr wf.program).machine ((hverifier hcr wf.program).inputTapes x w) =
      RecoveryFocus.config (swap12 _ (three_le wf.program.tapeCount)) (fun _ => 0)
        ((hverifier hcr wf.program).inputTapes x w)
        (initialConfiguration (innerM hcr wf.program) (coldBank (ocold wf.program x w))) := by
    apply configuration_ext
    · rfl
    · funext i; simp [RecoveryFocus.config, pick_swap12, initialConfiguration]
    · funext i; simp only [RecoveryFocus.config, pick_swap12, initialConfiguration]; rw [bank_swap']
  obtain ⟨rV, hrV, hrVf, _⟩ := RecoveryFocus.run_config (swap12 _ (three_le wf.program.tapeCount))
    (swap12_inj _ _) (innerM hcr wf.program) (fun _ => 0) ((hverifier hcr wf.program).inputTapes x w) _ _ _ hjoin
  have hrun : run (hverifier hcr wf.program).machine (c + 1 + (clockLen (T x.length) + 1))
      ((hverifier hcr wf.program).inputTapes x w) = some rV := by
    show runFrom _ _ (initialConfiguration (hverifier hcr wf.program).machine
      ((hverifier hcr wf.program).inputTapes x w)) = some rV
    rw [hinit]; exact hrV
  refine ⟨rV, ?_, ?_⟩
  · have := runFrom_mono _ _ _ rV hrun (prepBound C x.length (T x.length) - c)
    rw [show c + 1 + (clockLen (T x.length) + 1) + (prepBound C x.length (T x.length) - c) =
      prepBound C x.length (T x.length) + 1 + (clockLen (T x.length) + 1) by omega] at this
    exact this
  · have hctl : rV.final.control.val = (prep wf.program).size + rb.final.control.val := by
      rw [hrVf]
      simp [RecoveryFocus.config, Composition.joinedReceipt, Composition.rightConfig, hresf]
    show decide (rV.final.control.val = (prep wf.program).size + body.size + 1) = true ↔ _
    rw [hctl]
    unfold BodyAcc
    unfold CappedResultAgreement at hag
    cases hB : run bodyFull (clockLen (T x.length)) (coldBank (coldSt x w)) with
    | none =>
      rw [hB] at hag
      simp only at hag
      rw [hag]
      constructor
      · intro h; simp at h; omega
      · rintro ⟨rB, h1, _⟩; cases h1
    | some rB =>
      rw [hB] at hag
      obtain ⟨hcB, _⟩ := hag
      rw [hcB]
      constructor
      · intro h
        refine ⟨rB, rfl, ?_⟩
        simp at h; omega
      · rintro ⟨rB', h1, h2⟩
        cases h1
        simp; omega

end NearCubicGates.Adapters.Refuter.Clock
