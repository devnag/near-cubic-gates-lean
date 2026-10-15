import Proof.SourceAssembly.SLoadWords

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SLoad.Lead
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
noncomputable section

/-- Retained framed source, mask input target, shared reset log. -/
def ports {U : Nat} (src dst log : Fin U) : Fin 3 → Fin U := ![src, dst, log]

/-- The docked unframing producer: five states. -/
noncomputable def bareStage {U : Nat} (src dst log : Fin U) : Machine U 5 :=
  RecoveryFocus.machine (ports src dst log) Streaming.machine

/-- The docked unary-width producer: eight states. -/
noncomputable def widthStage {U : Nat} (src dst log : Fin U) : Machine U 8 :=
  RecoveryFocus.machine (ports src dst log) RecoveryFieldCopy.widthMachine

theorem bare_stage_step {U : Nat} (src dst log : Fin U)
    (hsd : src ≠ dst) (hsl : src ≠ log) (hdl : dst ≠ log)
    (cap : Nat) (w : List Bool) (hcap : w.length ≤ cap)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hHs : H src = 0) (hHd : H dst = 0) (hHl : H log = 0)
    (hAs : A src = ZeroPadding.pad cap (frame w)) (hAd : A dst = [])
    (hAl : A log = List.replicate cap false) :
    Step (bareStage src dst log) (4 * w.length + 2) H A H (Function.update A dst w) := by
  have hinj := SLoad.triple_injective src dst log hsd hsl hdl
  have h := SLoad.step_update (Words.bare_step cap w hcap) 1
    (by
      intro i hi
      fin_cases i
      · rfl
      · exact absurd rfl hi
      · rfl)
    (ports src dst log) hinj H A
    (by intro i; fin_cases i <;> assumption)
    (by
      intro i
      fin_cases i
      · exact hAs
      · exact hAd
      · exact hAl)
  exact h

theorem width_stage_step {U : Nat} (src dst log : Fin U)
    (hsd : src ≠ dst) (hsl : src ≠ log) (hdl : dst ≠ log)
    (cap : Nat) (w : List Bool) (hcap : 4 * w.length + 3 ≤ cap)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hHs : H src = 0) (hHd : H dst = 0) (hHl : H log = 0)
    (hAs : A src = ZeroPadding.pad cap (frame w)) (hAd : A dst = [])
    (hAl : A log = List.replicate cap false) :
    Step (widthStage src dst log) (8 * w.length + 8) H A H
      (Function.update A dst (CompareMachine.word w.length)) := by
  have hinj := SLoad.triple_injective src dst log hsd hsl hdl
  have h := SLoad.step_update (Words.width_step cap w hcap) 1
    (by
      intro i hi
      fin_cases i
      · rfl
      · exact absurd rfl hi
      · rfl)
    (ports src dst log) hinj H A
    (by intro i; fin_cases i <;> assumption)
    (by
      intro i
      fin_cases i
      · exact hAs
      · exact hAd
      · exact hAl)
  exact h

/-- The fixed prefix program: one unframing call and three width calls,
twenty-nine states, chosen with no request in scope. -/
noncomputable def machine {U : Nat} (ret mslot : Fin 4 → Fin U) (log : Fin U) : Machine U 29 :=
  Composition.machine (bareStage (ret 0) (mslot 0) log)
    (Composition.machine (widthStage (ret 1) (mslot 1) log)
      (Composition.machine (widthStage (ret 2) (mslot 2) log)
        (widthStage (ret 3) (mslot 3) log)))

/-- Fuel for the prefix, in the four actual retained field lengths. -/
def cost (s q k m : Nat) : Nat := 4 * s + 8 * (q + k + m) + 29

/-- The four words the mask worker consumes, as a local bank. -/
def payload (support uq uK um : List Bool) : Fin 4 → List Bool :=
  ![support, CompareMachine.word uq.length, CompareMachine.word uK.length,
    CompareMachine.word um.length]

/-- Any bank agreeing with a slot map on the slots and with the ambient off
them is the installed bank. -/
theorem install_eq {t u : Nat} (slot : Fin t → Fin u) (hinj : Function.Injective slot)
    (A B : Fin u → List Bool) (f : Fin t → List Bool) (hin : ∀ j, B (slot j) = f j)
    (hout : ∀ i, (∀ j, slot j ≠ i) → B i = A i) : B = install slot A f := by
  classical
  funext i
  by_cases hp : ∃ j, slot j = i
  · obtain ⟨j, rfl⟩ := hp
    rw [hin j, install_slot slot hinj]
  · have hn : ∀ j, slot j ≠ i := fun j hj => hp ⟨j, hj⟩
    rw [hout i hn, install_other slot A f i hn]

/-- The prefix run. From an ambient source bank holding the four retained
framed fields and four blank mask input slots, the mask worker's live input
tapes are physically resident, with every mask head at zero and every other
ambient tape and head untouched. -/
theorem lead_step {U : Nat} (ret mslot : Fin 4 → Fin U) (log : Fin U)
    (hm : Function.Injective mslot)
    (hrm : ∀ i j, ret i ≠ mslot j) (hrl : ∀ i, ret i ≠ log) (hlm : ∀ j, log ≠ mslot j)
    (cap : Nat) (support uq uK um : List Bool)
    (cs : support.length ≤ cap) (cq : 4 * uq.length + 3 ≤ cap)
    (ck : 4 * uK.length + 3 ≤ cap) (cmm : 4 * um.length + 3 ≤ cap)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (hHr : ∀ i, H (ret i) = 0) (hHm : ∀ j, H (mslot j) = 0) (hHl : H log = 0)
    (hA : A (ret 0) = ZeroPadding.pad cap (frame support))
    (hAq : A (ret 1) = ZeroPadding.pad cap (frame uq))
    (hAk : A (ret 2) = ZeroPadding.pad cap (frame uK))
    (hAm : A (ret 3) = ZeroPadding.pad cap (frame um))
    (hBlank : ∀ j, A (mslot j) = []) (hAl : A log = List.replicate cap false) :
    Step (machine ret mslot log) (cost support.length uq.length uK.length um.length) H A H
      (install mslot A (payload support uq uK um)) := by
  classical
  have mne : ∀ i j : Fin 4, i ≠ j → mslot i ≠ mslot j := fun i j hij h => hij (hm h)
  have e0 := bare_stage_step (ret 0) (mslot 0) log (hrm 0 0) (hrl 0) (Ne.symm (hlm 0))
    cap support cs H A (hHr 0) (hHm 0) hHl hA (hBlank 0) hAl
  set A1 : Fin U → List Bool := Function.update A (mslot 0) support with hA1
  have e1 := width_stage_step (ret 1) (mslot 1) log (hrm 1 1) (hrl 1) (Ne.symm (hlm 1))
    cap uq cq H A1 (hHr 1) (hHm 1) hHl
    (by rw [hA1, Function.update_of_ne (hrm 1 0)]; exact hAq)
    (by rw [hA1, Function.update_of_ne (mne 1 0 (by decide))]; exact hBlank 1)
    (by rw [hA1, Function.update_of_ne (hlm 0)]; exact hAl)
  set A2 : Fin U → List Bool := Function.update A1 (mslot 1) (CompareMachine.word uq.length) with hA2
  have e2 := width_stage_step (ret 2) (mslot 2) log (hrm 2 2) (hrl 2) (Ne.symm (hlm 2))
    cap uK ck H A2 (hHr 2) (hHm 2) hHl
    (by
      rw [hA2, Function.update_of_ne (hrm 2 1), hA1, Function.update_of_ne (hrm 2 0)]
      exact hAk)
    (by
      rw [hA2, Function.update_of_ne (mne 2 1 (by decide)),
        hA1, Function.update_of_ne (mne 2 0 (by decide))]
      exact hBlank 2)
    (by rw [hA2, Function.update_of_ne (hlm 1), hA1, Function.update_of_ne (hlm 0)]; exact hAl)
  set A3 : Fin U → List Bool := Function.update A2 (mslot 2) (CompareMachine.word uK.length) with hA3
  have e3 := width_stage_step (ret 3) (mslot 3) log (hrm 3 3) (hrl 3) (Ne.symm (hlm 3))
    cap um cmm H A3 (hHr 3) (hHm 3) hHl
    (by
      rw [hA3, Function.update_of_ne (hrm 3 2), hA2, Function.update_of_ne (hrm 3 1),
        hA1, Function.update_of_ne (hrm 3 0)]
      exact hAm)
    (by
      rw [hA3, Function.update_of_ne (mne 3 2 (by decide)),
        hA2, Function.update_of_ne (mne 3 1 (by decide)),
        hA1, Function.update_of_ne (mne 3 0 (by decide))]
      exact hBlank 3)
    (by
      rw [hA3, Function.update_of_ne (hlm 2), hA2, Function.update_of_ne (hlm 1),
        hA1, Function.update_of_ne (hlm 0)]
      exact hAl)
  set A4 : Fin U → List Bool := Function.update A3 (mslot 3) (CompareMachine.word um.length) with hA4
  have joined := e0.seq (e1.seq (e2.seq e3))
  have k0 : A4 (mslot 0) = payload support uq uK um 0 := by
    rw [hA4, Function.update_of_ne (mne 0 3 (by decide)),
      hA3, Function.update_of_ne (mne 0 2 (by decide)),
      hA2, Function.update_of_ne (mne 0 1 (by decide)),
      hA1, Function.update_self]
    rfl
  have k1 : A4 (mslot 1) = payload support uq uK um 1 := by
    rw [hA4, Function.update_of_ne (mne 1 3 (by decide)),
      hA3, Function.update_of_ne (mne 1 2 (by decide)),
      hA2, Function.update_self]
    rfl
  have k2 : A4 (mslot 2) = payload support uq uK um 2 := by
    rw [hA4, Function.update_of_ne (mne 2 3 (by decide)), hA3, Function.update_self]
    rfl
  have k3 : A4 (mslot 3) = payload support uq uK um 3 := by
    rw [hA4, Function.update_self]
    rfl
  have hbank : A4 = install mslot A (payload support uq uK um) := by
    refine install_eq mslot hm A A4 (payload support uq uK um) ?_ ?_
    · intro j
      fin_cases j
      · exact k0
      · exact k1
      · exact k2
      · exact k3
    · intro i hi
      rw [hA4, Function.update_of_ne (Ne.symm (hi 3)), hA3, Function.update_of_ne (Ne.symm (hi 2)),
        hA2, Function.update_of_ne (Ne.symm (hi 1)), hA1, Function.update_of_ne (Ne.symm (hi 0))]
  rw [hbank] at joined
  refine joined.enlarge ?_
  simp only [cost]
  omega

end
end SLoad.Lead
