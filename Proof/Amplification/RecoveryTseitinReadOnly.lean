import Proof.Amplification.RecoveryTseitinNativeColdNodeRun

/-! Rule-table preservation used to retain the actual arity and node counter
through each repeated cold node consumer. -/
namespace NearCubicWires.RepairSource.RecoveryTseitinReadOnly
open LocalBitMultitape RepairOrdinary RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def NoWrite {t s : Nat} (p : Machine t s) (i : Fin t) : Prop :=
  ∀ q bits a,p.rule q bits=some a → a.write i=none
theorem composition {t a b : Nat} (p : Machine t a) (q : Machine t b) (i : Fin t)
    (hp : NoWrite p i) (hq : NoWrite q i) : NoWrite (Composition.machine p q) i := by
  intro state
  refine Fin.addCases (fun c bits x hx=>?_) (fun c bits x hx=>?_) state
  · by_cases hh : p.halted c=true
    · simp [Composition.machine,hh] at hx
      subst x
      simp [Composition.bridge]
    · cases hr : p.rule c bits with
      | none => simp [Composition.machine,hh,hr] at hx
      | some y =>
        simp [Composition.machine,hh,hr] at hx
        subst x
        exact hp c bits y hr
  · cases hr : q.rule c bits with
    | none => simp [Composition.machine,hr] at hx
    | some y =>
      simp [Composition.machine,hr] at hx
      subst x
      exact hq c bits y hr
theorem focus {t u s : Nat} (slots : Fin t→Fin u) (hinj : Function.Injective slots)
    (p : Machine t s) (i : Fin t) (hp : NoWrite p i) : NoWrite (RecoveryFocus.machine slots p) (slots i) := by
  intro q bs a ha
  obtain ⟨b,hb,he⟩:=Option.map_eq_some_iff.mp ha
  subst a
  simpa only [RecoveryFocus.action,RecoveryFocus.pick_slot slots hinj] using hp q (bs ∘ slots) b hb
theorem unselected {t u s : Nat} (slots : Fin t→Fin u) (p : Machine t s) (i : Fin u)
    (hi : ∀ j,slots j≠i) : NoWrite (RecoveryFocus.machine slots p) i := by
  intro q bs a ha
  obtain ⟨b,_hb,he⟩:=Option.map_eq_some_iff.mp ha
  subst a
  have hn : RecoveryFocus.pick slots i=none := by
    unfold RecoveryFocus.pick
    apply dif_neg
    simpa using hi
  simp [RecoveryFocus.action,hn]
theorem embedded {t s : Nat} (extra : Nat) (p : Machine t s) (i : Fin t)
    (hp : NoWrite p i) : NoWrite (TapeEmbedding.machine extra p) (i.castAdd extra) := by
  intro q bs a ha
  obtain ⟨b,hb,he⟩:=Option.map_eq_some_iff.mp ha
  subst a
  simpa only [TapeEmbedding.action,Fin.addCases_left] using hp q (fun j=>bs (j.castAdd extra)) b hb
theorem calls {t k : Nat} (sizes : Fin k→Nat)
    (programs : (j : Fin k)→Machine t (sizes j)) (first : Fin k)
    (next : (j : Fin k)→Fin (sizes j)→(Fin t→Bool)→Option (Fin k)) (i : Fin t)
    (hf : ∀ j,NoWrite (programs j) i) : NoWrite (RecoveryCalls.machine sizes programs first next) i := by
  intro q bs a ha
  cases hc : (RecoveryCalls.controlCode sizes).symm q with
  | none => simp [RecoveryCalls.machine,hc] at ha
  | some j =>
    simp only [RecoveryCalls.machine,hc] at ha
    split at ha
    · cases ha; rfl
    · obtain ⟨b,hb,he⟩:=Option.map_eq_some_iff.mp ha
      subst a
      exact hf j.1 j.2 bs b hb
theorem step_tape {t s : Nat} (p : Machine t s) (i : Fin t) (hp : NoWrite p i)
    (c d : Configuration t s) (hs : step p c=some d) : d.tapes i=c.tapes i := by
  unfold step at hs
  obtain ⟨a,ha,he⟩:=Option.map_eq_some_iff.mp hs
  subst d
  simp only [applyAction,hp c.control c.scanned a ha]
theorem prefix_tape {t s space steps : Nat} (p : Machine t s) (i : Fin t) (hp : NoWrite p i)
    {c d : Configuration t s} (h : Prefix p space steps c d) : d.tapes i=c.tapes i := by
  induction h with
  | refl => rfl
  | step _ _ hs _ ih => exact ih.trans (step_tape p i hp _ _ hs)
theorem run_tape {t s : Nat} (p : Machine t s) (i : Fin t) (hp : NoWrite p i)
    (fuel : Nat) (c : Configuration t s) (r : ExecutionReceipt t s)
    (hr : runFrom p fuel c=some r) : r.final.tapes i=c.tapes i := by
  exact prefix_tape p i hp (prefix_of_run p fuel c r hr).1
theorem rewind {t s : Nat} (p : Machine t s) (i : Fin t) (hp : NoWrite p i) :
    NoWrite (Rewind.machine p) (i.castAdd 1) := by
  intro state
  refine Fin.addCases (fun q bits a ha=>?_) (fun q bits a ha=>?_) state
  · by_cases hh : p.halted q=true
    · simp [Rewind.machine,hh] at ha
      subst a
      simp [Rewind.bridgeAction]
    · cases hr : p.rule q (fun j=>bits (j.castAdd 1)) with
      | none => simp [Rewind.machine,hh,hr] at ha
      | some b =>
        simp [Rewind.machine,hh,hr] at ha
        subst a
        simpa only [Rewind.recordAction,Fin.addCases_left] using hp q (fun j=>bits (j.castAdd 1)) b hr
  · simp only [Rewind.machine,Fin.addCases_right] at ha
    split at ha
    · split at ha
      · cases ha; simp [Rewind.rewindAction]
      · cases ha; simp [Rewind.finishAction]
    · contradiction

end NearCubicWires.RepairSource.RecoveryTseitinReadOnly
