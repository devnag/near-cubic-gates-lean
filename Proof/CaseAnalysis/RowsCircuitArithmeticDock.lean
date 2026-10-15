import Proof.CaseAnalysis.RowsCircuitResourceCopies
import Proof.CaseAnalysis.RowsCircuitCaps

/-! The actual measured counters enter the existing small native arithmetic
at the full circuit ports. Policy caps and the native prefix are untouched. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitArithmeticDock
open LocalBitMultitape RecoveryRootRound CloseoutRowsGatePairHeads
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (n : ℕ) (hn : n ≤ 16) (i : Fin n) : Fin 1703:=⟨639+i.val,by omega⟩
theorem slots_injective (n : ℕ) (hn : n ≤ 16) : Function.Injective (slots n hn):=by
  intro i j h;apply Fin.ext
  have hv:=congrArg Fin.val h
  simp only [slots] at hv;omega
noncomputable def stage (threshold : Bool) : Σ s,Machine 1703 s:=
  if threshold then ⟨_,RecoveryFocus.machine (slots 16 (by decide)) CloseoutRowsCircuitThresholdDescription.machine⟩
  else ⟨_,RecoveryFocus.machine (slots 12 (by decide)) CloseoutRowsCircuitSymmetricDescription.machine⟩
def amount (threshold : Bool) (D n : ℕ):=if threshold then (D-(n+1))/2 else (D+n+2)/2
def budget (threshold : Bool) (D n : ℕ):=
  if threshold then CloseoutRowsCircuitThresholdDescription.budget D n
  else CloseoutRowsCircuitSymmetricDescription.budget D n

theorem arithmetic_run (threshold : Bool) (C D n : ℕ) (H : Fin 1703 → ℕ)
    (A : Fin 1703 → List Bool) (hc : 32*(D+n+3) ≤ C)
    (hn : threshold=true → n+1 ≤ D)
    (hh : ∀ i,639 ≤ i.val ∧ i.val ≤ 654 → H i=0)
    (hd : A 639=ZeroPadding.pad C (List.replicate D true))
    (hcoun : A 640=ZeroPadding.pad C (List.replicate n true))
    (fresh : ∀ i,641 ≤ i.val ∧ i.val ≤ 654 → A i=List.replicate C false) : ∃ out,
    ReadyAt (stage threshold).2 (budget threshold D n) H A out ∧
      out (if threshold then 653 else 649)=ZeroPadding.pad C (List.replicate (amount threshold D n) true) ∧
      (∀ i,(A i).length ≤ C → (out i).length ≤ C) ∧
      (∀ i,i.val<639 ∨ 655 ≤ i.val → out i=A i):=by
  cases threshold
  · obtain ⟨bank,run,_b0,_b1,value,bounds⟩:=CloseoutRowsCircuitDescriptionMeaning.symmetric_padded C D n (by constructor <;> omega) (by omega)
    have heads:∀ i,H (slots 12 (by decide) i)=0:=by
      intro i;apply hh;change 639 ≤ 639+i.val ∧ 639+i.val ≤ 654;omega
    have tapes:∀ i,A (slots 12 (by decide) i)=
        ZeroPadding.pad C (CloseoutRowsCircuitSymmetricDescription.input D n i):=by
      intro i
      by_cases h0:i=0
      · subst i;exact hd
      by_cases h1:i=1
      · subst i;exact hcoun
      rw [CloseoutRowsCircuitSymmetricDescription.input,if_neg h0,if_neg h1]
      have hi:=i.isLt
      have pos0:i.val≠0:=by exact fun h=>h0 (Fin.ext h)
      have pos1:i.val≠1:=by exact fun h=>h1 (Fin.ext h)
      rw [fresh _ (by change 641 ≤ 639+i.val ∧ 639+i.val ≤ 654;omega)]
      simp [ZeroPadding.pad]
    obtain ⟨r,hr,rh,rt,rs⟩:=run.focus_at (slots 12 (by decide)) (slots_injective _ _) H A tapes heads
    let out:=install (slots 12 (by decide)) A bank
    refine ⟨out,⟨r,hr,rt,rh,rs⟩,?_,?_,?_⟩
    · change out (slots 12 (by decide) 10)=_
      rw [show out=install _ A bank by rfl,install_slot _ (slots_injective _ _)]
      exact value
    · intro i ha
      by_cases hit:∃ j,slots 12 (by decide) j=i
      · obtain ⟨j,rfl⟩:=hit
        rw [show out=install _ A bank by rfl,install_slot _ (slots_injective _ _)]
        exact bounds j
      · rw [show out=install _ A bank by rfl,install_other _ _ _ _ (by simpa only [not_exists] using hit)]
        exact ha
    · intro i hi
      apply install_other
      intro j h
      have hv:=congrArg Fin.val h
      change 639+j.val=i.val at hv
      omega
  · obtain ⟨bank,run,_b0,_b1,value,bounds⟩:=CloseoutRowsCircuitDescriptionMeaning.threshold_padded C D n (hn rfl) (by constructor <;> omega) (by omega)
    have heads:∀ i,H (slots 16 (by decide) i)=0:=by
      intro i;apply hh;change 639 ≤ 639+i.val ∧ 639+i.val ≤ 654;omega
    have tapes:∀ i,A (slots 16 (by decide) i)=
        ZeroPadding.pad C (CloseoutRowsCircuitThresholdDescription.input D n i):=by
      intro i
      by_cases h0:i=0
      · subst i;exact hd
      by_cases h1:i=1
      · subst i;exact hcoun
      rw [CloseoutRowsCircuitThresholdDescription.input,if_neg h0,if_neg h1]
      have hi:=i.isLt
      have pos0:i.val≠0:=by exact fun h=>h0 (Fin.ext h)
      have pos1:i.val≠1:=by exact fun h=>h1 (Fin.ext h)
      rw [fresh _ (by change 641 ≤ 639+i.val ∧ 639+i.val ≤ 654;omega)]
      simp [ZeroPadding.pad]
    obtain ⟨r,hr,rh,rt,rs⟩:=run.focus_at (slots 16 (by decide)) (slots_injective _ _) H A tapes heads
    let out:=install (slots 16 (by decide)) A bank
    refine ⟨out,⟨r,hr,rt,rh,rs⟩,?_,?_,?_⟩
    · change out (slots 16 (by decide) 14)=_
      rw [show out=install _ A bank by rfl,install_slot _ (slots_injective _ _)]
      exact value
    · intro i ha
      by_cases hit:∃ j,slots 16 (by decide) j=i
      · obtain ⟨j,rfl⟩:=hit
        rw [show out=install _ A bank by rfl,install_slot _ (slots_injective _ _)]
        exact bounds j
      · rw [show out=install _ A bank by rfl,install_other _ _ _ _ (by simpa only [not_exists] using hit)]
        exact ha
    · intro i hi
      apply install_other
      intro j h
      have hv:=congrArg Fin.val h
      change 639+j.val=i.val at hv
      omega

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitArithmeticDock
