import Proof.PCP.PCPPNativeProjectionLookup
import Proof.Circuits.DecompositionSerializerCount

/-! The lookup consumes the exact sentinel emitted by the native node
reader, including its physically present final false cell. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeProjectionLookup
open LocalBitMultitape RadixSemantics RepairSource.ProjectionNormalization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def templateCaps (count : ℕ) (i : Fin 28) : ℕ := if i=2 then count+2 else 0
def templateData (source : List Bool) (count : ℕ) (i : Fin 28) : List Bool :=
  if i=0 then source else if i=2 then UnaryTemplate.tape count else []
noncomputable def templateEntry (source : List Bool) (pos count : ℕ) :=
  (⟨machine.start,heads pos,templateData source count⟩ : Configuration 28 _)

theorem padded_entry (source : List Bool) (pos count : ℕ) :
    ZeroPadding.config (templateCaps count) (entry source pos count)=templateEntry source pos count := by
  apply configuration_ext
  · rfl
  · rfl
  · funext i
    by_cases hi : i=2
    · subst i
      exact DecompositionSerializerCount.padded_count count
    · change ZeroPadding.pad (templateCaps count i) (data source count i)=templateData source count i
      simp only [templateCaps,data,templateData,hi,ite_false,ZeroPadding.pad_zero]

theorem template_run (pre : List Bool) (skipped : List (List Bool)) (bits suffix : List Bool) :
    ∃ r,runFrom machine (budget skipped bits)
      (templateEntry (pre++FieldList.stream skipped++frame bits++suffix) pre.length skipped.length)=some r ∧
      r.steps≤budget skipped bits ∧
      r.final.tapes 0=pre++FieldList.stream skipped++frame bits++suffix ∧
      r.final.heads 0=pre.length+(FieldList.stream skipped).length+2*bits.length+1 ∧
      r.final.tapes 2=UnaryTemplate.tape skipped.length ∧ r.final.heads 2=1 ∧
      r.final.tapes 22=CompareMachine.word (Nat.unpair (value bits)).1 ∧
      r.final.tapes 26=CompareMachine.word (Nat.unpair (value bits)).2 ∧
      r.final.heads 22=1 ∧ r.final.heads 26=1 := by
  obtain ⟨base,hb,bs,b0,bh0,b2,bh2,b22,b26,bh22,bh26⟩ := lookup_run pre skipped bits suffix
  obtain ⟨r,hr,rf,rs,_⟩ := ZeroPadding.run_config machine (templateCaps skipped.length) _ _ base hb
  rw [padded_entry] at hr
  refine ⟨r,hr,by omega,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 0)=_
    rw [ZeroPadding.pad_zero,b0]
  · rw [rf]; exact bh0
  · rw [rf]
    change ZeroPadding.pad (skipped.length+2) (base.final.tapes 2)=_
    rw [b2,DecompositionSerializerCount.padded_count]
  · rw [rf]; exact bh2
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 22)=_
    rw [ZeroPadding.pad_zero,b22]
  · rw [rf]
    change ZeroPadding.pad 0 (base.final.tapes 26)=_
    rw [ZeroPadding.pad_zero,b26]
  · rw [rf]; exact bh22
  · rw [rf]; exact bh26

end NearCubicWires.RepairOrdinary.PCPPNativeProjectionLookup
