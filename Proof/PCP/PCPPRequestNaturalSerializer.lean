import Proof.PCP.PCPPRequestNaturalReady

/-! The native natural's actual width and bit fields feed the existing
balanced serializer, yielding the literal positive encodeNat code. -/
namespace NearCubicWires.RepairOrdinary.PCPPRequestNaturalSerializer
open LocalBitMultitape RepairRepresentation SignedSortKey
open RepairSource.ProjectionNormalization DecompositionMagnitudeSerializer
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def source (pre tail : List Bool) (n : ℕ) := pre++natWord n++tail
def ready (pre tail : List Bool) (n : ℕ) :=
  PCPPRequestNaturalReady.prepared (source pre tail n) (pre.length+(natWord n).length) n
def heads (pre tail : List Bool) (n : ℕ) : Fin 136 → ℕ :=
  Fin.addCases (m:=10) (n:=126) (ready pre tail n).heads (fun _ => 0)
def tapes (pre tail : List Bool) (n : ℕ) : Fin 136 → List Bool :=
  Fin.addCases (m:=10) (n:=126) (ready pre tail n).tapes (fun _ => [])
noncomputable def entry (pre tail : List Bool) (n : ℕ) :=
  (⟨DecompositionMagnitudeSerializer.machine.start,heads pre tail n,tapes pre tail n⟩ : Configuration 136 _)

theorem fresh_heads (pre tail : List Bool) (n : ℕ) (i : Fin 136) (hi : 10 ≤ i.val) :
    heads pre tail n i=0 := by simp [heads,Fin.addCases,show ¬i.val<10 by omega]
theorem fresh_tapes (pre tail : List Bool) (n : ℕ) (i : Fin 136) (hi : 10 ≤ i.val) :
    tapes pre tail n i=[] := by simp [tapes,Fin.addCases,show ¬i.val<10 by omega]

theorem input_heads (pre tail : List Bool) (n : ℕ) (j : Fin 128) :
    heads pre tail n (slots j)=PCPTraversal.heads 0 j := by
  by_cases h0 : j=0
  · subst j; rfl
  by_cases h2 : j=2
  · subst j; rfl
  rw [fresh_heads _ _ _ _ (slots_fresh j h0 h2)]
  simp only [PCPTraversal.heads,h0,h2,ite_false]

theorem input_tapes (pre tail : List Bool) (n : ℕ) (j : Fin 128) :
    tapes pre tail n (slots j)=DecompositionSerializerCount.input
      (DecompositionBitFields.stream (binary (natBitLength n) n)) (natBitLength n) j := by
  by_cases h0 : j=0
  · subst j; rfl
  by_cases h2 : j=2
  · subst j
    change UnaryTemplate.tape (binary (natBitLength n) n).length=_
    rw [binary_length]
    rfl
  rw [fresh_tapes _ _ _ _ (slots_fresh j h0 h2)]
  simp only [DecompositionSerializerCount.input,h0,h2,ite_false]

theorem serialized_run (pre tail : List Bool) (n : ℕ) (hn : 0<n) :
    ∃ r,runFrom DecompositionMagnitudeSerializer.machine (PCPTraversal.budget (3*natBitLength n))
      (entry pre tail n)=some r ∧
      r.final.tapes 85=ZeroPadding.pad (PCPPairReusable.capacity (3*natBitLength n))
        (frame (CanonicalBinary.encodeNat n).bits) ∧
      r.final.tapes 86=(CanonicalBinary.encodeNat n).bits ∧ r.final.heads 85=0 ∧
      r.final.tapes 0=source pre tail n ∧ r.final.heads 0=pre.length+(natWord n).length ∧
      r.steps ≤ PCPTraversal.budget (3*natBitLength n) := by
  let bits := binary (natBitLength n) n
  let fs := DecompositionBitFields.fields bits
  obtain ⟨base,hb,b77,b78,_,_,bh,bs⟩ := DecompositionSerializerCount.cold_run [] fs []
  have hmass : PCPSerializerMass.mass fs=3*natBitLength n := by
    rw [DecompositionBitFields.mass,binary_length]
  have hcount : fs.length=natBitLength n := by simp [fs,DecompositionBitFields.fields,bits,binary_length]
  have hstream : FieldList.stream fs=DecompositionBitFields.stream bits := rfl
  have hcode : PCPTraversal.code fs=CanonicalBinary.encodeNat n := DecompositionNativeMagnitude.native_code _ hn
  simp only [List.nil_append,List.append_nil,List.length_nil,hmass,hcount,hstream] at hb
  rw [hmass] at bs
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config slots slots_injective PCPTraversal.machine
    (heads pre tail n) (tapes pre tail n) _ _ base hb
  have hi : RecoveryFocus.config slots (heads pre tail n) (tapes pre tail n)
      (DecompositionSerializerCount.entry (DecompositionBitFields.stream bits) 0 (natBitLength n))=
      entry pre tail n := by
    exact WilliamsSourceCrop.focus_same slots (entry pre tail n) _
      (input_heads pre tail n) (input_tapes pre tail n)
  rw [hi] at hr
  have localT (j : Fin 128) : r.final.tapes (slots j)=base.final.tapes j := by
    rw [rf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have localH (j : Fin 128) : r.final.heads (slots j)=base.final.heads j := by
    rw [rf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have keep0 : RecoveryFocus.pick slots (0 : Fin 136)=none := by
    have hn : ¬∃ j,slots j=(0 : Fin 136) := by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      simp only [slots] at hv
      split_ifs at hv <;> dsimp at hv <;> omega
    simp [RecoveryFocus.pick,hn]
  refine ⟨r,hr,?_,?_,?_,?_,?_,by omega⟩
  · have h := localT 77
    change r.final.tapes 85=base.final.tapes 77 at h
    rw [b77,hmass,hcode] at h
    exact h
  · have h := localT 78
    change r.final.tapes 86=base.final.tapes 78 at h
    rw [b78,hcode] at h
    exact h
  · have h := localH 77
    rw [bh] at h
    exact h
  all_goals rw [rf]
  all_goals simp only [RecoveryFocus.config,keep0]
  all_goals rfl

end NearCubicWires.RepairOrdinary.PCPPRequestNaturalSerializer
