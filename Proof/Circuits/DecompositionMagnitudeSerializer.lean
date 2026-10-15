import Proof.Circuits.DecompositionMagnitudeReady
import Proof.Circuits.DecompositionSerializerCount

/-! The actual native preparation endpoint docks into the ONE shared
serializer. This positive-magnitude tail uses the parsed width and byte
stream; a later physical nonzero branch selects it or the zero output. -/
namespace NearCubicWires.RepairOrdinary.DecompositionMagnitudeSerializer
open LocalBitMultitape RecoveryRootRound RepairRepresentation SignedSortKey
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 128) : Fin 136 :=
  if i=0 then 7 else if i=2 then 3 else if i=1 then 10 else ⟨i.val+8,by omega⟩
theorem slots_injective : Function.Injective slots := by
  intro i j h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [slots] at hv
  split_ifs at hv <;> simp_all only [Fin.ext_iff,Fin.val_zero,Fin.val_one ]
  all_goals omega
theorem slots_fresh (i : Fin 128) (h0 : i≠0) (h2 : i≠2) : 10 ≤ (slots i).val := by
  unfold slots
  simp only [h0,h2,ite_false]
  split
  · decide
  · have h1 : i.val≠1 := by intro h; have : i=1 := Fin.ext h; contradiction
    have hz : i.val≠0 := fun h => h0 (Fin.ext h)
    change 10 ≤ i.val+8
    omega

noncomputable def machine := RecoveryFocus.machine slots PCPTraversal.machine
def source (pre tail : List Bool) (z : ℤ) := pre++intWord z++tail
def ready (pre tail : List Bool) (z : ℤ) :=
  DecompositionMagnitudeReady.prepared (source pre tail z) (pre.length+(intWord z).length) z
def heads (pre tail : List Bool) (z : ℤ) : Fin 136 → ℕ :=
  Fin.addCases (m:=10) (n:=126) (ready pre tail z).heads (fun _ => 0)
def tapes (pre tail : List Bool) (z : ℤ) : Fin 136 → List Bool :=
  Fin.addCases (m:=10) (n:=126) (ready pre tail z).tapes (fun _ => [])
noncomputable def entry (pre tail : List Bool) (z : ℤ) :=
  (⟨machine.start,heads pre tail z,tapes pre tail z⟩ : Configuration 136 _)

theorem fresh_heads (pre tail : List Bool) (z : ℤ) (i : Fin 136) (hi : 10 ≤ i.val) :
    heads pre tail z i=0 := by simp [heads,Fin.addCases,show ¬i.val<10 by omega]
theorem fresh_tapes (pre tail : List Bool) (z : ℤ) (i : Fin 136) (hi : 10 ≤ i.val) :
    tapes pre tail z i=[] := by simp [tapes,Fin.addCases,show ¬i.val<10 by omega]

theorem input_heads (pre tail : List Bool) (z : ℤ) (j : Fin 128) :
    heads pre tail z (slots j)=PCPTraversal.heads 0 j := by
  by_cases h0 : j=0
  · subst j; rfl
  by_cases h2 : j=2
  · subst j; rfl
  rw [fresh_heads _ _ _ _ (slots_fresh j h0 h2)]
  simp only [PCPTraversal.heads,h0,h2,ite_false]

theorem input_tapes (pre tail : List Bool) (z : ℤ) (j : Fin 128) :
    tapes pre tail z (slots j)=DecompositionSerializerCount.input
      (DecompositionBitFields.stream (binary (natBitLength z.natAbs) z.natAbs))
      (natBitLength z.natAbs) j := by
  by_cases h0 : j=0
  · subst j; rfl
  by_cases h2 : j=2
  · subst j
    change UnaryTemplate.tape (binary (natBitLength z.natAbs) z.natAbs).length=_
    rw [binary_length]
    rfl
  rw [fresh_tapes _ _ _ _ (slots_fresh j h0 h2)]
  simp only [DecompositionSerializerCount.input,h0,h2,ite_false]

theorem serialized_run (pre tail : List Bool) (z : ℤ) (hz : 0<z.natAbs) :
    ∃ r,runFrom machine (PCPTraversal.budget (3*natBitLength z.natAbs))
      (entry pre tail z)=some r ∧
      r.final.tapes 85=ZeroPadding.pad (PCPPairReusable.capacity (3*natBitLength z.natAbs))
        (frame (CanonicalBinary.encodeNat z.natAbs).bits) ∧
      r.final.tapes 86=(CanonicalBinary.encodeNat z.natAbs).bits ∧
      r.final.heads 85=0 ∧
      r.final.tapes 0=source pre tail z ∧
      r.final.heads 0=pre.length+(intWord z).length ∧
      r.final.tapes 6=[decide (z<0)] ∧ r.final.heads 6=0 ∧
      r.steps ≤ PCPTraversal.budget (3*natBitLength z.natAbs) := by
  let bits := binary (natBitLength z.natAbs) z.natAbs
  let fs := DecompositionBitFields.fields bits
  obtain ⟨base,hb,b77,b78,_,_,bh,bs⟩ := DecompositionSerializerCount.cold_run [] fs []
  have hmass : PCPSerializerMass.mass fs=3*natBitLength z.natAbs := by
    rw [DecompositionBitFields.mass,binary_length]
  have hcount : fs.length=natBitLength z.natAbs := by simp [fs,DecompositionBitFields.fields,bits,binary_length]
  have hstream : FieldList.stream fs=DecompositionBitFields.stream bits := rfl
  have hcode : PCPTraversal.code fs=CanonicalBinary.encodeNat z.natAbs :=
    DecompositionNativeMagnitude.native_code _ hz
  simp only [List.nil_append,List.append_nil,List.length_nil,hmass,hcount,hstream] at hb
  rw [hmass] at bs
  obtain ⟨r,hr,rf,rs⟩ := RecoveryFocus.run_config slots slots_injective PCPTraversal.machine
    (heads pre tail z) (tapes pre tail z) _ _ base hb
  have hi : RecoveryFocus.config slots (heads pre tail z) (tapes pre tail z)
      (DecompositionSerializerCount.entry (DecompositionBitFields.stream bits) 0 (natBitLength z.natAbs))=
      entry pre tail z := by
    exact WilliamsSourceCrop.focus_same slots (entry pre tail z)
      (DecompositionSerializerCount.entry (DecompositionBitFields.stream bits) 0 (natBitLength z.natAbs))
      (input_heads pre tail z) (input_tapes pre tail z)
  rw [hi] at hr
  have localT (j : Fin 128) : r.final.tapes (slots j)=base.final.tapes j := by
    rw [rf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have localH (j : Fin 128) : r.final.heads (slots j)=base.final.heads j := by
    rw [rf]
    simp only [RecoveryFocus.config,RecoveryFocus.pick_slot slots slots_injective]
  have absent (i : Fin 136) (hi : i.val<3 ∨ i.val=6) : RecoveryFocus.pick slots i=none := by
    have hn : ¬∃ j,slots j=i := by
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      by_cases h0 : j=0
      · have he : 7=i.val := by simpa [slots,h0] using hv
        omega
      by_cases h2 : j=2
      · have he : 3=i.val := by simpa [slots,h0,h2] using hv
        omega
      have hf := slots_fresh j h0 h2
      rw [hv] at hf
      omega
    simp [RecoveryFocus.pick,hn]
  have keep0 := absent 0 (Or.inl (by decide))
  have keep6 := absent 6 (Or.inr rfl)
  refine ⟨r,hr,?_,?_,?_,?_,?_,?_,?_,by omega⟩
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
  all_goals simp only [RecoveryFocus.config,keep0,keep6]
  all_goals rfl

end NearCubicWires.RepairOrdinary.DecompositionMagnitudeSerializer
