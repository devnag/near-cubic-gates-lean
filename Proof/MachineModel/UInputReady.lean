import Proof.MachineModel.UInputEntry

/-! Total parsing/scalar semantics at U's literal external-input boundary.
The success implication supplies every scalar guard before decoder expansion
or witness-dependent initialization. -/
namespace NearCubicWires.RepairOrdinary.UInputEntry
open LocalBitMultitape RecoveryRootRound RadixSemantics ClockDyadicLedger
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem source_unique (code x bound padding code' x' bound' padding' : List Bool)
    (h : VerifierInputFields.source code x bound padding=
      VerifierInputFields.source code' x' bound' padding') :
    code=code' ∧ x=x' ∧ bound=bound' ∧ padding=padding' := by
  have hp := congrArg UInputSyntax.peel h
  simp only [VerifierInputFields.source,UInputSyntax.peel_frame,Option.some.injEq,Prod.mk.injEq] at hp
  have hx := congrArg UInputSyntax.peel hp.2
  simp only [UInputSyntax.peel_frame,Option.some.injEq,Prod.mk.injEq] at hx
  have hb := congrArg UInputSyntax.peel hx.2
  simp only [UInputSyntax.peel_frame,Option.some.injEq,Prod.mk.injEq] at hb
  exact ⟨hp.1,hx.1,hb⟩

def Valid (raw : List Bool) : Prop := ∃ code x bound padding,
  raw=VerifierInputFields.source code x bound padding ∧ UInputScalars.Guards raw x bound

theorem valid_iff_guards (code x bound padding : List Bool) :
    Valid (VerifierInputFields.source code x bound padding) ↔
      UInputScalars.Guards (VerifierInputFields.source code x bound padding) x bound := by
  constructor
  · rintro ⟨code',x',bound',padding',he,hg⟩
    obtain ⟨rfl,rfl,rfl,rfl⟩ := source_unique _ _ _ _ _ _ _ _ he
    exact hg
  · exact fun h => ⟨code,x,bound,padding,rfl,h⟩

theorem endpoint_fields (raw code x bound : List Bool) (g carry reset degree cap scratch : ℕ) :
    let out := endpoint raw code x bound g carry reset degree cap scratch
    out 0=frame raw ∧ out 5=frame code ∧ out 7=frame x ∧ out 9=frame bound ∧
    out 12=frame (ClockBinary.word raw.length) ∧
    out 19=List.replicate (width raw.length) true ∧
    out 20=List.replicate (2*width raw.length) true ∧
    out 21=List.replicate (2*width raw.length+2) true ∧
    out 25=frame (UInputScalars.normalized raw bound) ∧
    out 28=frame (SignedSortKey.binary (width raw.length) (limit raw.length)) ∧
    out 46=[UInputScalars.flag raw x bound] ∧
    out 47=RepairSource.VerifierDecoding.CompareMachine.word (Nat.log 2 raw.length) := by
  have h (j : Fin 40) := install_slot scalarSlots scalar_injective (extracted raw code x bound g)
    (UInputScalars.fullOutput raw x bound carry reset degree cap scratch) j
  obtain ⟨h0,h1,h2,h3,h10,h11,h12,h16,h19,h37,h38⟩ :=
    UInputScalars.output_fields raw x bound carry reset degree cap scratch
  have hcode : endpoint raw code x bound g carry reset degree cap scratch 5=frame code := by
    unfold endpoint
    rw [install_other scalarSlots _ _ 5 (by
      intro j hj
      have hv := congrArg Fin.val hj
      rw [scalar_value] at hv
      split_ifs at hv <;> omega)]
    rfl
  exact ⟨(h 0).trans h0,hcode,(h 1).trans h1,(h 2).trans h2,(h 3).trans h3,
    (h 10).trans h10,(h 11).trans h11,(h 12).trans h12,(h 16).trans h16,
    (h 19).trans h19,(h 37).trans h37,(h 38).trans h38⟩

def Prepared (raw : List Bool) (tapes : Store) : Prop := ∃ code x bound padding,
  raw=VerifierInputFields.source code x bound padding ∧
  UInputScalars.Guards raw x bound ∧
  tapes 0=frame raw ∧ tapes 5=frame code ∧ tapes 7=frame x ∧ tapes 9=frame bound ∧
  tapes 12=frame (ClockBinary.word raw.length) ∧
  tapes 19=List.replicate (width raw.length) true ∧
  tapes 20=List.replicate (2*width raw.length) true ∧
  tapes 21=List.replicate (2*width raw.length+2) true ∧
  tapes 25=frame (SignedSortKey.binary (width raw.length) (value bound)) ∧
  tapes 28=frame (SignedSortKey.binary (width raw.length) (limit raw.length)) ∧
  tapes 47=RepairSource.VerifierDecoding.CompareMachine.word (Nat.log 2 raw.length)

theorem endpoint_prepared (code x bound padding : List Bool) (g carry reset degree cap scratch : ℕ)
    (hg : UInputScalars.Guards (VerifierInputFields.source code x bound padding) x bound) :
    Prepared (VerifierInputFields.source code x bound padding)
      (endpoint (VerifierInputFields.source code x bound padding) code x bound g carry reset degree cap scratch) := by
  let raw := VerifierInputFields.source code x bound padding
  obtain ⟨h0,h5,h7,h9,h12,h19,h20,h21,h25,h28,_,h47⟩ :=
    endpoint_fields raw code x bound g carry reset degree cap scratch
  have hB : UInputScalars.normalized raw bound=SignedSortKey.binary (width raw.length) (value bound) :=
    ClockScalarFields.resize_binary _ _ hg.1
  rw [hB] at h25
  exact ⟨code,x,bound,padding,rfl,hg,h0,h5,h7,h9,h12,h19,h20,h21,h25,h28,h47⟩

theorem total_run (raw : List Bool) :
    ∃ r,run machine (budget raw) (input raw)=some r ∧
      r.final.tapes 0=frame raw ∧ (r.final.scanned 46=true ↔ Valid raw) ∧
      (r.final.scanned 46=true → Prepared raw r.final.tapes ∧ r.final.heads=heads) ∧
      r.steps ≤ budget raw := by
  classical
  by_cases hp : UInputSyntax.Fields raw
  · obtain ⟨code,x,bound,padding,he⟩ := hp
    change raw=VerifierInputFields.source code x bound padding at he
    subst raw
    let raw := VerifierInputFields.source code x bound padding
    obtain ⟨g,carry,reset,degree,cap,scratch,r,hr,ht,hh,hs⟩ := valid_shape_run code x bound padding
    have hf := endpoint_fields raw code x bound g carry reset degree cap scratch
    have hflag : r.final.scanned 46=UInputScalars.flag raw x bound := by
      have hout := hf.2.2.2.2.2.2.2.2.2.2.1
      simp only [Configuration.scanned,ht,hh,heads]
      rw [hout]
      rfl
    have hlen := raw_length code x bound padding
    have hiff := UInputScalars.flag_iff raw x bound (by dsimp [raw]; omega) hlen.2
    refine ⟨r,hr,by rw [ht]; exact hf.1,?_,?_,hs⟩
    · rw [hflag]
      exact hiff.trans (valid_iff_guards code x bound padding).symm
    · intro h
      rw [hflag] at h
      exact ⟨by rw [ht]; exact endpoint_prepared code x bound padding _ _ _ _ _ _ (hiff.mp h),hh⟩
  · obtain ⟨r,hr,ht,hh,hs⟩ := invalid_shape_run raw hp
    have hfalse : r.final.scanned 46=false := by
      simp [Configuration.scanned,ht,hh,afterScan,input,readTapeBit]
    have hvalid : ¬Valid raw := by
      rintro ⟨code,x,bound,padding,he,_⟩
      exact hp ⟨code,x,bound,padding,he⟩
    refine ⟨r,hr,by simp [ht,afterScan,input],by simp [hfalse,hvalid],by simp [hfalse],?_⟩
    exact runFrom_steps_le machine _ _ r hr

theorem short_reject (raw : List Bool) (hsmall : raw.length < 2) :
    ∃ r,run machine (budget raw) (input raw)=some r ∧
      r.final.scanned 46=false ∧ r.steps ≤ 4*raw.length+5 := by
  have hb : ¬UInputSyntax.Fields raw := by intro h; have := UInputSyntax.fields_length raw h; omega
  obtain ⟨r,hr,ht,hh,hs⟩ := invalid_shape_run raw hb
  exact ⟨r,hr,by simp [Configuration.scanned,ht,hh,afterScan,input,readTapeBit],hs⟩

end NearCubicWires.RepairOrdinary.UInputEntry
