import Proof.Amplification.RecoveryCanonicalFront

/-! Identify the actual count and row tapes produced by the canonical
cold front. The parser equalities determine these same physical buffers. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdCanonical
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle CompactCertificate CompactCertificate.Serialization
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def TableTapes {t : Nat} (slots : Fin 4→Fin t) (code : Nat) (c : Certificate)
    (a : Fin t→List Bool) : Prop :=
  a (slots 0)=CompareMachine.word c.inner.length ∧
  a (slots 1)=frame (innerBits code c) ∧
  a (slots 2)=CompareMachine.word c.outer.length ∧
  a (slots 3)=frame (outerBits code c)

def frontTableSlots : Fin 4→Fin 279 := ![270,271,274,275]

theorem produced_tables (code : Nat) (c : Certificate) (hc : Fits code c)
    (g : Fin 270→Nat) (b : Fin 270→List Bool) (H : Fin 279→Nat) (A : Fin 279→List Bool)
    (hp : RecoveryColdTablesAmbient.Produced (RecoveryColdView.width code.bits)
      (RecoveryColdView.limit code.bits) (TableFirst.pack (Serialization.width code) c)
      (tablePosition code c) g b H A) : TableTapes frontTableSlots code c A := by
  obtain ⟨n,ib,m,ob,logged,_,_,hi,ho,_,_,ht⟩ := hp
  have he := Option.some.inj ((inner_read code c hc).symm.trans hi)
  have hn : c.inner.length=n := congrArg Prod.fst he
  have hib : innerBits code c=ib := congrArg Prod.snd he
  subst n
  subst ib
  have he := Option.some.inj ((outer_read code c hc).symm.trans ho)
  have hm : c.outer.length=m := congrArg Prod.fst he
  have hob : outerBits code c=ob := congrArg Prod.snd he
  subst m
  subst ob
  rw [ht]
  have p1 := RecoveryFocus.pick_slot RecoveryColdTablesAmbient.slots RecoveryColdTablesAmbient.slots_injective 1
  have p3 := RecoveryFocus.pick_slot RecoveryColdTablesAmbient.slots RecoveryColdTablesAmbient.slots_injective 3
  have p7 := RecoveryFocus.pick_slot RecoveryColdTablesAmbient.slots RecoveryColdTablesAmbient.slots_injective 7
  have p8 := RecoveryFocus.pick_slot RecoveryColdTablesAmbient.slots RecoveryColdTablesAmbient.slots_injective 8
  change RecoveryFocus.pick RecoveryColdTablesAmbient.slots (270 : Fin 279)=some 1 at p1
  change RecoveryFocus.pick RecoveryColdTablesAmbient.slots (271 : Fin 279)=some 3 at p3
  change RecoveryFocus.pick RecoveryColdTablesAmbient.slots (274 : Fin 279)=some 7 at p7
  change RecoveryFocus.pick RecoveryColdTablesAmbient.slots (275 : Fin 279)=some 8 at p8
  unfold TableTapes
  change (RecoveryFocus.config _ _ _ _).tapes 270=_ ∧
    (RecoveryFocus.config _ _ _ _).tapes 271=_ ∧
    (RecoveryFocus.config _ _ _ _).tapes 274=_ ∧
    (RecoveryFocus.config _ _ _ _).tapes 275=_
  simp only [RecoveryFocus.config,p1,p3,p7,p8]
  exact ⟨rfl,rfl,rfl,rfl⟩

end NearCubicWires.RepairOrdinary.RecoveryColdCanonical
