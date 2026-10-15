import Proof.SourceAssembly.SourceBundle

/- Same ordinary source programs on retained backing.  No allocation or erasure
is inferred from these representation identities. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace SourceAssemblyReuse
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairOrdinary.RecoveryExecution RepairRepresentation
open FixedLivePackets PacketProduction
open MaskedFamilySource
noncomputable section

theorem pad_pad (a b : Nat) (tape : List Bool) :
    ZeroPadding.pad a (ZeroPadding.pad b tape) = ZeroPadding.pad (max a b) tape := by
  simp only [ZeroPadding.pad, List.length_append, List.length_replicate,
    List.append_assoc, ← List.replicate_add]
  congr 1
  congr 1
  omega

theorem pad_install {t u : Nat} (slots : Fin t → Fin u)
    (R : Fin u → Nat) (ambient : Fin u → List Bool) (bank : Fin t → List Bool) :
    (fun i => ZeroPadding.pad (R i) (install slots ambient bank i)) =
    install slots (fun i => ZeroPadding.pad (R i) (ambient i))
      (fun j => ZeroPadding.pad (R (slots j)) (bank j)) := by
  funext i
  cases hp : RecoveryFocus.pick slots i with
  | none => simp [install, hp]
  | some j =>
    have he := RecoveryFocus.slot_of_pick slots hp
    simp only [install, hp]
    rw [he]

theorem ready_pad {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a} {U : Nat}
    (c : MaskSeedCode mask packet U) (r : Request) (fuel : Nat)
    (H H' : Fin U → Nat) (A A' : Fin U → List Bool) (R : Fin U → Nat)
    (h : c.Ready r fuel H H' A A') :
    c.Ready r fuel H H' (fun i => ZeroPadding.pad (R i) (A i))
      (fun i => ZeroPadding.pad (R i) (A' i)) := by
  obtain ⟨mR,mH,mA,pR,pH,pA,leadFuel,suffixFuel,tailFuel,lead,suffix,tail,bound⟩ := h
  refine ⟨(fun j => max (R (c.maskSlots j)) (mR j)),mH,
    (fun i => ZeroPadding.pad (R i) (mA i)),
    (fun j => max (R (c.slots j)) (pR j)),pH,
    (fun i => ZeroPadding.pad (R i) (pA i)),leadFuel,suffixFuel,tailFuel,?_,?_,?_,bound⟩
  · simpa only [pad_install, pad_pad] using lead.pad R
  · intro B run out
    simpa only [pad_install, pad_pad] using (suffix B run out).pad R
  · intro B run out
    simpa only [pad_install, pad_pad] using (tail B run out).pad R

theorem dockH_existing {t u : Nat} (slot : Fin t → Fin u) (ambient : Fin u → Nat)
    (heads : Fin t → Nat) (h : ∀ j, ambient (slot j) = heads j) :
    dockH slot ambient heads = ambient := by
  funext i
  cases hp : RecoveryFocus.pick slot i with
  | none => simp [dockH, hp]
  | some j =>
    have he := RecoveryFocus.slot_of_pick slot hp
    simp only [dockH, hp]
    exact (h j).symm.trans (congrArg ambient he)

def haltMachine (T : Nat) : Machine T 1 where
  descriptionBits := 0
  start := 0
  halted := fun _ => true
  rule := fun _ _ => none

theorem halt_step {T : Nat} (H : Fin T → Nat) (A : Fin T → List Bool) :
    Step (haltMachine T) 0 H A H A :=
  ⟨{ final := ⟨(haltMachine T).start,H,A⟩, steps := 0,
      peakTapeCells := (⟨(haltMachine T).start,H,A⟩ : Configuration T 1).tapeCells },
    (by simp [runFrom, haltMachine]),rfl,rfl,le_rfl⟩

def identityTail {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a} {U : Nat}
    (c : MaskSeedCode mask packet U) : MaskSeedCode mask packet U :=
  { c with tailStates := 1, tail := haltMachine U }

theorem step_tapes_unique {t s : Nat} {p : Machine t s} {n : Nat}
    {H H₁ H₂ : Fin t → Nat} {A A₁ A₂ : Fin t → List Bool}
    (h₁ : Step p n H A H₁ A₁) (h₂ : Step p n H A H₂ A₂) : A₁ = A₂ := by
  obtain ⟨r₁,hr₁,_,ha₁,_⟩ := h₁
  obtain ⟨r₂,hr₂,_,ha₂,_⟩ := h₂
  have he : r₁ = r₂ := Option.some.inj (hr₁.symm.trans hr₂)
  subst he
  exact ha₁.symm.trans ha₂

/-- The suffix must genuinely construct the disjoint pool input.  After that,
the existing packet output is retained in place, with zero tail cost and no
precomputed raw-output-length driver.  This is exactly Prepared's seed exit. -/
theorem identity_tail_pool {mask : MaskProducer} {selector : CyclicChoice.Laws}
    {a : DecompositionAlgorithm} {packet : PacketWriter selector a} {U : Nat}
    (c : MaskSeedCode mask packet U) (r : Request) (fuel : Nat)
    (H : Fin U → Nat) (A : Fin U → List Bool)
    (mR : Fin (5+mask.work) → Nat) (mH : Fin U → Nat) (mA : Fin U → List Bool)
    (pR : Fin packet.ordinary.program.tapeCount → Nat)
    (pH : Fin U → Nat) (pA : Fin U → List Bool) (leadFuel suffixFuel : Nat)
    (poolSlots : Fin 373 → Fin U) (poolReserve : Fin 373 → Nat)
    (disjoint : ∀ i j, c.slots i ≠ poolSlots j)
    (pool_heads : ∀ j, pH (poolSlots j) = 0)
    (pool_bank : ∀ j, pA (poolSlots j) = ZeroPadding.pad (poolReserve j)
      (P1Closure.BinaryCacheColdRun.input
        (CachedFamilyLoader.cacheArgs a (r.family a)) j))
    (lead : Step c.lead leadFuel H A
      (dockH c.maskSlots mH (fun _ => 0))
      (install c.maskSlots mA (fun i => ZeroPadding.pad (mR i)
        ((maskData a r).input mask.work i))))
    (suffix : ∀ B : Fin (5+mask.work) → List Bool,
      Step mask.machine (maskBudget mask.coefficient mask.degree (maskData a r))
        (fun _ => 0) ((maskData a r).input mask.work) (fun _ => 0) B →
      B ⟨4,by omega⟩ = (maskData a r).word →
      Step c.suffix suffixFuel (dockH c.maskSlots mH (fun _ => 0))
        (install c.maskSlots mA (fun i => ZeroPadding.pad (mR i) (B i)))
        (dockH c.slots pH (fun _ => 0))
        (install c.slots pA (fun i => ZeroPadding.pad (pR i)
          (packet.ordinary.program.inputTapes (r.input a) i))))
    (bound : (leadFuel+1+(maskBudget mask.coefficient mask.degree (maskData a r)+1+
      suffixFuel))+1+(packetBudget a packet.coefficient packet.degree r+1+0) ≤ fuel) :
    ∃ (poolH : Fin U → Nat) (poolA : Fin U → List Bool),
      (identityTail c).Ready r fuel H (dockH poolSlots poolH (fun _ => 0)) A
        (install poolSlots poolA (fun j => ZeroPadding.pad (poolReserve j)
          (P1Closure.BinaryCacheColdRun.input
            (CachedFamilyLoader.cacheArgs a (r.family a)) j))) ∧
      poolA (c.slots packet.ordinary.program.outputTape) =
        ZeroPadding.pad (pR packet.ordinary.program.outputTape) (r.raw selector a) := by
  obtain ⟨B,run,out⟩ := packet.run selector a r
  let endH := dockH c.slots pH (fun _ => 0)
  let endA := install c.slots pA (fun i => ZeroPadding.pad (pR i) (B i))
  have hH : dockH poolSlots endH (fun _ => 0) = endH := by
    apply dockH_existing
    intro j
    exact (dockH_other c.slots pH _ (poolSlots j) (fun i => disjoint i j)).trans
      (pool_heads j)
  have hA : install poolSlots endA (fun j => ZeroPadding.pad (poolReserve j)
      (P1Closure.BinaryCacheColdRun.input
        (CachedFamilyLoader.cacheArgs a (r.family a)) j)) = endA := by
    apply install_existing
    intro j
    exact (install_other c.slots pA _ (poolSlots j) (fun i => disjoint i j)).trans
      (pool_bank j)
  refine ⟨endH,endA,?_,?_⟩
  · rw [hH,hA]
    refine ⟨mR,mH,mA,pR,pH,pA,leadFuel,suffixFuel,0,lead,suffix,?_,bound⟩
    intro B' run' out'
    have he := step_tapes_unique run' run
    subst he
    exact halt_step endH endA
  · dsimp only [endA]
    rw [install_slot c.slots c.injective, out]

end
end SourceAssemblyReuse
