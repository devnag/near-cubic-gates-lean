import Proof.MachineModel.UDecoderRuntimeMetadata

/-! Only these eight physical fields are needed to retain decoder runtime
metadata through later phases. Other tapes and their cursors may change. -/
namespace NearCubicWires.RepairOrdinary.UDecoder
open LocalBitMultitape RecoveryExecution RepairSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def RuntimeSlot (i : Fin 69) : Prop :=
  i=6 ∨ i=50 ∨ i=51 ∨ i=52 ∨ i=55 ∨ i=58 ∨ i=59 ∨ i=68
instance (i : Fin 69) : Decidable (RuntimeSlot i) := by unfold RuntimeSlot; infer_instance

theorem RuntimeMetadata.transport {N : ℕ} {heads heads' : Fin 69 → ℕ}
    {tapes tapes' : Fin 69 → List Bool} {v : OrdinaryVerifier} {word : List Bool}
    (h : RuntimeMetadata N heads tapes v word)
    (hk : ∀ i,RuntimeSlot i → heads' i=heads i ∧ tapes' i=tapes i) :
    RuntimeMetadata N heads' tapes' v word := by
  have h6 := hk 6 (by decide)
  have h50 := hk 50 (by decide)
  have h51 := hk 51 (by decide)
  have h52 := hk 52 (by decide)
  have h55 := hk 55 (by decide)
  have h58 := hk 58 (by decide)
  have h59 := hk 59 (by decide)
  have h68 := hk 68 (by decide)
  exact ⟨h.decoded,h.canonical,h.code_eq,h.code_bound,h.tapes_bound,h.states_bound,h.width_bound,
    h6.2.trans h.code_tape,h6.1.trans h.code_head,
    (congrArg (ZeroPadding.pad (word.length+2)) h50.2).trans h.t_tape,
    (congrArg (ZeroPadding.pad (word.length+2)) h51.2).trans h.s_tape,
    (congrArg (ZeroPadding.pad (word.length+2)) h52.2).trans h.c_tape,
    h50.1.trans h.t_head,h51.1.trans h.s_head,h52.1.trans h.c_head,
    h55.2.trans h.binary_s,h55.1.trans h.binary_s_head,h58.2.trans h.j_tape,h58.1.trans h.j_head,
    h59.2.trans h.start_tape,h59.1.trans h.start_head,h68.2.trans h.four_t,h68.1.trans h.four_t_head⟩

def RuntimeOrigin (raw witness : List Bool) (heads : Fin 69 → ℕ) (tapes : Fin 69 → List Bool) : Prop :=
  ∃ base : Configuration 69 (Fintype.card (RecoveryCalls.Control sizes)),
    Accepted raw ∧ Successful raw witness base ∧
    ∀ i,RuntimeSlot i → heads i=base.heads i ∧ tapes i=base.tapes i

theorem RuntimeOrigin.metadata {raw witness : List Bool} {heads : Fin 69 → ℕ}
    {tapes : Fin 69 → List Bool} (h : RuntimeOrigin raw witness heads tapes) :
    ∃ v word,RuntimeMetadata raw.length heads tapes v word := by
  obtain ⟨base,ha,hs,hk⟩ := h
  obtain ⟨v,word,hm⟩ := successful_runtime_metadata raw witness base hs ha
  exact ⟨v,word,hm.transport hk⟩

end NearCubicWires.RepairOrdinary.UDecoder
