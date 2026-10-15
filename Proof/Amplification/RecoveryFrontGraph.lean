import Proof.Amplification.RecoveryFrontScan

/-! The cold front's physical valuation/raw-syntax/table gates. Its
success predicate retains both native raw banks and produced table buffers. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdFront
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
open RecoveryColdView
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev stateCount {t s : Nat} (_p : Machine t s) := s
noncomputable abbrev sizes : Fin 3→Nat := ![stateCount prefixProgram,stateCount scanProgram,
  stateCount RecoveryColdTablesAmbient.program]
noncomputable def programs : (j : Fin 3)→Machine 279 (sizes j)
  | ⟨0,_⟩=>prefixProgram
  | ⟨1,_⟩=>scanProgram
  | ⟨2,_⟩=>RecoveryColdTablesAmbient.program
  | ⟨n+3,h⟩=>False.elim (by omega)
noncomputable def next (j : Fin 3) (_ : Fin (sizes j)) (bits : Fin 279→Bool) : Option (Fin 3) :=
  if j.val=0 then if bits 30 then some 1 else none else
  if j.val=1 then if bits 230 then some 2 else none else none
noncomputable abbrev machine := RecoveryCalls.machine sizes programs 0 next
def budget (bits word : List Bool) := prefixBudget bits word+RecoveryColdScanner.scanBudget bits word+
  RecoveryColdTables.resetBudget (width bits) (limit bits) word+3

def Prepared (bits word : List Bool) (H : Fin 279→Nat) (A : Fin 279→List Bool) : Prop :=
  ∃ k,∃ (g : Fin 270→Nat) (b : Fin 270→List Bool),
    RecoveryColdTablesAmbient.Sources word k (width bits) (limit bits) g b ∧
    RecoveryColdTablesAmbient.Produced (width bits) (limit bits) word k g b H A ∧
    RecoveryColdSAT.Ready bits word (fun i=>H (i.castAdd 107)) (fun i=>A (i.castAdd 107)) ∧
    A 0=frame bits

theorem prepared_of_produced (bits word : List Bool) (h : Fin 172→Nat) (a : Fin 172→List Bool)
    (ha : RecoveryColdSAT.Ready bits word h a) (hcode : a 0=frame bits)
    (g : Fin 270→Nat) (b : Fin 270→List Bool)
    (hkeepH : (fun i : Fin 172=>g (i.castAdd 98))=h)
    (hkeepT : (fun i : Fin 172=>b (i.castAdd 98))=a)
    (k : Nat) (hs : RecoveryColdTablesAmbient.Sources word k (width bits) (limit bits) g b)
    (H : Fin 279→Nat) (A : Fin 279→List Bool)
    (hp : RecoveryColdTablesAmbient.Produced (width bits) (limit bits) word k g b H A) :
    Prepared bits word H A := by
  obtain ⟨hh,ht⟩ := RecoveryColdTablesAmbient.produced_retained word k (width bits) (limit bits) g b hs H A hp
  have hh' := hh.trans hkeepH
  have ht' := ht.trans hkeepT
  refine ⟨k,g,b,hs,hp,?_,?_⟩
  · rw [hh',ht']; exact ha
  · have h0 := congrFun ht' (0 : Fin 172)
    rw [show (0 : Fin 172).castAdd 107=(0 : Fin 279) by decide] at h0
    exact h0.trans hcode

end NearCubicWires.RepairOrdinary.RecoveryColdFront
