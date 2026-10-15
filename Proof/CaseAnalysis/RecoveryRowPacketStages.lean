import Proof.CaseAnalysis.RecoveryRowPacketWord

/-! Every prototype append consumes the same physically retained raw
scalar fields. This record only states the actual input tapes and backing. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
open LocalBitMultitape Composition
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Loaded (v : Fin 10→ℕ) (B : ℕ) (H : Fin 88→ℕ) (A : Fin 88→List Bool) : Prop where
  heads : ∀ i,H (scalarPort i)=0
  tapes : ∀ i,A (scalarPort i)=List.replicate (v i) true
  scratch_head : H 73=0
  scratch_tape : A 73=List.replicate B false
  bounds : ∀ i,2*v i+4≤B

theorem scalar_ne_output (i : Fin 10) : scalarPort i≠75:=by
  intro h
  have he:=congrArg Fin.val h
  change 78+i.val=75 at he
  omega
theorem scalar_ne_scratch (i : Fin 10) : scalarPort i≠73:=by
  intro h
  have he:=congrArg Fin.val h
  change 78+i.val=73 at he
  omega
theorem scalar_injective : Function.Injective scalarPort:=by
  intro i j h
  have he:=congrArg Fin.val h
  change 78+i.val=78+j.val at he
  exact Fin.ext (by omega)

theorem Loaded.field_run {v : Fin 10→ℕ} {B : ℕ} {H : Fin 88→ℕ} {A : Fin 88→List Bool}
    (h : Loaded v B H A) (i : Fin 10) (sentinel : Bool) (out : List Bool) :
    Appends (scalarField (scalarPort i) sentinel) (fieldBudget sentinel (v i)) H A out
      (out++field sentinel (v i)) :=
  RecoveryBoundedRowPacketAppend.field_run (scalarPort i) sentinel (v i) B out H A
    (scalar_ne_output i) (scalar_ne_scratch i) (h.heads i) h.scratch_head
    (h.tapes i) h.scratch_tape (h.bounds i)

noncomputable def paddedHeader (source width : Fin 10) (sentinel : Bool):=
  Composition.machine (write (header sentinel)) (paddedField (scalarPort source) (scalarPort width))
def paddedBudget (sentinel : Bool) (width : ℕ):=(header sentinel).length+1+(4*width+4)
def paddedWord (sentinel : Bool) (n width : ℕ):=
  header sentinel++frame (ZeroPadding.pad width (List.replicate n true))

theorem Loaded.padded_run {v : Fin 10→ℕ} {B : ℕ} {H : Fin 88→ℕ} {A : Fin 88→List Bool}
    (h : Loaded v B H A) (source width : Fin 10) (sentinel : Bool) (out : List Bool)
    (hsw : source≠width) (hfit : v source≤v width) :
    Appends (paddedHeader source width sentinel) (paddedBudget sentinel (v width)) H A out
      (out++paddedWord sentinel (v source) (v width)) := by
  have a:=write_run (header sentinel) out H A
  have b:=RecoveryBoundedRowPacketAppend.padded_run (scalarPort source) (scalarPort width)
    (List.replicate (v source) true) (v width) B (out++header sentinel) H A
    (scalar_ne_output source) (scalar_ne_scratch source) (scalar_ne_output width) (scalar_ne_scratch width)
    (fun he=>hsw (scalar_injective he)) (h.heads source) (h.heads width) h.scratch_head
    (h.tapes source) (h.tapes width) h.scratch_tape
    (by simpa only [List.length_replicate] using hfit) (by have hb:=h.bounds width;omega)
  simpa only [paddedHeader,paddedBudget,paddedWord,List.append_assoc] using a.join b

end NearCubicWires.RepairOrdinary.RecoveryBoundedRowPacketAppend
