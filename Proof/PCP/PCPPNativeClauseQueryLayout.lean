import Proof.PCP.PCPPNativeClauseRawLayout

/-! The native Q consumer's actual counters/output are the M consumer's
ports. Only original clause fields and the two original-oracle scalars use
fresh input ports; those are supplied by the enclosing metadata producer. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeClauseQuery
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 58) : Fin 336 :=
  if i=4 then 6 else if i=26 then 276 else if i=27 then 99
  else if i=47 then 102 else if i=52 then 42 else if i=53 then 2 else i.natAdd 278
theorem slots_injective : Function.Injective slots := by decide
def extra (fields : List Bool) (p n : ℕ) (i : Fin 58) : List Bool :=
  if i=5 then List.replicate p true else if i=6 then List.replicate n true else if i=13 then fields else []
def tapes (old : Fin 278→List Bool) (fields : List Bool) (p n : ℕ) : Fin 336→List Bool :=
  Fin.addCases (m:=278) (n:=58) (motive:=fun _=>List Bool) old (extra fields p n)
def heads (old : Fin 278→ℕ) : Fin 336→ℕ :=
  Fin.addCases (m:=278) (n:=58) (motive:=fun _=>ℕ) old (fun _=>0)
noncomputable def first := TapeEmbedding.machine 58 PCPPNativeQueryConjunction.machine
noncomputable def last := RecoveryFocus.machine slots PCPPNativeClauseRawRun.machine
noncomputable def machine := Composition.machine first last

theorem clause_data (old : Fin 278→List Bool) (fields : List Bool) (stride p n C base accumulator M : ℕ)
    (out : List Bool) (hstride : old 6=UnaryTemplate.tape stride)
    (hbase : old 276=List.replicate base true) (hacc : old 99=List.replicate accumulator true)
    (hout : old 102=out) (hC : old 42=List.replicate C true) (hM : old 2=List.replicate M true)
    (i : Fin 58) :
    tapes old fields p n (slots i)=(PCPPNativeClauseRawRun.entry fields 0 stride p n C base accumulator out M).tapes i := by
  rw [PCPPNativeClauseRawRun.input_data]
  fin_cases i
  all_goals first | exact hstride | exact hbase | exact hacc | exact hout | exact hC | exact hM | rfl

theorem clause_heads (old : Fin 278→ℕ) (fields : List Bool) (stride p n C base accumulator M : ℕ)
    (out : List Bool) (hstride : old 6=0) (hbase : old 276=0) (hacc : old 99=0)
    (hout : old 102=out.length) (hC : old 42=0) (hM : old 2=0) (i : Fin 58) :
    heads old (slots i)=(PCPPNativeClauseRawRun.entry fields 0 stride p n C base accumulator out M).heads i := by
  rw [PCPPNativeClauseRawRun.input_heads]
  fin_cases i
  all_goals first | exact hstride | exact hbase | exact hacc | exact hout | exact hC | exact hM | rfl

theorem away14 : ∀ j,slots j≠14 := by decide
theorem away16 : ∀ j,slots j≠16 := by decide

end NearCubicWires.RepairOrdinary.PCPPNativeClauseQuery
