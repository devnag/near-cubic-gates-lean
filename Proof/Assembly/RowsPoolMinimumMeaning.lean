import Proof.Assembly.RowsPoolMinimumState

/-! Projection and support facts for the actual native reader/add/erase join.
Only the four retained fields and the physical capacity driver survive. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolMinimum
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem parsed_input (source mask : List Bool) (pos w C a : ℕ) (z : ℤ)
    (hw : natBitLength z.natAbs≤w) (j : Fin 5) :
    parsed source mask pos w C a z (addSlots j)=addInput C w (-z).toNat a j:=by
  fin_cases j
  · exact (CloseoutRowsPoolMagnitude.parts source pos w C z hw).2
  all_goals rfl

theorem parsed_support (pre tail mask : List Bool) (w C a : ℕ) (z : ℤ)
    (hC : RowPowerNativeReset.rawTime z w+1≤C) (j : Fin 14) :
    (parsed (pre++intWord z++tail) mask (pre.length+(intWord z).length) w C a z
      (workSlots j)).length≤C:=by
  fin_cases j
  all_goals simp only [parsed,workSlots,Fin.addCases]
  all_goals first
    | exact CloseoutRowsPoolMagnitude.support pre tail w C z hC _ (by decide)
    | simp [extra,MatrixScoreWeight.zeros]

theorem added_support (C w x a : ℕ) (live : Bool) (A : Fin 20→List Bool)
    (hc : 2*w+1≤C) (ha : ∀ j,(A (workSlots j)).length≤C) (j : Fin 14) :
    (added C w x a live A (workSlots j)).length≤C:=by
  cases live with
  | false=>exact ha j
  | true=>
    change (install addSlots A (addOutput C w x a) (workSlots j)).length≤C
    cases hp:RecoveryFocus.pick addSlots (workSlots j) with
    | none=>simpa [install,hp] using ha j
    | some k=>
      simp only [install,hp]
      fin_cases k <;>
        simp [addOutput,MatrixScoreWeight.scalar,MatrixScoreWeight.zeros,
          ZeroPadding.pad_length,SignedSortKey.binary_length,max_eq_left hc]

theorem cleared_added (source mask : List Bool) (pos w C a : ℕ) (z : ℤ) (live : Bool) :
    cleared C (added C w (-z).toNat a live (parsed source mask pos w C a z))=
      data source mask w C (a+if live then (-z).toNat else 0):=by
  let A:=parsed source mask pos w C a z
  funext i
  fin_cases i
  · exact (cleared_live C _ 0 (by simp)).trans
      ((added_other C w (-z).toNat a live A 0 (by intro j;fin_cases j <;> decide)).trans
        (CloseoutRowsPoolMagnitude.source source pos w C z))
  · exact cleared_work C _ 0
  · exact cleared_work C _ 1
  · exact cleared_work C _ 2
  · exact cleared_work C _ 3
  · exact cleared_work C _ 4
  · exact cleared_work C _ 5
  · exact cleared_work C _ 6
  · exact cleared_work C _ 7
  · exact (cleared_live C _ 9 (by simp)).trans
      ((added_other C w (-z).toNat a live A 9 (by intro j;fin_cases j <;> decide)).trans
        (CloseoutRowsPoolMagnitude.width source pos w C z))
  · exact cleared_work C _ 8
  · exact cleared_work C _ 9
  · exact cleared_work C _ 10
  · exact (cleared_live C _ 13 (by simp)).trans
      (added_other C w (-z).toNat a live A 13 (by intro j;fin_cases j <;> decide))
  · exact (cleared_live C _ 14 (by simp)).trans
      (added_accumulator C w (-z).toNat a live A rfl)
  · exact cleared_work C _ 11
  · exact cleared_work C _ 12
  · exact cleared_work C _ 13
  · exact (cleared_driver C _).1
  · exact (cleared_driver C _).2

end NearCubicWires.RepairOrdinary.CloseoutRowsPoolMinimum
