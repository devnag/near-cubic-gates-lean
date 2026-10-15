import Proof.CaseAnalysis.RowsCircuitAppendFocus

/-! Actual bottom metadata is appended before the global circuit guards.
Description accounts for every serialized bottom. The selected body retains
one native request and charges its actual support plus the top incidence. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
open LocalBitMultitape RadixSemantics RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem heads_native (pos memberPos : ℕ) (out next : List Bool) (description wires : ℕ) :
    Function.update (heads pos memberPos out description wires) 1049 next.length=
      heads pos memberPos next description wires := by
  funext i
  by_cases h:i.val=1049
  · have he:i=1049:=Fin.ext h;subst i;rfl
  · rw [Function.update_of_ne (by intro he;exact h (congrArg Fin.val he))]
    simp only [heads,if_neg h]
theorem heads_description (pos memberPos : ℕ) (out : List Bool) (description next wires : ℕ) :
    Function.update (heads pos memberPos out description wires) 1050 next=
      heads pos memberPos out next wires := by
  funext i
  by_cases h:i.val=1050
  · have he:i=1050:=Fin.ext h;subst i;rfl
  · rw [Function.update_of_ne (by intro he;exact h (congrArg Fin.val he))]
    simp only [heads,if_neg h]
theorem heads_wires (pos memberPos : ℕ) (out : List Bool) (description wires next : ℕ) :
    Function.update (heads pos memberPos out description wires) 1051 next=
      heads pos memberPos out description next := by
  funext i
  by_cases h:i.val=1051
  · have he:i=1051:=Fin.ext h;subst i;rfl
  · rw [Function.update_of_ne (by intro he;exact h (congrArg Fin.val he))]
    simp only [heads,if_neg h]

noncomputable def describe:=RecoveryFocus.machine descriptionSlots CloseoutRowsCircuitAppend.unary
noncomputable def native:=RecoveryFocus.machine nativeSlots CompetitorFrameAppend.machine
noncomputable def wires:=RecoveryFocus.machine wireSlots CloseoutRowsCircuitAppend.unary
noncomputable def selected:=Composition.machine native wires

theorem describe_run (cap core pos memberPos a b : ℕ) (out source membership : List Bool)
    (description wireCount : ℕ) (flag : Bool) (tapes : Fin 1059→List Bool)
    (hs : Stored cap core out source membership description wireCount flag tapes)
    (ha : tapes 1041=ZeroPadding.pad cap (List.replicate a true))
    (hb : tapes 1045=ZeroPadding.pad cap (List.replicate b true)) (hc : a+b+2 ≤ cap) :
    PCPOuter.Exact describe (2*(a+b)+6) (heads pos memberPos out description wireCount) tapes
      (heads pos memberPos out (description+(a+b)) wireCount)
      (Function.update tapes 1050 (List.replicate (description+(a+b)) true)) := by
  have h:=CloseoutRowsCircuitAppend.unary_focus descriptionSlots (by decide) cap a b
    (List.replicate description true) hc (heads pos memberPos out description wireCount) tapes
    (by intro i;fin_cases i <;> first | rfl | exact (List.length_replicate ..).symm)
    (by
      intro i;fin_cases i
      · exact ha
      · exact hb
      · exact hs.extra 1
      · exact hs.extra 8)
  change PCPOuter.Exact describe _ _ _
    (Function.update (heads pos memberPos out description wireCount) 1050
      (List.replicate description true++List.replicate (a+b) true).length)
    (Function.update tapes 1050 (List.replicate description true++List.replicate (a+b) true)) at h
  rw [←List.replicate_add,List.length_replicate,heads_description] at h
  exact h

theorem selected_run (cap core pos memberPos support : ℕ) (bits out source membership : List Bool)
    (description wireCount : ℕ) (flag : Bool) (tapes : Fin 1059→List Bool)
    (hs : Stored cap core out source membership description wireCount flag tapes)
    (hn : tapes 1033=ZeroPadding.pad cap (frame bits))
    (hw : tapes 1047=ZeroPadding.pad cap (List.replicate support true))
    (hbits : 2*bits.length+1 ≤ cap) (hwire : support+1+2 ≤ cap) :
    PCPOuter.Exact selected ((4*bits.length+3)+1+(2*(support+1)+6))
      (heads pos memberPos out description wireCount) tapes
      (heads pos memberPos (out++frame bits) description (wireCount+(support+1)))
      (Function.update (Function.update tapes 1049 (out++frame bits)) 1051
        (List.replicate (wireCount+(support+1)) true)) := by
  have first:=CloseoutRowsCircuitAppend.frame_focus nativeSlots (by decide) cap bits out hbits
    (heads pos memberPos out description wireCount) tapes (by intro i;fin_cases i <;> rfl)
    (by
      intro i;fin_cases i
      · exact hn
      · exact hs.extra 0
      · exact hs.extra 8)
  change PCPOuter.Exact native _ _ _
    (Function.update (heads pos memberPos out description wireCount) 1049 (out++frame bits).length)
    (Function.update tapes 1049 (out++frame bits)) at first
  rw [heads_native] at first
  have last:=CloseoutRowsCircuitAppend.unary_focus wireSlots (by decide) cap support 1
    (List.replicate wireCount true) hwire
    (heads pos memberPos (out++frame bits) description wireCount) (Function.update tapes 1049 (out++frame bits))
    (by intro i;fin_cases i <;> first | rfl | exact (List.length_replicate ..).symm)
    (by
      intro i;fin_cases i <;> rw [Function.update_of_ne (by decide)]
      · exact hw
      · exact hs.extra 9
      · exact hs.extra 2
      · exact hs.extra 8)
  change PCPOuter.Exact wires _ _ _
    (Function.update (heads pos memberPos (out++frame bits) description wireCount) 1051
      (List.replicate wireCount true++List.replicate (support+1) true).length)
    (Function.update (Function.update tapes 1049 (out++frame bits)) 1051
      (List.replicate wireCount true++List.replicate (support+1) true)) at last
  rw [←List.replicate_add,List.length_replicate,heads_wires] at last
  exact PCPOuter.exact_join first last

end NearCubicWires.RepairOrdinary.CloseoutRowsCircuitBottom
