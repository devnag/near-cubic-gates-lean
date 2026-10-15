import Proof.CaseAnalysis.RowsBankClear
import Proof.CaseAnalysis.RowsPacketLoad

/-! The exact fixed packet port set is the whole native bank except its
growing output and the two shared erase resources. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsBankPorts
open LocalBitMultitape CloseoutRowsBankClear
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem work_complete (i : Fin 113) (h31 : i≠31) (h104 : i≠104) (h105 : i≠105) :
    ∃ j,work j=i := by
  have hn31 : i.val≠31 := fun h=>h31 (Fin.ext h)
  have hn104 : i.val≠104 := fun h=>h104 (Fin.ext h)
  have hn105 : i.val≠105 := fun h=>h105 (Fin.ext h)
  have hib := i.isLt
  by_cases h0 : i.val<31
  · let j : Fin 110:=⟨i.val,by omega⟩
    refine ⟨j,Fin.ext ?_⟩
    rw [work_val]
    simp [j,h0]
  · by_cases h1 : i.val<104
    · let j : Fin 110:=⟨i.val-1,by omega⟩
      refine ⟨j,Fin.ext ?_⟩
      rw [work_val]
      simp only [j]
      split_ifs <;> omega
    · let j : Fin 110:=⟨i.val-3,by omega⟩
      refine ⟨j,Fin.ext ?_⟩
      rw [work_val]
      simp only [j]
      split_ifs <;> omega

theorem erased_store (C : ℕ) (out : List Bool) (data : Fin 113→List Bool)
    (ho : data 31=out) (hs : ∀ i,data (slots i)=erased C i) : data=blank C out := by
  funext i
  by_cases h31 : i=31
  · subst i
    simpa only [blank,↓reduceIte] using ho
  by_cases h104 : i=104
  · subst i
    exact hs 110
  by_cases h105 : i=105
  · subst i
    exact hs 111
  obtain ⟨j,hj⟩ := work_complete i h31 h104 h105
  have he := hs ((j.castAdd 1).castAdd 1)
  rw [slots_work,hj] at he
  simpa only [erased,Fin.addCases_left,blank,h31,h104,h105,↓reduceIte] using he

def port (i : Fin 110) : Fin 114 := (work i).castAdd 1
def ports : List (Fin 114) := (List.finRange 110).map port
theorem port_injective : Function.Injective port := by
  intro i j he
  apply work_injective
  exact Fin.ext (congrArg (fun k : Fin 114=>k.val) he)
theorem ports_nodup : ports.Nodup := List.Nodup.map port_injective (List.nodup_finRange 110)
theorem port_mem (i : Fin 110) : port i∈ports := List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩
theorem port_avoids (i : Fin 110) : port i≠31 ∧ port i≠104 ∧ port i≠105 ∧ port i≠113 := by
  have hs:=work_avoids i
  have hne (k : Fin 113) (hk : work i≠k) : port i≠k.castAdd 1 := by
    intro he
    exact hk (Fin.ext (congrArg (fun a : Fin 114=>a.val) he))
  refine ⟨hne 31 hs.1,hne 104 hs.2.1,hne 105 hs.2.2,?_⟩
  intro he
  have hv:=congrArg (fun k : Fin 114=>k.val) he
  change (work i).val=113 at hv
  have hb:=(work i).isLt
  omega
theorem mem_ports (i : Fin 114) : i∈ports ↔ i≠31 ∧ i≠104 ∧ i≠105 ∧ i≠113 := by
  constructor
  · intro h
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp h
    exact port_avoids j
  · rintro ⟨h31,h104,h105,h113⟩
    have hlt : i.val<113 := by
      have hb:=i.isLt
      have hn : i.val≠113 := fun h=>h113 (Fin.ext h)
      omega
    let old : Fin 113:=⟨i.val,hlt⟩
    have hold (k : Fin 113) (hk : i≠k.castAdd 1) : old≠k := by
      intro he
      exact hk (Fin.ext (congrArg (fun a : Fin 113=>a.val) he))
    obtain ⟨j,hj⟩ := work_complete old (hold 31 h31) (hold 104 h104) (hold 105 h105)
    have he : port j=i := Fin.ext (congrArg (fun a : Fin 113=>a.val) hj)
    exact he ▸ port_mem j

theorem written_apply {t : ℕ} (fields : Fin t→List Bool) (C : ℕ)
    (js : List (Fin t)) (data : Fin t→List Bool) (i : Fin t) :
    CloseoutRowsPacketLoad.written fields C js data i=
      if i∈js then ZeroPadding.pad C (fields i) else data i := by
  induction js generalizing data with
  | nil => rfl
  | cons j js ih =>
    rw [CloseoutRowsPacketLoad.written,ih]
    by_cases hm : i∈js
    · simp [hm]
    · by_cases he : i=j
      · subst i
        simp [hm]
      · simp [hm,he]

end NearCubicWires.RepairOrdinary.CloseoutRowsBankPorts
