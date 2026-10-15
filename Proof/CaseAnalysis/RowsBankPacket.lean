import Proof.CaseAnalysis.RowsSourceLoad

/-! The fixed native packet is actually loaded into the erased bank.
The source cursor advances once and the growing cut output is never copied. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsBankPacket
open LocalBitMultitape CloseoutRowsBankPorts CloseoutRowsBankClear
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extend {α : Type} (old : Fin 113→α) (fresh : α) : Fin 114→α :=
  Fin.addCases (m:=113) (n:=1) (motive:=fun _=>α) old (fun _ : Fin 1=>fresh)
def fields (data : Fin 113→List Bool) := extend data []
def word (data : Fin 113→List Bool) := CloseoutRowsPacketLoad.stream (fields data) ports
def heads (out : List Bool) (pos : ℕ) := extend (zeroHeads out) pos
def tapes (C : ℕ) (out packet : List Bool) := extend (blank C out) packet
def padded (C : ℕ) (data : Fin 113→List Bool) :=
  fun i=>ZeroPadding.pad (CloseoutRowsBankCapacity.capacities C i) (data i)
noncomputable def machine := CloseoutRowsPacketLoad.machine (113 : Fin 114) 105 ports
def budget (data : Fin 113→List Bool) := CloseoutRowsPacketLoad.cost (fields data) ports

theorem heads_port (out : List Bool) (pos : ℕ) (j : Fin 110) : heads out pos (port j)=0 := by
  simp only [heads,extend,port,Fin.addCases_left,zeroHeads,(work_avoids j).1,↓reduceIte]

theorem tapes_port (C : ℕ) (out packet : List Bool) (j : Fin 110) :
    tapes C out packet (port j)=List.replicate C false := by
  simp only [tapes,extend,port,Fin.addCases_left,blank,(work_avoids j).1,
    (work_avoids j).2.1,(work_avoids j).2.2,↓reduceIte]

theorem field_bound (C : ℕ) (data : Fin 113→List Bool)
    (hb : ∀ i,i≠31 → i≠105 → (data i).length ≤ C) :
    ∀ j∈ports,(fields data j).length ≤ C := by
  intro j hj
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
  simp only [fields,extend,port,Fin.addCases_left]
  exact hb (work i) (work_avoids i).1 (work_avoids i).2.2

theorem budget_bound (C : ℕ) (data : Fin 113→List Bool)
    (hb : ∀ i,i≠31 → i≠105 → (data i).length ≤ C) : budget data ≤ 110*(3*C+3) := by
  have h:=CloseoutRowsPacketLoad.cost_bound (fields data) ports C (field_bound C data hb)
  simpa only [budget,ports,List.length_map,List.length_finRange] using h

theorem written_tapes (C : ℕ) (out packet : List Bool) (data : Fin 113→List Bool)
    (ho : data 31=out) (hd : data 104=List.replicate C true)
    (hl : data 105=List.replicate (C+1) false) :
    CloseoutRowsPacketLoad.written (fields data) C ports (tapes C out packet)=
      extend (padded C data) packet := by
  funext i
  refine Fin.addCases (m:=113) (n:=1) (fun a=>?_) (fun a=>?_) i
  · rw [written_apply]
    simp only [tapes,fields,extend,Fin.addCases_left]
    by_cases h31 : a=31
    · subst a
      have hm : (31 : Fin 114)∉ports := by simp only [mem_ports,ne_eq,not_true_eq_false,false_and,not_false_eq_true]
      simp [hm,padded,blank,CloseoutRowsBankCapacity.capacities,ho]
    by_cases h104 : a=104
    · subst a
      have hm : (104 : Fin 114)∉ports := by simp [mem_ports]
      simp [hm,padded,blank,CloseoutRowsBankCapacity.capacities,hd,ZeroPadding.pad]
    by_cases h105 : a=105
    · subst a
      have hm : (105 : Fin 114)∉ports := by simp [mem_ports]
      simp [hm,padded,blank,CloseoutRowsBankCapacity.capacities,hl,ZeroPadding.pad]
    have hne (k : Fin 113) (hk : a≠k) : a.castAdd 1≠k.castAdd 1 := by
      intro he
      exact hk (Fin.ext (congrArg (fun x : Fin 114=>x.val) he))
    have h113 : a.castAdd 1≠(113 : Fin 114) := by
      intro he
      have hv:=congrArg (fun x : Fin 114=>x.val) he
      have ha:=a.isLt
      change a.val=113 at hv
      omega
    have hm : a.castAdd 1∈ports := mem_ports _ |>.mpr ⟨hne 31 h31,hne 104 h104,hne 105 h105,h113⟩
    simp only [hm,↓reduceIte,padded,CloseoutRowsBankCapacity.capacities,
      h31,h105,↓reduceIte]
  · fin_cases a
    rw [written_apply]
    have hm : (113 : Fin 114)∉ports := by simp [mem_ports]
    change (if (113 : Fin 114)∈ports then _ else packet)=packet
    simp only [hm,↓reduceIte]

theorem load_run (C : ℕ) (data : Fin 113→List Bool) (out pre tail : List Bool)
    (ho : data 31=out) (hd : data 104=List.replicate C true)
    (hl : data 105=List.replicate (C+1) false)
    (hb : ∀ i,i≠31 → i≠105 → (data i).length ≤ C) :
    ∃ r,runFrom machine (budget data)
      ⟨machine.start,heads out pre.length,tapes C out (pre++word data++tail)⟩=some r ∧
      r.final.heads=heads out (pre.length+(word data).length) ∧
      r.final.tapes=extend (padded C data) (pre++word data++tail) ∧
      r.steps ≤ 110*(3*C+3) := by
  obtain ⟨r,hr,rh,rt,rs⟩ := CloseoutRowsPacketLoad.list_run (113 : Fin 114) 105 ports
    (fields data) (by decide) ports_nodup (fun j hj=>(mem_ports j).mp hj |>.2.2.2)
    (fun j hj=>(mem_ports j).mp hj |>.2.2.1) pre tail C (C+1)
    (heads out pre.length) (tapes C out (pre++word data++tail)) rfl rfl
    (by intro j hj; obtain ⟨i,_,rfl⟩:=List.mem_map.mp hj; exact heads_port out pre.length i)
    rfl rfl (by intro j hj; obtain ⟨i,_,rfl⟩:=List.mem_map.mp hj; exact tapes_port C out _ i)
    (fun j hj=>(field_bound C data hb j hj).trans (Nat.le_succ _))
  refine ⟨r,hr,?_,rt.trans (written_tapes C out _ data ho hd hl),rs.le.trans (budget_bound C data hb)⟩
  rw [rh]
  funext i
  refine Fin.addCases (m:=113) (n:=1) (fun a=>?_) (fun a=>?_) i
  · have hne : a.castAdd 1≠(113 : Fin 114) := by
      intro he
      have hv:=congrArg (fun x : Fin 114=>x.val) he
      have ha:=a.isLt
      change a.val=113 at hv
      omega
    rw [Function.update_of_ne hne]
    simp only [heads,extend,Fin.addCases_left]
  · fin_cases a
    rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsBankPacket
