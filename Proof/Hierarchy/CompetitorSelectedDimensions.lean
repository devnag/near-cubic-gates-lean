import Proof.Hierarchy.CompetitorSelectedCountBounds

/-! Actual production of every selector/SUM driver from raw Q, a short
additional scalar width, and the physical cell count. The long cell count
occurs only linearly in time and never inside the scalar bit width. -/
namespace NearCubicWires.RepairOrdinary.CompetitorSelectedDimensions
open LocalBitMultitape RecoveryRootRound CompetitorRationalProducts
open RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def qTemplateSlots : Fin 3 → Fin 17 := ![0,3,4]
noncomputable def qTemplate := RecoveryFocus.machine qTemplateSlots (DimensionTemplate.machine false)
def nTemplateSlots : Fin 3 → Fin 17 := ![2,5,6]
noncomputable def nTemplate := RecoveryFocus.machine nTemplateSlots (DimensionTemplate.machine false)
def productSlots : Fin 4 → Fin 17 := ![0,5,7,8]
noncomputable def product := RecoveryFocus.machine productSlots (ClockUnaryProduct.machine)
def bitTemplateSlots : Fin 3 → Fin 17 := ![7,9,10]
noncomputable def bitTemplate := RecoveryFocus.machine bitTemplateSlots (DimensionTemplate.machine false)
def zeroTemplateSlots : Fin 2 → Fin 17 := ![11,12]
noncomputable def zeroTemplate := RecoveryFocus.machine zeroTemplateSlots (HierarchyFixedWord.machine (UnaryTemplate.tape 0))
def oneTemplateSlots : Fin 2 → Fin 17 := ![13,14]
noncomputable def oneTemplate := RecoveryFocus.machine oneTemplateSlots (HierarchyFixedWord.machine (UnaryTemplate.tape 1))
def widthSumSlots : Fin 4 → Fin 17 := ![0,1,15,16]
noncomputable def widthSum := RecoveryFocus.machine widthSumSlots (ClockUnarySum.machine)
noncomputable def machine := Composition.machine qTemplate (Composition.machine nTemplate (Composition.machine product (Composition.machine bitTemplate (Composition.machine zeroTemplate (Composition.machine oneTemplate (widthSum))))))
def budget (Q M N : ℕ) := (2*Q+8)+1+((2*N+8)+1+((WilliamsUnaryProduct.budget Q N)+1+((2*(Q*N)+8)+1+((6)+1+((8)+1+(2*(Q+M)+6))))))

theorem word_ready (n : ℕ) : ClockJoin.ReadyRun
    (HierarchyFixedWord.machine (UnaryTemplate.tape n)) (2*n+6) (fun _ => [])
    ![UnaryTemplate.tape n,List.replicate (n+2) false] := by
  obtain ⟨r,hr,ht,hh,hs⟩ := HierarchyFixedWord.word_ready (UnaryTemplate.tape n)
  have hn : (UnaryTemplate.tape n).length=n+2 := by simp [UnaryTemplate.tape]
  simp only [hn] at hr ht hs
  have hc : 2*(n+2)+2=2*n+6 := by omega
  rw [hc] at hr hs
  exact ⟨r,hr,ht,hh,hs.le⟩

def data0 (Q M N : ℕ) : Fin 17 → List Bool :=
  ![List.replicate Q true,List.replicate M true,List.replicate N true,[],[],[],[],[],[],[],[],[],[],[],[],[],[]]
noncomputable def data1 (Q M N : ℕ) := install qTemplateSlots (data0 Q M N) (DimensionTemplate.output false Q)
noncomputable def data2 (Q M N : ℕ) := install nTemplateSlots (data1 Q M N) (DimensionTemplate.output false N)
noncomputable def data3 (Q M N : ℕ) := install productSlots (data2 Q M N) (WilliamsUnaryProduct.output Q N)
noncomputable def data4 (Q M N : ℕ) := install bitTemplateSlots (data3 Q M N) (DimensionTemplate.output false (Q*N))
noncomputable def data5 (Q M N : ℕ) := install zeroTemplateSlots (data4 Q M N) (![UnaryTemplate.tape 0,List.replicate 2 false])
noncomputable def data6 (Q M N : ℕ) := install oneTemplateSlots (data5 Q M N) (![UnaryTemplate.tape 1,List.replicate 3 false])
noncomputable def data7 (Q M N : ℕ) := install widthSumSlots (data6 Q M N) (CompetitorSameBucketGroupColdDimensions.sumOutput Q M)

theorem stage0_run (Q M N : ℕ) : ClockJoin.ReadyRun qTemplate
    (2*Q+8) (data0 Q M N) (data1 Q M N) := by
  exact bounded_focus qTemplateSlots (by decide) _ _ _ (DimensionTemplate.ready false Q) (data0 Q M N) (by
    intro i
    fin_cases i
    · rfl
    · rfl
    · rfl)

theorem stage1_run (Q M N : ℕ) : ClockJoin.ReadyRun nTemplate
    (2*N+8) (data1 Q M N) (data2 Q M N) := by
  exact bounded_focus nTemplateSlots (by decide) _ _ _ (DimensionTemplate.ready false N) (data1 Q M N) (by
    intro i
    fin_cases i
    · exact install_other qTemplateSlots _ _ _ (by decide)
    · exact install_other qTemplateSlots _ _ _ (by decide)
    · exact install_other qTemplateSlots _ _ _ (by decide))

theorem stage2_run (Q M N : ℕ) : ClockJoin.ReadyRun product
    (WilliamsUnaryProduct.budget Q N) (data2 Q M N) (data3 Q M N) := by
  exact bounded_focus productSlots (by decide) _ _ _ (CompetitorDimensions.unary_ready Q N) (data2 Q M N) (by
    intro i
    fin_cases i
    · exact (install_other nTemplateSlots _ _ _ (by decide)).trans (install_slot qTemplateSlots (by decide) _ _ 0)
    · exact install_slot nTemplateSlots (by decide) _ _ 1
    · exact (install_other nTemplateSlots _ _ _ (by decide)).trans (install_other qTemplateSlots _ _ _ (by decide))
    · exact (install_other nTemplateSlots _ _ _ (by decide)).trans (install_other qTemplateSlots _ _ _ (by decide)))

theorem stage3_run (Q M N : ℕ) : ClockJoin.ReadyRun bitTemplate
    (2*(Q*N)+8) (data3 Q M N) (data4 Q M N) := by
  exact bounded_focus bitTemplateSlots (by decide) _ _ _ (DimensionTemplate.ready false (Q*N)) (data3 Q M N) (by
    intro i
    fin_cases i
    · exact install_slot productSlots (by decide) _ _ 2
    · exact (install_other productSlots _ _ _ (by decide)).trans ((install_other nTemplateSlots _ _ _ (by decide)).trans (install_other qTemplateSlots _ _ _ (by decide)))
    · exact (install_other productSlots _ _ _ (by decide)).trans ((install_other nTemplateSlots _ _ _ (by decide)).trans (install_other qTemplateSlots _ _ _ (by decide))))

theorem stage4_run (Q M N : ℕ) : ClockJoin.ReadyRun zeroTemplate
    (6) (data4 Q M N) (data5 Q M N) := by
  exact bounded_focus zeroTemplateSlots (by decide) _ _ _ (word_ready 0) (data4 Q M N) (by
    intro i
    fin_cases i
    · exact (install_other bitTemplateSlots _ _ _ (by decide)).trans ((install_other productSlots _ _ _ (by decide)).trans ((install_other nTemplateSlots _ _ _ (by decide)).trans (install_other qTemplateSlots _ _ _ (by decide))))
    · exact (install_other bitTemplateSlots _ _ _ (by decide)).trans ((install_other productSlots _ _ _ (by decide)).trans ((install_other nTemplateSlots _ _ _ (by decide)).trans (install_other qTemplateSlots _ _ _ (by decide)))))

theorem stage5_run (Q M N : ℕ) : ClockJoin.ReadyRun oneTemplate
    (8) (data5 Q M N) (data6 Q M N) := by
  exact bounded_focus oneTemplateSlots (by decide) _ _ _ (word_ready 1) (data5 Q M N) (by
    intro i
    fin_cases i
    · exact (install_other zeroTemplateSlots _ _ _ (by decide)).trans ((install_other bitTemplateSlots _ _ _ (by decide)).trans ((install_other productSlots _ _ _ (by decide)).trans ((install_other nTemplateSlots _ _ _ (by decide)).trans (install_other qTemplateSlots _ _ _ (by decide)))))
    · exact (install_other zeroTemplateSlots _ _ _ (by decide)).trans ((install_other bitTemplateSlots _ _ _ (by decide)).trans ((install_other productSlots _ _ _ (by decide)).trans ((install_other nTemplateSlots _ _ _ (by decide)).trans (install_other qTemplateSlots _ _ _ (by decide))))))

theorem stage6_run (Q M N : ℕ) : ClockJoin.ReadyRun widthSum
    (2*(Q+M)+6) (data6 Q M N) (data7 Q M N) := by
  exact bounded_focus widthSumSlots (by decide) _ _ _ (CompetitorSameBucketGroupColdDimensions.sum_ready Q M) (data6 Q M N) (by
    intro i
    fin_cases i
    · exact (install_other oneTemplateSlots _ _ _ (by decide)).trans ((install_other zeroTemplateSlots _ _ _ (by decide)).trans ((install_other bitTemplateSlots _ _ _ (by decide)).trans (install_slot productSlots (by decide) _ _ 0)))
    · exact (install_other oneTemplateSlots _ _ _ (by decide)).trans ((install_other zeroTemplateSlots _ _ _ (by decide)).trans ((install_other bitTemplateSlots _ _ _ (by decide)).trans ((install_other productSlots _ _ _ (by decide)).trans ((install_other nTemplateSlots _ _ _ (by decide)).trans (install_other qTemplateSlots _ _ _ (by decide))))))
    · exact (install_other oneTemplateSlots _ _ _ (by decide)).trans ((install_other zeroTemplateSlots _ _ _ (by decide)).trans ((install_other bitTemplateSlots _ _ _ (by decide)).trans ((install_other productSlots _ _ _ (by decide)).trans ((install_other nTemplateSlots _ _ _ (by decide)).trans (install_other qTemplateSlots _ _ _ (by decide))))))
    · exact (install_other oneTemplateSlots _ _ _ (by decide)).trans ((install_other zeroTemplateSlots _ _ _ (by decide)).trans ((install_other bitTemplateSlots _ _ _ (by decide)).trans ((install_other productSlots _ _ _ (by decide)).trans ((install_other nTemplateSlots _ _ _ (by decide)).trans (install_other qTemplateSlots _ _ _ (by decide)))))))

theorem dimensions_run (Q M N : ℕ) : ClockJoin.ReadyRun machine (budget Q M N)
    (data0 Q M N) (data7 Q M N) := by
  have h6 := stage6_run Q M N
  have h5 := ClockJoin.join _ _ _ _ _ _ _ (stage5_run Q M N) h6
  have h4 := ClockJoin.join _ _ _ _ _ _ _ (stage4_run Q M N) h5
  have h3 := ClockJoin.join _ _ _ _ _ _ _ (stage3_run Q M N) h4
  have h2 := ClockJoin.join _ _ _ _ _ _ _ (stage2_run Q M N) h3
  have h1 := ClockJoin.join _ _ _ _ _ _ _ (stage1_run Q M N) h2
  have h0 := ClockJoin.join _ _ _ _ _ _ _ (stage0_run Q M N) h1
  exact h0

def outputSlots : Fin 7 → Fin 17 := ![0,3,5,9,11,13,15]
def outputWords (Q M N : ℕ) : Fin 7 → List Bool :=
  ![List.replicate Q true,UnaryTemplate.tape Q,UnaryTemplate.tape N,UnaryTemplate.tape (Q*N),
    UnaryTemplate.tape 0,UnaryTemplate.tape 1,List.replicate (Q+M) true]

theorem output_read (Q M N : ℕ) (i : Fin 7) : data7 Q M N (outputSlots i)=outputWords Q M N i := by
  fin_cases i
  · exact install_slot widthSumSlots (by decide) _ _ 0
  · exact (install_other widthSumSlots _ _ _ (by decide)).trans ((install_other oneTemplateSlots _ _ _ (by decide)).trans ((install_other zeroTemplateSlots _ _ _ (by decide)).trans ((install_other bitTemplateSlots _ _ _ (by decide)).trans ((install_other productSlots _ _ _ (by decide)).trans ((install_other nTemplateSlots _ _ _ (by decide)).trans (install_slot qTemplateSlots (by decide) _ _ 1))))))
  · exact (install_other widthSumSlots _ _ _ (by decide)).trans ((install_other oneTemplateSlots _ _ _ (by decide)).trans ((install_other zeroTemplateSlots _ _ _ (by decide)).trans ((install_other bitTemplateSlots _ _ _ (by decide)).trans (install_slot productSlots (by decide) _ _ 1))))
  · exact (install_other widthSumSlots _ _ _ (by decide)).trans ((install_other oneTemplateSlots _ _ _ (by decide)).trans ((install_other zeroTemplateSlots _ _ _ (by decide)).trans (install_slot bitTemplateSlots (by decide) _ _ 1)))
  · exact (install_other widthSumSlots _ _ _ (by decide)).trans ((install_other oneTemplateSlots _ _ _ (by decide)).trans (install_slot zeroTemplateSlots (by decide) _ _ 0))
  · exact (install_other widthSumSlots _ _ _ (by decide)).trans (install_slot oneTemplateSlots (by decide) _ _ 0)
  · exact install_slot widthSumSlots (by decide) _ _ 2

end NearCubicWires.RepairOrdinary.CompetitorSelectedDimensions
