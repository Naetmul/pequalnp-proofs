import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

-- Neither junk AND has an AND ancestor. A traced uncovered edge therefore
-- has a raw endpoint on each of the two OR sides of its junk gate.
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_4901_54
  (products : ∀ (n : ℕ) (C : Circuit) (j : ℕ) (u v : Fin n),
    IsAO2 n C → j < C.size → (gateAt C j).op = .and →
    (∀ k < C.size, k ≠ j → InCone n C k j → (gateAt C k).op ≠ .and) →
    gateVal n C j (pairInput u v) = true →
    ∀ b : Fin 2, u ∈ side C j b ∨ v ∈ side C j b)
  (coverSeven : let G := edgeGraph 11 [(0,9), (0,10), (1,4), (1,8), (2,5), (2,10), (3,6), (3,7), (4,8), (4,10), (5,8), (5,9), (6,7), (6,10), (7,9), (8,9)]
  ∀ K : Finset (Fin 11), G.IsVertexCover (↑K : Set (Fin 11)) → 7 ≤ K.card)
  (charge : let G := edgeGraph 11 [(0,9), (0,10), (1,4), (1,8), (2,5), (2,10), (3,6), (3,7), (4,8), (4,10), (5,8), (5,9), (6,7), (6,10), (7,9), (8,9)]
    ∀ [DecidableRel G.Adj] (C : Circuit) (p q : ℕ),
      let U := Ustar G C
      let B := 2 * (centreless G C).card + 2 + (orN G C \ lam G C).card
      let K := InCone 11 C
      C.size ≤ 21 → IsLeastAO G C → TopForm G C → p < q → junk G C = {p,q} →
      ¬ K p q → ¬ K q p → (∀ a ∈ tops G C, K p a → ¬ K q a) →
      (∀ u v : Fin 11, s(u,v) ∈ U →
        ∃ a ∈ tops G C, ∃ (b : Fin 2), ∃ j ∈ junk G C,
          gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) j ∧
          ∀ i : Fin 2, u ∈ side C j i ∨ v ∈ side C j i) →
      3 ≤ U.card → B < 2 * U.card →
      ∃ T A : Finset (Fin 11), IsMinCover (G.deleteEdges ↑U) T ∧
        G.IsVertexCover (↑(T ∪ A)) ∧ A.card + U.card ≤ B) :
∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit) (x4 x5 : ℕ),   have x6 : Finset (Sym2 (Fin (11 : ℕ))) := PEqualNP.TopForm.Ustar x1 x3;   have x7 : Finset ℕ := PEqualNP.TopForm.centreless x1 x3;   have x8 : ℕ := (PEqualNP.TopForm.tops x1 x3 \ x7).card;   have x9 : ℕ := (PEqualNP.TopForm.orN x1 x3 \ PEqualNP.TopForm.lam x1 x3).card;   x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] → PEqualNP.TopForm.IsLeastAO x1 x3 → x4 < x5 → PEqualNP.TopForm.TopForm x1 x3 → PEqualNP.TopForm.junk x1 x3 = {x4, x5} → ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x5 → ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x5 x4 → (∀ x17 ∈ PEqualNP.TopForm.tops x1 x3, PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x4 x17 → ¬PEqualNP.EdgeOwnership.InCone (11 : ℕ) x3 x5 x17) → (∀ (x18 x19 : Fin (11 : ℕ)), s(x18, x19) ∈ x6 → ∃ x21 ∈ PEqualNP.TopForm.tops x1 x3, ∃ (x22 : Fin (2 : ℕ)) (x23 : ℕ), (x23 = x4 ∨ x23 = x5) ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x21 (PEqualNP.EdgeOwnership.pairInput x18 x19) = Bool.true ∧ PEqualNP.CleanedNonEdge.OrReaches (11 : ℕ) x3 (PEqualNP.TopForm.opnd x3 x21 x22) x23 ∧ PEqualNP.EdgeOwnership.gateVal (11 : ℕ) x3 x23 (PEqualNP.EdgeOwnership.pairInput x18 x19) = Bool.true) → (∀ (x19 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.NestedCover.IsMinCover (x1.deleteEdges ↑x6) x19 → x19.card ≤ x8) → (17 : ℕ) + x8 + (2 : ℕ) * x7.card + x9 ≤ x3.size + x6.card → (3 : ℕ) ≤ x6.card → (8 : ℕ) ≤ x8 + x6.card → (22 : ℕ) ≤ x3.size := by
  intro G inst C p q U Z T R graph least pq top exactJ noPQ noQP disjoint trace cover budget many profile
  by_contra short
  have sz : C.size ≤ 21 := by omega
  have inside (j : ℕ) (hj : j ∈ junk G C) :
      j < C.size ∧ (gateAt C j).op = .and := by
    obtain ⟨bound, h⟩ := Finset.mem_filter.mp hj
    exact ⟨Finset.mem_range.mp bound, h.1⟩
  have projected (u v : Fin 11) (h : s(u,v) ∈ U) :
      ∃ a ∈ tops G C, ∃ (b : Fin 2), ∃ j ∈ junk G C,
        gateVal 11 C a (pairInput u v) = true ∧ OrReaches 11 C (opnd C a b) j ∧
        ∀ i : Fin 2, u ∈ side C j i ∨ v ∈ side C j i := by
    obtain ⟨a, ha, b, j, isJ, hitTop, reach, hitJ⟩ := trace u v h
    have jIn : j ∈ junk G C := by
      rw [exactJ]
      simpa only [Finset.mem_insert, Finset.mem_singleton] using isJ
    obtain ⟨jlt, jAND⟩ := inside j jIn
    have onlyOR (k : ℕ) (hk : k < C.size) (ne : k ≠ j) (kj : InCone 11 C k j) :
        (gateAt C k).op ≠ .and := by
      intro kAND
      have dirty : ¬ BelowF G C k := fun below => top k hk j jlt kAND below jAND kj
      have falseRow : ∃ x, gateVal 11 C k x = true ∧ graphFun G ∅ x = false := by
        by_contra none
        apply dirty
        intro x hx
        by_contra bad
        exact none ⟨x,hx,Bool.eq_false_iff.mpr bad⟩
      have kIn : k ∈ junk G C :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, kAND, hk, falseRow⟩
      rw [exactJ] at kIn
      simp only [Finset.mem_insert, Finset.mem_singleton] at kIn
      rcases isJ with rfl | rfl <;> rcases kIn with rfl | rfl
      · exact ne rfl
      · exact noQP kj
      · exact noPQ kj
      · exact ne rfl
    exact ⟨a,ha,b,j,jIn,hitTop,reach,products 11 C j u v least.1 jlt jAND onlyOR hitJ⟩
  have budget' : 2 * Z.card + 2 + R < 2 * U.card := by omega
  subst G
  obtain ⟨K,A,hK,hFull,hA⟩ := charge C p q sz least top pq exactJ noPQ noQP disjoint
    projected many budget'
  have charged : A.card + U.card ≤ 2 * Z.card + 2 + R := hA
  have smallK : K.card ≤ T := cover K hK
  have large : 7 ≤ (K ∪ A).card := coverSeven (K ∪ A) hFull
  have sum := Finset.card_union_le K A
  omega
