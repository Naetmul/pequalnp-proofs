import PEqualNP.Defs

open scoped BigOperators

-- The dependency frontier follows R_meta_3254_719.
-- The incidence count follows R_meta_3254_1.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_5339_26
    (coreMass : ∀ (q N : ℕ) (E : Finset (Fin N × Fin N)) (A B : Finset (Fin N)),
      100 < q → N = q^2+q+1 →
      (∀ p r l k : Fin N, p ≠ r → l ≠ k →
        (p,l) ∈ E → (r,l) ∈ E → (p,k) ∈ E → (r,k) ∉ E) →
      B.Nonempty →
      (∀ p ∈ A, 12*q/25 < (B.filter fun l => (p,l) ∈ E).card) →
      (∀ l ∈ B, 12*q/25 < (A.filter fun p => (p,l) ∈ E).card) →
      N*q ≤ 10 * ((A.product B).filter fun e => e ∈ E).card)
    (charge : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I],
      let U := Fin N → Bool
      let m := N+N
      let one := fun p r : Fin N => decide (r=p)
      200 ≤ q → N = q^2+q+1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (W : ℕ → Set (U × U)),
        m ≤ s+1 → o < m+s → 100*s < N*q →
        (∀ p : Fin N, W p.val = {z | z.1 p = true} ∧ W (N+p.val) = {z | z.2 p = true}) →
        (∀ i < s, ∃ a b, max a b < m+i ∧ W (m+i) ∈ [W a ∪ W b, W a, ∅, W a ∩ W b]) →
        (∀ p l, I p l → (one p,one l) ∈ W o) →
        (∀ y : U, Fintype.card {l : Fin N // y l = true} ≤ q →
          ((fun p => decide (¬∃ l, I p l ∧ y l = true)),y) ∉ W o) →
        ∀ (E : Finset (Fin N × Fin N)),
          (∀ z ∈ E, I z.1 z.2) → N*(q+1) ≤ E.card+4*s →
          (∀ i < s, W (m+i) ⊆ W o → ∀ a b, max a b < m+i → W (m+i) = W a ∩ W b →
            ∀ P L : Set U, W a = P ×ˢ Set.univ → W b = Set.univ ×ˢ L →
            ∀ z ∈ E, (one z.1,one z.2) ∉ W (m+i)) →
          ∀ A B : Finset (Fin N), A.Nonempty → B.Nonempty →
            (∀ p ∈ A, 12*q/25 < (B.filter fun l => (p,l) ∈ E).card) →
            (∀ l ∈ B, 12*q/25 < (A.filter fun p => (p,l) ∈ E).card) →
            10*s < ((A.product B).filter fun e => e ∈ E).card → False) :
∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             have x12 : ℕ := x2 + x2;             have x13 : Fin x2 → Fin x2 → Bool := fun (x13 x14 : Fin x2) => Decidable.decide (x14 = x13);             have x14 : Set (Fin x2 × Fin x2) := {x14 : Fin x2 × Fin x2 | x3 x14.1 x14.2 ∧ ∃ x15 < x9, x11 (x12 + x15) ⊆ x11 x10 ∧ (x13 x14.1, x13 x14.2) ∈ x11 (x12 + x15) ∧ ∃ (x16 : ℕ) (x17 : ℕ), Max.max x16 x17 < x12 + x15 ∧ x11 (x12 + x15) = x11 x16 ∩ x11 x17 ∧ ∃ (x18 : Set (Fin x2 → Bool)) (x19 : Set (Fin x2 → Bool)), x11 x16 = x18 ×ˢ Set.univ ∧ x11 x17 = Set.univ ×ˢ x19};             x10 < x12 + x9 → (∀ (x16 : Fin x2), x11 ↑x16 = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.1 x16 = Bool.true} ∧ x11 (x2 + ↑x16) = {x17 : (Fin x2 → Bool) × (Fin x2 → Bool) | x17.2 x16 = Bool.true}) → (∀ x17 < x9, ∃ (x19 : ℕ) (x20 : ℕ), Max.max x19 x20 < x12 + x17 ∧ x11 (x12 + x17) ∈ [x11 x19 ∪ x11 x20, x11 x19, ∅, x11 x19 ∩ x11 x20]) → (∀ (x18 x19 : Fin x2), x3 x18 x19 → (x13 x18, x13 x19) ∈ x11 x10) → (∀ (x19 : Fin x2 → Bool), Fintype.card { x20 : Fin x2 // x19 x20 = Bool.true } ≤ x1 → (fun (x21 : Fin x2) => Decidable.decide ¬∃ (x22 : Fin x2), x3 x21 x22 ∧ x19 x22 = Bool.true, x19) ∉ x11 x10) → x14.ncard ≤ (4 : ℕ) * x9 → ∀ (x21 : Finset (Fin x2 × Fin x2)), (∀ (x22 : Fin x2 × Fin x2), x22 ∈ x21 ↔ x3 x22.1 x22.2 ∧ x22 ∉ x14) → ∀ (x23 x24 : Finset (Fin x2)), x23.Nonempty → x24.Nonempty → (∀ x27 ∈ x23, (12 : ℕ) * x1 / (25 : ℕ) < {x29 ∈ x24 | (x27, x29) ∈ x21}.card) → (∀ x28 ∈ x24, (12 : ℕ) * x1 / (25 : ℕ) < {x30 ∈ x23 | (x30, x28) ∈ x21}.card) → x2 * x1 ≤ (100 : ℕ) * x9 := by
  classical
  intro q N I _ hq hN hDegree hUnique s o W
  dsimp only
  intro hOut hBase hGate hPlus hMinus hFew E hE A B hA hB hrow hcol
  have hChoice (i : Fin s) : ∃ a b : ℕ,
      a < N + N + i.val ∧ b < N + N + i.val ∧
      (W (N + N + i.val) = W a ∪ W b ∨ W (N + N + i.val) = W a ∨
        W (N + N + i.val) = ∅ ∨ W (N + N + i.val) = W a ∩ W b) := by
    obtain ⟨a, b, hPrior, h⟩ := hGate i.val i.isLt
    obtain ⟨ha, hb⟩ := max_lt_iff.mp hPrior
    exact ⟨a, b, ha, hb, by simpa only [List.mem_cons, List.not_mem_nil, or_false] using h⟩
  choose a b hChoice using hChoice
  have frontier (k : ℕ) (hk : k ≤ s) (T : Finset ℕ) (hT : ∀ w ∈ T, w < N + N + k) :
      ∃ S : Finset ℕ, S.card ≤ T.card + k ∧ (∀ w ∈ S, w < N + N) ∧
        ∀ x y : (Fin N → Bool) × (Fin N → Bool),
          (∀ w ∈ S, x ∈ W w → y ∈ W w) →
          ∀ t ∈ T, x ∈ W t → y ∈ W t := by
    induction k generalizing T with
    | zero =>
      refine ⟨T, by simp, ?_, ?_⟩
      · intro w hw
        simpa using hT w hw
      · intro x y h t ht
        exact h t ht
    | succ k ih =>
      let w := N + N + k
      by_cases hw : w ∈ T
      · let i : Fin s := ⟨k, by omega⟩
        obtain ⟨ha, hb, hop⟩ := hChoice i
        change a i < w at ha
        change b i < w at hb
        change W w = W (a i) ∪ W (b i) ∨ W w = W (a i) ∨ W w = ∅ ∨
          W w = W (a i) ∩ W (b i) at hop
        let U := insert (a i) (insert (b i) (T.erase w))
        have hU : ∀ u ∈ U, u < N + N + k := by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact ha
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact hb
          obtain ⟨hne, hin⟩ := Finset.mem_erase.mp hu
          have hbound := hT u hin
          dsimp [w] at hne
          omega
        obtain ⟨S, hSize, hIn, hMove⟩ := ih (by omega) U hU
        have hCard : U.card ≤ T.card + 1 := by
          have h1 := Finset.card_insert_le (a i) (insert (b i) (T.erase w))
          have h2 := Finset.card_insert_le (b i) (T.erase w)
          rw [Finset.card_erase_of_mem hw] at h2
          have hpos := Finset.card_pos.mpr ⟨w, hw⟩
          dsimp [U]
          omega
        refine ⟨S, by omega, hIn, ?_⟩
        intro x y hs t ht hin
        by_cases he : t = w
        · subst t
          have A := hMove x y hs (a i) (by simp [U])
          have B := hMove x y hs (b i) (by simp [U])
          rcases hop with h | h | h | h
          · rw [h] at hin ⊢
            exact hin.imp A B
          · rw [h] at hin ⊢
            exact A hin
          · rw [h] at hin
            exact False.elim (Set.notMem_empty _ hin)
          · rw [h] at hin ⊢
            exact ⟨A hin.1, B hin.2⟩
        · exact hMove x y hs t (by simp [U, he, ht]) hin
      · have hU : ∀ u ∈ T, u < N + N + k := by
          intro u hu
          have hn : u ≠ w := fun e => hw (e ▸ hu)
          have hb := hT u hu
          dsimp [w] at hn
          omega
        obtain ⟨S, hSize, hIn, hMove⟩ := ih (by omega) T hU
        exact ⟨S, by omega, hIn, hMove⟩
  obtain ⟨S, hs, hS, hFlow⟩ := frontier s le_rfl {o} (by simpa using hOut)
  have preserve (bad : ℕ) (x y : (Fin N → Bool) × (Fin N → Bool))
      (hp : ∀ p : Fin N, p.val ≠ bad → x.1 p = true → y.1 p = true)
      (hl : ∀ l : Fin N, N + l.val ≠ bad → x.2 l = true → y.2 l = true)
      (hNo : bad ∉ S) :
      x ∈ W o → y ∈ W o := by
    apply hFlow x y ?_ o (by simp)
    intro w hw hx
    have hn : w ≠ bad := fun he => hNo (he ▸ hw)
    have hb := hS w hw
    by_cases hpw : w < N
    · let p : Fin N := ⟨w, hpw⟩
      rw [(hBase p).1] at hx ⊢
      exact hp p hn hx
    · let l : Fin N := ⟨w - N, by omega⟩
      have hL : N + l.val = w := by dsimp [l]; omega
      rw [← hL, (hBase l).2] at hx ⊢
      exact hl l (hL ▸ hn) hx
  have hPoint (p : Fin N) : ∃ l, I p l := by
    by_cases hp : p.val = 0
    · let r : Fin N := ⟨1, by omega⟩
      have hpr : p ≠ r := by intro he; have hv := congrArg Fin.val he; change p.val = 1 at hv; omega
      obtain ⟨l, h, _⟩ := hUnique p r hpr
      exact ⟨l, h.1⟩
    · let r : Fin N := ⟨0, by omega⟩
      have hpr : p ≠ r := by intro he; have hv := congrArg Fin.val he; change p.val = 0 at hv; omega
      obtain ⟨l, h, _⟩ := hUnique p r hpr
      exact ⟨l, h.1⟩
  have hLine (l : Fin N) : ∃ p, I p l := by
    have hn : Nonempty {p : Fin N // I p l} := Fintype.card_pos_iff.mp (by rw [hDegree l]; omega)
    obtain ⟨⟨p, hp⟩⟩ := hn
    exact ⟨p, hp⟩
  have hCover : Finset.range (N + N) ⊆ S := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    by_contra hn
    by_cases hpk : k < N
    · let p : Fin N := ⟨k, hpk⟩
      obtain ⟨l, hpl⟩ := hPoint p
      let z : Fin N → Bool := fun l' => decide (l' = l)
      let x : (Fin N → Bool) × (Fin N → Bool) := (fun p' => decide (p' = p), z)
      let y : (Fin N → Bool) × (Fin N → Bool) := (fun p' => decide (¬ ∃ l', I p' l' ∧ z l' = true), z)
      have cardZ : Fintype.card {l' : Fin N // z l' = true} ≤ q := by
        simpa [z] using (show 1 ≤ q by omega)
      apply hMinus z cardZ
      apply preserve k x y ?_ (fun _ _ h => h) hn (hPlus p l hpl)
      intro p' hNot' hYes
      change decide (p' = p) = true at hYes
      exact (hNot' (congrArg Fin.val (of_decide_eq_true hYes))).elim
    · let l : Fin N := ⟨k - N, by omega⟩
      obtain ⟨p, hpl⟩ := hLine l
      let z : Fin N → Bool := fun _ => false
      let x : (Fin N → Bool) × (Fin N → Bool) := (fun p' => decide (p' = p), fun l' => decide (l' = l))
      let y : (Fin N → Bool) × (Fin N → Bool) := (fun p' => decide (¬ ∃ l', I p' l' ∧ z l' = true), z)
      have cardZ : Fintype.card {l' : Fin N // z l' = true} ≤ q := by simp [z]
      apply hMinus z cardZ
      apply preserve k x y (by intro p' _ _; simp [y, z]) ?_ hn (hPlus p l hpl)
      intro l' hNot' hYes
      change decide (l' = l) = true at hYes
      have he : l' = l := of_decide_eq_true hYes
      apply (hNot' _).elim
      subst l'
      dsimp [l]
      omega
  have hRaw := Finset.card_le_card hCover
  rw [Finset.card_range] at hRaw
  simp only [Finset.card_singleton] at hs
  have hAll : N + N ≤ s + 1 := by omega
  by_cases hSmall : q < 200
  · have upper : N * q ≤ N * 199 := Nat.mul_le_mul_left N (by omega)
    have roomy : 100 ≤ N := by omega
    omega
  by_contra! small
  let one := fun (p r : Fin N) => decide (r=p)
  let m := N+N
  let pure : Set (Fin N × Fin N) := {z | I z.1 z.2 ∧ ∃ i < s, W (m+i) ⊆ W o ∧
    (one z.1,one z.2) ∈ W (m+i) ∧ ∃ a b, max a b < m+i ∧ W (m+i) = W a ∩ W b ∧
    ∃ P L : Set (Fin N → Bool), W a = P ×ˢ Set.univ ∧ W b = Set.univ ×ˢ L}
  change pure.ncard ≤ 4*s at hFew
  have memE (z : Fin N × Fin N) : z ∈ E ↔ I z.1 z.2 ∧ z ∉ pure := hE z
  have incid (z : Fin N × Fin N) (hz : z ∈ E) : I z.1 z.2 := (memE z).mp hz |>.1
  have noRect (p r l k : Fin N) (neP : p ≠ r) (neL : l ≠ k) (a : (p,l) ∈ E)
      (b : (r,l) ∈ E) (c : (p,k) ∈ E) : (r,k) ∉ E := by
    intro d
    exact neL ((hUnique p r neP).unique ⟨incid _ a,incid _ b⟩ ⟨incid _ c,incid _ d⟩)
  have coreSize := coreMass q N E A B hq hN noRect hB hrow hcol
  have coreBig : 10*s < ((A.product B).filter fun e => e ∈ E).card := by omega
  let edges := (Finset.univ : Finset (Fin N × Fin N)).filter fun e => I e.1 e.2
  have incidenceCount : edges.card = N*(q+1) := by
    have count (l : Fin N) : (edges.filter fun e => e.2 = l).card = q+1 := by
      rw [← hDegree l,Fintype.card_subtype]
      apply Finset.card_bij (fun e _ => e.1)
      · intro e he
        obtain ⟨he,hl⟩ := Finset.mem_filter.mp he
        have hI := (Finset.mem_filter.mp he).2
        simpa [hl] using hI
      · intro a ha b hb heq
        exact Prod.ext heq ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
      · intro p hp
        exact ⟨(p,l), by simpa [edges] using hp,rfl⟩
    calc
      edges.card = ∑ l : Fin N, (edges.filter fun e => e.2 = l).card := by
        symm
        simpa using Finset.sum_card_fiberwise_eq_card_filter edges (Finset.univ : Finset (Fin N)) Prod.snd
      _ = N*(q+1) := by simp [count]
  have full : edges ⊆ E ∪ pure.toFinset := by
    intro z hz
    by_cases hz' : z ∈ pure
    · exact Finset.mem_union_right E (Set.mem_toFinset.mpr hz')
    · exact Finset.mem_union_left _ ((memE z).mpr ⟨(Finset.mem_filter.mp hz).2,hz'⟩)
  have large := (Finset.card_le_card full).trans (Finset.card_union_le E pure.toFinset)
  rw [incidenceCount, ← Set.ncard_eq_toFinset_card'] at large
  apply charge q N I (by omega) hN hDegree hUnique s o W hAll hOut small hBase hGate hPlus hMinus
    E incid (by omega) ?_ A B hA hB hrow hcol coreBig
  intro i hi contained a b earlier meet P L left right z hz accepted
  exact ((memE z).mp hz).2 ⟨incid z hz, i, hi, contained, accepted, a, b, earlier, meet, P, L, left, right⟩
