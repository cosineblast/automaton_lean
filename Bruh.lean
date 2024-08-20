
/-
example : ∀ (L1 L2: List Unit), L1.length = L2.length → L1 = L2 := by

  have : ∀ n: Nat, ∀ (L1 L2: List Unit), L1.length = n → L1.length = L2.length → L1 = L2  :=  by
    intro k
    induction k

    case zero => 
      admit

    case succ n ih =>
      intro L1 L2 
      intros 

      show L1 = L2 

      have : L2.length = n + 1 := ‹L1.length = L2.length› ▸ ‹L1.length = n+1› 

      have : n + 1 > 0 := by simp
      have : L1.length > 0 := ‹L1.length = n+1› ▸ this
      let ⟨x1, r1, _⟩ := List.length_pos_iff_exists_cons.mp this

      have : r1.length = n := by 
        apply Eq.symm
        have := List.length_cons x1 r1
        rw [←‹L1 = x1 :: r1›] at this
        rw [‹L1.length = n + 1›] at this
        injection this

      have : n + 1 > 0 := by simp
      rw [←‹L2.length = n+1›] at this
      let ⟨x2, r2, _⟩ := List.length_pos_iff_exists_cons.mp this

      have : r2.length = n := by 
        apply Eq.symm
        have := List.length_cons x2 r2
        rw [←‹L2 = x2 :: r2›] at this
        rw [‹L2.length = n + 1›] at this
        injection this

      have : r1.length = r2.length := by simp [*]

      have : r1 = r2 := ih r1 r2 ‹r1.length = n› ‹r1.length = r2.length›
      simp [*]

  admit
  -/
