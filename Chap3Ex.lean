import HTPILib.Chap3
namespace HTPI.Exercises

/- Sections 3.1 and 3.2 -/
-- 1.
theorem Exercise_3_2_1a (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → R) : P → R := by
  -- assume h3 : P
  -- have h4 : Q := h1 h3
  -- show R from h2 h4
  assume hP
  apply h2
  apply h1
  show P from hP
  done

-- 2.
theorem Exercise_3_2_1b (P Q R : Prop)
    (h1 : ¬R → (P → ¬Q)) : P → (Q → R) := by
  -- assume h2 : P
  -- contrapos
  -- assume h3 : ¬R
  -- show ¬Q from h1 h3 h2
  assume hP
  assume hQ
  contradict hQ with h!R
  show ¬Q from h1 h!R hP
  done

-- 3.
theorem Exercise_3_2_2a (P Q R : Prop)
    (h1 : P → Q) (h2 : R → ¬Q) : P → ¬R := by
  assume hP
  contrapos at h2
  show ¬R from h2 (h1 hP)
  done

-- 4.
theorem Exercise_3_2_2b (P Q : Prop)
    (h1 : P) : Q → ¬(Q → ¬P) := by
  contrapos
  assume h2 : Q → ¬P
  contrapos at h2
  show ¬Q from h2 h1
  done

/- Section 3.3 -/
-- 1.
theorem Exercise_3_3_1
    (U : Type) (P Q : Pred U) (h1 : ∃ (x : U), P x → Q x) :
    (∀ (x : U), P x) → ∃ (x : U), Q x := by

  -- Solution 1
  -- obtain (a : U) (h1' : P a → Q a) from h1
  -- assume h3 : (∀ (x : U), P x)
  -- have h4 : P a := h3 a
  -- have h5 : Q a := h1' h4
  -- exact Exists.intro a h5

  -- Solution 2
  assume h
  obtain a PaQa from h1
  have hQ := PaQa (h a)
  apply Exists.intro a
  show Q a from hQ
  done

theorem Example_3_3_5 (U : Type) (B : Set U)
    (F : Set (Set U)) : ⋃₀ F ⊆ B → F ⊆ 𝒫 B := by
  assume h1 : ⋃₀ F ⊆ B
  define
  fix x : Set U
  assume h2 : x ∈ F
  define
  fix y : U
  assume h3: y ∈ x
  define at h1
  apply h1 _
  define
  apply Exists.intro x
  exact And.intro h2 h3
  done
-- 2.
theorem Exercise_3_3_8 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  define
  fix a
  assume h2 : a ∈ A
  define
  apply Exists.intro A

  -- Can use \langle ... \rangle instead of And.intro
  show A ∈ F ∧ a ∈ A from ⟨h1, h2⟩
  done

-- 3.
theorem Exercise_3_3_9 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  define
  fix a : U
  assume h2 : a ∈ ⋂₀ F
  define at h2
  show a ∈ A from (h2 A) h1
  done

-- 4.
theorem Exercise_3_3_10 (U : Type) (B : Set U) (F : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → B ⊆ A) : B ⊆ ⋂₀ F := by
  fix a : U
  assume h2 : a ∈ B
  define
  fix S : Set U
  assume h3 : S ∈ F
  have h4 : B ⊆ S := h1 S h3
  show a ∈ S from h4 h2
  done

-- 5.
theorem Exercise_3_3_13 (U : Type)
    (F G : Set (Set U)) : F ⊆ G → ⋂₀ G ⊆ ⋂₀ F := by
  assume h1 : F ⊆ G
  fix x : U
  assume h2 : x ∈ ⋂₀G
  fix A : Set U
  assume h3 : A ∈ F
  define at h2

  -- apply h2
  -- apply h1
  -- exact h3

  exact h2 A (h1 h3)
  done

/- Section 3.4 -/
-- 1.
theorem Exercise_3_4_2 (U : Type) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  define
  fix x
  assume xA : x ∈ A
  define
  define at h1
  define at h2
  have xB : x ∈ B := h1 xA
  have xC : x ∈ C := h2 xA
  exact And.intro xB xC
  done

-- 2.
theorem Exercise_3_4_4 (U : Type) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : A ⊈ C) : B ⊈ C := by
  define
  define at h1
  define at h2
  quant_neg at h2
  obtain (x : U) (h2' : ¬(x ∈ A → x ∈ C)) from h2
  conditional at h2'
  have xA : x ∈ A := And.left h2'
  have x!C : x ∉ C := And.right h2'
  have xB := h1 xA
  quant_neg
  apply Exists.intro x _
  conditional
  exact And.intro xB x!C
  done

-- 3.
theorem Exercise_3_3_16 (U : Type) (B : Set U)
    (F : Set (Set U)) : F ⊆ 𝒫 B → ⋃₀ F ⊆ B := by
  assume h
  define
  fix x : U
  assume hUF
  define at h
  define at hUF
  obtain b hb from hUF
  have bPB := h hb.left
  define at bPB
  have xB := bPB hb.right
  show x ∈ B from xB
  done

-- 4.
theorem Exercise_3_3_17 (U : Type) (F G : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → ∀ (B : Set U), B ∈ G → A ⊆ B) :
    ⋃₀ F ⊆ ⋂₀ G := by
  define
  fix a : U
  assume aUF : a ∈ ⋃₀ F
  define at aUF
  obtain t ht from aUF
  have h4 : ∀ (B : Set U), B ∈ G → t ⊆ B := h1 t ht.left
  define
  fix p : Set U
  assume pG
  have h5 := h4 p pG
  exact h5 ht.right
  done

-- 5.
theorem Exercise_3_4_7 (U : Type) (A B : Set U) :
    𝒫 (A ∩ B) = 𝒫 A ∩ 𝒫 B := by
  ext S
  apply Iff.intro
  · assume h1 : S ∈ 𝒫 (A ∩ B)
    define at h1
    define
    apply And.intro
    · define
      fix a
      assume aS : a ∈ S
      exact (h1 aS).left
    · define
      fix a
      assume aS : a ∈ S
      exact (h1 aS).right
    done
  · assume h1 : S ∈ 𝒫 A ∩ 𝒫 B
    fix a : U
    assume aS : a ∈ S

    exact ⟨h1.left aS, h1.right aS⟩
    done
  done

-- 6.
theorem Exercise_3_4_17 (U : Type) (A : Set U) : A = ⋃₀ (𝒫 A) := by
  ext c
  apply Iff.intro
  · assume h1 : c ∈ A
    define
    apply Exists.intro A
    apply And.intro
    · define
      fix a
      assume h2
      exact h2
    exact h1
    done
  · assume h1 : c ∈ ⋃₀ (𝒫 A)
    define at h1
    obtain t h2 from h1
    exact h2.left h2.right
    done
  done

-- 7.
theorem Exercise_3_4_18a (U : Type) (F G : Set (Set U)) :
    ⋃₀ (F ∩ G) ⊆ (⋃₀ F) ∩ (⋃₀ G) := by
  define
  fix s : U
  assume h1
  define at h1
  define
  obtain S hS from h1

  apply And.intro
  · define
    have hh := hS.left.left
    apply Exists.intro S
    exact ⟨hh, hS.right⟩
  · define
    have hh := hS.left.right
    apply Exists.intro S
    exact ⟨hh, hS.right⟩
  done

-- 8.
theorem Exercise_3_4_19 (U : Type) (F G : Set (Set U)) :
    (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) ↔
      ∀ (A B : Set U), A ∈ F → B ∈ G → A ∩ B ⊆ ⋃₀ (F ∩ G) := by

  done

/- Section 3.5 -/
-- 1.
theorem Exercise_3_5_2 (U : Type) (A B C : Set U) :
    (A ∪ B) \ C ⊆ A ∪ (B \ C) := by
  define
  fix x : U
  assume h1
  define
  define at h1
  by_cases on h1.left
  ·
    apply Or.inl
    show x ∈ A from this
  ·
    apply Or.inr
    show x ∈ B \ C from ⟨this, h1.right⟩

-- 2.
theorem Exercise_3_5_5 (U : Type) (A B C : Set U)
    (h1 : A ∩ C ⊆ B ∩ C) (h2 : A ∪ C ⊆ B ∪ C) : A ⊆ B := by
  intro x
  assume xA : x ∈ A
  have xAuC : x ∈ A ∪ C := Or.inl xA
  have xBuC : x ∈ B ∪ C := h2 xAuC

  by_cases on xBuC
  · exact xBuC
  · exact (h1 ⟨xA, xBuC⟩).left
  done

-- 3.
theorem Exercise_3_5_7 (U : Type) (A B C : Set U) :
    A ∪ C ⊆ B ∪ C ↔ A \ C ⊆ B \ C := by
  apply Iff.intro
  · assume h1 : A ∪ C ⊆ B ∪ C
    intro x
    assume xAmC : x ∈ A \ C
    define

    have xA : x ∈ A := xAmC.left
    have x!C : x ∉ C := xAmC.right
    have xAuC : x ∈ A ∪ C := Or.inl xA
    have xBuC : x ∈ B ∪ C := h1 xAuC

    by_cases on xBuC
    · exact ⟨xBuC, x!C⟩
    · by_contra
      show False from x!C xBuC
    done
  · assume h1 : A\C ⊆ B\C
    intro x
    assume xAuC : x ∈ A ∪ C
    or_left with x!C
    by_cases on xAuC
    · exact (h1 ⟨xAuC, x!C⟩).left
    · by_contra
      show False from x!C xAuC
    done
  done

-- 4.
theorem Exercise_3_5_8 (U : Type) (A B : Set U) :
    𝒫 A ∪ 𝒫 B ⊆ 𝒫 (A ∪ B) := sorry

-- 5.
theorem Exercise_3_5_17b (U : Type) (F : Set (Set U)) (B : Set U) :
    B ∪ (⋂₀ F) = {x : U | ∀ (A : Set U), A ∈ F → x ∈ B ∪ A} := sorry

-- 6.
theorem Exercise_3_5_18 (U : Type) (F G H : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → ∀ (B : Set U), B ∈ G → A ∪ B ∈ H) :
    ⋂₀ H ⊆ (⋂₀ F) ∪ (⋂₀ G) := sorry

-- 7.
theorem Exercise_3_5_24a (U : Type) (A B C : Set U) :
    (A ∪ B) △ C ⊆ (A △ C) ∪ (B △ C) := sorry

/- Section 3.6 -/
-- 1.
theorem Exercise_3_4_15 (U : Type) (B : Set U) (F : Set (Set U)) :
    ⋃₀ {X : Set U | ∃ (A : Set U), A ∈ F ∧ X = A \ B}
      ⊆ ⋃₀ (F \ 𝒫 B) := sorry

-- 2.
theorem Exercise_3_5_9 (U : Type) (A B : Set U)
    (h1 : 𝒫 (A ∪ B) = 𝒫 A ∪ 𝒫 B) : A ⊆ B ∨ B ⊆ A := by
  --Hint:  Start like this:
  have h2 : A ∪ B ∈ 𝒫 (A ∪ B) := sorry
  done

/- Section 3.6 -/
theorem empty_union {U : Type} (B : Set U) :
    ∅ ∪ B = B := by
  apply Set.ext
  fix x : U
  apply Iff.intro
  · -- (→)
    assume h1 : x ∈ ∅ ∪ B
    define at h1
    have h2 : x ∉ ∅ := by
      by_contra h3
      define at h3  --h3 : False
      show False from h3
      done
    disj_syll h1 h2  --h1 : x ∈ B
    show x ∈ B from h1
    done
  · -- (←)
    assume h1 : x ∈ B
    show x ∈ ∅ ∪ B from Or.inr h1
    done
  done

-- 3.
theorem Exercise_3_6_6b (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U), A ∪ B = A := sorry

-- 4.
theorem Exercise_3_6_7b (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U), A ∩ B = A := sorry

-- 5.
theorem Exercise_3_6_8a (U : Type) : ∀ (A : Set U),
    ∃! (B : Set U), ∀ (C : Set U), C \ A = C ∩ B := sorry

-- 6.
theorem Exercise_3_6_10 (U : Type) (A : Set U)
    (h1 : ∀ (F : Set (Set U)), ⋃₀ F = A → A ∈ F) :
    ∃! (x : U), x ∈ A := by
  --Hint:  Start like this:
  set F0 : Set (Set U) := {X : Set U | X ⊆ A ∧ ∃! (x : U), x ∈ X}
  --Now F0 is in the tactic state, with the definition above
  have h2 : ⋃₀ F0 = A := sorry

  done

/- Section 3.7 -/
-- 1.
theorem Exercise_3_3_18a (a b c : Int)
    (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ (b + c) := by
  define
  define at h1
  define at h2

  obtain (k : ℤ) (hk : b = a * k) from h1
  obtain (j : ℤ) (hj : c = a * j) from h2

  apply Exists.intro (k + j)
  rw [mul_add, ← hk, ← hj]
  done

-- 2.
theorem Exercise_3_4_6 (U : Type) (A B C : Set U) :
    A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  apply Set.ext
  fix x : U
  show x ∈ A \ (B ∩ C) ↔ x ∈ A \ B ∪ A \ C from
    calc x ∈ A \ (B ∩ C)
      _ ↔ x ∈ A ∧ ¬(x ∈ B ∧ x ∈ C) := sorry
      _ ↔ x ∈ A ∧ (x ∉ B ∨ x ∉ C) := sorry
      _ ↔ (x ∈ A ∧ x ∉ B) ∨ (x ∈ A ∧ x ∉ C) := sorry
      _ ↔ x ∈ (A \ B) ∪ (A \ C) := sorry
  done

-- 3.
theorem Exercise_3_4_10 (x y : Int)
    (h1 : odd x) (h2 : odd y) : even (x - y) := by
-- define
-- define at h1
-- define at h2

obtain (k : ℤ) (hk : x = 2*k + 1) from h1
obtain (j : ℤ) (hj : y = 2*j + 1) from h2

apply Exists.intro (k-j)

rw [hk, hj]

ring!
done

-- 4.
theorem Exercise_3_4_27a :
    ∀ (n : Int), 15 ∣ n ↔ 3 ∣ n ∧ 5 ∣ n := sorry

-- 5.
theorem Like_Exercise_3_7_5 (U : Type) (F : Set (Set U))
    (h1 : 𝒫 (⋃₀ F) ⊆ ⋃₀ {𝒫 A | A ∈ F}) :
    ∃ (A : Set U), A ∈ F ∧ ∀ (B : Set U), B ∈ F → B ⊆ A := sorry
